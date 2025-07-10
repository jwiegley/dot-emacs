;;; org-ql-ext --- Extra functions for use with Org-ql -*- lexical-binding: t -*-

;; Copyright (C) 2024 John Wiegley

;; Author: John Wiegley <johnw@gnu.org>
;; Created: 9 Apr 2023
;; Version: 1.0
;; Keywords: org capture task todo context
;; X-URL: https://github.com/jwiegley/dot-emacs

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2, or (at
;; your option) any later version.

;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;;; Code:

(require 'cl-lib)
(eval-when-compile
  (require 'cl)
  (require 'cl-macs))

(require 'org)
(require 'org-ext)
(require 'org-ql)
(require 'org-ql-find)

(org-ql-defpred keyword (&rest keywords)
  "Search for entries about any of NAMES."
  :body (cl-loop
         for kw in keywords
         thereis (member kw (split-string
                             (or (org-entry-get (point) "KEYWORDS") "")))))

(org-ql-defpred shown ()
  "Whether this entry is not marked as HIDE."
  :body (not (org-entry-get (point) "HIDE")))

(org-ql-defpred about (&rest keywords)
  "Whether this entry is \"about\" the given keyword.
   This means checking if it's in the tags or CATEGORY."
  :body (cl-loop for kw in keywords
                 thereis (or (member kw (org-get-tags (point)))
                             (string= kw (org-get-category (point))))))

(org-ql-defpred tasks-for (&rest who)
  "True if this task is assigned to, or related to, anyone in WHO."
  :body (and (apply #'org-ql--predicate-about who)
             (org-ql--predicate-todo)
             (org-ql--predicate-shown)
             ))

(org-ql-defpred refile-target ()
  "Return non-nil if entry is a refile target."
  :body (org-ext-refile-heading-p))

(org-ql-defpred property-ts (property &key from to _on regexp _with-time args)
  "Match timestamps in property value."
  :normalizers ((`(,predicate-names ,property . ,rest)
                 `(property-ts ,property
                               ,@(org-ql--normalize-from-to-on
                                   `(:from ,from :to ,to)))))
  :body (when-let ((value (org-entry-get (point) property))
                   (ts (ignore-errors
                         (ts-parse-org value))))
          (cond ((not (or from to)) ts)
                ((and from to) (ts-in from to ts))
                (from (ts<= from ts))
                (to (ts<= ts to)))))

(defvar org-ql-ext-heading-to-id (make-hash-table :test 'equal))

(defun org-ql-ext-completions-at-point ()
  "Function to be used as `completion-at-point' in Org mode."
  (when (looking-back "@\\(\\(?:\\sw\\|\\s_\\|\\s-\\|\\s-:\\)+\\)" nil)
    (let* ((start (match-beginning 1))
           (end (point))
           (input (match-string-no-properties 1))
           (candidates
            (org-ql-select
              (org-agenda-files)
              (org-ql--query-string-to-sexp input)
              :action (lambda ()
                        (let* ((heading (org-get-heading t t))
                               (id (org-id-get (point))))
                          ;; Avoid having to look up the ID again since we
                          ;; are visiting all the locations with org-ql
                          ;; anyway
                          (puthash heading id org-ql-ext-heading-to-id)
                          heading))))
           (exit-function
            (lambda (heading status)
              (when (eq status 'finished)
                ;; The +1 removes the @ symbol
                (delete-char (- (+ (length heading) 1)))
                (insert
                 (format "[[id:%s][%s]]"
                         (gethash heading org-ql-ext-heading-to-id)
                         heading))))))
      (list start end candidates :exit-function exit-function))))

(defun org-ql-ext-completion-hook ()
  "Configure org-mode for completion at point for org-agenda headlines."
  (add-to-list 'completion-at-point-functions
               'org-ql-ext-completions-at-point))

(defun org-ql-ext-find-refile-targets ()
  (interactive)
  (let ((query-prefix "refile-target: ")
        current-prefix-arg)
    (cond
     ((eq major-mode 'dired-mode)
      (let ((org-ql-search-directories-files-recursive t))
        (org-ql-find (org-ql-search-directories-files
                      :directories (list org-directory))
                     :query-prefix query-prefix)))
     ((eq major-mode 'org-mode)
      (org-ql-find (org-ql-find--buffers)))
     (t
      (org-ql-find (org-agenda-files)
                   :query-prefix query-prefix)))))

(cl-defun org-ext-ql-columnview (&key (properties "TODO ITEM_BY_ID TAGS")
                                      sort sort-ts query who review-by
                                      &allow-other-keys)
  "Create a table view of an org-ql query.
For example:

#+begin: ql-columnview :query \"(todo)\" :properties \"TODO ITEM_BY_ID\"
#+end:

PROPERTIES, if provided, is a space-separated list of Org
properties (whether special or explicit) to be included, each as a
column, in the report. ITEM_BY_ID is accepted as a special case, which
is morally the same as [[id:ID][ITEM]].

SORT takes the 1-indexed column mentioned in PROPERTIES, and sorts that
column, ascending.

SORT-TS takes the 1-indexed column mentioned in PROPERTIES, interprets
it as an Org-time, and sorts the resulting table on that column,
ascending.

QUERY is any Org-ql query expression.

WHO is a |-separated string of names that will expand to a `tasks-for'
Org-ql query, which must be defined.

REVIEW-BY takes a date, and only includes those entries whose
NEXT_REVIEW date is <= that date."
  (let* ((columns (split-string properties " "))
         (query
          `(and (not (or (org-ext-project-p)
                         (org-ext-category-p)))

                ;; Handle :query and :who keywords
                ,(let ((topics (and (stringp who)
                                    (split-string who "|"))))
                   (when topics
                     (setq who
                           (concat "(tasks-for"
                                   (mapconcat
                                    (apply-partially #'format " \"%s\"")
                                    topics)
                                   ")")))
                   (read (if (and query who)
                             (format "(or %s %s)" who query)
                           (or query who))))

                ;; Handle :review-by keyword
                ,(if review-by
                     (read (format
                            "(property-ts \"NEXT_REVIEW\" :to \"%s\")"
                            review-by))
                   t)))
         (table
          (org-ql-select 'org-agenda-files query
            :action `(org-ext-get-properties ,@columns)
            :sort
            #'(lambda (x y)
                (cond
                 (sort-ts
                  (let ((x-value (nth sort-ts x))
                        (y-value (nth sort-ts y)))
                    (when (and x-value y-value)
                      (time-less-p
                       (org-encode-time
                        (org-parse-time-string x-value))
                       (org-encode-time
                        (org-parse-time-string y-value))))))
                 (sort
                  (let ((x-value (nth sort x))
                        (y-value (nth sort y)))
                    (string-lessp (or x-value "")
                                  (or y-value "")))))))))
    ;; Add column titles and a horizontal rule in front of the table.
    (setq table (cons columns (cons 'hline table)))
    (let ((hlines nil)
          new-table)
      ;; Copy header and first rule.
      (push (pop table) new-table)
      (push (pop table) new-table)
      (dolist (row table (setq table (nreverse new-table)))
        (let ((level (car row)))
	  (when (and (not (eq (car new-table) 'hline))
		     (or (eq hlines t)
			 (and (numberp hlines) (<= level hlines))))
	    (push 'hline new-table))
	  (push (cdr row) new-table))))
    (save-excursion
      ;; Insert table at point.
      (insert
       (mapconcat (lambda (row)
		    (if (eq row 'hline) "|-|"
		      (format "|%s|" (mapconcat #'identity row "|"))))
		  table
		  "\n")))
    (org-table-align)))

(defsubst org-dblock-write:ql-columnview (params)
  "Create a table view of an org-ql query using PARAMS.
See `org-ext-ql-columnview'."
  (apply #'org-ext-ql-columnview params))

(provide 'org-ql-ext)

;;; org-ql-ext.el ends here
