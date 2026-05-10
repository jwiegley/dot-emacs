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
  :body (cl-loop for tags = (org-get-tags (point))
                 for kw in keywords
                 thereis
                 (or (member kw tags)
                     (string= kw (org-get-category (point))))))

(org-ql-defpred tasks-for (&rest who)
  "True if this task is assigned to, or related to, anyone in WHO."
  :body (and (apply #'org-ql--predicate-about who)
             (org-ql--predicate-todo)
             (org-ql--predicate-shown)))

(org-ql-defpred refile-target ()
  "Return non-nil if entry is a refile target."
  :body (org-ext-refile-heading-p))

(defcustom org-ql-ext-verb-regexp
  "\\`\\(?:([^)]+)[[:space:]]+\\)*\\([[:alpha:]]+\\):[[:space:]]"
  "Regular expression matching headings whose title begins with a \"verb\".
The first capture group must hold the verb itself.  The default matches
zero or more `(Name)' prefixes followed by a single alphabetic word, a
colon, and whitespace, e.g. `Review: Foo' or `(Nikhil) Read: Bar'."
  :type 'regexp
  :group 'org-ql)

(defun org-ql-ext-heading-verb (&optional title)
  "Return the verb at the start of an Org heading title, or nil.
TITLE, if given, is matched directly; otherwise the title of the
entry at point is used (as returned by `org-get-heading').  Any
Org links in the title are first replaced with their description
via `org-link-display-format' so titles like
`[[id:abc][Review: Foo]]' are matched correctly.  The returned
verb is normalized with `capitalize' for stable display."
  (when-let* ((title (or title (org-get-heading t t t t)))
              ((stringp title))
              (text (org-link-display-format title))
              ((string-match org-ql-ext-verb-regexp text)))
    (capitalize (match-string 1 text))))

(org-ql-defpred verb (&rest verbs)
  "Match entries whose heading title begins with one of VERBS.
A heading title \"begins with a verb\" when it matches
`org-ql-ext-verb-regexp'.  Comparison is case-insensitive."
  :body (when-let* ((found (org-ql-ext-heading-verb)))
          (cl-loop for verb in verbs
                   thereis (and (stringp verb)
                                (string-equal-ignore-case verb found)))))

(defvar org-ql-ext-verb-history nil
  "Minibuffer history for `org-ql-ext-verb-search'.")

(defun org-ql-ext-get-all-verbs (&optional files)
  "Return a sorted list of unique verbs found in heading titles.
FILES defaults to `org-agenda-files'.  Verbs are extracted by
`org-ql-ext-heading-verb' and normalized to title case so that
\"Review\" and \"review\" do not appear as separate completions."
  (let ((verbs '()))
    (org-ql-select (or files (org-agenda-files))
      ;; Pre-filter to headings containing `WORD:' followed by space.
      ;; This is a necessary (but not sufficient) condition for the
      ;; full predicate, so we still re-check inside the action.
      '(heading-regexp "[[:alpha:]]+:[[:space:]]")
      :action (lambda ()
                (when-let* ((verb (org-ql-ext-heading-verb)))
                  (cl-pushnew verb verbs :test #'string=))))
    (sort verbs #'string-lessp)))

;;;###autoload
(defun org-ql-ext-verb-search (verb)
  "Search agenda files for entries whose heading title begins with VERB.
Interactively, prompt for VERB with completion across the verbs
currently in use across `org-agenda-files'."
  (interactive
   (list (completing-read "Verb: " (org-ql-ext-get-all-verbs)
                          nil nil nil 'org-ql-ext-verb-history)))
  (org-ql-search (org-agenda-files)
    `(verb ,verb)
    :title (format "Items with verb %S" verb)))

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
  "Configure `org-mode' with capf for `org-agenda' headlines."
  (add-to-list 'completion-at-point-functions
               'org-ql-ext-completions-at-point))

(defun org-ql-ext-find-refile-targets ()
  "Search for org-ql refile targets across different contexts.

Behavior depends on current major mode:
- In `dired-mode': Recursively searches all org files in `org-directory'
- In `org-mode': Searches buffers returned by `org-ql-find--buffers'
- Otherwise: Searches files returned by the function `org-agenda-files'

All searches use the \"refile-target: \" query prefix."
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
          (org-ql-select 'org-agenda-files
            (progn
              (message "QL Query: %S" query)
              query)
            :action `(org-ext-get-properties ,@columns)
            :sort #'(lambda (x y)
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

(defun org-ql-ext-export-columnview ()
  "Copy tasks in the current column view to pasteboard."
  (interactive)
  (save-excursion
    (org-beginning-of-dblock)
    (forward-line 1)
    (let (result)
      (while (not (looking-at-p "^#"))
        (when-let* ((fields (split-string (buffer-substring-no-properties
                                           (line-beginning-position)
                                           (line-end-position))
                                          "|"))
                    (keyword (nth 1 fields))
                    (link (nth 2 fields))
                    (tags (nth 3 fields)))
          (when (string-match org-link-bracket-re link)
            (setq result
                  (cons
                   (concat
                    "- "
                    (match-string 2 link)
                    (and tags
                         (not (string-empty-p (string-trim tags)))
                         (concat " ("
                                 (and (string= (string-trim keyword) "TASK")
                                      "← ")
                                 (mapconcat #'identity
                                            (split-string (string-trim tags)
                                                          ":" t)
                                            ", ")
                                 (and (string= (string-trim keyword) "TODO")
                                      " ⟹")
                                 ")")))
                   result))))
        (forward-line 1))
      (kill-new (mapconcat #'identity (nreverse result) "\n"))
      (message "ql-columnview task list copied to kill ring"))))

(provide 'org-ql-ext)

;;; org-ql-ext.el ends here
