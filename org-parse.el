;;; org-parse.el --- Code to parse and rewrite Org entries

;; Copyright (C) 2011 John Wiegley <johnw@gnu.org>

;; Emacs Lisp Archive Entry
;; Filename: org-parse.el
;; Version: 1.0
;; Keywords: org-mode
;; Author: John Wiegley <johnw@gnu.org>
;; Maintainer: John Wiegley <johnw@gnu.org>
;; Description: Adds public key encryption to org-mode buffers
;; URL: http://www.newartpisans.com/software/emacs.html
;; Compatibility: Emacs23

;; This file is not part of GNU Emacs.

;; This is free software; you can redistribute it and/or modify it under
;; the terms of the GNU General Public License as published by the Free
;; Software Foundation; either version 2, or (at your option) any later
;; version.
;;
;; This is distributed in the hope that it will be useful, but WITHOUT
;; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
;; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
;; for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330, Boston,
;; MA 02111-1307, USA.

;;; Commentary:

(defun plist-to-alist (sym)
  (let ((l (symbol-plist sym))
        props)
    (while l
      (unless (or (null (cadr l))
                  (and (stringp (cadr l))
                       (= 0 (length (cadr l)))))
        (push (cons (car l) (cadr l)) props))
      (setq l (cddr l)))
    props))

(defsubst trim-string (str)
  (replace-regexp-in-string "\\(\\`[[:space:]\n]*\\|[[:space:]\n]*\\'\\)" ""
                            str))

(defmacro resolve-log-entry ()
  `(when log-entry
     (put 'log-entry 'body
          (trim-string (get 'log-entry 'body)))
     (put 'item 'log
          (cons (plist-to-alist 'log-entry)
                (get 'item 'log)))
     (setq log-entry nil)
     (setplist 'log-entry '())))

(defun org-parse-entry ()
  (save-restriction
    (save-excursion
      (outline-back-to-heading)
      (narrow-to-region (point) (progn (outline-next-heading) (point)))
      (goto-char (point-min))

      (let (item log-entry)
        (setplist 'item '())
        (put 'item 'body "")
        (put 'item 'tags '())
        (put 'item 'log '())
        (put 'item 'properties '())
        (while (not (eobp))
          (cond
           ((looking-at (concat "^\\(\\*+\\)\\( \\([A-Z][A-Z]+\\)\\)?"
                                "\\( \\[#\\([A-C]\\)\\]\\)? \\(.+?\\)"
                                "\\( +:\\(.+?\\):\\)?$"))
            (put 'item 'depth (length (match-string-no-properties 1)))
            (if (match-string-no-properties 2)
                (put 'item 'state (match-string-no-properties 3)))
            (put 'item 'priority (or (match-string-no-properties 5) "B"))
            (put 'item 'title (match-string-no-properties 6))
            (if (match-string-no-properties 8)
                (put 'item 'tags
                     (split-string (match-string-no-properties 8) ":" t))))

           ((looking-at (concat "^\\(\\s-*\\)- State \"\\([A-Z]+\\)\"\\s-*"
                                "\\(from \"\\([A-Z]*\\)\"\\s-*\\)?"
                                "\\[\\([^]]+\\)\\]\\(\\s-*\\\\\\\\\\)?\\s-*$"))
            (resolve-log-entry)

            (put 'log-entry 'depth
                 (+ 1 (length (match-string-no-properties 1))))
            (put 'log-entry 'to (match-string-no-properties 2))
            (if (and (match-string-no-properties 3)
                     (match-string-no-properties 4))
                (put 'log-entry 'from (match-string-no-properties 4)))
            (put 'log-entry 'date (match-string-no-properties 5))
            (if (match-string-no-properties 6)
                (progn
                  (put 'log-entry 'body "")
                  (setq log-entry t))
              (put 'item 'log
                   (cons (plist-to-alist 'log-entry)
                         (get 'item 'log)))
              (setplist 'log-entry '())))

           ((looking-at (concat "^\\(\\s-*\\)- Note taken on\\s-*"
                                "\\[\\([^]]+\\)\\]\\(\\s-*\\\\\\\\\\)?\\s-*$"))
            (resolve-log-entry)

            (put 'log-entry 'depth
                 (+ 1 (length (match-string-no-properties 1))))
            (put 'log-entry 'date (match-string-no-properties 2))
            (put 'log-entry 'note t)
            (if (match-string-no-properties 3)
                (progn
                  (put 'log-entry 'body "")
                  (setq log-entry t))
              (put 'item 'log
                   (cons (plist-to-alist 'log-entry)
                         (get 'item 'log)))
              (setplist 'log-entry '())))

           ((re-search-forward ":PROPERTIES:" (line-end-position) t)
            (while (not (re-search-forward ":END:" (line-end-position) t))
              (assert (not (eobp)))
              (if (looking-at "^\\s-*:\\([^:]+\\):\\s-*\\(.*\\)")
                  (let ((name (match-string-no-properties 1))
                        (data (match-string-no-properties 2)))
                    ;;(if (and (string= name "CREATED")
                    ;;         (string-match "\\[\\([^]\n]+\\)\\]" data))
                    ;;    (setq data (match-string 1 data)))
                    (unless (assoc name (get 'item 'properties))
                      (put 'item 'properties
                           (cons (cons name data)
                                 (get 'item 'properties))))))
              (forward-line)))

           ;; My old way of timestamping entries
           ((looking-at "^\\s-*\\[\\([^]]+\\)\\]\\s-*$")
            (unless (assoc "CREATED" (get 'item 'properties))
              (put 'item 'properties
                   (cons (cons "CREATED"
                               (concat "[" (match-string-no-properties 1) "]"))
                         (get 'item 'properties)))))

           (t
            (let (skip-line)
              (goto-char (line-beginning-position))
              (when (re-search-forward "SCHEDULED:\\s-*<\\([^>\n]+\\)>"
                                       (line-end-position) t)
                (put 'item 'scheduled (match-string-no-properties 1))
                (setq skip-line t))
              (goto-char (line-beginning-position))
              (when (re-search-forward "DEADLINE:\\s-*<\\([^>\n]+\\)>"
                                       (line-end-position) t)
                (put 'item 'deadline (match-string-no-properties 1))
                (setq skip-line t))
              (goto-char (line-beginning-position))
              (when (re-search-forward "CLOSED:\\s-*\\[\\([^]\n]+\\)\\]"
                                       (line-end-position) t)
                (put 'log-entry 'to (get 'item 'state))
                (put 'log-entry 'date (match-string-no-properties 1))
                (put 'item 'log
                     (cons (plist-to-alist 'log-entry)
                           (get 'item 'log)))
                (setplist 'log-entry '())
                (setq skip-line t))
              (goto-char (line-beginning-position))
              (when (re-search-forward "ARCHIVED:\\s-*<\\([^>\n]+\\)>"
                                       (line-end-position) t)
                (unless (assoc "ARCHIVE_TIME" (get 'item 'properties))
                  (put 'item 'properties
                       (cons (cons "ARCHIVE_TIME"
                                   (match-string-no-properties 1))
                             (get 'item 'properties))))
                (setq skip-line t))
              (if skip-line
                  (goto-char (line-end-position))))

            (assert (get (if log-entry 'log-entry 'item) 'depth))
            (dotimes (i (1+ (get (if log-entry 'log-entry 'item) 'depth)))
              (if (eq (char-after) ? )
                  (forward-char)
                (unless (looking-at "^\\s-*$")
                  (resolve-log-entry))))

            (put (if log-entry 'log-entry 'item) 'body
                 (concat (get (if log-entry 'log-entry 'item) 'body) "\n"
                         (buffer-substring-no-properties
                          (point) (line-end-position))))))
          (forward-line))

        (resolve-log-entry)

        (put 'item 'body (trim-string (get 'item 'body)))
        (plist-to-alist 'item)))))

(defun org-insert-parsed-entry (entry)
  (insert (make-string (cdr (assq 'depth entry)) ?*) ? )
  (if (assq 'state entry)
      (insert (cdr (assq 'state entry)) ? ))
  (if (and (assq 'priority entry)
           (not (string= "B" (cdr (assq 'priority entry)))))
      (insert "[#" (cdr (assq 'priority entry)) "] "))
  (insert (cdr (assq 'title entry)))
  (when (assq 'tags entry)
    (insert "  :" (mapconcat 'identity (cdr (assq 'tags entry)) ":") ":")
    (org-align-all-tags))
  (insert ?\n)

  (when (or (assq 'scheduled entry) (assq 'deadline entry))
    (insert (make-string (+ 1 (cdr (assq 'depth entry))) ? ))
    (if (assq 'scheduled entry)
        (insert "SCHEDULED: <" (cdr (assq 'scheduled entry)) ">"))
    (when (assq 'deadline entry)
      (if (assq 'scheduled entry)
          (insert ? ))
      (insert "DEADLINE: <" (cdr (assq 'deadline entry)) ">"))
    (insert ?\n))
        
  (when (assq 'log entry)
    (dolist (log (reverse (cdr (assq 'log entry))))
      (insert (make-string (+ 1 (cdr (assq 'depth entry))) ? ))
      (cond
       ((assq 'note log)
        (insert "- Note taken on [" (cdr (assq 'date log)) "]"))
       ((assq 'from log)
        (insert (format "- State %-12s from %-12s [%s]"
                        (concat "\"" (cdr (assq 'to log)) "\"")
                        (concat "\"" (cdr (assq 'from log)) "\"")
                        (cdr (assq 'date log)))))
       (t
        (insert (format "- State %-12s [%s]"
                        (concat "\"" (cdr (assq 'to log)) "\"")
                        (cdr (assq 'date log))))))
      (if (assq 'body log)
          (progn
            (insert " \\\\\n")
            (dolist (line (split-string (cdr (assq 'body log)) "\n"))
              (insert (make-string (+ 3 (cdr (assq 'depth entry))) ? )
                      line ?\n)))
        (insert ?\n))))

  (when (assq 'body entry)
    (dolist (line (split-string (cdr (assq 'body entry)) "\n"))
      (insert (make-string (+ 1 (cdr (assq 'depth entry))) ? )
              line ?\n)))

  (when (assq 'properties entry)
    (insert (make-string (+ 1 (cdr (assq 'depth entry))) ? )
            ":PROPERTIES:\n")
    (dolist (prop (if nil
                      (sort (cdr (assq 'properties entry))
                            (lambda (a b) (or (string= (car a) "ID")
                                         (string< (car a) (car b)))))
                    (reverse (cdr (assq 'properties entry)))))
      (insert (make-string (+ 1 (cdr (assq 'depth entry))) ? )
              (format "%-10s %s\n"
                      (concat ":" (car prop) ":") (cdr prop))))
    (insert (make-string (+ 1 (cdr (assq 'depth entry))) ? )
            ":END:\n")))

(defun org-normalize-entry ()
  (interactive)
  (let ((entry (org-parse-entry)))
    (save-restriction
      (save-excursion
        (outline-back-to-heading)
        (narrow-to-region (point) (progn (outline-next-heading) (point)))
        (delete-region (point-min) (point-max))
        (org-insert-parsed-entry entry)))))

(defun org-replace-entry (entry)
  (interactive)
  (save-restriction
    (save-excursion
      (outline-back-to-heading)
      (narrow-to-region (point) (progn (outline-next-heading) (point)))
      (delete-region (point-min) (point-max))
      (org-insert-parsed-entry entry))))

(defun org-normalize-all ()
  (interactive)
  (goto-char (point-min))
  (show-all)
  (untabify (point-min) (point-max))
  (while (re-search-forward "^\\*" nil t)
    (org-normalize-entry)
    (forward-line))
  (goto-char (point-min))
  (delete-trailing-whitespace)
  (save-buffer))

(provide 'org-parse)

;;; org-parse.el ends here
