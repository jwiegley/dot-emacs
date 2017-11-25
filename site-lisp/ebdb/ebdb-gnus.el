;;; ebdb-gnus.el --- Gnus interface to EBDB          -*- lexical-binding: t; -*-

;; Copyright (C) 2016-2017  Free Software Foundation, Inc.

;; Author: Eric Abrahamsen <eric@ericabrahamsen.net>

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; Code for interaction with Gnus.

;;; Code:

(require 'ebdb-com)
(require 'ebdb-mua)
(require 'gnus-sum)
(require 'gnus-art)

(autoload 'message-make-domain "message")

(defgroup ebdb-mua nil
  "Variables that specify the EBDB-MUA interface"
  :group 'ebdb)

(defgroup ebdb-mua-gnus nil
  "Gnus-specific EBDB customizations"
  :group 'ebdb-mua)
(put 'ebdb-mua-gnus 'custom-loads '(ebdb-gnus))

(defgroup ebdb-mua-gnus-scoring nil
  "Gnus-specific scoring EBDB customizations"
  :group 'ebdb-mua-gnus)
(put 'ebdb-mua-gnus-scoring 'custom-loads '(ebdb-gnus))

(defgroup ebdb-mua-gnus-splitting nil
  "Gnus-specific splitting EBDB customizations"
  :group 'ebdb-mua-gnus)
(put 'ebdb-mua-gnus-splitting 'custom-loads '(ebdb-gnus))

;;; Gnus-specific field types.  All should subclass
;;; `ebdb-field-user'.

;;;###autoload
(defclass ebdb-gnus-score-field (ebdb-field-user)
  ((score
    :type (or null number)
    :initarg :score
    :initval nil))
  :human-readable "gnus score")

(cl-defmethod ebdb-read ((field (subclass ebdb-gnus-score-field)) &optional slots obj)
  (let ((score (string-to-number
		(ebdb-read-string
		 "Score: " (when obj (slot-value obj 'score))))))
    (cl-call-next-method field (plist-put slots :score score) obj)))

(cl-defmethod ebdb-string ((field ebdb-gnus-score-field))
  (slot-value field 'score))

;; Scoring

(defcustom ebdb/gnus-score-default nil
  "If this is set, then every mail address in the EBDB that does not have
an associated score field will be assigned this score.  A value of nil
implies a default score of zero."
  :group 'ebdb-mua-gnus-scoring
  :type '(choice (const :tag "Do not assign default score" nil)
                 (integer :tag "Assign this default score" 0)))

(defvar ebdb/gnus-score-default-internal nil
  "Internal variable for detecting changes to
`ebdb/gnus-score-default'.  You should not set this variable directly -
set `ebdb/gnus-score-default' instead.")

(defvar ebdb/gnus-score-alist nil
  "The text version of the scoring structure returned by
ebdb/gnus-score.  This is built automatically from the EBDB.")

(defvar ebdb/gnus-score-rebuild-alist t
  "Set to t to rebuild ebdb/gnus-score-alist on the next call to
ebdb/gnus-score.  This will be set automatically if you change a EBDB
record which contains a gnus-score field.")

(defun ebdb/gnus-score-invalidate-alist (record)
  "This function is called through `ebdb-after-change-hook',
and sets `ebdb/gnus-score-rebuild-alist' to t if the changed
record contains a gnus-score field."
  (if (ebdb-record-user-field record 'ebdb-gnus-score-field)
      (setq ebdb/gnus-score-rebuild-alist t)))

;;;###autoload
(defun ebdb/gnus-score (group)
  "Return a score alist for Gnus.
A score pair will be made for every member of the mail field in
records which also have a `gnus-score' field.  This allows the
EBDB to serve as a supplemental global score file, with the
advantage that it can keep up with multiple and changing
addresses better than the traditionally static global scorefile."
  (list (list
         (condition-case nil
             (read (ebdb/gnus-score-as-text group))
           (error (setq ebdb/gnus-score-rebuild-alist t)
                  (message "Problem building EBDB score table.")
                  (ding) (sit-for 2)
                  nil)))))

(defun ebdb/gnus-score-as-text (_group)
  "Returns a SCORE file format string built from the EBDB."
  (cond ((or (cond ((/= (or ebdb/gnus-score-default 0)
                        (or ebdb/gnus-score-default-internal 0))
                    (setq ebdb/gnus-score-default-internal
                          ebdb/gnus-score-default)
                    t))
             (not ebdb/gnus-score-alist)
             ebdb/gnus-score-rebuild-alist)
         (setq ebdb/gnus-score-rebuild-alist nil)
         (setq ebdb/gnus-score-alist
               (concat "((touched nil) (\"from\"\n"
                       (mapconcat
                        (lambda (record)
                          (let ((score (or (ebdb-record-user-field record 'ebdb-gnus-score-field)
                                           ebdb/gnus-score-default))
                                (mail (ebdb-record-mail record)))
                            (when (and score mail)
                              (mapconcat
                               (lambda (address)
                                 (format "(\"%s\" %s)\n" (ebdb-string address) score))
                               mail ""))))
                        ebdb-record-tracker "")
                       "))"))))
  ebdb/gnus-score-alist)

;;; Gnus splitting support

;; First, catch and upgrade instances of `ebdb-gnus-private-field' and
;; `ebdb-gnus-imap-field'.  These upgrade routines were put in place
;; September 3, 2017.  Give it... a year?  Two?  Then delete them.

;;;###autoload
(defclass ebdb-gnus-private-field (ebdb-field-user)
  ((group
    :initarg :group)))

;;;###autoload
(defclass ebdb-gnus-imap-field (ebdb-field-user)
  ((group
    :initarg :group)))

(cl-defmethod make-instance ((_cls (subclass ebdb-gnus-private-field)) &rest slots)
  (apply #'make-instance 'ebdb-field-mail-folder
	 (list :folder (plist-get slots :group))))

(cl-defmethod make-instance ((_cls (subclass ebdb-gnus-imap-field)) &rest slots)
  (apply #'make-instance 'ebdb-field-mail-folder
	 (list :folder (plist-get slots :group))))

(defun ebdb/gnus-split-folders-list ()
  "Return a list of \( \"From\" mail-regexp imap-folder-name\) tuples
based on the contents of the EBDB.

Mail address elements are already `regexp-quote'-ed, so we just
concat them.  Please note: in order that this will work with the
`nnimap-split-fancy' or `nnmail-split-fancy' methods you have to
use a backquote template, that is your setting will look like:

\(setq nnimap-split-rule  'nnimap-split-fancy
       nnimap-split-inbox \"INBOX\"
       nnimap-split-fancy
       `\(| ,@\(ebdb/gnus-split-folders-list\)
            ... \)\)

Note that `\( is the backquote, NOT the quote '\(."
  (mapcar
   (lambda (elt)
     (list "From"
	   (mapconcat #'identity (cdr elt) "\\|")
	   (car elt)))
   ebdb-mail-folder-list))

;;
;; Insinuation
;;

(add-hook 'gnus-article-prepare-hook 'ebdb-mua-auto-update)

(add-hook 'gnus-startup-hook 'ebdb-insinuate-gnus)

(defsubst ebdb-gnus-buffer-name ()
  (format "*%s-Gnus*" ebdb-buffer-name))

(cl-defmethod ebdb-make-buffer-name (&context (major-mode gnus-summary-mode))
  "Produce a EBDB buffer name associated with Gnus."
  (ebdb-gnus-buffer-name))

(cl-defmethod ebdb-make-buffer-name (&context (major-mode gnus-article-mode))
  "Produce a EBDB buffer name associated with Gnus."
  (ebdb-gnus-buffer-name))

(cl-defmethod ebdb-popup-window (&context (major-mode gnus-summary-mode))
  (let ((win
	 (progn
	   (unless (gnus-buffer-live-p gnus-article-buffer)
	     (gnus-summary-show-article))
	   (get-buffer-window gnus-article-buffer))))
    (list win 0.3)))

(cl-defmethod ebdb-popup-window (&context (major-mode gnus-article-mode))
  (list (get-buffer-window) 0.3))

;; It seems that `gnus-fetch-field' fetches decoded content of
;; `gnus-visible-headers', ignoring `gnus-ignored-headers'.
;; Here we use instead `gnus-fetch-original-field' that fetches
;; the encoded content of `gnus-original-article-buffer'.
;; Decoding makes this possibly a bit slower, but something like
;; `ebdb-select-message' does not get fooled by an apparent
;; absence of some headers.
;; See http://permalink.gmane.org/gmane.emacs.gnus.general/78741

(cl-defmethod ebdb-mua-message-header ((header string)
				   &context (major-mode gnus-summary-mode))
  "Return value of HEADER for current Gnus message."
  (set-buffer gnus-article-buffer)
  (gnus-fetch-original-field header))

;; This is all a little goofy.
(cl-defmethod ebdb-mua-message-header ((header string)
				   &context (major-mode gnus-article-mode))
  (set-buffer gnus-article-buffer)
  (gnus-fetch-original-field header))

(cl-defmethod ebdb-mua-message-header ((header string)
				   &context (major-mode gnus-tree-mode))
  (set-buffer gnus-article-buffer)
  (gnus-fetch-original-field header))

(cl-defmethod ebdb-mua-prepare-article (&context (major-mode gnus-summary-mode))
  (gnus-summary-select-article))

(cl-defmethod ebdb-mua-prepare-article (&context (major-mode gnus-article-mode))
  (gnus-summary-select-article))

(cl-defmethod ebdb-mua-article-body (&context (major-mode gnus-summary-mode))
  "Return the current article body as a string.

Must not include article headers, though can include headers in
quoted replies."
  (gnus-with-article-buffer
    ;; This pretends that there's no such thing as mime parts, and
    ;; will probably fail horribly.
    (article-goto-body)
    (buffer-substring-no-properties (point) (point-max))))

(cl-defmethod ebdb-mua-article-body (&context (major-mode gnus-article-mode))
   (gnus-with-article-buffer
    (article-goto-body)
    (buffer-substring-no-properties (point) (point-max))))

(cl-defmethod ebdb-mua-article-signature (&context (major-mode gnus-summary-mode))
  (gnus-with-article-buffer
    (gnus-article-search-signature)
    (forward-line)
    (buffer-substring-no-properties
     (point)
     ;; Assume a blank line concludes a signature.
     (or (re-search-forward "\n\n" nil t)
	 (point-max)))))

(defun ebdb-insinuate-gnus ()
  "Hook EBDB into Gnus."
  ;; `ebdb-mua-display-sender' fails in *Article* buffers, where
  ;; `gnus-article-read-summary-keys' provides an additional wrapper
  ;; that restores the window configuration.
  (define-key gnus-summary-mode-map ";" ebdb-mua-keymap)
  (define-key gnus-article-mode-map ";" ebdb-mua-keymap)

  ;; Set up user field for use in `gnus-summary-line-format'
  ;; (1) Big solution: use whole name
  (if ebdb-mua-summary-unify-format-letter
      (fset (intern (concat "gnus-user-format-function-"
                            ebdb-mua-summary-unify-format-letter))
            (lambda (header)
	      (let ((from (mail-header-from header)))
		(or
		 (and gnus-ignored-from-addresses
		      (cond ((functionp gnus-ignored-from-addresses)
			     (funcall gnus-ignored-from-addresses
				      (mail-strip-quoted-names from)))
			    (t (string-match (gnus-ignored-from-addresses) from)))
		      (let ((extra-headers (mail-header-extra header))
			    to
			    newsgroups)
			(cond
			 ((setq to (cdr (assq 'To extra-headers)))
			  (concat gnus-summary-to-prefix
				  (ebdb-mua-summary-unify to)))
			 ((setq newsgroups
				(or
				 (cdr (assq 'Newsgroups extra-headers))
				 (and
				  (memq 'Newsgroups gnus-extra-headers)
				  (eq (car (gnus-find-method-for-group
					    gnus-newsgroup-name)) 'nntp)
				  (gnus-group-real-name gnus-newsgroup-name))))
			  (concat gnus-summary-newsgroup-prefix newsgroups)))))
		 (ebdb-mua-summary-unify (mail-header-from header)))))))

  ;; (2) Small solution: a mark for messages whos sender is in EBDB.
  (if ebdb-mua-summary-mark-format-letter
      (fset (intern (concat "gnus-user-format-function-"
                            ebdb-mua-summary-mark-format-letter))
            (lambda (header)
              (ebdb-mua-summary-mark (mail-header-from header))))))

(provide 'ebdb-gnus)
;;; ebdb-gnus.el ends here
;;;
