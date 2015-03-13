;;; infohack.el --- a hack to format info file.
;; Copyright (C) 2001-2014 Free Software Foundation, Inc.

;; Author: Shenghuo Zhu <zsh@cs.rochester.edu>
;; Keywords: info

;; This file is part of GNU Emacs.

;; GNU Emacs is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; GNU Emacs is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;;; Code:

(require 'texinfmt)

(if (fboundp 'texinfo-copying)
    nil
  ;; Support @copying and @insertcopying for Emacs 21.3 and lesser and
  ;; XEmacs.
  (defvar texinfo-copying-text ""
    "Text of the copyright notice and copying permissions.")

  (defun texinfo-copying ()
    "Copy the copyright notice and copying permissions from the Texinfo file,
as indicated by the @copying ... @end copying command;
insert the text with the @insertcopying command."
    (let ((beg (progn (beginning-of-line) (point)))
	  (end  (progn (re-search-forward "^@end copying[ \t]*\n") (point))))
      (setq texinfo-copying-text
	    (buffer-substring-no-properties
	     (save-excursion (goto-char beg) (forward-line 1) (point))
	     (save-excursion (goto-char end) (forward-line -1) (point))))
      (delete-region beg end)))

  (defun texinfo-insertcopying ()
    "Insert the copyright notice and copying permissions from the Texinfo file,
which are indicated by the @copying ... @end copying command."
    (insert (concat "\n" texinfo-copying-text)))

  (defadvice texinfo-format-scan (before expand-@copying-section activate)
    "Extract @copying and replace @insertcopying with it."
    (goto-char (point-min))
    (when (search-forward "@copying" nil t)
      (texinfo-copying))
    (while (search-forward "@insertcopying" nil t)
      (delete-region (match-beginning 0) (match-end 0))
      (texinfo-insertcopying))))

(if (fboundp 'texinfo-format-comma)
    nil
  (put 'comma 'texinfo-format 'texinfo-format-comma)
  (defun texinfo-format-comma ()
    (texinfo-parse-arg-discard)
    (insert ",")
    (put-text-property (1- (point)) (point) 'ignore t))

  ;; Redefine this function so as to work for @comma
  (defun texinfo-format-parse-args ()
    (let ((start (1- (point)))
	  next beg end
	  args)
      (search-forward "{")
      (save-excursion
	(texinfo-format-expand-region
	 (point)
	 (save-excursion (up-list 1) (1- (point)))))
      ;; The following does not handle cross references of the form:
      ;; `@xref{bullet, , @code{@@bullet}@{@}}.' because the
      ;; re-search-forward finds the first right brace after the second
      ;; comma.
      (while (/= (preceding-char) ?\})
	(skip-chars-forward " \t\n")
	(setq beg (point))
;;;	(re-search-forward "[},]")
	;; Ignore commas that are derived from @comma{}.
	(while (and (re-search-forward "[},]" nil t)
		    (get-text-property (match-beginning 0) 'ignore)))
;;;
	(setq next (point))
	(forward-char -1)
	(skip-chars-backward " \t\n")
	(setq end (point))
	(cond ((< beg end)
	       (goto-char beg)
	       (while (search-forward "\n" end t)
		 (replace-match " "))))
	(push (if (> end beg) (buffer-substring-no-properties beg end))
	      args)
	(goto-char next))
      ;;(if (eolp) (forward-char 1))
      (setq texinfo-command-end (point))
      (nreverse args))))

(defun infohack-remove-unsupported ()
  (goto-char (point-min))
  (while (re-search-forward "@\\(end \\)?ifnottex" nil t) 
    (replace-match ""))
  (goto-char (point-min))
  (while (search-forward "\n@iflatex\n" nil t)
    (delete-region (1+ (match-beginning 0))
		   (search-forward "\n@end iflatex\n"))))

(defun infohack-replace-unsupported ()
  (goto-char (point-min))
  (while (search-forward "@indicateurl{" nil t)
    (replace-match "@url{")))

(defun infohack-include-files ()
  "Insert @include files."
  (goto-char (point-min))
  (set-syntax-table texinfo-format-syntax-table)
  (let (start texinfo-command-end filename)
    (while (re-search-forward "^@include" nil t)
      (setq start (match-beginning 0)
	    texinfo-command-end (point)
	    filename (texinfo-parse-line-arg))
      (delete-region start (point-at-bol 2))
      (message "Reading included file: %s" filename)
      (save-excursion
	(save-restriction
	  (narrow-to-region
	   (point)
	   (+ (point) (car (cdr (insert-file-contents filename)))))
	  (goto-char (point-min))
	  ;; Remove `@setfilename' line from included file, if any,
	  ;; so @setfilename command not duplicated.
	  (if (re-search-forward "^@setfilename" (point-at-eol 100) t)
	      (delete-region (point-at-bol 1)
			     (point-at-bol 2))))))))

(defun infohack (file)
  (let ((dest-directory default-directory)
	(max-lisp-eval-depth (max max-lisp-eval-depth 600))
	coding-system)
    ;; Emacs 21.3 doesn't support @documentencoding
    (unless (get 'documentencoding 'texinfo-format)
      (put 'documentencoding 'texinfo-format 
	   'texinfo-discard-line-with-args))
    (find-file file)
    (setq buffer-read-only nil)
    (setq coding-system buffer-file-coding-system)
    (infohack-remove-unsupported)
    (infohack-include-files)
    (infohack-replace-unsupported)
    (texinfo-every-node-update) 
    (texinfo-format-buffer t) ;; Don't save any file.
    (setq default-directory dest-directory)
    (setq buffer-file-name 
	  (expand-file-name (file-name-nondirectory buffer-file-name)
			    default-directory))
    (setq buffer-file-coding-system coding-system)
    ;;(if (> (buffer-size) (if (boundp 'Info-split-threshold)
    ;;			       (+ 50000 Info-split-threshold)
    ;;			     100000))
    ;;	  (Info-split))
    (save-buffer)))

(eval-and-compile
  (when (string-match "windows-nt\\|os/2\\|emx\\|cygwin"
                      (symbol-name system-type))
    (defun subst-char-in-region (START END FROMCHAR TOCHAR &optional NOUNDO)
      "From START to END, replace FROMCHAR with TOCHAR each time it occurs.
If optional arg NOUNDO is non-nil, don't record this change for undo
and don't mark the buffer as really changed.
Both characters must have the same length of multi-byte form."
      (let ((original-buffer-undo-list buffer-undo-list)
            (modified (buffer-modified-p)))
        (if NOUNDO
            (setq buffer-undo-list t))
        (goto-char START)
        (let ((from (char-to-string FROMCHAR))
              (to (char-to-string TOCHAR)))
          (while (search-forward from END t)
            (replace-match to t t)))
        (if NOUNDO
            (progn (setq buffer-undo-list original-buffer-undo-list)
                   (set-buffer-modidifed-p modified)))))))

(defun batch-makeinfo ()
  "Emacs makeinfo in batch mode."
  (infohack (car command-line-args-left))
  (setq command-line-args-left nil))

;;; infohack.el ends here
