;;; check-mail.el --- A slightly more sophisticated mail checking function

;; Copyright (C) 2001, 2002, 2003 John Wiegley <johnw@gnu.org>

;; Emacs Lisp Archive Entry
;; Filename: check-mail.el
;; Version: 1.7
;; Keywords: mail
;; Author: John Wiegley <johnw@gnu.org>
;; Maintainer: John Wiegley <johnw@gnu.org>
;; Description: A slightly more sophisticated mail checking function
;; URL: http://www.gci-net.com/~johnw/Emacs/check-mail.el
;; Compatibility: Emacs20, Emacs21

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

;; To use this package, just load it and change
;; `display-time-mail-function' to `check-mail'.  Example config:

;;  (setq check-mail-summary-function (quote check-mail-mh-summary))
;;  (setq check-mail-sound-program "/usr/bin/esdplay")
;;  (setq check-mail-sound-file "~/Mail/gotmail.wav")
;;  (setq check-mail-boxes (quote ("/var/mail/johnw"
;;                                 "~/Mail/incoming/mail\\..*\\.spool")))

;; What does it do?  It allows you to check multiple files for
;; incoming mail, even filenames generated from a regular expression.
;; This is useful if you have lots of procmail incoming spools, for
;; example.  It also support playing a sound file when new mail is
;; detected.

(defgroup check-mail nil
  "A more sophisticated mail checking function.
This module enhances the `display-time' module, where the actual check
for mail occurs.  Just customize the value of
`display-time-mail-function' to be `check-mail'."
  :group 'display-time)

(defcustom check-mail-boxes nil
  "A list of mailboxes that will be checked for mail.
Each can also be a regexp, in which case any file matching that regexp
will be checked for new mail."
  :type '(repeat (choice file regexp))
  :group 'check-mail)

(defcustom check-mail-sound-file nil
  "If non-nil, a sound file to play when new mail arrives."
  :type 'file
  :group 'check-mail)

(defcustom check-mail-sound-program nil
  "If non-nil, invoke this with `check-mail-sound-file' as sole argument.
If nil, uses Emacs 21's `play-sound-file' function."
  :type 'file
  :group 'check-mail)

(defcustom check-mail-summary-function 'check-mail-box-summary
  "The function called to produce a summary of a mailbox file.
This function is passed the filename of the mailbox file."
  :type 'function
  :group 'check-mail)

(defcustom check-mail-only-check-if nil
  "If this function returns a nil value, don't check for mail."
  :type '(choice function
		 (const :tag "Always check" nil))
  :group 'check-mail)

(defvar check-mail-last-value nil)

(defun check-mail-box-summary (file)
  "Insert summary information about the mailbox FILE."
  (let ((count 0)
	(senders (list t)))
    (with-temp-buffer
      (insert-file-contents-literally file)
      (while (re-search-forward "^From:\\s-+\\(.+\\)" nil t)
	(let* ((from (match-string 1))
	       (addr (mail-extract-address-components from)))
	  (setq count (1+ count))
	  (if (re-search-forward "^Subject:\\s-+\\(.+\\)" nil t)
	      (nconc senders (list (cons (if addr
					     (or (car addr)
						 (cadr addr)))
					 (match-string 1))))))))
    (insert (format "%d  %s\n" count file))
    (setq senders (cdr senders))
    (while senders
      (insert (format "     %s: %s\n" (or (caar senders) "Somebody")
		      (cdar senders)))
      (setq senders (cdr senders)))))

(defun check-mail-mh-summary (file)
  (insert " " file ":\n")
  (call-process (executable-find "scan") nil t nil "-file" file))

;;;###autoload
(defun check-mail ()
  "Check all of the boxes listed in `mail-boxes-to-check' for new mail."
  (interactive)
  (when (or (null check-mail-only-check-if)
	    (funcall check-mail-only-check-if))
    (let ((boxes check-mail-boxes)
	  (buf (and (interactive-p)
		    (get-buffer-create "*check mail*")))
	  you-have-mail)
      (while boxes
	(let ((files (list (car boxes))))
	  (unless (file-exists-p (car files))
	    (setq files
		  (directory-files (file-name-directory (car files)) t
				   (file-name-nondirectory (car files)))))
	  (while files
	    (when (> (nth 7 (file-attributes (car files))) 0)
	      (if (interactive-p)
		  (with-current-buffer buf
		    (funcall check-mail-summary-function (car files))))
	      (setq you-have-mail t)
	      (unless (interactive-p)
		(setq files nil boxes nil)))
	    (setq files (cdr files))))
	(setq boxes (cdr boxes)))
      (if (and (fboundp 'play-sound-file)
	       (null check-mail-last-value)
	       you-have-mail
	       check-mail-sound-file)
	  (if check-mail-sound-program
	      (start-process "checkmail" nil
			     (expand-file-name check-mail-sound-program)
			     (expand-file-name check-mail-sound-file))
	    (play-sound-file check-mail-sound-file)))
      (when (and (interactive-p) you-have-mail)
	(with-current-buffer buf
	  (let ((text (buffer-string)))
	    (with-output-to-temp-buffer "*Check Mail*"
	      (princ text)
	      (current-buffer))))
	(kill-buffer buf)
	(with-current-buffer (get-buffer "*Check Mail*")
	  (let ((inhibit-read-only t))
	    (setq truncate-lines t)
	    (goto-char (point-min))
	    (while (re-search-forward "^\\s-+\\([^0-9 ][^:]+\\):" nil t)
	      (add-text-properties (match-beginning 1) (match-end 1)
				   '(face bold))))))
      (setq check-mail-last-value you-have-mail))))

(provide 'check-mail)

;;; check-mail.el ends here
