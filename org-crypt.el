;;; org-crypt.el --- Public key encryption for org-mode entries

;; Copyright (C) 2007 John Wiegley <johnw@gnu.org>

;; Emacs Lisp Archive Entry
;; Filename: org-crypt.el
;; Version: 0.1
;; Keywords: org-mode
;; Author: John Wiegley <johnw@gnu.org>
;; Maintainer: John Wiegley <johnw@gnu.org>
;; Description: Adds public key encryption to org-mode buffers
;; URL: http://www.newartisans.com/software/emacs.html
;; Compatibility: Emacs22

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

;; Right now this is just a set of functions to play with.  It depends on the
;; epg library.  Here's how you would use it:
;;
;; 1. To mark an entry for encryption, use `M-x org-set-property' to set the
;;    property CRYPTKEY to any address in your public keyring.  The text of
;;    the entry (but not its properties or headline) will be encrypted for
;;    this user.  For them to read it, the corresponding secret key must be
;;    located in the secret key ring of the account where you try to decrypt
;;    it.  This makes it possible to leave secure notes that only the intended
;;    recipient can read in a shared-org-mode-files scenario.
;;
;; 2. Next, at the top of your org-mode buffer, add this line:
;;
;;      -*- mode: org; after-save-hook: (org-encrypt-entries) -*-
;;
;;    This ensures that entries marked for encryption are encrypted whenever
;;    the file is saved.  If you want encryption to be manual, use `M-x
;;    org-encrypt-entries'.  Note that in this version -- mainly because I
;;    don't know epg.el better -- you will be asked for your password for
;;    every entry that needs encryption.
;;
;; 3. To later decrypt an entry, use `M-x org-decrypt-entry'.  It might be
;;    useful to bind this to a key, like C-c C-/.  I hope that in the future,
;;    C-c C-r can be might overloaded to also decrypt an entry if it's
;;    encrypted, since that fits nicely with the meaning of "reveal".

(require 'epg)

(defun org-apply-to-entry-contents (function property &optional content-re)
  "Apply the given FUNCTION to applicable entry contents.
Matching entries are those having a value for PROPERTY.  If the
optional CONTENT-RE is nil, then only the presence of the
PROPERTY is tested for.  Otherwise, the contents of the property
must match the regular expression CONTENT-RE.  If either
condition is met, FUNCTION will be called with four arguments:
the beginning and ending of the entry content's range (with point
always at the beginning), the property, and its value."
  (save-excursion
    (goto-char (point-min))
    (while (not (eobp))
      (outline-next-heading)
      (let* ((props (org-entry-properties))
	     (prop-value (and props (cdr (assoc property props)))))
	(when (and prop-value (stringp prop-value)
		   (or (null content-re)
		       (string-match content-re prop-value)))
	  (forward-line)
	  (let* ((begin (point))
		 (end (save-excursion
			(goto-char (car (org-get-property-block begin)))
			(forward-line -1)
			(point))))
	    (funcall function begin end property prop-value)))))))

(defun org-encrypt-entry-content (beg end prop-name prop-value)
  (unless (looking-at "-----BEGIN PGP MESSAGE-----")
    (let* ((epg-context (epg-make-context nil t t))
	   (encrypted-text
	    (epg-encrypt-string
	     epg-context (buffer-substring-no-properties beg end)
	     (epg-list-keys epg-context prop-value) t)))
      (delete-region beg end)
      (insert encrypted-text))))

(defun org-encrypt-entries ()
  (interactive)
  (org-apply-to-entry-contents #'org-encrypt-entry-content "CRYPTKEY"))

(defun org-decrypt-entry ()
  (interactive)
  (save-excursion
    (let* ((props (org-entry-properties))
	   (crypt-key (and props (cdr (assoc "CRYPTKEY" props)))))
      (when (and crypt-key (stringp crypt-key))
	(org-back-to-heading t)
	(forward-line)
	(when (looking-at "-----BEGIN PGP MESSAGE-----")
	  (let* ((begin (point))
		 (end (save-excursion
			(goto-char (car (org-get-property-block begin)))
			(forward-line -1)
			(point)))
		 (epg-context (epg-make-context nil t t))
		 (decrypted-text
		  (epg-decrypt-string
		   epg-context
		   (buffer-substring-no-properties begin end))))
	    (delete-region begin end)
	    (insert decrypted-text)))))))

(provide 'org-crypt)

;;; org-crypt.el ends here
