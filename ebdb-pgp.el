;;; ebdb-pgp.el --- Interaction between EBDB and PGP  -*- lexical-binding: t; -*-

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

;; Interaction between EDBD and PGP encryption/signing.  This file was
;; copied from bbdb-pgp.el, originally written by Kevin Davidson and
;; Gijs Hillenius.

;;; Code:

(require 'message)
(require 'ebdb-com)

(declare-function ebdb-mua-message-header "ebdb-mua")

(defcustom ebdb-pgp-default-action nil
  "Default action when sending a message and the recipients are not in EBDB.
This should be one of the following symbols:
  nil             Do nothing
  sign            Sign the message
  sign-query      Query whether to sign the message
  encrypt         Encrypt the message
  encrypt-query   Query whether to encrypt the message
See info node `(message)security'."
  :type '(choice
	  (const :tag "Do Nothing" nil)
	  (const :tag "Encrypt" encrypt)
	  (const :tag "Query encryption" encrypt-query)
	  (const :tag "Sign" sign)
	  (const :tag "Query signing" sign-query))
  :group 'ebdb-utilities-pgp)

(defcustom ebdb-pgp-ranked-actions
  '(encrypt-query sign-query encrypt sign)
  "Ranked list of actions when sending a message.
If a message has multiple recipients such that their EBDB records specify
different actions for this message, `ebdb-pgp' will perform the action
which appears first in `ebdb-pgp-ranked-actions'.
This list should include the following four symbols:
  sign            Sign the message
  sign-query      Query whether to sign the message
  encrypt         Encrypt the message
  encrypt-query   Query whether to encrypt the message."
  :type '(repeat (symbol :tag "Action"))
  :group 'ebdb-utilities-pgp)

(defcustom ebdb-pgp-headers '("To" "Cc")
  "Message headers to look at."
  :type '(repeat (string :tag "Message header"))
  :group 'ebdb-utilities-pgp)

(defcustom ebdb-pgp-method 'pgpmime
  "Default method for signing and encrypting messages.
It should be one of the keys of `ebdb-pgp-method-alist'.
The default methods include
  pgp       Add MML tags for PGP format
  pgpauto   Add MML tags for PGP-auto format
  pgpmime   Add MML tags for PGP/MIME
  smime     Add MML tags for S/MIME
See info node `(message)security'."
  :type '(choice
	  (const :tag "MML PGP" pgp)
	  (const :tag "MML PGP-auto" pgpauto)
	  (const :tag "MML PGP/MIME" pgpmime)
	  (const :tag "MML S/MIME" smime)
	  (symbol :tag "Custom"))
  :group 'ebdb-utilities-pgp)

(defcustom ebdb-pgp-method-alist
  '((pgp mml-secure-message-sign-pgp
         mml-secure-message-encrypt-pgp)
    (pgpmime mml-secure-message-sign-pgpmime
             mml-secure-message-encrypt-pgpmime)
    (smime mml-secure-message-sign-smime
           mml-secure-message-encrypt-smime)
    (pgpauto mml-secure-message-sign-pgpauto
             mml-secure-message-encrypt-pgpauto))
  "Alist of methods for signing and encrypting a message with `ebdb-pgp'.
Each method is a list (KEY SIGN ENCRYPT).
The symbol KEY identifies the method.  The function SIGN signs the message;
the function ENCRYPT encrypts it.  These functions take no arguments.
The default methods include
  pgp       Add MML tags for PGP format
  pgpauto   Add MML tags for PGP-auto format
  pgpmime   Add MML tags for PGP/MIME
  smime     Add MML tags for S/MIME
See info node `(message)security'."
  :type '(repeat (list (symbol :tag "Key")
                       (symbol :tag "Sign method")
                       (symbol :tag "Encrypt method")))
  :group 'ebdb-utilities-pgp)

;;;###autoload
(defclass ebdb-field-pgp (ebdb-field-user)
  ((action
    :initarg :action
    :type symbol
    :custom (choice
	     (const :tag "Encrypt" encrypt)
	     (const :tag "Query encryption" encrypt-query)
	     (const :tag "Sign" sign)
	     (const :tag "Query signing" sign-query))
    :documentation
    "A symbol indicating what action to take when sending a
    message to this contact."))
  :documentation "A field defining a default signing/encryption
  action for a record.  This action is taken by calling
  `ebdb-pgp' in a message/mail composition buffer, or by adding
  that function to the message/mail-send-hook."
    :human-readable "pgp action")

(cl-defmethod ebdb-string ((field ebdb-field-pgp))
  (symbol-name (slot-value field 'action)))

(cl-defmethod ebdb-read ((class (subclass ebdb-field-pgp)) &optional slots obj)
  (let ((val (intern (ebdb-read-string
		      "PGP action: " (when obj (slot-value obj 'action))
		      ebdb-pgp-ranked-actions t))))
    (cl-call-next-method class (plist-put slots :action val) obj)))

;;;###autoload
(defun ebdb-pgp ()
  "Add PGP MML tags to a message according to the recipients' EBDB records.

Use it by adding a \"pgp action\" field to one or more records.

When sending a message to those records (ie, the records appear
in `ebdb-pgp-headers' headers), this grabs the action from their
`ebdb-field-pgp' field.  If multiple records propose different
actions, perform the action which appears first in
`ebdb-pgp-ranked-actions'.  If this proposes no action at all,
use `ebdb-pgp-default-action'.  The variable `ebdb-pgp-method'
defines the method which is actually used for signing and
encrypting.

This command works with both `mail-mode' and `message-mode' to send
signed or encrypted mail.

This file does not automatically set up hooks for signing and
encryption, see Info node `(message)Signing and encryption' for
reasons why.  Instead, you might want to call the command
`ebdb-pgp' manually, then call `mml-preview'.

If you do decide to set up automatic signing/encryption hooks,
use one of the following, as appropriate:

(add-hook 'message-send-hook 'ebdb-pgp)
(add-hook 'mail-send-hook 'ebdb-pgp)"
  (interactive)
  (save-excursion
    (save-restriction
      (widen)
      (message-narrow-to-headers)
      (when mail-aliases
        ;; (sendmail-sync-aliases) ; needed?
        (expand-mail-aliases (point-min) (point-max)))
      (let* (field
	     (actions
              (or (delq nil
                       (delete-dups
                        (mapcar
                         (lambda (record)
                           (when (setq
				    field (car-safe (ebdb-record-field
						     record 'ebdb-field-pgp)))
			       (slot-value field 'action)))
                         (delete-dups
                          (apply 'nconc
                                 (mapcar
                                  (lambda (address)
                                    (ebdb-message-search (car address)
                                                         (cadr address)))
                                  (ebdb-extract-address-components
                                   (mapconcat
                                    (lambda (header)
                                      (ebdb-mua-message-header header))
                                    ebdb-pgp-headers ", ")
                                   t)))))))
                 (and ebdb-pgp-default-action
                      (list ebdb-pgp-default-action)))))
        (when actions
          (widen) ; after analyzing the headers
          (let ((ranked-actions ebdb-pgp-ranked-actions)
                action)
            (while ranked-actions
              (if (memq (setq action (pop ranked-actions)) actions)
                  (cond ((or (eq action 'sign)
                             (and (eq action 'sign-query)
                                  (y-or-n-p "Sign message? ")))
                         (funcall (nth 1 (assq ebdb-pgp-method
                                               ebdb-pgp-method-alist)))
                         (setq ranked-actions nil))
                        ((or (eq action 'encrypt)
                             (and (eq action 'encrypt-query)
                                  (y-or-n-p "Encrypt message? ")))
                         (funcall (nth 2 (assq ebdb-pgp-method
                                               ebdb-pgp-method-alist)))
                         (setq ranked-actions nil)))))))))))

(provide 'ebdb-pgp)
;;; ebdb-pgp.el ends here
