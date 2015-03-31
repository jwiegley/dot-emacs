;;; tramp-vc.el --- Version control integration for TRAMP.el

;; Copyright (C) 2000-2013 Free Software Foundation, Inc.

;; Author: Daniel Pittman <daniel@danann.net>
;; Keywords: comm, processes
;; Package: tramp

;; This file is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; GNU Emacs is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; See the main module, 'tramp.el' for discussion of the purpose of
;; Tramp.  This module provides integration between remote files
;; accessed by Tramp and the Emacs version control system.

;; Since Tramp 2.1, most of the advices are not necessary any longer
;; because `start-process' and `call-process' are supported by file
;; name handler functions now.

;;; Code:

(require 'tramp)

(require 'vc)
;; Old VC defines vc-rcs-release in vc.el, new VC requires extra module.
(eval-and-compile
  (unless (boundp 'vc-rcs-release)
    (require 'vc-rcs)))

;; -- vc --
;; Wire ourselves into the VC infrastructure...

;; We rely on the fact that `file' is bound when this is called.
;; This appears to be the case everywhere in vc.el and vc-hooks.el
;; as of Emacs 20.5.

;; The following defadvice is no longer necessary after changes in VC
;; on 2006-01-25, Andre.

;; That means either GNU Emacs >= 22 or the "new vc" package from XEmacs
;; packages collection; as of 2007-09-06, test for availability of
;; `vc-find-version' works for both of those cases.
(unless (fboundp 'vc-find-version)
  (defadvice vc-user-login-name
    (around tramp-vc-user-login-name activate)
    "Support for files on remote machines accessed by Tramp."
    ; Pacify byte-compiler.
    (let ((file (when (boundp 'file) (symbol-value 'file))))
      (or (and (eq (tramp-find-foreign-file-name-handler file)
		   'tramp-sh-file-name-handler)
	       (with-parsed-tramp-file-name file nil
		 (let ((uid (ad-get-arg 0)))
		   (if (integerp uid)
		       (let ((tmpfile
			      (tramp-make-tramp-file-name
			       method user host
			       (tramp-make-tramp-temp-file v))))
			 (unwind-protect
			     (save-excursion
			       (set-file-times tmpfile (current-time))
			       (tramp-send-command
				v (format "chown %d %s" uid tmpfile))
			       (setq ad-return-value
				     (nth 2 (file-attributes
					     tmpfile 'string))))
			   (delete-file tmpfile)))
		     (setq ad-return-value
			   (tramp-get-remote-uid v 'string))))))
	  ad-do-it)))

  (add-hook 'tramp-unload-hook
	    (lambda () (ad-unadvise 'vc-user-login-name))))


;; This function does not exist any more in Emacs-21's VC
(when (fboundp 'vc-file-owner)
  (defadvice vc-file-owner
    (around tramp-vc-file-owner activate)
    "Support for files on remote machines accessed by Tramp."
    (let ((filename (ad-get-arg 0)))
      (or (and (eq (tramp-find-foreign-file-name-handler filename)
		   'tramp-sh-file-name-handler)
	       (setq ad-return-value
		     (nth 2 (file-attributes filename 'string))))
	  ad-do-it)))

  (add-hook 'tramp-unload-hook
	    (lambda () (ad-unadvise 'vc-file-owner))))


;; We need to make the version control software backend version
;; information local to the current buffer. This is because each TRAMP
;; buffer can (theoretically) have a different VC version and I am
;; *way* too lazy to try and push the correct value into each new
;; buffer.
;;
;; Remote VC costs will just have to be paid, at least for the moment.
;; Well, at least, they will right until I feel guilty about doing a
;; botch job here and fix it. :/
;;
;; Daniel Pittman <daniel@danann.net>
;; CCC: this is probably still needed for Emacs 21.
(defun tramp-vc-setup-for-remote ()
  "Make the backend release variables buffer local.
This makes remote VC work correctly at the cost of some processing time."
  (when (and (buffer-file-name)
             (tramp-tramp-file-p (buffer-file-name)))
    (make-local-variable 'vc-rcs-release)
    (setq vc-rcs-release nil)))
(add-hook 'find-file-hooks 'tramp-vc-setup-for-remote t)
(add-hook 'tramp-unload-hook
	  (lambda ()
	    (remove-hook 'find-file-hooks 'tramp-vc-setup-for-remote)))

(add-hook 'tramp-unload-hook
	  (lambda ()
	    (unload-feature 'tramp-vc 'force)))

;; No need to load this again if anyone asks.
(provide 'tramp-vc)

;;; tramp-vc.el ends here
