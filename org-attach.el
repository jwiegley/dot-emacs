;;; org-attach.el --- Manage file attachments to org-mode tasks

;; Copyright (C) 2008  John Wiegley

;; Author: John Wiegley <johnw@newartisans.com>
;; Keywords: org data task
;; Version: 1.00
;; location: http://www.newartisans.com/software/emacs.html

;; This file is not yet part of GNU Emacs.

;; This module is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published
;; by the Free Software Foundation; either version 2, or (at your
;; option) any later version.

;; This module is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;; At the moment, this code only works on OS X.

;; Also, the keybindings it uses are hacked into the global C-c user
;; keyspace, which is very bad form.

;; Anyway, here's how you use it: while point is on an org-mode task, in
;; either the org-mode buffer itself or the agenda view, you have the
;; following keys available:
;;
;; C-c x a    Select a file and move it into the task's attachment
;;            directory.
;;
;; C-c x z    Synchronize the current task with its attachment
;;            directory, in case you added attachments yourself.
;;
;; C-c x o    Open current task's attachment, if there is only one.
;; C-c x o    Also open the attachment, but using the Finder.
;;
;; C-c x f    Open current task's attachment directory in dired.
;; C-c x F    Also open the directory, but using the Finder.
;;
;; C-c x D    Delete all of a task's attachments.  A safer way is
;;            to open the directory in dired and delete from there.
;;
;; Attachments are managed in a special directory called "data", which
;; is in the same directory as the org-mode file.  If this data
;; directory is initialized as a Git repository, then org-attach will
;; automatically commit changes when it sees them.
;;
;; Attachment directories are identified using a UUID generated for the
;; task which has the attachments.  These are added as property to the
;; task when necessary, and should not be deleted or changed by the
;; user, ever.  UUIDs are generated using the shell command "uuidgen".

(eval-when-compile
  (require 'cl))

(defun org-attach-dir (&optional create-if-not-exists-p)
  (let ((uuid (org-entry-get (point) "UUID")))
    (when (or uuid create-if-not-exists-p)
      (unless uuid
	(let ((uuid-string (shell-command-to-string "uuidgen")))
	  (setf uuid-string
		(substring uuid-string 0 (1- (length uuid-string))))
	  (org-entry-put (point) "UUID" uuid-string)
	  (setf uuid uuid-string)))
      (let ((attach-dir (format "data/%s/%s"
				(substring uuid 0 2)
				(substring uuid 2))))
	(if (and create-if-not-exists-p
		 (not (file-directory-p attach-dir)))
	    (make-directory attach-dir t))
	(and (file-exists-p attach-dir)
	     attach-dir)))))

(defun org-attach-commit ()
  (if (file-exists-p "data/.git")
      (shell-command
       (concat "(cd data; "
	       " git add .; "
	       " git ls-files --deleted -z | xargs -0 git rm; "
	       " git commit -m 'Synchronized attachments')"))))

(defun org-attach-create (file &optional visit-dir)
  (interactive "fFile to keep as an attachment: \nP")
  (let ((basename (file-name-nondirectory file)))
    (org-entry-add-to-multivalued-property (point) "Attachments"
					   basename)
    (let ((attach-dir (org-attach-dir t)))
      (rename-file file (expand-file-name basename attach-dir))
      (org-attach-commit)
      (if visit-dir
	  (dired attach-dir)
	(message "File \"%s\" is now a task attachment." basename)))))

(defun org-attach-delete ()
  (interactive)
  (org-entry-delete (point) "Attachments")
  (let ((attach-dir (org-attach-dir)))
    (if attach-dir
	(shell-command (format "rm -fr %s" attach-dir))))
  (org-attach-commit))

(defun org-attach-sync ()
  (interactive)
  (org-attach-commit)
  (org-entry-delete (point) "Attachments")
  (let ((attach-dir (org-attach-dir)))
    (when attach-dir
      (let ((files (directory-files attach-dir)))
	(dolist (file files)
	  (unless (string-match "^\\." file)
	    (org-entry-add-to-multivalued-property
	     (point) "Attachments" file)))))))

(defun org-attach-reveal ()
  (interactive)
  (let ((attach-dir (org-attach-dir t)))
    (dired attach-dir)))

(defun org-attach-reveal-external ()
  (interactive)
  (let ((attach-dir (org-attach-dir t)))
    (shell-command (format "open \"%s\"" (expand-file-name attach-dir)))))

(defun org-attach-open ()
  (interactive)
  (let ((attach-dir (org-attach-dir t)))
    (find-file (expand-file-name (org-entry-get (point) "Attachments")
				 attach-dir))))

(defun org-attach-open-external ()
  (interactive)
  (let ((attach-dir (org-attach-dir t)))
    (shell-command
     (format "open \"%s\""
	     (expand-file-name (org-entry-get (point) "Attachments")
			       attach-dir)))))

(define-key mode-specific-map [?x ?a] 'org-attach-create)
(define-key mode-specific-map [?x ?o] 'org-attach-open)
(define-key mode-specific-map [?x ?O] 'org-attach-open-external)
(define-key mode-specific-map [?x ?f] 'org-attach-reveal)
(define-key mode-specific-map [?x ?F] 'org-attach-reveal-external)
(define-key mode-specific-map [?x ?z] 'org-attach-sync)
(define-key mode-specific-map [?x ?D] 'org-attach-delete)

(provide 'org-attach)

;;; org-attach.el ends here
