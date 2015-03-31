;;; tramp2-hack.el --- Hooks and hacks to allow better file-operation handling

;; Copyright (C) 2001 Free Software Foundation, Inc.

;;; Commentary:

;; The code and routines in here ensure that we can hook into some operations
;; that need specific support for tramp files but that don't, by default,
;; provide the file-handler hooks for doing so.

;; This code rudely installs it's hooks through the system when loaded. This
;; violates policy but, hell, it's rude enough as it is. :)

;; To make it possible for future versions of the routines hacked on in here
;; to improve their support for file handlers, every hack should test that it
;; is needed before it makes any system changes.

;;; Code:
(eval-when-compile
  (require 'tramp2))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; `file-remote-p' does not use a file operation to test, it has hard-coded
;; knowledge about efs and, presumably, ange-ftp. This should be fixed but,
;; until then, we code around it.
;;
;; We do this by replacing the original version with one that uses a
;; file-operation, then call the original only if that does nothing for us.
(when (fboundp 'file-remote-p)
  
(let ((file-name-handler-alist '(("test-file" . (lambda (&rest args) (setq pass t)))))
      (pass nil))
  (file-remote-p "test-file")
  (unless pass

(or (fboundp 'tramp2-original-file-remote-p)
    (fset 'tramp2-original-file-remote-p (symbol-function 'file-remote-p)))
(defalias 'file-remote-p 'tramp2-sane-file-remote-p)
    
(defun tramp2-sane-file-remote-p (file)
  "Determine if a file is remote.
This uses the file operation `file-remote-p' to determine if the
file is remote or not. This is much nicer than the original version
which hard-coded the knowledge about remote file handlers.

The original definition is called `tramp2-original-file-remote-p'."
  (when allow-remote-paths
    (let ((handler (find-file-name-handler file 'file-remote-p)))
      (if handler
	  (funcall handler 'file-remote-p file)
	(tramp2-original-file-remote-p file)))))

))

)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; EFS and ange-ftp have some, er, issues with the tramp paths. Specifically,
;; they treat our paths as their own which, unsurprisingly, does not work real
;; well.
;;
;; Sometimes their handlers get through despite our best efforts. This
;; requires us to hack around them, dammit.

(defun tramp2-hack-efs-ftp-path ()
  "Install the hacks for EFS ftp path handling."
  (require 'advice)
  
  (defadvice efs-ftp-path (around tramp2-safe-efs-ftp-path activate)
    "Cause efs-ftp-path to fail when the path is a TRAMP path."
    (save-match-data
      (unless (string-match tramp2-path-tag (ad-get-arg 0))
	ad-do-it))))

(if (fboundp 'efs-ftp-path)
    (tramp2-hack-efs-ftp-path)
  (eval-after-load "efs-cu" (tramp2-hack-efs-ftp-path)))



(provide 'tramp2-hack)

;;; tramp2-hack.el ends here
