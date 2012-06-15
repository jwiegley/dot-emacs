;;; persistent-scratch --- Save scratch buffer between sessions

;; Copyright (C) 2012 J.V. Toups

;; Author: J.V. Toups <unknown@unknown.org>
;; Created: 14 Jun 2012
;; Version: 1.0
;; Keywords: scratch emacs initial startup
;; X-URL: https://github.com/jwiegley/persistent-scratch

;;; Commentary:

;; Emacs has a handy, but sometimes decried, feature called the "scratch"
;; buffer. This is a special buffer which is created upon startup and allows
;; the user to type in and evaluate Emacs Lisp code. Handy for editing tasks
;; too specific (or not useful enough) to put into an function and handy for
;; exploratory Emacs Lisp interactive development (although this development
;; is just as easily accomplished in any file in Lisp mode).
;;
;; One problem with *scratch* is that its tempting to put significant bits of
;; code (and other information) into it. This isn't a problem in itself, but
;; *scratch* isn't associated with a file, and its contents are lost without
;; warning when Emacs is closed. Today we'll modify the default behavior of
;; Emacs so that it saves the scratch buffer to a file on exit and loads it
;; back in on startup.

(defgroup persistent-scratch nil
  "Save scratch buffer between sessions"
  :group 'initialization)

(defcustom persistent-scratch-file-name "~/.emacs-persistent-scratch"
  "Location of *scratch* file contents for persistent-scratch."
  :type 'directory
  :group 'persistent-scratch)

(defun save-persistent-scratch ()
  "Write the contents of *scratch* to the file name
`persistent-scratch-file-name'."
  (with-current-buffer (get-buffer-create "*scratch*")
    (write-region (point-min) (point-max) persistent-scratch-file-name)))

(defun load-persistent-scratch ()
  "Load the contents of `persistent-scratch-file-name' into the
  scratch buffer, clearing its contents first."
  (if (file-exists-p persistent-scratch-file-name)
      (with-current-buffer (get-buffer "*scratch*")
        (delete-region (point-min) (point-max))
        (insert-file-contents persistent-scratch-file-name))))

(push #'load-persistent-scratch after-init-hook)
(push #'save-persistent-scratch kill-emacs-hook)

(run-with-idle-timer 300 t 'save-persistent-scratch)

(provide 'persistent-scratch)

;;; persistent-scratch.el ends here
