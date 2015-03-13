;;; cmake-font-lock-test-setup.el --- Setup and execute all tests

;;; Commentary:

;; This package sets up a suitable enviroment for testing
;; cmake-font-lock, and executes the tests.
;;
;; Usage:
;;
;;   emacs -q -l cmake-font-lock-test-setup.el
;;
;; Note that this package assumes that some packages are located in
;; specific locations.

;;; Code:

(setq inhibit-startup-screen t)
(prefer-coding-system 'utf-8)

(defvar cmake-font-lock-test-setup-directory
  (if load-file-name
      (file-name-directory load-file-name)
    default-directory))

(dolist (dir '("." ".." "../../faceup" "../../../lisp"))
  (add-to-list 'load-path
               (concat cmake-font-lock-test-setup-directory dir)))

(require 'cmake-mode)
(require 'cmake-font-lock)
(add-hook 'cmake-mode-hook 'cmake-font-lock-activate)

(require 'cmake-font-lock-test-simple)
(require 'cmake-font-lock-test-facit)

(ert t)

;;; cmake-font-lock-test-setup.el ends here
