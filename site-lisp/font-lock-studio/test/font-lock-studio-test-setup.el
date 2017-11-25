;;; font-lock-studio-test-setup.el --- Setup and execute all tests

;;; Commentary:

;; This package sets up a suitable enviroment for testing
;; font-lock-studio, and executes the tests.
;;
;; Usage:
;;
;;   emacs -q -l font-lock-studio-test-setup.el
;;
;; Note that this package assumes that some packages are located in
;; specific locations.

;;; Code:

(setq inhibit-startup-screen t)
(prefer-coding-system 'utf-8)

(defvar font-lock-studio-test-setup-directory
  (if load-file-name
      (file-name-directory load-file-name)
    default-directory))

(dolist (dir '("." ".." "../../faceup" "../../../lisp"))
  (add-to-list 'load-path
               (expand-file-name dir font-lock-studio-test-setup-directory)))

(require 'font-lock-studio)

(require 'font-lock-studio-test)

(ert t)

;;; font-lock-studio-test-setup.el ends here
