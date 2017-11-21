;; Usage:
;;
;;   emacs -Q -l tests/run-test.el           # interactive mode
;;   emacs -batch -Q -l tests/run-test.el    # batch mode


;; Utils
(defun ws-butler-test-join-path (path &rest rest)
  "Join a list of PATHS with appropriate separator (such as /).

\(fn &rest paths)"
  (if rest
      (concat (file-name-as-directory path) (apply 'ws-butler-test-join-path rest))
    path))

(defvar ws-butler-test-dir (file-name-directory load-file-name))
(defvar ws-butler-root-dir (file-name-as-directory (expand-file-name ".." ws-butler-test-dir)))


;; Setup `load-path'
(mapc (lambda (p) (add-to-list 'load-path p))
      (list ws-butler-test-dir
            ws-butler-root-dir))


;; Use ERT from github when this Emacs does not have it
(unless (locate-library "ert")
  (add-to-list
   'load-path
   (ws-butler-test-join-path ws-butler-root-dir "lib" "ert" "lisp" "emacs-lisp"))
  (require 'ert-batch)
  (require 'ert-ui))


;; Load tests
(load "ws-butler-tests")


;; Run tests
(if noninteractive
    (ert-run-tests-batch-and-exit)
  (ert t))
