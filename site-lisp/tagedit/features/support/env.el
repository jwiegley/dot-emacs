;; This is an example of how you could set up this file. This setup
;; requires a directory called util in the project root and that the
;; util directory contains the testing tools ert and espuds.

(let* ((features-directory
        (file-name-directory
         (directory-file-name (file-name-directory load-file-name))))
       (project-directory
        (file-name-directory
         (directory-file-name features-directory))))
  (setq tagedit-root-path project-directory)
  (setq tagedit-util-path (expand-file-name "util" tagedit-root-path)))

(add-to-list 'load-path tagedit-root-path)
(add-to-list 'load-path (expand-file-name "espuds" tagedit-util-path))
(add-to-list 'load-path (expand-file-name "ert" tagedit-util-path))

(require 'tagedit)
(require 'espuds)
(require 'ert)

(eval-after-load 'sgml-mode
  '(progn
     (tagedit-add-experimental-features)
     (tagedit-add-paredit-like-keybindings)))

(Setup)

(Before
 (switch-to-buffer
  (get-buffer-create "tagedit-tests.html"))
 (require 'sgml-mode)
 (te/conclude-tag-edit)
 (erase-buffer)
 (html-mode)
 (tagedit-mode 1))

(After
 ;; After each scenario is run
 )

(Teardown
 ;; After when everything has been run
 )
