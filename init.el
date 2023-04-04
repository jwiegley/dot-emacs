(add-to-list 'load-path "~/.emacs.d/lisp/org-mode/lisp")

(require 'org)

(org-babel-load-file (expand-file-name "emacs.org" user-emacs-directory))
