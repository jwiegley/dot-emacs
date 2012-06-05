;;; init.el --- Where all the magic begins

(if (featurep 'aquamacs)
    (load "~/.emacs.d/init-aquamacs")
  (load "~/.emacs.d/load-path")
  (load "~/.emacs.d/emacs"))

;;; init.el ends here
