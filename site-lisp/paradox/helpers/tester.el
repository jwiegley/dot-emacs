(progn
  (add-to-list 'load-path (expand-file-name "../"))
  (add-to-list 'load-path (expand-file-name "./"))
  (setq package-user-dir "~/oi")
  (require 'paradox)
  (call-interactively 'paradox-list-packages))
