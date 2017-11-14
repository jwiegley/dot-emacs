(setq package-user-dir
      (expand-file-name (format ".cask/%s/elpa" emacs-version)))
(package-initialize)
(message "ELPA dir: %S" package-user-dir)
(add-to-list 'load-path default-directory)

