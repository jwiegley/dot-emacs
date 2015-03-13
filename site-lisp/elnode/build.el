;; Batch test Elnode

(package-initialize)
(package-refresh-contents)
(let ((tar-package
       (concat
        (file-name-directory
         (or (buffer-file-name)
             load-file-name))
        (car (reverse command-line-args)))))
  (message "the package is: %s" tar-package)
  (package-install-file tar-package))

;; End
