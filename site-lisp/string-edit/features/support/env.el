(let* ((current-directory (file-name-directory load-file-name))
       (features-directory (expand-file-name ".." current-directory))
       (project-directory (expand-file-name ".." features-directory)))
  (setq string-edit-root-path project-directory))

(add-to-list 'load-path string-edit-root-path)

(require 'string-edit)
(require 'espuds)
(require 'ert)

(Before
 (switch-to-buffer
  (get-buffer-create "*string-edit-main-buffer*"))
 (delete-other-windows)
 (erase-buffer)
 (fundamental-mode)
 (deactivate-mark))

(After)
