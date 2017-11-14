(let* ((current-dir (file-name-directory load-file-name))
       (git-gutter+-root-dir (expand-file-name ".." current-dir)))

  (add-to-list 'load-path git-gutter+-root-dir))
