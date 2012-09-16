;;; load-path.el

(defconst user-data-directory
  (expand-file-name "data/" user-emacs-directory))
(defconst user-lisp-directory
  (expand-file-name "lisp/" user-emacs-directory))
(defconst user-lib-directory
  (expand-file-name "lib/" user-emacs-directory))
(defconst user-site-lisp-directory
  (expand-file-name "site-lisp/" user-emacs-directory))
(defconst user-override-directory
  (expand-file-name "override/" user-emacs-directory))

(defun add-to-load-path (path &optional dir)
  (setq load-path
        (cons (expand-file-name path (or dir user-emacs-directory)) load-path)))

;; Add top-level lisp directories, in case they were not setup by the
;; environment.
(dolist (dir (nreverse
              (list user-override-directory
                    user-lisp-directory
                    user-lib-directory
                    user-site-lisp-directory)))
  (dolist (entry (nreverse (directory-files-and-attributes dir)))
    (if (cadr entry)
        (add-to-load-path (car entry) dir))))

(if (and (boundp 'misc-dirs)
         misc-dirs)
    (mapc #'add-to-load-path
          (nreverse misc-dirs)))

(if (and (boundp 'override-dirs)
         override-dirs)
    (mapc #'add-to-load-path
          (nreverse override-dirs)))

(add-to-load-path user-emacs-directory)

(let ((cl-p load-path))
  (while cl-p
    (setcar cl-p (file-name-as-directory
                  (expand-file-name (car cl-p))))
    (setq cl-p (cdr cl-p))))

(setq load-path (delete-dups load-path))

;; (require 'autoloads nil t)
(require 'cus-load nil t)

(provide 'load-path)

;;; load-path.el ends here
