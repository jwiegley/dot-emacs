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
(defconst user-elpa-directory
  (expand-file-name "elpa/packages/" user-emacs-directory))

(defconst nix-site-lisp-directory
  (expand-file-name "~/.nix-profile/share/emacs/site-lisp"))

(defun add-to-load-path (path &optional dir)
  (setq load-path
        (cons (expand-file-name path (or dir user-emacs-directory)) load-path)))

;; Add top-level lisp directories, in case they were not setup by the
;; environment.
(dolist (dir (nreverse
              (list user-override-directory
                    user-lisp-directory
                    user-lib-directory
                    user-site-lisp-directory
                    ;; user-elpa-directory
                    )))
  (dolist (entry (nreverse (directory-files-and-attributes dir)))
    (if (cadr entry)
        (add-to-load-path (car entry) dir))))

(mapc #'add-to-load-path
      (nreverse
       (list
        user-emacs-directory

        "override/"
        "override/bbdb/lisp/"
        "override/gnus/contrib/"
        "override/gnus/lisp/"
        "override/org-mode/contrib/lisp/"
        "override/org-mode/lisp/"
        "override/tramp/lisp/"

        nix-site-lisp-directory
        )))

(let ((cl-p load-path))
  (while cl-p
    (setcar cl-p (file-name-as-directory
                  (expand-file-name (car cl-p))))
    (setq cl-p (cdr cl-p))))

(setq load-path (delete-dups load-path))

;; (require 'autoloads nil t)
(require 'cus-load nil t)

(defun quickping (host)
  (= 0 (call-process "/sbin/ping" nil nil nil "-c1" "-W50" "-q" host)))

(defun slowping (host)
  (= 0 (call-process "/sbin/ping" nil nil nil "-c1" "-W5000" "-q" host)))

(provide 'load-path)

;;; load-path.el ends here
