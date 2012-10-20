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

(mapc #'add-to-load-path
      (nreverse
       (list
        user-emacs-directory

        "override/bbdb/lisp/"
        "override/gnus/contrib/"
        "override/gnus/lisp/"
        "override/org-mode/contrib/lisp/"
        "override/org-mode/lisp/"
        "override/tramp/lisp/"

        ;; Packages located elsewhere on the system...
        "~/src/ledger/lisp/"

        "/usr/local/share/emacs/site-lisp/"
        "/usr/local/opt/git/share/git-core/contrib/emacs/"
        "/Users/johnw/Archives/Languages/Ruby/Sources/ruby/misc/"
        ;;"/opt/local/share/texmf-texlive-dist/doc/latex/latex2e-help-texinfo/"
        )))

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
