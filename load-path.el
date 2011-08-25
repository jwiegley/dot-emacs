;;;_* initial packages

(defconst user-lisp-directory
  (expand-file-name "lisp/" user-emacs-directory))
(defconst user-site-lisp-directory
  (expand-file-name "site-lisp/" user-emacs-directory))
(defconst user-override-directory
  (expand-file-name "override/" user-emacs-directory))
(defconst user-el-get-directory
  (expand-file-name "el-get/" user-emacs-directory))
(defconst user-staging-directory
  (expand-file-name "staging/" user-emacs-directory))

;; Add top-level lisp directories, in case they were not setup by the
;; environment.
(dolist (dir (list user-lisp-directory
                   user-site-lisp-directory
                   user-override-directory
                   user-el-get-directory))
 (dolist (entry (directory-files-and-attributes dir))
   (if (cadr entry)
       (add-to-list 'load-path (expand-file-name (car entry) dir)))))

(dolist (path (nreverse
               (list "override/eshell/"
                     "override/gnus/contrib/"
                     "override/gnus/lisp/"
                     "override/org-mode/contrib/lisp/"
                     "override/org-mode/lisp/"
                     "override/tramp/lisp/"

                     ;; Packages with Lisp code in subdirectories...
                     "site-lisp/anything/extensions/"
                     "site-lisp/auctex/preview/"
                     "site-lisp/bbdb/lisp/"
                     "site-lisp/bbdb/bits/"
                     "site-lisp/doxymacs/lisp/"
                     "site-lisp/ess/lisp/"
                     "site-lisp/session/lisp/"
                     "site-lisp/slime/contrib/"

                     ;; Packages located elsewhere on the system...
                     "/opt/local/share/emacs/site-lisp/"
                     "/opt/local/share/doc/git-core/contrib/emacs/"

                     "~/src/ledger/lisp/"
                     )))
  (setq path (expand-file-name path user-emacs-directory)
        load-path (delete path load-path)
        load-path (delete (file-name-as-directory path) load-path))

  (add-to-list 'load-path path))

(provide 'load-path)

;;; load-path.el ends here
