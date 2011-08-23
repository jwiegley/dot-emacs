;;;_* initial packages

(defconst user-site-lisp-directory
  (expand-file-name "site-lisp" user-emacs-directory))

(setq gnus-home-directory "~/Library/Mail/Gnus/") ; override gnus.el

;; Add other site-lisp directories, in case they were not setup by the
;; environment.

(dolist (dir (list user-site-lisp-directory
                   (expand-file-name "el-get" user-emacs-directory)))
 (dolist (entry (directory-files-and-attributes dir))
   (if (cadr entry)
       (add-to-list 'load-path (expand-file-name (car entry) dir)))))

(dolist (path
         (list "el-get/el-get"

               ;; Packages that bury their Lisp code in subdirectories...
               "site-lisp/anything/extensions"
               "site-lisp/auctex/preview"
               "site-lisp/bbdb/lisp"
               "site-lisp/bbdb/bits"
               "site-lisp/eshell"
               "site-lisp/ess/lisp"
               "site-lisp/gnus/contrib"
               "site-lisp/gnus/lisp"
               "site-lisp/org-mode/contrib/lisp"
               "site-lisp/org-mode/lisp"
               "site-lisp/session/lisp"
               "site-lisp/slime/contrib"
               "site-lisp/tramp/lisp"
               ;; Packages located elsewhere on the system...
               "staging"
               "~/src/ledger/lisp"
               "/opt/local/share/doc/git-core/contrib/emacs"
               "/opt/local/share/emacs/site-lisp"
               ))
  (setq path (expand-file-name path user-emacs-directory)
        load-path (delete path load-path)
        load-path (delete (file-name-as-directory path) load-path))

  (add-to-list 'load-path path))

(provide 'load-path)

;;; load-path.el ends here
