(require 'cl) ; for mapcar* block and return

(defvar hsenv-active-environment nil)

(defconst hsenv-path-prepend-file "path_var_prependix")
(defconst hsenv-ghc-package-path-file "ghc_package_path_var")

(defun hsenv-compare-ghc-version (version-string &optional threshold)
  (save-match-data
    (when (string-match "\\(\\([0-9]+\\.?\\)+\\)$" version-string)
      (let* ((threshold (or threshold (list 7 6 1)))
             (version (match-string 1 version-string))
             (version-numbers
              (mapcar #'string-to-number (split-string version "\\."))))
        (block nil
            (mapcar* #'(lambda (v1 v2)
                         (when (< v1 v2)
                           (return 'lt))
                         (when (> v1 v2)
                           (return 'gt)))
                     version-numbers
                     threshold)
            'eq)))))

(defun hsenv-select-opt-suffix ()
  (let ((cmp-result (hsenv-compare-ghc-version (shell-command-to-string "ghc --version"))))
    (unless cmp-result
      (error "Cannot get GHC version"))
    (if (eq 'lt cmp-result)
        "conf"
      "db")))

(defun hsenv-valid-dirp (hsenv-dir)
  (let ((valid (and (file-accessible-directory-p hsenv-dir)
                    (file-readable-p
                     (concat hsenv-dir hsenv-path-prepend-file))
                    (file-readable-p
                     (concat hsenv-dir hsenv-ghc-package-path-file)))))
    (when (not valid)
      (message "The environment you provided is not a valid hsenv directory (%s)."
               hsenv-dir))
    valid))

(defun hsenv-is-not-active ()
  (let ((is-not-active (not hsenv-active-environment)))
    (when (not is-not-active)
      (message "An hsenv is already activated (%s)."
               (assoc-default 'dir hsenv-active-environment)))
    is-not-active))

(defun hsenv-is-active ()
  (let ((is-active hsenv-active-environment))
    (when (not is-active)
      (message "No hsenv currently activated."))
    is-active))

(defun hsenv-read-file-content (hsenv-dir file)
  (with-temp-buffer
    (insert-file-contents (concat hsenv-dir file))
    (replace-regexp-in-string "\n+$" "" (buffer-string))))

(defun hsenv-replace-pkg (template package-dbs)
  (apply #'concat
         (mapcar #'(lambda (db)
                     (concat template db))
                 package-dbs)))

(defun hsenv-activate-environment (hsenv-dir env env-name)
  "Activate the Virtual Haskell Environment in directory HSENV-DIR"
  (when (and (hsenv-valid-dirp hsenv-dir)
             (hsenv-is-not-active))

    ; Prepend paths
    (let* ((new-hsenv-active-environment (list `(path-backup . ,(getenv "PATH"))
                                               `(exec-path-backup . ,exec-path)
                                               `(dir . ,hsenv-dir)))
           (path-prepend (hsenv-read-file-content hsenv-dir
                                                  hsenv-path-prepend-file))
           (package-db (hsenv-read-file-content hsenv-dir hsenv-ghc-package-path-file))
           (package-dbs (split-string package-db ":"))
           (suffix (hsenv-select-opt-suffix)))
      (setenv "PATH" (concat  path-prepend ":" (getenv "PATH")))
      (setq exec-path (append (split-string path-prepend ":") exec-path))
      (setenv "PACKAGE_DB_FOR_GHC"
              (concat "-no-user-package-" suffix
                      (hsenv-replace-pkg (concat " -package-" suffix "=") package-dbs)))
      (setenv "PACKAGE_DB_FOR_CABAL"
              (hsenv-replace-pkg " --package-db=" package-dbs))
      (setenv "PACKAGE_DB_FOR_GHC_PKG"
              (concat "--no-user-package-" suffix
                      (hsenv-replace-pkg (concat " --package-" suffix "=") package-dbs)))
      (setenv "PACKAGE_DB_FOR_GHC_MOD"
              (concat "-g -no-user-package-" suffix
                      (hsenv-replace-pkg (concat " -g -package-" suffix "=") package-dbs)))
      (setenv "HASKELL_PACKAGE_SANDBOX" package-db)
      (setenv "HSENV" env)
      (setenv "HSENV_NAME" env-name)
      ; Save an hsenv active environment and backup paths
      (setq hsenv-active-environment new-hsenv-active-environment)
      (message "Environment activated: %s" hsenv-dir))))

(defun hsenv-env-name-from-dir (directory)
  "Return the name of an environment based on DIRECTORY."
  (save-match-data
    (let ((offs (string-match "[.]hsenv\\([^\\/]*\\)$" directory)))
      (cond
       (offs
        (substring directory (+ 6 offs)))
       ((string-match "[.]hsenv$" directory)
        "(default)")
       (t
        (error "Not an hsenv directory %s" directory))))))

;;; Tests:
;; (and (equal "foo" (hsenv-env-name-from-dir "/home/bar/baz/.hsenv_foo"))
;;      (equal "foo" (hsenv-env-name-from-dir "/home/bar/.hsenv_boo/baz/.hsenv_foo"))
;;      (equal "(default)"
;;             (hsenv-env-name-from-dir "/home/bar/.hsenv_boo/baz/.hsenv")))

(defun hsenv-make-env (directory)
  (cons (hsenv-env-name-from-dir directory) directory))

(defun hsenv-env-name (env)
  (car env))

(defun hsenv-env-dir (env)
  (cdr env))

(defun hsenv-deactivate ()
  "Deactivate the Virtual Haskell Environment"
  (interactive)
  (when (hsenv-is-active)
    ; Restore paths
    (setenv "PATH" (assoc-default 'path-backup hsenv-active-environment))
    (setq exec-path (assoc-default 'exec-path-backup hsenv-active-environment))
    ; Unset variables
    (setenv "PACKAGE_DB_FOR_GHC")
    (setenv "PACKAGE_DB_FOR_GHC_PKG")
    (setenv "PACKAGE_DB_FOR_GHC_MOD")
    (setenv "PACKAGE_DB_FOR_CABAL")
    (setenv "HSENV")
    (setenv "HSENV_NAME")
    (setenv "HASKELL_PACKAGE_SANDBOX")
    ; Destroy the hsenv active environment
    (let ((old-dir (cdr (assoc 'dir hsenv-active-environment))))
      (setq hsenv-active-environment nil)
      (message "Environment deactivated: %s" old-dir))))

(defun hsenv-activate-dir (dir)
  (let ((environments (hsenv-list-environments dir)))
    (if (null environments)
        (message "Directory %s does not contain any hsenv." dir)
      (let* ((env-name
              (if (= 1 (length environments))
                  (hsenv-env-name (car environments))
                (completing-read "Environment:"
                                 (mapcar #'hsenv-env-name environments))))
             (env (assoc env-name environments)))
        (let* ((hsenv-dir-name (hsenv-env-dir env))
               (hsenv-dir (file-name-as-directory hsenv-dir-name)))
          (hsenv-activate-environment hsenv-dir dir env-name))))))

(defun hsenv-list-environments (dir)
  "Returns an assoc list of all environments avaliable in DIR.

The assoc list contains pairs of the form (NAME . DIRECTORY)."
  (let ((hsenv-dirs (directory-files dir t "^\\.hsenv\\(_.*\\)?$")))
    (mapcar #'hsenv-make-env hsenv-dirs)))

(defun hsenv-activate (&optional select-dir)
  "Activate a Virtual Haskell Environment"
  (interactive "P")
  (if (or select-dir
          (null (hsenv-list-environments default-directory)))
      (hsenv-activate-dir (read-directory-name "Directory:"))
    (hsenv-activate-dir default-directory)))

(provide 'hsenv)
