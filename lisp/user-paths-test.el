;;; user-paths-test.el --- Tests for user-paths.el -*- lexical-binding: t; -*-

;; Run with:
;;   emacs --batch -Q -l lisp/user-paths-test.el -f ert-run-tests-batch-and-exit
;;
;; These tests never touch real state.  Every root lives in a scratch
;; directory, and user-paths.el is loaded only after the environment and
;; `user-emacs-directory' point there.  Loading the library creates its
;; directories, so each of the three XDG variables must be set first.

(require 'ert)
(require 'cl-lib)

(defconst user-paths-test-root
  (file-name-as-directory (make-temp-file "user-paths-test-" t))
  "Scratch directory that stands in for the home directory.")

;; Leave nothing behind in the temporary directory.
(add-hook 'kill-emacs-hook
          (lambda () (delete-directory user-paths-test-root t)))

(defconst user-paths-test-file
  (expand-file-name "user-paths.el"
                    (file-name-directory (or load-file-name buffer-file-name)))
  "The library under test.")

(setenv "XDG_DATA_HOME" (concat user-paths-test-root "share"))
(setenv "XDG_STATE_HOME" (concat user-paths-test-root "state"))
(setenv "XDG_CACHE_HOME" (concat user-paths-test-root "cache"))
(setenv "NIX_MYENV_NAME" nil)
(setq user-emacs-directory (concat user-paths-test-root "config/emacs/"))
(make-directory user-emacs-directory t)
(load user-paths-test-file nil t)

(defconst user-paths-test--bare
  '("XDG_DATA_HOME" "XDG_STATE_HOME" "XDG_CACHE_HOME" "NIX_MYENV_NAME")
  "Environment entries that unset every variable the library reads.")

(defun user-paths-test--child (environment form &optional init-directory file)
  "Return the value of FORM in a fresh Emacs that loaded FILE.
FILE defaults to user-paths.el.  ENVIRONMENT is a list of \"VAR=value\"
strings; a bare \"VAR\" unsets that variable.  The child's home is a
scratch directory, and so is its init directory unless INIT-DIRECTORY
names another, so it cannot reach real state either."
  (let* ((home (concat user-paths-test-root "child-home/"))
         (init-directory (or init-directory (concat home ".config/emacs/")))
         ;; `call-process' starts the child in `default-directory'.  In a
         ;; checkout below the home directory that begins with "~", which
         ;; the HOME bound below would expand to a directory that does not
         ;; exist.  The child needs no particular directory, so it gets the
         ;; scratch root.
         (default-directory user-paths-test-root)
         (process-environment
          (append environment
                  (list (concat "HOME=" home))
                  process-environment)))
    (make-directory init-directory t)
    (with-temp-buffer
      (let ((status
             (call-process (expand-file-name invocation-name
                                             invocation-directory)
                           nil t nil
                           "--batch" "-Q"
                           (concat "--init-directory=" init-directory)
                           "-l" (or file user-paths-test-file)
                           "--eval" (format "(prin1 %S)" form))))
        (unless (eq status 0)
          (error "Child Emacs failed (%s): %s" status (buffer-string))))
      (goto-char (point-min))
      (read (current-buffer)))))

(ert-deftest user-paths-test-roots-follow-xdg-variables ()
  (should (equal user-data-directory
                 (concat user-paths-test-root "share/emacs/")))
  (should (equal user-state-directory
                 (concat user-paths-test-root "state/emacs/")))
  (should (equal user-cache-directory
                 (concat user-paths-test-root "cache/emacs/")))
  (should (equal (user-data "bm-repository")
                 (concat user-paths-test-root "share/emacs/bm-repository")))
  (should (equal (user-state "history")
                 (concat user-paths-test-root "state/emacs/history")))
  (should (equal (user-cache "url/")
                 (concat user-paths-test-root "cache/emacs/url/"))))

(ert-deftest user-paths-test-roots-are-distinct-and-outside-the-config ()
  (let ((roots (list user-data-directory user-state-directory
                     user-cache-directory)))
    (should (equal roots (cl-remove-duplicates roots :test #'equal)))
    (dolist (root roots)
      (should (file-name-absolute-p root))
      (should (string-suffix-p "/" root))
      (should-not (string-prefix-p (expand-file-name user-emacs-directory)
                                   root)))))

(ert-deftest user-paths-test-unusable-xdg-values-fall-back ()
  ;; The roots come from xdg.el, for which an empty or a relative value
  ;; is no value at all.
  (let ((home (concat user-paths-test-root "child-home/")))
    (dolist (value '("" "relative/path"))
      (should (equal (user-paths-test--child
                      (list (concat "XDG_DATA_HOME=" value)
                            (concat "XDG_STATE_HOME=" value)
                            (concat "XDG_CACHE_HOME=" value)
                            "NIX_MYENV_NAME")
                      '(list user-data-directory user-state-directory
                             user-cache-directory))
                     (list (concat home ".local/share/emacs/")
                           (concat home ".local/state/emacs/")
                           (concat home ".cache/emacs/")))))
    (should (equal (user-paths-test--child
                    (list (concat "XDG_STATE_HOME=" home "elsewhere")
                          "XDG_DATA_HOME" "XDG_CACHE_HOME" "NIX_MYENV_NAME")
                    'user-state-directory)
                   (concat home "elsewhere/emacs/")))))

(ert-deftest user-paths-test-table-is-well-formed ()
  (let ((variables (mapcar #'car user-paths-table)))
    (should (equal variables (cl-remove-duplicates variables))))
  (dolist (entry user-paths-table)
    (should (= (length entry) 3))
    (should (symbolp (nth 0 entry)))
    (should (memq (nth 1 entry) '(data state cache)))
    (should (stringp (nth 2 entry)))
    (should-not (file-name-absolute-p (nth 2 entry)))))

(ert-deftest user-paths-test-each-kind-has-its-root ()
  ;; One example of each kind, so that a row cannot change root unnoticed.
  (dolist (expected '((transient-values-file . data)
                      (lsp-server-install-dir . data)
                      (emojify-emojis-dir . data)
                      (persist--directory-location . data)
                      (transient-history-file . state)
                      (eshell-history-file-name . state)
                      (treemacs-persist-file . state)
                      (chess-autosave-file . state)
                      (url-configuration-directory . state)
                      (url-cache-directory . cache)
                      (pcache-directory . cache)
                      (org-persist-directory . cache)
                      (coq-lookup-cache-directory . cache)))
    (should (eq (nth 1 (assq (car expected) user-paths-table))
                (cdr expected)))))

(ert-deftest user-paths-test-table-is-applied ()
  (dolist (entry user-paths-table)
    (let* ((variable (nth 0 entry))
           (root (pcase (nth 1 entry)
                   ('data user-data-directory)
                   ('state user-state-directory)
                   ('cache user-cache-directory)))
           (value (and (boundp variable) (symbol-value variable))))
      (should (stringp value))
      (should (equal value (expand-file-name (nth 2 entry) root)))
      (should (string-prefix-p (directory-file-name root) value))
      (should-not (string-prefix-p (expand-file-name user-emacs-directory)
                                   value)))))

(ert-deftest user-paths-test-trailing-slashes-survive ()
  ;; pcache builds file names with `concat', so the slash is required.
  (should (string-suffix-p "/pcache/" pcache-directory))
  (dolist (entry user-paths-table)
    (when (string-suffix-p "/" (nth 2 entry))
      (should (string-suffix-p "/" (symbol-value (nth 0 entry)))))))

(ert-deftest user-paths-test-special-cases-are-applied ()
  (should (equal TeX-auto-private (list (user-cache "auctex/auto"))))
  ;; elpy computes its own virtualenv directory with this function; the
  ;; advice must survive the function being defined afterwards.
  (defun elpy-rpc-default-virtualenv-path ()
    "/default/elpy/rpc-venv")
  (should (equal (elpy-rpc-default-virtualenv-path)
                 (user-data "elpy/rpc-venv")))
  ;; web.el defines its cookie jar with `defconst'; the redirect has to
  ;; survive that definition.
  (should
   (equal (user-paths-test--child
           user-paths-test--bare
           '(progn
              (defconst web-cookie-jar-file "/default/web-cookies")
              (provide 'web)
              web-cookie-jar-file))
          (concat user-paths-test-root
                  "child-home/.local/state/emacs/web-cookies"))))

(ert-deftest user-paths-test-directories-are-private ()
  (dolist (directory (list user-data-directory
                           user-state-directory
                           user-cache-directory
                           (user-state "eshell/")
                           (user-state "url/")
                           user-paths-tree-sitter-directory))
    (should (file-directory-p directory))
    (should (= (file-modes directory) #o700))))

;; `ert-run-tests-batch' points the native-compilation cache at a scratch
;; directory of its own, so this is checked in a child Emacs.
(ert-deftest user-paths-test-native-cache-is-redirected ()
  (skip-unless (and (featurep 'native-compile)
                    (fboundp 'startup-redirect-eln-cache)))
  (let ((home (concat user-paths-test-root "child-home/")))
    (should
     (equal (user-paths-test--child
             user-paths-test--bare
             '(list (car native-comp-eln-load-path)
                    (seq-some
                     (lambda (directory)
                       (string-prefix-p
                        (expand-file-name user-emacs-directory)
                        (expand-file-name directory)))
                     native-comp-eln-load-path)))
            (list (concat home ".cache/emacs/eln-cache/") nil)))))

(ert-deftest user-paths-test-grammars-are-installed-under-data ()
  (skip-unless (boundp 'treesit-extra-load-path))
  (should (equal user-paths-tree-sitter-directory
                 (user-data "tree-sitter/")))
  (should (member user-paths-tree-sitter-directory treesit-extra-load-path))
  (should (equal treesit--install-language-grammar-out-dir-history
                 (list user-paths-tree-sitter-directory))))

(ert-deftest user-paths-test-loading-twice-changes-nothing ()
  ;; early-init.el loads the file and init.el may load it again.
  (should
   (equal (user-paths-test--child
           user-paths-test--bare
           `(let ((eln (copy-sequence native-comp-eln-load-path))
                  (grammars (copy-sequence treesit-extra-load-path)))
              (load ,user-paths-test-file nil t)
              (list (equal eln native-comp-eln-load-path)
                    (equal grammars treesit-extra-load-path))))
          '(t t))))

(ert-deftest user-paths-test-guard-rejects-unmigrated-state ()
  (let ((legacy (expand-file-name "data" user-emacs-directory)))
    (should-not (file-exists-p legacy))
    (should-not (user-paths-check-migrated))
    (make-directory legacy)
    (unwind-protect
        (let ((message (cadr (should-error (user-paths-check-migrated)))))
          (should (string-match-p (regexp-quote legacy) message))
          (should (string-match-p "xdg/migrate\\.sh --apply" message)))
      (delete-directory legacy))))

(ert-deftest user-paths-test-roots-cannot-be-redefined ()
  (dolist (root '(user-data-directory user-state-directory
                  user-cache-directory))
    (let ((value (symbol-value root)))
      (unwind-protect
          (progn
            ;; The message names the variable and the library.  Nothing
            ;; is being loaded here, so it does not blame an init file.
            (let ((message (cadr (should-error (set root "/elsewhere/")))))
              (should (string-match-p (symbol-name root) message))
              (should (string-match-p "user-paths\\.el" message))
              (should-not (string-match-p "init\\.el" message)))
            (should (equal (symbol-value root) value))
            (should-error (eval `(defconst ,root "/elsewhere/") t))
            (should (equal (symbol-value root) value)))
        ;; If the guard is missing, the root has moved: put it back, so
        ;; that this test fails alone.  Setting the value a root already
        ;; has is no change, which is also what lets the library be
        ;; loaded twice.
        (set root value))
      (should (equal (symbol-value root) value))))
  ;; A binding is not a redefinition.
  (should (equal (let ((user-cache-directory "/elsewhere/"))
                   (user-cache "x"))
                 "/elsewhere/x"))
  ;; Nor is loading the library again, which defines each root a second
  ;; time with the value it has.
  (let ((roots (list user-data-directory user-state-directory
                     user-cache-directory)))
    (load user-paths-test-file nil t)
    (should (equal (list user-data-directory user-state-directory
                         user-cache-directory)
                   roots)))
  ;; A file that is not an init file is named, and is not taken for an
  ;; init from before the move.
  (let ((file (concat user-paths-test-root "package.el"))
        (value user-cache-directory))
    (with-temp-file file
      (insert ";;; -*- lexical-binding: t -*-\n"
              "(setq user-cache-directory \"/elsewhere/\")\n"))
    (let ((message (cadr (should-error (load file nil t)))))
      (should (string-match-p "package\\.el" message))
      (should-not (string-match-p "make -B" message)))
    (should (equal user-cache-directory value))))

(ert-deftest user-paths-test-a-root-without-a-value-can-be-given-one ()
  ;; The guard itself, on a variable that is nobody's root.
  (let ((root (make-symbol "root")))
    (add-variable-watcher root #'user-paths--keep-root)
    (set root "/first/")
    (should (equal (symbol-value root) "/first/"))
    (set root "/first/")
    (should-error (set root "/second/"))
    (should (equal (symbol-value root) "/first/"))
    (makunbound root)
    (set root "/third/")
    (should (equal (symbol-value root) "/third/"))))

(ert-deftest user-paths-test-a-stale-init-stops-at-its-first-definition ()
  ;; The first two forms below stood near the top of init.org until the
  ;; move: they put `user-data-directory' inside the configuration
  ;; directory and then replace `user-data'.  The third is what the rest
  ;; of that init went on to do.  Loaded after early-init.el has loaded
  ;; the library, the file must stop at the definition, with an error that
  ;; names the variable, the library and the file and says what to run.
  ;; The file is called init.el, as the one it stands for is.
  ;; Nothing may be created in the configuration directory, and the root
  ;; and `user-data' must stay as the library made them.
  (let* ((home (concat user-paths-test-root "child-home/"))
         (stale (concat user-paths-test-root "stale/init.el"))
         (legacy (concat home ".config/emacs/data"))
         result)
    (make-directory (file-name-directory stale) t)
    (with-temp-file stale
      (insert ";;; -*- lexical-binding: t -*-\n")
      (dolist (form '((eval-and-compile
                        (defsubst emacs-path (path)
                          (expand-file-name path user-emacs-directory)))
                      (eval-and-compile
                        (defconst emacs-environment (getenv "NIX_MYENV_NAME"))
                        (let ((emacs-data-suffix
                               (and (string= "emacsERC" emacs-environment)
                                    "alt")))
                          (defconst alternate-emacs
                            (string= emacs-data-suffix "alt"))
                          (defconst user-data-directory
                            (emacs-path (if emacs-data-suffix
                                            (format "data-%s" emacs-data-suffix)
                                          "data"))))
                        (defun user-data (dir)
                          (expand-file-name dir user-data-directory)))
                      (progn
                        (make-directory user-data-directory t)
                        (write-region "x" nil (user-data "history")))))
        (prin1 form (current-buffer))
        (insert "\n")))
    (unwind-protect
        (setq result
              (user-paths-test--child
               user-paths-test--bare
               `(list (condition-case err
                          (progn (load ,stale nil t) 'no-error)
                        (error (error-message-string err)))
                      user-data-directory
                      (user-data "history")
                      (file-exists-p ,legacy))))
      ;; Without the guard the child has made this directory.  Remove it,
      ;; so that this test fails alone.
      (delete-directory legacy t))
    (should (stringp (nth 0 result)))
    (should (string-match-p "user-data-directory" (nth 0 result)))
    (should (string-match-p "user-paths\\.el" (nth 0 result)))
    (should (string-match-p "stale/init\\.el" (nth 0 result)))
    (should (string-match-p "make -B init\\.el" (nth 0 result)))
    (should (equal (nth 1 result) (concat home ".local/share/emacs/")))
    (should (equal (nth 2 result)
                   (concat home ".local/share/emacs/history")))
    (should-not (nth 3 result))))

(ert-deftest user-paths-test-early-init-loads-the-library ()
  ;; early-init.el sits beside lisp/ and finds the library from
  ;; `user-emacs-directory', so start the child in the checkout.
  (let* ((checkout (file-name-directory
                    (directory-file-name
                     (file-name-directory user-paths-test-file))))
         (home (concat user-paths-test-root "child-home/")))
    (should
     (equal (user-paths-test--child
             user-paths-test--bare
             '(list (featurep 'user-paths)
                    package-enable-at-startup
                    user-state-directory)
             checkout
             (expand-file-name "early-init.el" checkout))
            (list t nil (concat home ".local/state/emacs/"))))))

(ert-deftest user-paths-test-defaults-without-xdg-variables ()
  ;; A GUI Emacs started from the Dock has no XDG variables at all.
  (let ((home (concat user-paths-test-root "child-home/")))
    (should (equal (user-paths-test--child
                    user-paths-test--bare
                    '(list user-data-directory user-state-directory
                           user-cache-directory))
                   (list (concat home ".local/share/emacs/")
                         (concat home ".local/state/emacs/")
                         (concat home ".cache/emacs/"))))))

(ert-deftest user-paths-test-alternate-instance-is-separate ()
  (let ((home (concat user-paths-test-root "child-home/")))
    (should (equal (user-paths-test--child
                    '("XDG_DATA_HOME" "XDG_STATE_HOME" "XDG_CACHE_HOME"
                      "NIX_MYENV_NAME=emacsERC")
                    '(list alternate-emacs
                           user-data-directory
                           user-state-directory
                           user-cache-directory))
                   (list t
                         (concat home ".local/share/emacs-alt/")
                         (concat home ".local/state/emacs-alt/")
                         (concat home ".cache/emacs-alt/"))))))

(ert-deftest user-paths-test-values-survive-loading-their-libraries ()
  ;; The point of setting these early: a library that loads later must not
  ;; put its own default back.
  (let* ((home (concat user-paths-test-root "child-home/"))
         (data (concat home ".local/share/emacs/"))
         (state (concat home ".local/state/emacs/"))
         (cache (concat home ".cache/emacs/"))
         (result
          (user-paths-test--child
           user-paths-test--bare
           '(progn
              (dolist (feature '(url url-cache multisession tramp-cache
                                 transient project eshell em-hist em-dirs
                                 ielm eww server package))
                (require feature))
              (list transient-history-file
                    transient-levels-file
                    transient-values-file
                    url-configuration-directory
                    url-cache-directory
                    multisession-directory
                    tramp-persistency-file-name
                    project-list-file
                    eshell-history-file-name
                    eshell-last-dir-ring-file-name
                    ielm-history-file-name
                    eww-bookmarks-directory
                    server-auth-dir
                    package-user-dir
                    package-gnupghome-dir
                    auto-save-list-file-prefix)))))
    (should (equal result
                   (list (concat state "transient/history.el")
                         (concat data "transient/levels.el")
                         (concat data "transient/values.el")
                         (concat state "url/")
                         (concat cache "url/")
                         (concat state "multisession/")
                         (concat state "tramp")
                         (concat state "projects")
                         (concat state "eshell/history")
                         (concat state "eshell/lastdir")
                         (concat state "ielm-history.eld")
                         (directory-file-name data)
                         (concat state "server/")
                         (concat data "elpa")
                         (concat data "elpa/gnupg")
                         (concat state "auto-save-list/.saves-"))))))

(provide 'user-paths-test)

;;; user-paths-test.el ends here
