;;; apply-init-edits.el --- Apply the XDG path edits to init.org -*- lexical-binding: t; -*-

;;; Commentary:

;; Usage:
;;   emacs --batch -Q -l xdg/apply-init-edits.el -f xdg-init-edits-batch FILE
;;   emacs --batch -Q -l xdg/apply-init-edits.el -f xdg-init-edits-batch --check FILE
;;
;; Each edit replaces one exact piece of text.  An edit whose replacement is
;; already in FILE is skipped, so applying twice is harmless.  If any piece
;; of text is missing or occurs more than once, nothing is written and the
;; exit status is 1.  With --check, FILE is never written.
;;
;; The edits live here, not in a patch, so that the same text is applied to
;; the sandbox copy under test and, at cutover, to the canonical file.  FILE
;; is read and written as raw bytes; every edit is plain ASCII.

;;; Code:

(defconst xdg-init-edits
  '((:name "load user-paths before anything else"
     :old "** Load Nix-managed packages into the macOS application
"
     :new "** Keep data, state and caches out of the configuration directory

#+begin_src emacs-lisp
;; Data lives under $XDG_DATA_HOME/emacs, state under $XDG_STATE_HOME/emacs
;; and caches under $XDG_CACHE_HOME/emacs; see lisp/user-paths.el.  An
;; interactive session has loaded it from early-init.el already.  Batch runs
;; (make, tests) never read early-init.el, so load it here as well.
(eval-and-compile
  (require 'user-paths
           (expand-file-name \"lisp/user-paths.el\" user-emacs-directory)))

;; Refuse to run on state that is still inside this checkout.
(user-paths-check-migrated)
#+end_src

** Load Nix-managed packages into the macOS application
"
     :marker "(user-paths-check-migrated)")
    (:name "drop the old data-environment block"
     :old "** Define the \"data environment\" for this instance of Emacs

#+begin_src emacs-lisp
(eval-and-compile
  (defconst emacs-environment (getenv \"NIX_MYENV_NAME\"))

  (let ((emacs-data-suffix
         (and (string= \"emacsERC\" emacs-environment) \"alt\")))

    (defconst alternate-emacs (string= emacs-data-suffix \"alt\"))

    (defconst user-data-directory
      (emacs-path (if emacs-data-suffix
                      (format \"data-%s\" emacs-data-suffix)
                    \"data\"))))

  (defun user-data (dir)
    (expand-file-name dir user-data-directory)))
#+end_src

** Disable warnings about obsolete functions when compiling
"
     :new "** Disable warnings about obsolete functions when compiling
"
     :removes "(defconst user-data-directory")
    (:name "auto-save-list prefix is set in user-paths"
     :old "  ;; startup.el
  (auto-save-list-file-prefix (user-data \"auto-save-list/.saves-\"))
  (inhibit-startup-echo-area-message \"johnw\")
"
     :new "  ;; startup.el
  (inhibit-startup-echo-area-message \"johnw\")
")
    (:name "backups are state"
     :old "  (backup-directory-alist '((\".\" . \"~/.local/share/emacs/backups\")))
"
     :new "  (backup-directory-alist `((\".\" . ,(user-state \"backups\"))))
")
    (:name "network security decisions are state"
     :old "  (nsm-settings-file (user-data \"network-security.data\"))
"
     :new "  (nsm-settings-file (user-state \"network-security.data\"))
")
    (:name "line bookmarks are state"
     :old "  (bm-repository-file (user-data \"bm-repository\")))
"
     :new "  (bm-repository-file (user-state \"bm-repository\")))
")
    (:name "bookmark-list display state is state"
     :old "  (bmkp-bmenu-state-file (user-data \"bmk-bmenu-state.el\"))
"
     :new "  (bmkp-bmenu-state-file (user-state \"bmk-bmenu-state.el\"))
")
    (:name "nov reading positions are state"
     :old "  (nov-save-place-file (user-data \"nov-places\")))
"
     :new "  (nov-save-place-file (user-state \"nov-places\")))
")
    (:name "persistent scratch is state"
     :old "  (persistent-scratch-save-file (user-data \"persistent-scratch\"))
"
     :new "  (persistent-scratch-save-file (user-state \"persistent-scratch\"))
")
    (:name "prescient usage counts are state"
     :old "  (prescient-save-file (user-data \"prescient-save.el\"))
"
     :new "  (prescient-save-file (user-state \"prescient-save.el\"))
")
    (:name "projectile index is a cache"
     :old "  (projectile-cache-file (user-data \"projectile.cache\"))
"
     :new "  (projectile-cache-file (user-cache \"projectile.cache\"))
")
    (:name "projectile known projects are state"
     :old "  (projectile-known-projects-file (user-data \"projectile-bookmarks.eld\"))
"
     :new "  (projectile-known-projects-file (user-state \"projectile-bookmarks.eld\"))
")
    (:name "recent files are state"
     :old "  (recentf-save-file (user-data \"recentf\"))
"
     :new "  (recentf-save-file (user-state \"recentf\"))
")
    (:name "minibuffer history is state"
     :old "  (savehist-file (user-data \"history\"))
"
     :new "  (savehist-file (user-state \"history\"))
")
    (:name "saved positions are state"
     :old "  (save-place-file (user-data \"places\"))
"
     :new "  (save-place-file (user-state \"places\"))
")
    (:name "tramp auto-saves are state"
     :old "  (tramp-auto-save-directory \"~/.local/share/emacs/backups\")
"
     :new "  (tramp-auto-save-directory (user-state \"backups\"))
")
    (:name "tramp persistency is set in user-paths"
     :old "  ;; Without this change, tramp ends up sending hundreds of shell commands to
  ;; the remote side to ask what the temporary directory is.
  (put 'temporary-file-directory 'standard-value '(\"/tmp\"))

  ;; Setting this with `:custom' does not take effect.
  (setq tramp-persistency-file-name (user-data \"tramp\")))
"
     :new "  ;; `tramp-persistency-file-name' is set in lisp/user-paths.el: tramp reads
  ;; that file while it loads, which is before this form runs.

  ;; Without this change, tramp ends up sending hundreds of shell commands to
  ;; the remote side to ask what the temporary directory is.
  (put 'temporary-file-directory 'standard-value '(\"/tmp\")))
")
    (:name "transient files are set in user-paths"
     :old "(use-package transient
  :defer t
  :custom
  (transient-history-file (user-data \"transient/history.el\"))
  (transient-values-file (user-data \"transient/values.el\")))
"
     :new ";; The history, values and levels files are set in lisp/user-paths.el:
;; transient reads them while it loads, and other packages load it early.
(use-package transient
  :defer t)
")
    (:name "url directory is set in user-paths"
     :old "(use-package url
  :defer t
  :custom
  (url-configuration-directory (user-data \"url/\")))
"
     :new ";; The url directories are set in lisp/user-paths.el, before any package
;; that fetches at startup can load the library.
(use-package url
  :defer t)
")
    (:name "url cache directory is set in user-paths"
     :old "(use-package url-cache
  :defer t
  :custom
  (url-cache-directory (user-data \"url/cache\")))
"
     :new "(use-package url-cache
  :defer t)
")
    (:name "slime history is state"
     :old "  (slime-repl-history-file (user-data \"slime-history.eld\"))
"
     :new "  (slime-repl-history-file (user-state \"slime-history.eld\"))
")
    (:name "lsp servers are data and the lsp session is state"
     :old "  (lsp-server-install-dir (user-data \".cache/lsp\"))
  (lsp-session-file (user-data \".lsp-session-v1\"))
"
     :new "  (lsp-server-install-dir (user-data \"lsp/\"))
  (lsp-session-file (user-state \"lsp-session-v1\"))
")
    (:name "org clock persistence is state"
     :old "  (org-clock-persist-file (user-data \"org-clock-save.el\"))
"
     :new "  (org-clock-persist-file (user-state \"org-clock-save.el\"))
")
    (:name "org-id locations are state"
     :old "  (org-id-locations-file (user-data \"org-id-locations\"))
"
     :new "  (org-id-locations-file (user-state \"org-id-locations\"))
")
    (:name "org-roam database is a cache"
     :old "  (org-roam-db-location (user-data \"org-roam.db\"))
"
     :new "  (org-roam-db-location (user-cache \"org-roam.db\"))
")
    (:name "xeft index is a cache"
     :old "  (xeft-database (user-data \"xeft.db\"))
"
     :new "  (xeft-database (user-cache \"xeft.db\"))
"))
  "Edits to make, in order, as plists.
:old is the text to find and :new its replacement.  An edit counts as
done when :new is present; :removes names a string that must then be
absent, for an edit whose :new is also part of the unedited file.
:marker names a string whose presence alone means done, for an edit
whose :old is still in the file afterwards: without it, rewording the
inserted text would make the next run insert it a second time.")

(defun xdg-init-edits--count (text)
  "Return how often TEXT occurs in the current buffer."
  (save-excursion
    (goto-char (point-min))
    (let ((count 0))
      (while (search-forward text nil t)
        (setq count (1+ count)))
      count)))

(defun xdg-init-edits--state (edit)
  "Return `done', `pending' or an error string for EDIT in this buffer."
  (let ((old (xdg-init-edits--count (plist-get edit :old)))
        (new (xdg-init-edits--count (plist-get edit :new)))
        (removes (plist-get edit :removes))
        (marker (plist-get edit :marker)))
    (cond
     ((and marker (> (xdg-init-edits--count marker) 0)) 'done)
     ((and removes (= old 0) (= new 1)
           (= (xdg-init-edits--count removes) 0))
      'done)
     ((and (not removes) (= new 1)) 'done)
     ((= old 1) 'pending)
     ((= old 0) "the text to replace was not found")
     (t (format "the text to replace occurs %d times" old)))))

(defun xdg-init-edits-apply (file &optional check)
  "Apply `xdg-init-edits' to FILE; with CHECK non-nil, only report.
Return non-nil if every edit is done or can be made.  FILE is written
only when all of them can, and only if something changed."
  (let ((coding-system-for-read 'no-conversion)
        (coding-system-for-write 'no-conversion)
        (case-fold-search nil)
        (ok t)
        (changed nil))
    (with-temp-buffer
      (set-buffer-multibyte nil)
      (insert-file-contents-literally file)
      (dolist (edit xdg-init-edits)
        (let ((state (xdg-init-edits--state edit)))
          (message "%-9s %s"
                   (cond ((eq state 'done) "done")
                         ((eq state 'pending) (if check "pending" "applied"))
                         (t "ERROR"))
                   (if (stringp state)
                       (format "%s: %s" (plist-get edit :name) state)
                     (plist-get edit :name)))
          (cond
           ((stringp state) (setq ok nil))
           ((eq state 'pending)
            (goto-char (point-min))
            (search-forward (plist-get edit :old))
            (replace-match (plist-get edit :new) t t)
            (setq changed t)))))
      (when (and ok changed (not check))
        (write-region (point-min) (point-max) file nil 'silent)))
    (unless ok
      (message "Nothing was written to %s" file))
    ok))

(defun xdg-init-edits-batch ()
  "Apply the edits to the file named on the command line.
The arguments are an optional --check followed by the file."
  (let* ((check (equal (car command-line-args-left) "--check"))
         (file (if check
                   (cadr command-line-args-left)
                 (car command-line-args-left))))
    (setq command-line-args-left nil)
    (unless file
      (message "usage: apply-init-edits.el [--check] FILE")
      (kill-emacs 2))
    (kill-emacs (if (xdg-init-edits-apply file check) 0 1))))

(provide 'apply-init-edits)

;;; apply-init-edits.el ends here
