;;; user-paths.el --- Keep data, state and caches out of the config directory -*- lexical-binding: t; -*-

;;; Commentary:

;; `user-emacs-directory' (~/.config/emacs) holds configuration only.
;; Everything Emacs writes while it runs goes to one of three roots, chosen
;; by what the file is, in the words of the XDG Base Directory specification:
;;
;;   `user-data-directory'   $XDG_DATA_HOME/emacs    what is worth carrying
;;       to another machine, and what was installed on request: saved
;;       choices, tokens, learned parameters, grammars, language servers,
;;       downloaded artwork.
;;   `user-state-directory'  $XDG_STATE_HOME/emacs   what Emacs records about
;;       its own use on this machine and keeps between restarts: histories,
;;       recent files, positions, sessions, cookies, backups, crash-recovery
;;       indexes.
;;   `user-cache-directory'  $XDG_CACHE_HOME/emacs   what Emacs can make
;;       again from what is on this machine, or fetches again unasked:
;;       compiled code, indexes, web responses.  What comes back only when
;;       someone agrees to a download or a build is installed, not cached.
;;
;; early-init.el loads this file, so the native-compilation cache is
;; redirected before anything is compiled.  Batch Emacs never reads
;; early-init.el, so init.el requires it as well.
;;
;; This file owns two kinds of path: those a library reads while it loads
;; (a later `use-package :custom' is too late for them), and defaults that
;; no `use-package' form in init.org mentions.  Every other path stays
;; beside its package in init.org, written as (user-data "..."),
;; (user-state "...") or (user-cache "...").
;;
;; The three roots cannot be given another value once this file has set
;; them.  That is what stops an init.el from before this layout, which
;; defines `user-data-directory' inside the configuration directory before
;; it loads any package: it fails at that definition, having written
;; nothing.
;;
;; An Emacs started with -Q or -q reads neither early-init.el nor init.el
;; and still writes to the built-in defaults under `user-emacs-directory'.
;; xdg/check-litter.sh reports what such runs leave behind.

;;; Code:

(defconst emacs-environment (getenv "NIX_MYENV_NAME")
  "Name of the Nix environment that started this Emacs, or nil.")

(defconst alternate-emacs (equal emacs-environment "emacsERC")
  "Non-nil in the alternate instance, which keeps its own files.")

;; xdg.el treats an unset, empty or relative XDG variable as unset.  A GUI
;; Emacs started from the Dock has no XDG variables at all; it then gets
;; ~/.local/share, ~/.local/state and ~/.cache, which must be the
;; directories that the shell's values name.
(require 'xdg)

(defconst user-paths--instance (if alternate-emacs "emacs-alt/" "emacs/")
  "Directory name of this instance below each XDG root.")

(defconst user-data-directory
  (expand-file-name user-paths--instance (xdg-data-home))
  "Directory for data: saved choices, tokens, installed grammars.")

(defconst user-state-directory
  (expand-file-name user-paths--instance (xdg-state-home))
  "Directory for state: histories, recent files, sessions, backups.")

(defconst user-cache-directory
  (expand-file-name user-paths--instance (xdg-cache-home))
  "Directory for caches that can be deleted and rebuilt.")

(defun user-data (path)
  "Expand PATH below `user-data-directory'."
  (expand-file-name path user-data-directory))

(defun user-state (path)
  "Expand PATH below `user-state-directory'."
  (expand-file-name path user-state-directory))

(defun user-cache (path)
  "Expand PATH below `user-cache-directory'."
  (expand-file-name path user-cache-directory))

;; An init.el tangled from an init.org that predates this file defines
;; `user-data-directory' itself, near its top, as a directory inside the
;; configuration directory.  Loaded after early-init.el it would start
;; Emacs on empty histories there, and say nothing.
(defun user-paths--keep-root (symbol newval operation _where)
  "Refuse to give the root SYMBOL a value other than the one it has.
This is a variable watcher; NEWVAL, OPERATION and _WHERE are what
`add-variable-watcher' passes.  Only assignments are refused: `setq',
`defconst' and the like arrive as the operation `set'.  A `let'
binding is left alone, and so is a root that has no value yet.
The error names the file being loaded, and says what to do when
that file is an init file."
  (when (and (eq operation 'set)
             (boundp symbol)
             (not (equal newval (symbol-value symbol))))
    (let ((file (and load-file-name
                     (abbreviate-file-name load-file-name))))
      (if (and file (equal (file-name-base file) "init"))
          (error "%s is set by lisp/user-paths.el and cannot become %S \
\(in %s).  That file is from before the move of state out of %s: \
run `make -B init.el' there"
                 symbol newval file
                 (abbreviate-file-name user-emacs-directory))
        (error "%s is set by lisp/user-paths.el and cannot become %S%s"
               symbol newval
               (if file (format " (in %s)" file) ""))))))

(dolist (root '(user-data-directory user-state-directory
                user-cache-directory))
  (add-variable-watcher root #'user-paths--keep-root))

(defconst user-paths-table
  '(;; Data: worth carrying to another machine, or installed on request.
    (emojify-emojis-dir                data  "emojis")
    (eww-bookmarks-directory           data  ".")
    (hash-store-directory              data  "hash-store/")
    (lena-snapshot-directory           data  "lena-snapshots/")
    (lsp-server-install-dir            data  "lsp/")
    (org-table-highlight-metadata-file data  "org-table-highlight-metadata.el")
    (package-user-dir                  data  "elpa")
    (pandoc-data-dir                   data  "pandoc-mode/")
    (persist--directory-location       data  "persist/")
    (transient-levels-file             data  "transient/levels.el")
    (transient-values-file             data  "transient/values.el")
    (wikipedia-db-file                 data  "wikipedia.db")
    (wikipedia-draft-directory         data  "wikipedia-drafts")
    ;; State: what Emacs records about its own use on this machine.
    (aria2-cc-file                     state "aria2-controller.eieio")
    (aria2-session-file                state "aria2c.session")
    (auto-save-list-file-prefix        state "auto-save-list/.saves-")
    (chess-autosave-file               state "chess-save")
    (eshell-history-file-name          state "eshell/history")
    (eshell-last-dir-ring-file-name    state "eshell/lastdir")
    (ido-save-directory-list-file      state "ido.last")
    (ielm-history-file-name            state "ielm-history.eld")
    (lsp-session-file                  state "lsp-session-v1")
    (multisession-directory            state "multisession/")
    (project-list-file                 state "projects")
    (projectile-frecency-file          state "projectile-frecency.eld")
    (projectile-session-directory      state "projectile-sessions/")
    (request-storage-directory         state "request")
    (server-auth-dir                   state "server/")
    (tramp-persistency-file-name       state "tramp")
    (transient-history-file            state "transient/history.el")
    (treemacs-last-error-persist-file  state "treemacs-persist-at-last-error")
    (treemacs-persist-file             state "treemacs-persist")
    (url-configuration-directory       state "url/")
    (vimish-fold-dir                   state "vimish-fold/")
    ;; Caches: made again from what is on this machine, or fetched again
    ;; unasked.
    (TeX-auto-global                   cache "auctex/")
    (coq-lookup-cache-directory        cache "coq-lookup")
    (dired-filetags-tagtrees-directory cache "dired-filetags/tagtrees/")
    (gptel-crowdsourced-prompts-file   cache "gptel-crowdsourced-prompts.csv")
    (js-js-tmpdir                      cache "js")
    (org-persist-directory             cache "org-persist/")
    (package-quickstart-file           cache "package-quickstart.el")
    (pcache-directory                  cache "pcache/")
    (url-cache-directory               cache "url/"))
  "Path variables this file sets, as (VARIABLE ROOT NAME).
ROOT is `data', `state' or `cache'; NAME is relative to that root.  A
trailing slash in NAME is kept, because some libraries build file
names from these values with `concat'.")

(defun user-paths-apply ()
  "Point every variable in `user-paths-table' at its XDG location.
The variables need not be defined yet.  Setting one before its library
loads is what makes the value win over the library's default."
  (dolist (entry user-paths-table)
    (set (nth 0 entry)
         (funcall (cdr (assq (nth 1 entry) '((data . user-data)
                                             (state . user-state)
                                             (cache . user-cache))))
                  (nth 2 entry)))))

(defvar TeX-auto-private)
(defvar web-cookie-jar-file)

(defun user-paths--elpy-rpc-virtualenv ()
  "Return the directory for the virtualenv that elpy manages itself.
It is installed tooling, like a grammar or a language server."
  (user-data "elpy/rpc-venv"))

(defun user-paths-apply-special ()
  "Set the path variables that do not fit `user-paths-table'."
  ;; A list of directories, for what AUCTeX extracts from the TeX files on
  ;; this machine.
  (setq TeX-auto-private (list (user-cache "auctex/auto")))
  ;; `elpy-rpc-virtualenv-path' stays at `default', the one value for which
  ;; elpy creates and rebuilds the virtualenv unasked; only the place moves.
  (advice-add 'elpy-rpc-default-virtualenv-path
              :override #'user-paths--elpy-rpc-virtualenv)
  ;; A `defconst', so the value can change only after web.el has loaded.
  (with-eval-after-load 'web
    (setq web-cookie-jar-file (user-state "web-cookies"))))

(defconst user-paths-tree-sitter-directory (user-data "tree-sitter/")
  "Directory holding compiled tree-sitter grammars.
They are installed, not cached: a mode has no grammar until someone
agrees to build it again, which takes git, a C compiler and the network.")

(defvar treesit-extra-load-path)
(defvar treesit--install-language-grammar-out-dir-history)

(defun user-paths-ensure-directories ()
  "Create the directories that their writers do not create themselves.
recentf, nsm, tramp, project and eshell signal an error, or drop what
they were saving silently, when the directory is missing.
`treesit-ensure-installed' skips a grammar directory that does not
exist yet."
  (with-file-modes #o700
    (dolist (directory (list user-data-directory
                             user-state-directory
                             user-cache-directory
                             (user-state "eshell/")
                             (user-state "url/")
                             user-paths-tree-sitter-directory))
      (make-directory directory t))))

(defun user-paths-check-migrated ()
  "Signal an error if state is still inside `user-emacs-directory'.
Emacs would otherwise start on empty history files under the XDG roots
and write fresh ones there, which a later migration then has to merge."
  (let ((legacy (expand-file-name "data" user-emacs-directory)))
    (when (file-directory-p legacy)
      (error "Emacs state is still in %s; quit Emacs and run %s --apply"
             legacy
             (expand-file-name "xdg/migrate.sh" user-emacs-directory)))))

(user-paths-ensure-directories)
(user-paths-apply)
(user-paths-apply-special)

;; Native code written by this Emacs belongs in the cache.  Emacs leaves a
;; redirected path alone for the rest of startup.
(when (and (featurep 'native-compile)
           (fboundp 'startup-redirect-eln-cache))
  (startup-redirect-eln-cache (user-cache "eln-cache/")))

;; Grammars are found through `treesit-extra-load-path'.  Interactive
;; installation ignores that list and takes its default from this history.
(when (boundp 'treesit-extra-load-path)
  (add-to-list 'treesit-extra-load-path user-paths-tree-sitter-directory))
(setq treesit--install-language-grammar-out-dir-history
      (list user-paths-tree-sitter-directory))

(provide 'user-paths)

;;; user-paths.el ends here
