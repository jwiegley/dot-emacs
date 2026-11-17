# Emacs XDG Reorganization Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Leave only configuration in `~/.config/emacs`, with durable Emacs state under `$XDG_DATA_HOME/emacs` and regenerable caches under `$XDG_CACHE_HOME/emacs`, on Clio and Hera, without losing any state.

**Architecture:** A small library, `lisp/user-paths.el`, computes both roots from the XDG variables and sets every path that has to be in place before its package loads. A new `early-init.el` loads it first, and the first block of `init.org` loads it again for batch runs and refuses to run on state that has not been moved. The files themselves are moved once per host by `xdg/migrate.sh`, which previews by default, records every rename and can roll back. The `init.org` edit is applied by an anchored edit script inside the cutover window, because the canonical file reaches Hera through Syncthing the moment it changes.

**Tech Stack:** Emacs Lisp (GNU Emacs 31.1.50) with ERT, bash (must also run under the system bash 3.2), git, make, `sandbox-exec`, `shellcheck`.

**Spec:** Appendix A of this document (the audit report, verbatim). Appendix B lists every place where this plan departs from it, and why.

## Global Constraints

- The canonical `init.org` is `~/org/init.org` (it resolves to `~/Documents/org/init.org`). `~/.config/emacs/init.org` is a copy that `make` overwrites. Never edit the copy.
- `user-emacs-directory` stays `~/.config/emacs`. Redirection is per variable.
- Two roots only: `$XDG_DATA_HOME/emacs` and `$XDG_CACHE_HOME/emacs`. Nothing goes under `$XDG_STATE_HOME`: `~/.local/state` is excluded from every backup on these hosts.
- An unset, empty or relative XDG value means the default (`~/.local/share`, `~/.cache`). A GUI Emacs started from the Dock has no XDG variables at all.
- No compatibility symlinks.
- `xdg/migrate.sh --apply` runs only while no Emacs is running on that host.
- A hand-made trial of `xdg/migrate.sh` against a throw-away home must unset `XDG_CONFIG_HOME`, `XDG_DATA_HOME` and `XDG_CACHE_HOME` as well as setting `HOME`, as `xdg/migrate-test.sh` does. Those variables take precedence over `HOME`.
- The mover never deletes state. A leftover with no owner goes to an attic for a person to review.
- The existing `.gitignore` rules for runtime paths stay, as a safety net: `~/src/scripts/changes` runs `git add -A` and pushes.
- Tasks 1 to 6 change nothing outside the worktree, apart from git's own record of the worktree and its branch: not `~/org/init.org`, not the working tree of `master`, not a single file of state.
- Every edit text in `xdg/apply-init-edits.el` is plain ASCII.
- Every shell script passes `shellcheck` and runs under `/bin/bash` 3.2.
- Commit subjects follow the repository's style, `area: Sentence`. Add whatever attribution trailer your own instructions require.

## Review Focus

Each line names a condition the report implies but does not state, the behaviour a reasonable person expects, and the test that pins it.

1. **A GUI Emacs started from the Dock has no XDG variables.** Both roots must equal the directories the shell's values name. Pinned by `user-paths-test-defaults-without-xdg-variables` and `user-paths-test-unusable-xdg-values-fall-back` (Task 1).
2. **A library that loads after the redirect reads or restores its own default.** Tramp and transient read their files while they load; today both write files they never read back. Pinned by `user-paths-test-values-survive-loading-their-libraries` (Task 1) for built-in libraries and by the sealed audit (Task 3) for the whole init.
3. **Emacs is still running when the files move.** A running session rewrites its history at the old paths, on timers as well as on exit. Pinned by the `refuses while ... runs` checks in `xdg/migrate-test.sh` (Task 4).
4. **A destination already holds a different file**, because Emacs started at the wrong moment or the other host's copy arrived by sync. The mover must not guess which is right: it refuses until told, and keeps the copy that loses. Pinned by the checks `apply refuses to choose between two different files`, `the history that was there is kept` and `the copy from the configuration directory is kept` (Task 4).
5. **A host starts the new init before its own state has moved.** `init.org` reaches Hera through Syncthing within seconds. Emacs must refuse rather than start on empty history. Pinned by `user-paths-test-guard-rejects-unmigrated-state` (Task 1).

Two more, lower on the list: an interrupted move must be safe to run again (`a second apply moves nothing`, Task 4), and token and cookie files must end up owner-only (`token file is private`, Task 4).

## What the investigation found

An executor needs these facts; none of them is in the report.

- **`make init.el` loads the whole init.** The Makefile runs `org-babel-load-file`, which tangles and then loads `init.el` in batch Emacs. `~/src/nix/bin/runemacs` runs `make init.el` at every launch. Batch Emacs never reads `early-init.el`.
- **`init.org` travels by Syncthing; everything else by ChronoSync.** `~/Documents` is a Syncthing folder shared by Clio, Hera and Vulcan. A ChronoSync task named `Home` synchronizes the whole home directory between Hera and Clio every hour, in both directions, and already reports conflicts on `.config/emacs/data/recentf`. Its include and exclude rules could not be read from disk. Only John can inspect them.
- **`~/src/scripts/changes` runs `git add -A`, commits and pushes** this repository. That is how `multisession/files/emoji/emoji--recent.value`, a runtime file, came to be tracked.
- **An Emacs started with `-Q` or `-q` reads no init file** and writes to the built-in defaults under `~/.config/emacs`: `eln-cache/`, `auto-save-list/`, `transient/`, `url/`. No init setting can prevent that. The stray top-level `transient/`, `url/` and `auto-save-list/` most likely come from such runs, or from an init that stopped early.
- **Two package defaults point at `~/.emacs.d`:** `hash-store-directory` and `pandoc-data-dir`. If either package creates that directory, Emacs prefers it to `~/.config/emacs` at the next start and comes up with no configuration.
- **Two settings do not work today.** `tramp-persistency-file-name` is set in `:config`, after tramp has read the file. The transient files are set in a `:custom` that runs after another package has loaded transient. Going by the order in which the init loads them, both are written on exit and never read back.
- **The alternate instance is dead code.** Nothing sets `NIX_MYENV_NAME=emacsERC` since 2024. The plan keeps the one line that separates its state and leaves the uses of `alternate-emacs` elsewhere in `init.org` alone.
- **Nothing in the Nix configuration or the scripts repository has to change** for this move. No script reads `data/`, `org-roam.db` or `org-id-locations`, and the Nix tests run Emacs with `-Q` in a scratch home.
- **Backups.** A nightly job copies Clio's home to `tank` on Vulcan, and from there to B2. By its filter files, `~/.cache` and `~/.local/state` are excluded and `~/.local/share/emacs` is not; Task 9 checks that on `tank`. After the move, durable state keeps its backup and the caches lose theirs, which is what is wanted.

## File Structure

| File | Status | Responsibility |
|---|---|---|
| `lisp/user-paths.el` | new, permanent | The two roots, `user-data` and `user-cache`, the table of early path settings, the directory set-up, the native-cache redirect, the guard |
| `lisp/user-paths-test.el` | new, permanent | ERT tests for the library and for `early-init.el` |
| `early-init.el` | new, permanent | Loads the library before anything else; disables package.el |
| `xdg/check-litter.sh` | new, permanent | Reports runtime state that has come back into the checkout |
| `xdg/check-litter-test.sh` | new, permanent | Tests for the report |
| `xdg/migrate.sh` | new, permanent | Moves state out of the checkout; previews, logs, rolls back |
| `xdg/migrate-test.sh` | new, permanent | Tests for the mover against throw-away trees |
| `xdg/apply-init-edits.el` | new, removed in Task 10 | Applies the ten `init.org` edits by exact text |
| `xdg/apply-init-edits-test.el` | new, removed in Task 10 | Tests for the editor |
| `xdg/audit/run.sh`, `sandbox.sb`, `guards.el`, `audit.el` | new, removed in Task 10 | Loads the whole init in a sealed copy and reports paths that still point into the checkout |
| `.gitignore` | modified | Five more safety-net rules |
| `Makefile` | modified | Targets `check-litter`, `test-xdg`, `audit-xdg` |
| `README.md` | modified | One paragraph on the layout |
| `migrate-emacs-xdg.sh` | deleted | The earlier script; it was never run and cannot run on the current layout |
| `multisession/files/emoji/emoji--recent.value` | untracked in Task 9 | Runtime state that was committed by accident; the mover takes it to the data root |
| `~/org/init.org` | modified at cutover | Ten edits, applied by `xdg/apply-init-edits.el` |

What remains in `~/.config/emacs` after the cutover: the tracked files, `init.el`, `settings.el`, `nix-packages`, `nix-packages.el`, `certs/`, `eshell/alias`, `eshell/login`, the `*.elc` files under `lisp/`, `.claude/` and `.superpowers/`.

## Before you start

- Work on branch `xdg-layout` in a git worktree outside the checkout. Create it with exactly this command, and do not let superpowers:using-git-worktrees choose the place. Its default is a directory inside the checkout, which the mover and the litter report would then list.

  ```bash
  git -C ~/.config/emacs worktree add ~/src/emacs-xdg-layout -b xdg-layout
  ```

  In this plan `WT` is `~/src/emacs-xdg-layout`, and the commands of Tasks 1 to 6 run from there. Another agent edits `init.org` and `lisp/` in the main checkout; stay out of it.
- A committed `early-init.el` takes effect the next time Emacs starts. That is why the branch is merged into `master` only inside the cutover (Task 7), with Emacs closed.
- `emacs` on `PATH` is `/Applications/Emacs.app/Contents/MacOS/bin/emacs`.
- Never run plain `make` in the worktree. It would load the current init against live state.
- Tasks 7, 8 and 9 need John: they quit his Emacs, pause his sync, and reach Hera.

---

### Task 1: The path library and early-init.el

**Files:**
- Create: `lisp/user-paths.el`
- Create: `early-init.el`
- Test: `lisp/user-paths-test.el`

**Interfaces:**
- Consumes: nothing from other tasks. Reads the environment variables `XDG_DATA_HOME`, `XDG_CACHE_HOME` and `NIX_MYENV_NAME`.
- Produces:
  - `user-data-directory` and `user-cache-directory`: strings, absolute, each ending in `/`.
  - `(user-data PATH)` and `(user-cache PATH)`: return PATH expanded under the matching root.
  - `emacs-environment` (string or nil) and `alternate-emacs` (boolean), which `init.org` goes on using.
  - `user-paths-table`: a list of `(VARIABLE ROOT NAME)` with ROOT `data` or `cache`.
  - `(user-paths-check-migrated)`: signals `error` if `<user-emacs-directory>/data` is a directory, and otherwise returns nil.
  - The feature `user-paths`. Loading the file creates the directories, applies the table and redirects the native-compilation cache.

- [ ] **Step 1: Write the failing tests**

Create `lisp/user-paths-test.el`:

```elisp
;;; user-paths-test.el --- Tests for user-paths.el -*- lexical-binding: t; -*-

;; Run with:
;;   emacs --batch -Q -l lisp/user-paths-test.el -f ert-run-tests-batch-and-exit
;;
;; These tests never touch real state.  Every root lives in a scratch
;; directory, and user-paths.el is loaded only after the environment and
;; `user-emacs-directory' point there.

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
(setenv "XDG_CACHE_HOME" (concat user-paths-test-root "cache"))
(setenv "NIX_MYENV_NAME" nil)
(setq user-emacs-directory (concat user-paths-test-root "config/emacs/"))
(make-directory user-emacs-directory t)
(load user-paths-test-file nil t)

(defun user-paths-test--child (environment form &optional init-directory file)
  "Return the value of FORM in a fresh Emacs that loaded FILE.
FILE defaults to user-paths.el.  ENVIRONMENT is a list of \"VAR=value\"
strings; a bare \"VAR\" unsets that variable.  The child's home is a
scratch directory, and so is its init directory unless INIT-DIRECTORY
names another, so it cannot reach real state either."
  (let* ((home (concat user-paths-test-root "child-home/"))
         (init-directory (or init-directory (concat home ".config/emacs/")))
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
  (should (equal user-cache-directory
                 (concat user-paths-test-root "cache/emacs/")))
  (should (equal (user-data "history")
                 (concat user-paths-test-root "share/emacs/history")))
  (should (equal (user-cache "url/")
                 (concat user-paths-test-root "cache/emacs/url/"))))

(ert-deftest user-paths-test-unusable-xdg-values-fall-back ()
  (let ((fallback (concat user-paths-test-root "fallback")))
    (dolist (value '(nil "" "relative/path"))
      (let ((process-environment
             (cons (if value (concat "USER_PATHS_TEST=" value)
                     "USER_PATHS_TEST")
                   process-environment)))
        (should (equal (user-paths--xdg-home "USER_PATHS_TEST" fallback)
                       (concat fallback "/")))))
    (let ((process-environment
           (cons "USER_PATHS_TEST=/absolute/dir" process-environment)))
      (should (equal (user-paths--xdg-home "USER_PATHS_TEST" fallback)
                     "/absolute/dir/")))))

(ert-deftest user-paths-test-table-is-well-formed ()
  (let ((variables (mapcar #'car user-paths-table)))
    (should (equal variables (cl-remove-duplicates variables))))
  (dolist (entry user-paths-table)
    (should (= (length entry) 3))
    (should (symbolp (nth 0 entry)))
    (should (memq (nth 1 entry) '(data cache)))
    (should (stringp (nth 2 entry)))
    (should-not (file-name-absolute-p (nth 2 entry)))))

(ert-deftest user-paths-test-table-is-applied ()
  (dolist (entry user-paths-table)
    (let* ((variable (nth 0 entry))
           (root (if (eq (nth 1 entry) 'data)
                     user-data-directory
                   user-cache-directory))
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
                 (user-cache "elpy/rpc-venv")))
  ;; web.el defines its cookie jar with `defconst'; the redirect has to
  ;; survive that definition.
  (should
   (equal (user-paths-test--child
           '("XDG_DATA_HOME" "XDG_CACHE_HOME" "NIX_MYENV_NAME")
           '(progn
              (defconst web-cookie-jar-file "/default/web-cookies")
              (provide 'web)
              web-cookie-jar-file))
          (concat user-paths-test-root
                  "child-home/.local/share/emacs/web-cookies"))))

(ert-deftest user-paths-test-directories-are-private ()
  (dolist (directory (list user-data-directory
                           user-cache-directory
                           (user-data "eshell/")
                           (user-data "url/")
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
             '("XDG_DATA_HOME" "XDG_CACHE_HOME" "NIX_MYENV_NAME")
             '(list (car native-comp-eln-load-path)
                    (seq-some
                     (lambda (directory)
                       (string-prefix-p
                        (expand-file-name user-emacs-directory)
                        (expand-file-name directory)))
                     native-comp-eln-load-path)))
            (list (concat home ".cache/emacs/eln-cache/") nil)))))

(ert-deftest user-paths-test-grammars-live-in-data ()
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
           '("XDG_DATA_HOME" "XDG_CACHE_HOME" "NIX_MYENV_NAME")
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

(ert-deftest user-paths-test-early-init-loads-the-library ()
  ;; early-init.el sits beside lisp/ and finds the library from
  ;; `user-emacs-directory', so start the child in the checkout.
  (let* ((checkout (file-name-directory
                    (directory-file-name
                     (file-name-directory user-paths-test-file))))
         (home (concat user-paths-test-root "child-home/")))
    (should
     (equal (user-paths-test--child
             '("XDG_DATA_HOME" "XDG_CACHE_HOME" "NIX_MYENV_NAME")
             '(list (featurep 'user-paths)
                    package-enable-at-startup
                    user-data-directory)
             checkout
             (expand-file-name "early-init.el" checkout))
            (list t nil (concat home ".local/share/emacs/"))))))

(ert-deftest user-paths-test-defaults-without-xdg-variables ()
  ;; A GUI Emacs started from the Dock has no XDG variables at all.
  (let ((home (concat user-paths-test-root "child-home/")))
    (should (equal (user-paths-test--child
                    '("XDG_DATA_HOME" "XDG_CACHE_HOME" "NIX_MYENV_NAME")
                    '(list user-data-directory user-cache-directory))
                   (list (concat home ".local/share/emacs/")
                         (concat home ".cache/emacs/"))))))

(ert-deftest user-paths-test-alternate-instance-is-separate ()
  (let ((home (concat user-paths-test-root "child-home/")))
    (should (equal (user-paths-test--child
                    '("XDG_DATA_HOME" "XDG_CACHE_HOME"
                      "NIX_MYENV_NAME=emacsERC")
                    '(list alternate-emacs
                           user-data-directory
                           user-cache-directory))
                   (list t
                         (concat home ".local/share/emacs-alt/")
                         (concat home ".cache/emacs-alt/"))))))

(ert-deftest user-paths-test-values-survive-loading-their-libraries ()
  ;; The point of setting these early: a library that loads later must not
  ;; put its own default back.
  (let* ((home (concat user-paths-test-root "child-home/"))
         (data (concat home ".local/share/emacs/"))
         (cache (concat home ".cache/emacs/"))
         (result
          (user-paths-test--child
           '("XDG_DATA_HOME" "XDG_CACHE_HOME" "NIX_MYENV_NAME")
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
                   (list (concat data "transient/history.el")
                         (concat data "transient/levels.el")
                         (concat data "transient/values.el")
                         (concat data "url/")
                         (concat cache "url/")
                         (concat data "multisession/")
                         (concat data "tramp")
                         (concat data "projects")
                         (concat data "eshell/history")
                         (concat data "eshell/lastdir")
                         (concat data "ielm-history.eld")
                         (directory-file-name data)
                         (concat data "server/")
                         (concat data "elpa")
                         (concat data "elpa/gnupg")
                         (concat data "auto-save-list/.saves-"))))))

(provide 'user-paths-test)

;;; user-paths-test.el ends here
```

- [ ] **Step 2: Run the tests to verify they fail**

Run: `emacs --batch -Q -l lisp/user-paths-test.el -f ert-run-tests-batch-and-exit; echo "exit=$?"`

Expected: `exit=255`, and above it

```text
Cannot open load file: No such file or directory, <WT>/lisp/user-paths.el
```

- [ ] **Step 3: Write the library**

Create `lisp/user-paths.el`:

```elisp
;;; user-paths.el --- Keep state and caches out of the config directory -*- lexical-binding: t; -*-

;;; Commentary:

;; `user-emacs-directory' (~/.config/emacs) holds configuration only.
;; Durable state lives under `user-data-directory' ($XDG_DATA_HOME/emacs) and
;; regenerable caches under `user-cache-directory' ($XDG_CACHE_HOME/emacs).
;;
;; early-init.el loads this file, so the native-compilation cache is
;; redirected before anything is compiled.  Batch Emacs never reads
;; early-init.el, so init.el requires it as well.
;;
;; This file owns two kinds of path: those a library reads while it loads
;; (a later `use-package :custom' is too late for them), and defaults that
;; no `use-package' form in init.org mentions.  Every other state path stays
;; beside its package in init.org, written as (user-data "...").
;;
;; An Emacs started with -Q or -q reads neither early-init.el nor init.el
;; and still writes to the built-in defaults under `user-emacs-directory'.
;; xdg/check-litter.sh reports what such runs leave behind.

;;; Code:

(defconst emacs-environment (getenv "NIX_MYENV_NAME")
  "Name of the Nix environment that started this Emacs, or nil.")

(defconst alternate-emacs (equal emacs-environment "emacsERC")
  "Non-nil in the alternate instance, which keeps its own state.")

(defun user-paths--xdg-home (variable fallback)
  "Return the directory named by environment VARIABLE, else FALLBACK.
An unset, empty or relative value counts as unset, as in xdg.el.  A
GUI Emacs started from the Dock has no XDG variables at all, so
FALLBACK must name the directory the shell's value names."
  (let ((value (getenv variable)))
    (file-name-as-directory
     (expand-file-name
      (if (and value (file-name-absolute-p value)) value fallback)))))

(defconst user-paths--instance (if alternate-emacs "emacs-alt/" "emacs/")
  "Directory name of this instance below each XDG root.")

(defconst user-data-directory
  (expand-file-name user-paths--instance
                    (user-paths--xdg-home "XDG_DATA_HOME" "~/.local/share"))
  "Directory for durable state: histories, databases, tokens.")

(defconst user-cache-directory
  (expand-file-name user-paths--instance
                    (user-paths--xdg-home "XDG_CACHE_HOME" "~/.cache"))
  "Directory for caches that can be deleted and rebuilt.")

(defun user-data (path)
  "Expand PATH below `user-data-directory'."
  (expand-file-name path user-data-directory))

(defun user-cache (path)
  "Expand PATH below `user-cache-directory'."
  (expand-file-name path user-cache-directory))

(defconst user-paths-table
  '(;; Durable state.
    (aria2-cc-file                     data  "aria2-controller.eieio")
    (aria2-session-file                data  "aria2c.session")
    (auto-save-list-file-prefix        data  "auto-save-list/.saves-")
    (eshell-history-file-name          data  "eshell/history")
    (eshell-last-dir-ring-file-name    data  "eshell/lastdir")
    (eww-bookmarks-directory           data  ".")
    (hash-store-directory              data  "hash-store/")
    (ido-save-directory-list-file      data  "ido.last")
    (ielm-history-file-name            data  "ielm-history.eld")
    (lena-snapshot-directory           data  "lena-snapshots/")
    (lsp-session-file                  data  "lsp-session-v1")
    (multisession-directory            data  "multisession/")
    (org-table-highlight-metadata-file data  "org-table-highlight-metadata.el")
    (package-user-dir                  data  "elpa")
    (pandoc-data-dir                   data  "pandoc-mode/")
    (persist--directory-location       data  "persist/")
    (project-list-file                 data  "projects")
    (projectile-frecency-file          data  "projectile-frecency.eld")
    (projectile-session-directory      data  "projectile-sessions/")
    (request-storage-directory         data  "request")
    (server-auth-dir                   data  "server/")
    (tramp-persistency-file-name       data  "tramp")
    (transient-history-file            data  "transient/history.el")
    (transient-levels-file             data  "transient/levels.el")
    (transient-values-file             data  "transient/values.el")
    (treemacs-persist-file             data  "treemacs-persist")
    (url-configuration-directory       data  "url/")
    (vimish-fold-dir                   data  "vimish-fold/")
    (wikipedia-db-file                 data  "wikipedia.db")
    (wikipedia-draft-directory         data  "wikipedia-drafts")
    ;; Caches.
    (TeX-auto-global                   cache "auctex/")
    (emojify-emojis-dir                cache "emojis")
    (gptel-crowdsourced-prompts-file   cache "gptel-crowdsourced-prompts.csv")
    (js-js-tmpdir                      cache "js")
    (lsp-server-install-dir            cache "lsp/")
    (package-quickstart-file           cache "package-quickstart.el")
    (pcache-directory                  cache "pcache/")
    (treemacs-last-error-persist-file  cache "treemacs-persist-at-last-error")
    (url-cache-directory               cache "url/"))
  "Path variables this file sets, as (VARIABLE ROOT NAME).
ROOT is `data' or `cache'; NAME is relative to that root.  A trailing
slash in NAME is kept, because some libraries build file names from
these values with `concat'.")

(defun user-paths-apply ()
  "Point every variable in `user-paths-table' at its XDG location.
The variables need not be defined yet.  Setting one before its library
loads is what makes the value win over the library's default."
  (dolist (entry user-paths-table)
    (set (nth 0 entry)
         (funcall (if (eq (nth 1 entry) 'data) #'user-data #'user-cache)
                  (nth 2 entry)))))

(defvar TeX-auto-private)
(defvar web-cookie-jar-file)

(defun user-paths--elpy-rpc-virtualenv ()
  "Return the directory for the virtualenv that elpy manages itself."
  (user-cache "elpy/rpc-venv"))

(defun user-paths-apply-special ()
  "Set the path variables that do not fit `user-paths-table'."
  ;; A list of directories, for style files AUCTeX generates on request.
  (setq TeX-auto-private (list (user-cache "auctex/auto")))
  ;; `elpy-rpc-virtualenv-path' stays at `default', the one value for which
  ;; elpy creates and rebuilds the virtualenv unasked; only the place moves.
  (advice-add 'elpy-rpc-default-virtualenv-path
              :override #'user-paths--elpy-rpc-virtualenv)
  ;; A `defconst', so the value can change only after web.el has loaded.
  (with-eval-after-load 'web
    (setq web-cookie-jar-file (user-data "web-cookies"))))

(defconst user-paths-tree-sitter-directory (user-data "tree-sitter/")
  "Directory holding compiled tree-sitter grammars.
They are durable state, not a cache: rebuilding one needs git, a C
compiler and the network.")

(defvar treesit-extra-load-path)
(defvar treesit--install-language-grammar-out-dir-history)

(defun user-paths-ensure-directories ()
  "Create the directories that their writers do not create themselves.
recentf, nsm, tramp, project and eshell signal an error, or drop their
data silently, when the directory is missing.  `treesit-ensure-installed'
skips a grammar directory that does not exist yet."
  (with-file-modes #o700
    (dolist (directory (list user-data-directory
                             user-cache-directory
                             (user-data "eshell/")
                             (user-data "url/")
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
```

- [ ] **Step 4: Run the tests; all but one pass**

Run: `emacs --batch -Q -l lisp/user-paths-test.el -f ert-run-tests-batch-and-exit 2>&1 | grep -E 'FAILED|Ran '`

Expected:

```text
   FAILED   4/15  user-paths-test-early-init-loads-the-library (...)
Ran 15 tests, 14 results as expected, 1 unexpected (...)
   FAILED  user-paths-test-early-init-loads-the-library
```

The one failure is the test for the file the next step creates.

- [ ] **Step 5: Write early-init.el**

Create `early-init.el` at the root of the worktree:

```elisp
;;; early-init.el --- Work that must precede init.el -*- lexical-binding: t; -*-

;;; Commentary:

;; Interactive startup loads this file before init.el.  Batch, -q and -Q
;; runs skip it, so init.el requires lisp/user-paths.el again.

;;; Code:

;; Redirect the native-compilation cache, and every other state path,
;; before any library has a chance to use its default.  Load the source
;; file by name: a stale user-paths.elc must never be picked up.
(load (expand-file-name "lisp/user-paths.el" user-emacs-directory) nil t)

;; Packages come from the Nix bundle.  package.el decides whether to
;; activate packages between this file and init.el, so this must be here.
(setq package-enable-at-startup nil)

;;; early-init.el ends here
```

- [ ] **Step 6: Run the tests to verify they pass**

Run: `emacs --batch -Q -l lisp/user-paths-test.el -f ert-run-tests-batch-and-exit 2>&1 | grep -E 'FAILED|Ran '`

Expected: `Ran 15 tests, 15 results as expected, 0 unexpected (...)`

- [ ] **Step 7: Check that the library compiles without warnings**

The library is always loaded as source, so compile a copy elsewhere and leave no `.elc` behind.

```bash
copy=$(mktemp -d) && cp lisp/user-paths.el "$copy/" &&
  (cd "$copy" && emacs --batch -Q -f batch-byte-compile user-paths.el)
```

Expected: no output.

- [ ] **Step 8: Commit**

```bash
git add lisp/user-paths.el lisp/user-paths-test.el early-init.el
git commit -m "user-paths: Compute the XDG data and cache roots in one library"
```

---

### Task 2: The anchored init.org editor

**Files:**
- Create: `xdg/apply-init-edits.el`
- Test: `xdg/apply-init-edits-test.el`

**Interfaces:**
- Consumes: the names Task 1 defines, but only as text inside the edits: `user-paths`, `user-paths-check-migrated`, `user-data`, `user-cache`.
- Produces:
  - `xdg-init-edits`: a list of plists with `:name`, `:old`, `:new` and an optional `:removes`.
  - `(xdg-init-edits-apply FILE &optional CHECK)`: returns non-nil if every edit is done or can be made. It writes FILE only when all can and something changed, and never when CHECK is non-nil.
  - `xdg-init-edits-batch`: the command-line entry. Arguments `[--check] FILE`. Exit status 0, 1 if an edit cannot be made, or 2 if no file is named.

The ten edits, in order:

| # | Edit | Effect on `init.org` |
|---|---|---|
| 1 | load user-paths before anything else | New section before the Nix package loader, which is the first block that loads anything: requires `lisp/user-paths.el`, then calls the guard |
| 2 | drop the old data-environment block | The library now defines `emacs-environment`, `alternate-emacs`, `user-data-directory`, `user-data` |
| 3 | auto-save-list prefix | Removed from `use-package emacs`; the table sets it |
| 4 | backups | `backup-directory-alist` uses `(user-data "backups")`, the same directory as today |
| 5 | projectile index | `projectile-cache-file` moves to `(user-cache ...)` |
| 6 | tramp auto-saves | `tramp-auto-save-directory` uses `(user-data "backups")` |
| 7 | tramp persistency | The `setq` in `:config` is removed; the table sets it before tramp loads |
| 8 | transient files | The `:custom` is removed; the table sets all three files |
| 9 | url directory | The `:custom` is removed; the table sets it |
| 10 | url cache directory | The `:custom` is removed; the table sets it under the cache root |

- [ ] **Step 1: Write the failing tests**

Create `xdg/apply-init-edits-test.el`:

```elisp
;;; apply-init-edits-test.el --- Tests for apply-init-edits.el -*- lexical-binding: t; -*-

;; Run with:
;;   emacs --batch -Q -l xdg/apply-init-edits-test.el -f ert-run-tests-batch-and-exit

(require 'ert)

(load (expand-file-name "apply-init-edits.el"
                        (file-name-directory (or load-file-name
                                                 buffer-file-name)))
      nil t)

(defun xdg-init-edits-test--bytes (file)
  "Return the contents of FILE as a unibyte string."
  (with-temp-buffer
    (set-buffer-multibyte nil)
    (insert-file-contents-literally file)
    (buffer-string)))

(defun xdg-init-edits-test--fixture (&optional transform)
  "Write a scratch file holding every text the edits replace.
TRANSFORM, if given, is called on the list of texts and returns the
list to write.  A UTF-8 character outside the edits checks that the
file is handled as bytes."
  (let ((file (make-temp-file "init-edits-test-" nil ".org"))
        (texts (mapcar (lambda (edit) (plist-get edit :old)) xdg-init-edits))
        (coding-system-for-write 'no-conversion))
    (when transform
      (setq texts (funcall transform texts)))
    (with-temp-file file
      (set-buffer-multibyte nil)
      (insert "#+title: fixture \303\251\n\n")
      (dolist (text texts)
        (insert text "\nfiller between edits\n\n")))
    file))

(ert-deftest xdg-init-edits-test-edits-are-plain-ascii ()
  (dolist (edit xdg-init-edits)
    (dolist (key '(:old :new))
      (should (string-match-p "\\`[[:ascii:]]+\\'" (plist-get edit key))))
    (should-not (equal (plist-get edit :old) (plist-get edit :new)))))

(ert-deftest xdg-init-edits-test-check-writes-nothing ()
  (let* ((file (xdg-init-edits-test--fixture))
         (before (xdg-init-edits-test--bytes file)))
    (unwind-protect
        (progn
          (should (xdg-init-edits-apply file t))
          (should (equal before (xdg-init-edits-test--bytes file))))
      (delete-file file))))

(ert-deftest xdg-init-edits-test-apply-then-apply-again ()
  (let ((file (xdg-init-edits-test--fixture)))
    (unwind-protect
        (let (once)
          (should (xdg-init-edits-apply file))
          (setq once (xdg-init-edits-test--bytes file))
          (dolist (edit xdg-init-edits)
            (should (string-search (plist-get edit :new) once)))
          (should-not (string-search "(defconst user-data-directory" once))
          (should-not (string-search "~/.local/share/emacs/backups" once))
          (should (string-prefix-p "#+title: fixture \303\251\n" once))
          ;; A second run finds every edit done and leaves the bytes alone.
          (should (xdg-init-edits-apply file))
          (should (equal once (xdg-init-edits-test--bytes file))))
      (delete-file file))))

(ert-deftest xdg-init-edits-test-missing-text-aborts-everything ()
  (let* ((file (xdg-init-edits-test--fixture #'butlast))
         (before (xdg-init-edits-test--bytes file)))
    (unwind-protect
        (progn
          (should-not (xdg-init-edits-apply file))
          (should (equal before (xdg-init-edits-test--bytes file))))
      (delete-file file))))

(ert-deftest xdg-init-edits-test-ambiguous-text-aborts-everything ()
  (let* ((file (xdg-init-edits-test--fixture
                (lambda (texts) (append texts (last texts)))))
         (before (xdg-init-edits-test--bytes file)))
    (unwind-protect
        (progn
          (should-not (xdg-init-edits-apply file))
          (should (equal before (xdg-init-edits-test--bytes file))))
      (delete-file file))))

(provide 'apply-init-edits-test)

;;; apply-init-edits-test.el ends here
```

- [ ] **Step 2: Run the tests to verify they fail**

Run: `emacs --batch -Q -l xdg/apply-init-edits-test.el -f ert-run-tests-batch-and-exit; echo "exit=$?"`

Expected: `exit=255`, and above it

```text
Cannot open load file: No such file or directory, <WT>/xdg/apply-init-edits.el
```

- [ ] **Step 3: Write the editor**

Create `xdg/apply-init-edits.el`:

```elisp
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
     :new "** Keep state and caches out of the configuration directory

#+begin_src emacs-lisp
;; Durable state lives under $XDG_DATA_HOME/emacs and caches under
;; $XDG_CACHE_HOME/emacs; see lisp/user-paths.el.  An interactive session
;; has loaded it from early-init.el already.  Batch runs (make, tests) never
;; read early-init.el, so load it here as well.
(eval-and-compile
  (require 'user-paths
           (expand-file-name \"lisp/user-paths.el\" user-emacs-directory)))

;; Refuse to run on state that is still inside this checkout.
(user-paths-check-migrated)
#+end_src

** Load Nix-managed packages into the macOS application
")
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
    (:name "backups follow the data root"
     :old "  (backup-directory-alist '((\".\" . \"~/.local/share/emacs/backups\")))
"
     :new "  (backup-directory-alist `((\".\" . ,(user-data \"backups\"))))
")
    (:name "projectile index is a cache"
     :old "  (projectile-cache-file (user-data \"projectile.cache\"))
"
     :new "  (projectile-cache-file (user-cache \"projectile.cache\"))
")
    (:name "tramp auto-saves follow the data root"
     :old "  (tramp-auto-save-directory \"~/.local/share/emacs/backups\")
"
     :new "  (tramp-auto-save-directory (user-data \"backups\"))
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
"))
  "Edits to make, in order, as plists.
:old is the text to find and :new its replacement.  An edit counts as
done when :new is present; :removes names a string that must then be
absent, for an edit whose :new is also part of the unedited file.")

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
        (removes (plist-get edit :removes)))
    (cond
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
```

- [ ] **Step 4: Run the tests to verify they pass**

Run: `emacs --batch -Q -l xdg/apply-init-edits-test.el -f ert-run-tests-batch-and-exit 2>&1 | grep -E 'FAILED|Ran '`

Expected: `Ran 5 tests, 5 results as expected, 0 unexpected (...)`

- [ ] **Step 5: Check every edit against the canonical file, without writing it**

Run: `emacs --batch -Q -l xdg/apply-init-edits.el -f xdg-init-edits-batch --check ~/org/init.org; echo "exit=$?"`

Expected:

```text
pending   load user-paths before anything else
pending   drop the old data-environment block
pending   auto-save-list prefix is set in user-paths
pending   backups follow the data root
pending   projectile index is a cache
pending   tramp auto-saves follow the data root
pending   tramp persistency is set in user-paths
pending   transient files are set in user-paths
pending   url directory is set in user-paths
pending   url cache directory is set in user-paths
exit=0
```

If a line says `ERROR`, that block of `init.org` has changed since this plan was written. Open `~/org/init.org`, find the block the edit's name describes, and change that edit's `:old` in `xdg/apply-init-edits.el` to the block's current text, byte for byte. Change `:new` to match, keeping what the table above says the edit does. Then repeat Steps 4 and 5.

- [ ] **Step 6: Commit**

```bash
git add xdg/apply-init-edits.el xdg/apply-init-edits-test.el
git commit -m "xdg: Add an anchored editor for the init.org path edits"
```

---

### Task 3: The sealed audit of the whole init

**Files:**
- Create: `xdg/audit/sandbox.sb`
- Create: `xdg/audit/guards.el`
- Create: `xdg/audit/audit.el`
- Create: `xdg/audit/run.sh` (executable)

**Interfaces:**
- Consumes: `early-init.el` and `lisp/user-paths.el` (Task 1) and `xdg/apply-init-edits.el` with its entry `xdg-init-edits-batch` (Task 2), all taken from this branch's tracked files. Everything else comes from the live `~/.config/emacs`, read-only.
- Produces:
  - `xdg/audit/run.sh [INIT-ORG]`: exit status 0 only if no variable points into the configuration directory, no file was written there, and every form of `init.el` evaluated. INIT-ORG defaults to `~/org/init.org`. The file is copied; the original is never written.
  - `(xdg-audit-offenders ROOT)` in `audit.el`: returns a list of `(VARIABLE LIBRARY PATHS)`. Task 7 calls it in the live session.

This task has no unit test of its own. Its test is the self-test in Step 6, which plants one stray variable and one stray file and requires the run to fail on both.

- [ ] **Step 1: Write the sandbox profile**

Create `xdg/audit/sandbox.sb`:

```scheme
(version 1)
;; Profile for xdg/audit/run.sh.  Everything is allowed except writing to the
;; real home directory, writing to the directory of the live Emacs server
;; socket, and any use of the network.  The scratch directory is writable
;; even if it happens to lie below one of the denied directories.
(allow default)
(deny file-write*
      (subpath (param "REAL_HOME"))
      (subpath (param "SERVER_DIR")))
(deny network*)
(allow file-write* (subpath (param "SCRATCH")))
```

- [ ] **Step 2: Write the guards**

Create `xdg/audit/guards.el`:

```elisp
;;; guards.el --- Keep a sandboxed init away from shared resources -*- lexical-binding: t; -*-

;;; Commentary:

;; xdg/audit/run.sh loads this file before init.el.  The init is the real
;; one, so it would start a server, look up passwords and open network
;; connections.  sandbox-exec already denies the network and any write to
;; the real home directory; these stubs turn the remaining attempts into
;; logged no-ops, so that the init can finish.

;;; Code:

(let ((scratch (getenv "XDG_AUDIT_SCRATCH")))
  (unless (and scratch
               (string-prefix-p scratch (expand-file-name "~"))
               (string-prefix-p scratch
                                (expand-file-name user-emacs-directory)))
    (message "guards: HOME and the init directory must be inside %s" scratch)
    (kill-emacs 99)))

;; Servers and listeners.
(dolist (function '(server-start edit-server-start atomic-chrome-start-server
                    httpd-start))
  (advice-add function :override
              (lambda (&rest _)
                (message "guards: suppressed %s" function)
                nil)
              `((name . ,(intern (format "xdg-audit-%s" function))))))

;; Network.
(define-advice make-network-process (:override (&rest args) xdg-audit)
  (signal 'file-error
          (list "guards: network disabled" (plist-get args :name))))
(define-advice url-retrieve (:override (url &rest _) xdg-audit)
  (message "guards: refused url-retrieve %s" url)
  nil)
(define-advice url-retrieve-synchronously (:override (url &rest _) xdg-audit)
  (message "guards: refused url-retrieve-synchronously %s" url)
  nil)

;; Long-lived subprocesses.
(define-advice make-process (:override (&rest args) xdg-audit)
  (signal 'file-error
          (list "guards: subprocesses disabled" (plist-get args :command))))

;; emacsclient could reach the live session.
(define-advice call-process (:around (original program &rest args) xdg-audit)
  (if (and (stringp program)
           (string-match-p "emacsclient" (file-name-nondirectory program)))
      1
    (apply original program args)))

;; The init looks passwords up while it loads.
(define-advice lookup-password (:override (&rest _) xdg-audit)
  "not-a-real-password")

;; This reads a file from ~/org, which the scratch home does not have.
(advice-add 'org-ext-update-team :around
            (lambda (original &rest args)
              (condition-case err
                  (apply original args)
                (error (message "guards: org-ext-update-team: %S" err) nil)))
            '((name . xdg-audit-org-ext-update-team)))

;; No prompt may block a batch run.
(setq use-dialog-box nil)
(define-advice yes-or-no-p (:override (&rest _) xdg-audit) nil)
(define-advice y-or-n-p (:override (&rest _) xdg-audit) nil)

(provide 'guards)

;;; guards.el ends here
```

- [ ] **Step 3: Write the audit**

Create `xdg/audit/audit.el`:

```elisp
;;; audit.el --- Find variables that still point into the init directory -*- lexical-binding: t; -*-

;;; Commentary:

;; xdg/audit/run.sh loads this file in a batch Emacs whose home directory
;; is a scratch copy.  It loads early-init.el and init.el the way an
;; interactive start would, loads every feature a `use-package' form names,
;; and then looks at every variable.  A variable whose value names a path
;; inside the init directory is an offender unless it is on the lists below.
;;
;; Each offender is printed as "OFFENDER<TAB>variable<TAB>library<TAB>paths".
;; The exit status is 1 if there is an offender or a form of init.el failed.
;;
;; The scan cannot see a path that is a symbol or a function resolved on
;; use, a relative path, or a value inside a vector, hash table or closure.

;;; Code:

(require 'cl-lib)

(defconst xdg-audit-allowed-paths
  '("lisp" "snippets" "prompts" "certs" "auctex/style"
    "abbrevs.el" "settings.el" "runshell" "init.el" "early-init.el" "init.org"
    "eshell/alias" "eshell/login" "eshell/profile"
    "nix-packages" "nix-packages.el")
  "Configuration that Emacs reads, relative to the init directory.
A path is allowed if it equals an entry or lies beneath one.")

(defconst xdg-audit-allowed-variables
  '(;; Emacs's own record of where the configuration is.
    user-emacs-directory user-init-file early-init-file default-directory
    command-line-default-directory custom-file custom-theme-directory
    user-lisp-directory startup--xdg-config-default
    startup--xdg-config-home-emacs startup--original-eln-load-path
    ;; Bookkeeping, not settings.
    load-path load-history load-file-name current-load-list
    custom-current-group-alist command-line-args command-line-args-left
    ;; Configuration read from the checkout.
    eshell-directory-name aya-persist-snippets-dir
    dired-ext-directory-groups magit-user-githook-file
    ;; Written only by an explicit command, as settings a person chose.
    calc-settings-file diary-file purpose-default-layout-file
    purpose-layout-dirs TeX-style-private TeX-style-path
    ;; An obsolete constant; `treemacs-last-error-persist-file' replaced it.
    treemacs--last-error-persist-file)
  "Variables that may point into the init directory.")

(defconst xdg-audit-history-regexp
  (rx (or (seq (or "-history" "-ring") string-end)
          (seq string-start
               (or "recentf-list" "save-place-alist" "dired-buffers"
                   "project--list" "projectile-known-projects"
                   "projectile-known-projects-on-file")
               string-end)))
  "Variables that only remember paths a session has visited.")

(defun xdg-audit--prefixes (root)
  "Return the spellings under which a path counts as inside ROOT."
  (let* ((absolute (file-name-as-directory (expand-file-name root)))
         (home (file-name-as-directory (expand-file-name "~")))
         (prefixes (list absolute)))
    (cond ((string-prefix-p "/private/" absolute)
           (push (substring absolute (length "/private")) prefixes))
          ((string-match-p "\\`/\\(tmp\\|var\\)/" absolute)
           (push (concat "/private" absolute) prefixes)))
    (dolist (prefix (copy-sequence prefixes))
      (when (string-prefix-p home prefix)
        (push (concat "~/" (substring prefix (length home))) prefixes)))
    prefixes))

(defun xdg-audit--inside-p (value prefixes)
  "Return non-nil if VALUE is a path at or below one of PREFIXES."
  (and (stringp value)
       (< (length value) 4096)
       (cl-some (lambda (prefix)
                  (or (string-prefix-p prefix value)
                      (string= value (substring prefix 0 -1))))
                prefixes)))

(defun xdg-audit--paths (value prefixes)
  "Return the paths in VALUE that lie inside PREFIXES.
VALUE may be a string, a list of strings, or an alist with strings as
keys or values.  Nothing deeper is examined."
  (cond
   ((xdg-audit--inside-p value prefixes) (list value))
   ((and (consp value) (proper-list-p value))
    (let (found)
      (dolist (element (take 2000 value))
        (dolist (candidate (if (consp element)
                               (list (car element) (cdr element)
                                     (car-safe (cdr element)))
                             (list element)))
          (when (xdg-audit--inside-p candidate prefixes)
            (push candidate found))))
      (nreverse found)))
   ((consp value)
    (cl-remove-if-not (lambda (candidate)
                        (xdg-audit--inside-p candidate prefixes))
                      (list (car value) (cdr value))))))

(defun xdg-audit--relative (path prefixes)
  "Return PATH relative to the init directory named by PREFIXES."
  (or (cl-some (lambda (prefix)
                 (cond ((string-prefix-p prefix path)
                        (substring path (length prefix)))
                       ((string= path (substring prefix 0 -1)) "")))
               prefixes)
      path))

(defun xdg-audit--allowed-path-p (path prefixes)
  "Return non-nil if PATH is configuration on `xdg-audit-allowed-paths'."
  (let ((relative (xdg-audit--relative path prefixes)))
    (cl-some (lambda (allowed)
               (or (string= relative allowed)
                   (string-prefix-p (concat allowed "/") relative)))
             xdg-audit-allowed-paths)))

(defun xdg-audit-offenders (root)
  "Return (VARIABLE LIBRARY PATHS) for each offender under ROOT."
  (let ((prefixes (xdg-audit--prefixes root))
        offenders)
    (mapatoms
     (lambda (symbol)
       (when (and (not (keywordp symbol))
                  (default-boundp symbol)
                  (not (memq symbol xdg-audit-allowed-variables))
                  (not (string-match-p xdg-audit-history-regexp
                                       (symbol-name symbol))))
         (let ((paths (cl-remove-if
                       (lambda (path)
                         (xdg-audit--allowed-path-p path prefixes))
                       (xdg-audit--paths (default-value symbol) prefixes))))
           (when paths
             (push (list symbol
                         (let ((file (symbol-file symbol 'defvar)))
                           (if file (file-name-nondirectory file) "-"))
                         (mapcar (lambda (path)
                                   (concat "<init>/"
                                           (xdg-audit--relative path prefixes)))
                                 (take 6 paths)))
                   offenders))))))
    (sort offenders (lambda (a b) (string< (car a) (car b))))))

(defun xdg-audit--forms (file)
  "Return the top-level forms of FILE."
  (with-temp-buffer
    (insert-file-contents file)
    (let (forms)
      (condition-case nil
          (while t
            (push (read (current-buffer)) forms))
        (end-of-file nil))
      (nreverse forms))))

(defun xdg-audit-load (file)
  "Evaluate FILE one form at a time; return (FORMS . FAILED) as counts.
One failing form therefore cannot hide the forms after it."
  (let ((load-file-name file)
        (load-true-file-name file)
        (load-in-progress t)
        (forms (xdg-audit--forms file))
        (failed 0))
    (dolist (form forms)
      (condition-case err
          (eval form t)
        (error
         (setq failed (1+ failed))
         (message "audit: FAILED %s: %S"
                  (truncate-string-to-width (format "%S" form) 70)
                  err))))
    (cons (length forms) failed)))

(defun xdg-audit--features (file)
  "Return the feature named by each `use-package' form in FILE."
  (let (names)
    (cl-labels ((walk (form)
                  (when (and (consp form) (proper-list-p form))
                    (when (and (eq (car form) 'use-package)
                               (symbolp (cadr form))
                               (not (plist-get (cddr form) :disabled)))
                      (push (cadr form) names))
                    (mapc #'walk form))))
      (mapc #'walk (xdg-audit--forms file)))
    (nreverse names)))

(defun xdg-audit--run-hook (hook)
  "Run the functions on HOOK one at a time, logging errors."
  (dolist (function (let ((value (and (boundp hook) (symbol-value hook))))
                      (if (functionp value) (list value) value)))
    (unless (eq function t)
      (condition-case err
          (funcall function)
        (error (message "audit: %s: %S" hook err)))))
  (set hook nil))

(defvar xdg-audit-selftest-file nil
  "A path inside the init directory, set only by the self-test.")

(defun xdg-audit--selftest ()
  "Plant a stray variable and a stray file for the audit to find."
  (setq xdg-audit-selftest-file
        (expand-file-name "selftest-state" user-emacs-directory))
  (write-region "" nil xdg-audit-selftest-file nil 'silent))

(defun xdg-audit-main ()
  "Load the init, force every package to load, and report offenders."
  (let ((early (expand-file-name "early-init.el" user-emacs-directory))
        (init (expand-file-name "init.el" user-emacs-directory))
        (guards (expand-file-name "guards.el"
                                  (file-name-directory load-file-name)))
        (forms 0)
        (failed 0)
        (loaded 0)
        (refused 0))
    ;; An interactive start loads early-init.el before anything else.
    (when (file-exists-p early)
      (load early nil t))
    (load guards nil t)
    ;; Forms that test `noninteractive' or `window-system' (savehist,
    ;; persistent-scratch, the server) must take their interactive branch.
    (let ((noninteractive nil)
          (window-system 'ns))
      (setq user-init-file init)
      (let ((counts (xdg-audit-load init)))
        (setq forms (car counts)
              failed (cdr counts)))
      (mapc #'xdg-audit--run-hook
            '(after-init-hook emacs-startup-hook window-setup-hook))
      (dolist (feature (xdg-audit--features init))
        (unless (featurep feature)
          (condition-case nil
              (with-timeout (30 (setq refused (1+ refused)))
                (let ((inhibit-message t))
                  (require feature))
                (setq loaded (1+ loaded)))
            (error (setq refused (1+ refused)))))))
    (when (equal (getenv "XDG_AUDIT_SELFTEST") "1")
      (xdg-audit--selftest))
    (message "audit: %d forms, %d failed; %d more features loaded, %d would not; %d features in all"
             forms failed loaded refused (length features))
    (let ((offenders (xdg-audit-offenders user-emacs-directory)))
      (dolist (offender offenders)
        (princ (format "OFFENDER\t%s\t%s\t%S\n"
                       (nth 0 offender) (nth 1 offender) (nth 2 offender))))
      (princ (format "audit: %d offenders, %d failed forms\n"
                     (length offenders) failed))
      ;; Leave through `kill-emacs', so that exit hooks write their files.
      (kill-emacs (if (or offenders (> failed 0)) 1 0)))))

(when noninteractive
  (xdg-audit-main))

;;; audit.el ends here
```

- [ ] **Step 4: Write the runner**

Create `xdg/audit/run.sh`:

```bash
#!/usr/bin/env bash
# run.sh --- load the whole init in a sealed copy and report stray paths
#
# Usage: xdg/audit/run.sh [INIT-ORG]
#
# Copies the configuration into a throw-away home directory, applies
# xdg/apply-init-edits.el to a copy of INIT-ORG (default ~/org/init.org),
# tangles init.el there, and runs the real Emacs in batch on that copy with
# every `use-package' feature loaded.  Then it reports
#
#   - each variable whose value still names a path inside the
#     configuration directory, and
#   - each file the run wrote inside the configuration directory.
#
# The exit status is 0 only if both lists are empty and every form of
# init.el evaluated.
#
# Emacs runs under sandbox-exec with writes to the real home directory and
# all network access denied, and with HOME and the XDG variables pointing
# into the scratch directory.  Set XDG_AUDIT_KEEP=1 to keep that directory.
#
# XDG_AUDIT_SELFTEST=1 plants one stray variable and one stray file, to show
# that the run catches both; such a run must fail.

set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd -P)
checkout=$(cd "$here/../.." && pwd -P)
init_org=${1:-$HOME/org/init.org}
emacs=${EMACS:-/Applications/Emacs.app/Contents/MacOS/bin/emacs}
real_home=$(cd "$HOME" && pwd -P)
host=${XDG_AUDIT_HOST_CONFIG:-$real_home/.config/emacs}

fail() {
    printf 'run.sh: %s\n' "$*" >&2
    exit 2
}

[[ -x /usr/bin/sandbox-exec ]] || fail 'this needs /usr/bin/sandbox-exec (macOS)'
[[ -x $emacs ]] || fail "no Emacs at $emacs; set EMACS"
[[ -f $init_org ]] || fail "no such file: $init_org"

scratch=$(mktemp -d "${TMPDIR:-/tmp}/xdg-audit.XXXXXX")
[[ -n $scratch && -d $scratch ]] || fail 'cannot create a scratch directory'
scratch=$(cd "$scratch" && pwd -P)

# Remove the scratch directory on exit, and nothing that is not one.
# shellcheck disable=SC2329  # called by the EXIT trap below
cleanup() {
    if [[ ${XDG_AUDIT_KEEP:-} == 1 ]]; then
        return
    fi
    case $scratch in
    */xdg-audit.??????) rm -rf "$scratch" ;;
    esac
}
trap cleanup EXIT
home=$scratch/home
config=$home/.config/emacs
mkdir -p "$config" "$home/.local/share" "$home/.cache" "$scratch/tmp"

# Start from what the live configuration directory holds: tracked files,
# submodules, and the host's untracked configuration.  No runtime state is
# copied.  Then lay this checkout's tracked files over it, so that the copy
# shows this branch even when the script runs from a separate worktree.
for name in abbrevs.el settings.el runshell early-init.el Makefile; do
    if [[ -e $host/$name ]]; then
        cp -p "$host/$name" "$config/$name"
    fi
done
for name in lisp snippets prompts certs; do
    if [[ -d $host/$name ]]; then
        rsync -a --exclude .git "$host/$name/" "$config/$name/"
    fi
done
mkdir -p "$config/eshell"
for name in alias login; do
    if [[ -e $host/eshell/$name ]]; then
        cp -p "$host/eshell/$name" "$config/eshell/$name"
    fi
done
for name in nix-packages nix-packages.el; do
    if [[ -L $host/$name ]]; then
        ln -s "$(readlink "$host/$name")" "$config/$name"
    fi
done
git -C "$checkout" ls-files -z |
    rsync -a --from0 --files-from=- "$checkout/" "$config/"
# llm-setup reads these Nix-generated policy files while it loads.
if [[ -d $real_home/.config/ai ]]; then
    mkdir -p "$home/.config/ai"
    for file in "$real_home"/.config/ai/*; do
        target=$(readlink "$file" || true)
        case $target in
        /nix/store/*) ln -s "$target" "$home/.config/ai/${file##*/}" ;;
        esac
    done
fi
cp "$init_org" "$config/init.org"
chmod -R u+w "$config"

sealed() {
    /usr/bin/sandbox-exec \
        -D REAL_HOME="$real_home" \
        -D SERVER_DIR="/private/tmp/$(id -un)-emacs" \
        -D SCRATCH="$scratch" \
        -f "$here/sandbox.sb" \
        /usr/bin/env -i \
        HOME="$home" USER="$(id -un)" LOGNAME="$(id -un)" SHELL=/bin/sh \
        XDG_CONFIG_HOME="$home/.config" XDG_DATA_HOME="$home/.local/share" \
        XDG_CACHE_HOME="$home/.cache" XDG_STATE_HOME="$home/.local/state" \
        PATH="$PATH" TERM=dumb LANG=en_US.UTF-8 TMPDIR="$scratch/tmp/" \
        XDG_AUDIT_SCRATCH="$scratch" \
        XDG_AUDIT_SELFTEST="${XDG_AUDIT_SELFTEST:-}" \
        "$@"
}

printf 'Applying the init.org edits to the copy\n'
sealed "$emacs" --batch -Q -l "$config/xdg/apply-init-edits.el" \
    -f xdg-init-edits-batch "$config/init.org" 2>&1 | sed 's/^/  /'

printf 'Tangling init.el\n'
sealed "$emacs" --batch -Q --chdir="$config" --eval "(require 'org)" --eval \
    '(org-babel-tangle-file "init.org" "init.el" (rx string-start (or "emacs-lisp" "elisp") string-end))' \
    >"$scratch/tangle.log" 2>&1 || {
    cat "$scratch/tangle.log" >&2
    fail 'tangling failed'
}
[[ -s $config/init.el ]] || fail 'tangling produced no init.el'

touch "$scratch/stamp"
sleep 1

printf 'Loading the init; this takes about half a minute\n'
status=0
sealed "$emacs" --batch --init-directory="$config" --chdir="$home" \
    -l "$here/audit.el" >"$scratch/audit.out" 2>"$scratch/audit.log" || status=$?
grep -E '^audit: ' "$scratch/audit.log" | sed 's/^/  /' || true
grep -E '^(OFFENDER|audit: )' "$scratch/audit.out" || true

written=$(cd "$config" && find . -newer "$scratch/stamp" ! -type d | LC_ALL=C sort)
printf 'Written inside the configuration directory:\n'
if [[ -n $written ]]; then
    printf '%s\n' "$written" | sed 's/^/  /'
    status=1
fi
printf 'Written under the data and cache roots:\n'
(cd "$home" && find .local/share .cache -newer "$scratch/stamp" ! -type d |
    sed 's|\(eln-cache/[^/]*\)/.*|\1/*.eln|' | LC_ALL=C sort -u | sed 's/^/  /')

if [[ $status -eq 0 ]]; then
    printf 'PASS\n'
else
    printf 'FAIL (the log is %s; set XDG_AUDIT_KEEP=1 to keep it)\n' "$scratch/audit.log"
fi
exit "$status"
```

- [ ] **Step 5: Make it executable and lint it**

Run: `chmod +x xdg/audit/run.sh && shellcheck xdg/audit/run.sh; echo "exit=$?"`

Expected: `exit=0` and no other output.

- [ ] **Step 6: Run the self-test; it must fail**

Run: `XDG_AUDIT_SELFTEST=1 xdg/audit/run.sh 2>&1 | grep -E '^(OFFENDER|audit:|Written inside|  \./|FAIL|PASS)'`

Expected (each run takes about half a minute):

```text
OFFENDER	xdg-audit-selftest-file	-	("<init>/selftest-state")
audit: 1 offenders, 0 failed forms
Written inside the configuration directory:
  ./selftest-state
FAIL (the log is ...; set XDG_AUDIT_KEEP=1 to keep it)
```

This shows that the run catches a stray variable and a stray file.

- [ ] **Step 7: Run the audit; it must pass**

Run: `xdg/audit/run.sh; echo "exit=$?"`

Expected:

```text
Applying the init.org edits to the copy
  applied   load user-paths before anything else
  ... nine more "applied" lines ...
Tangling init.el
Loading the init; this takes about half a minute
  audit: emacs-startup-hook: (user-error "Not a directory: .../home/Desktop")
  audit: window-setup-hook: (file-error "guards: subprocesses disabled" (".../epdfinfo"))
  audit: 580 forms, 0 failed; 300 more features loaded, 30 would not; 1674 features in all
audit: 0 offenders, 0 failed forms
Written inside the configuration directory:
Written under the data and cache roots:
  .cache/emacs/eln-cache/31_1_50-ed4578ca/*.eln
  .local/share/emacs/bm-repository
  .local/share/emacs/history
  .local/share/emacs/org-roam.db
  .local/share/emacs/persistent-scratch
  .local/share/emacs/recentf
  .local/share/emacs/tramp
PASS
exit=0
```

The two hook lines are expected: the scratch home has no `~/Desktop`, and the guards refuse to start `epdfinfo`. The counts drift as the init and the packages change. What must hold is `0 offenders, 0 failed forms`, an empty list under `Written inside the configuration directory`, and `PASS`.

If the run reports an offender, `init.org` has gained a package since this plan was written. Decide as follows, then run `make test-xdg` (after Task 5) or the Task 1 tests, and this step again.

1. The value is configuration that a person writes, such as a snippets directory or a settings file: add the variable to `xdg-audit-allowed-variables` in `xdg/audit/audit.el`, under the comment that fits.
2. Otherwise add `(VARIABLE data "name")` or `(VARIABLE cache "name")` to `user-paths-table` in `lisp/user-paths.el`, in alphabetical order within its half. Choose `data` if losing the file loses information or a sign-in, and `cache` if Emacs rebuilds it unaided. Keep a trailing slash if the package's default has one.
3. The variable is a `defconst`, or its value is not a single string: set it in `user-paths-apply-special`.

If a form of `init.el` fails, the log names it. A form that needs one of John's documents can be tolerated the way `guards.el` tolerates `org-ext-update-team`.

- [ ] **Step 8: Commit**

```bash
git add xdg/audit
git commit -m "xdg: Audit the whole init in a sealed copy"
```

---

### Task 4: The mover

**Files:**
- Create: `xdg/migrate.sh` (executable)
- Test: `xdg/migrate-test.sh` (executable)
- Delete: `migrate-emacs-xdg.sh`

**Interfaces:**
- Consumes: nothing from other tasks. Reads `HOME`, `XDG_CONFIG_HOME`, `XDG_DATA_HOME`, `XDG_CACHE_HOME`, and for tests `EMACS_XDG_STAMP` and `EMACS_XDG_TEST_PS_FILE`.
- Produces:
  - `xdg/migrate.sh`: preview, exit 0, changes nothing. A running Emacs is only a warning.
  - `xdg/migrate.sh --apply`: moves, exit 0. Refuses with exit 1 if Emacs runs, if `~/.emacs.d`, `~/.emacs` or `~/.emacs.el` exists, if the configuration directory has no `init.org`, or if a source is a symbolic link.
  - `--prefer=source` or `--prefer=destination`, with or without `--apply`: says which copy wins where a destination already holds a different file. Without it, a preview marks each such pair with `clash` and `--apply` refuses before moving anything. The copy that loses is kept under `<run directory>/collisions/`.
  - `xdg/migrate.sh --rollback DIR`: undoes the renames listed in `DIR/moves.tsv`. It refuses to overwrite a file that has come back at an old path, and it can be run again after it stops.
  - The run directory `<data>/migration/<stamp>/` holding `moves.tsv`, `pre-migration.tar`, `attic/` and, if anything collided, `collisions/`.
  - The file `<data>/eshell/history` and its neighbours at exactly the names `user-paths-table` gives them.

Where each thing goes:

| Source in `~/.config/emacs` | Destination | Kind |
|---|---|---|
| `data/*` (history, recentf, org-roam.db, org-id-locations, places, tramp, transient/, url/cookies, auto-save-list/, ...) | `~/.local/share/emacs/` under the same names | data |
| `eshell/history`, `eshell/lastdir` | `~/.local/share/emacs/eshell/` | data |
| `projects`, `projectile-frecency.eld` | `~/.local/share/emacs/` | data |
| `multisession/`, `persist/`, `request/`, `tree-sitter/` | `~/.local/share/emacs/` | data |
| `eln-cache/`, `emojis/` | `~/.cache/emacs/` | cache |
| `var/pcache/` | `~/.cache/emacs/pcache/` | cache |
| `url/cache/` (stray), `data/url/cache/` | `~/.cache/emacs/url/` | cache |
| `data/projectile.cache`, `data/.cache/lsp/` | `~/.cache/emacs/` | cache |
| `data-MacPort/`, `data/mc-lists.elc`, `var/osm/`, `transient/` (stray), `auto-save-list/` (stray), `elpy/`, `gptel-agent/`, `.lsp-session-v1`, `.org-generic-id-locations`, `anvil-worker.log`, `%backup%~` | `<run directory>/attic/` under the same names | attic |
| `hash-store/`, `agent/`, and `var/`, `url/`, `data/` once emptied | removed if empty | prune |
| `eshell/alias`, `eshell/login`, `certs/`, `settings.el`, `init.el`, `nix-packages*` | stay | configuration |

- [ ] **Step 1: Write the failing tests**

Create `xdg/migrate-test.sh`:

```bash
#!/usr/bin/env bash
# migrate-test.sh --- exercise xdg/migrate.sh against throw-away trees
#
# Usage: xdg/migrate-test.sh
#
# Every test builds its own home directory under a scratch directory and
# points the script at it, so no real state is read or written.

set -uo pipefail

here=$(cd "$(dirname "$0")" && pwd -P)
migrate=$here/migrate.sh
scratch=$(mktemp -d "${TMPDIR:-/tmp}/migrate-test.XXXXXX")
if [[ -z $scratch || ! -d $scratch ]]; then
    printf 'migrate-test: cannot create a scratch directory\n' >&2
    exit 2
fi
scratch=$(cd "$scratch" && pwd -P)

# Remove the scratch directory on exit, and nothing that is not one.
cleanup() {
    case $scratch in
    */migrate-test.??????) rm -rf "$scratch" ;;
    esac
}
trap cleanup EXIT

passed=0
failed=0

ok() {
    passed=$((passed + 1))
    printf 'ok    %s\n' "$1"
}

not_ok() {
    failed=$((failed + 1))
    printf 'FAIL  %s\n' "$1"
    if [[ -n ${2:-} ]]; then
        printf '%s\n' "$2" | sed 's/^/        /'
    fi
}

# check DESCRIPTION COMMAND...: passes when COMMAND succeeds.
check() {
    local description=$1 output
    shift
    if output=$("$@" 2>&1); then
        ok "$description"
    else
        not_ok "$description" "$output"
    fi
}

put() {
    mkdir -p "$(dirname "$1")"
    printf '%s\n' "$2" >"$1"
}

# Build a home directory that looks like the real one before migration.
fixture() {
    local home=$1 config data cache
    config=$home/.config/emacs
    data=$home/.local/share/emacs
    cache=$home/.cache/emacs
    mkdir -p "$config" "$data/backups" "$cache"

    # Configuration that must stay.
    put "$config/init.org" 'init'
    put "$config/init.el" 'generated'
    put "$config/lisp/a.el" 'lisp'
    put "$config/eshell/alias" 'alias ll ls -l'
    put "$config/eshell/login" 'login'
    put "$config/mystery.txt" 'nobody knows this file'

    # State under data/.
    put "$config/data/history" 'legacy history'
    put "$config/data/recentf" 'recent files'
    put "$config/data/org-roam.db" 'database'
    put "$config/data/oauth2-auto.plist" 'token'
    chmod 644 "$config/data/oauth2-auto.plist"
    put "$config/data/mc-lists.el" 'lists'
    put "$config/data/mc-lists.elc" 'compiled'
    put "$config/data/workgroups" 'old'
    put "$config/data/.hidden" 'a dot file'
    put "$config/data/auto-save-list/.saves-1-host~" 'index'
    put "$config/data/transient/history.el" 'nil'
    put "$config/data/transient/values.el" 'values'
    put "$config/data/url/cookies" 'cookies'
    chmod 644 "$config/data/url/cookies"
    put "$config/data/url/cache/johnw/a" 'cached a'
    put "$config/data/.cache/lsp/server" 'server'
    put "$config/data/projectile.cache" 'index'

    # State and caches at the top level.
    put "$config/data-MacPort/auto-save-list/.saves-2-host~" 'stale'
    put "$config/eshell/history" 'ls'
    put "$config/eshell/lastdir" '/tmp'
    put "$config/projects" 'projects'
    put "$config/projectile-frecency.eld" 'frecency'
    put "$config/multisession/files/emoji/emoji--recent.value" 'emoji'
    put "$config/persist/listen-queues" 'queues'
    put "$config/persist/org-gcal--sync-tokens" 'tokens'
    chmod 644 "$config/persist/org-gcal--sync-tokens"
    put "$config/request/curl-cookie-jar" 'jar'
    chmod 644 "$config/request/curl-cookie-jar"
    put "$config/tree-sitter/libtree-sitter-c.dylib" 'grammar'
    put "$config/eln-cache/31/x.eln" 'native'
    put "$config/emojis/set/1.png" 'png'
    put "$config/var/pcache/fonts" 'fonts'
    put "$config/var/osm/default/1.png" 'tile'
    put "$config/url/cache/johnw/a" 'cached a'
    put "$config/url/cache/johnw/b" 'cached b'
    put "$config/transient/history.el" 'nil'
    put "$config/auto-save-list/.saves-3-host~" ''
    put "$config/elpy/rpc-venv/pyvenv.cfg" 'venv'
    mkdir -p "$config/elpy/rpc-venv/bin"
    ln -s /nonexistent/python "$config/elpy/rpc-venv/bin/python"
    put "$config/gptel-agent/sessions.db" 'db'
    put "$config/gptel-agent/sessions.db-wal" 'wal'
    put "$config/gptel-agent/sessions.db-shm" 'shm'
    mkdir -p "$config/gptel-agent/skills"
    put "$config/.lsp-session-v1" 'session'
    put "$config/.org-generic-id-locations" 'ids'
    put "$config/anvil-worker.log" 'log'
    put "$config/%backup%~" 'emergency backup'
    mkdir -p "$config/hash-store" "$config/agent"

    # What is already at the destinations.
    put "$data/backups/keep.txt" 'a backup'
    put "$data/history" 'a history written by a premature start'
    put "$data/recentf" 'recent files'
    mkdir -p "$data/url" "$data/eshell" "$data/tree-sitter"
    put "$cache/tramp.abc" 'stray'

    git -C "$config" init -q
    git -C "$config" add init.org lisp
    printf '/bin/zsh\n/usr/bin/ssh-agent\n/opt/emacsclient\n' >"$home/ps"
}

# Describe every file, link and directory below $1: the name of each,
# the target of each link, and a checksum of each file.
snapshot() {
    (cd "$1" && {
        find . -mindepth 1 -not -path './.git/*' -not -path './.git' \
            \( -type d -o -type l \) | LC_ALL=C sort | while IFS= read -r path; do
            if [[ -L $path ]]; then
                printf 'L %s -> %s\n' "$path" "$(readlink "$path")"
            else
                printf 'D %s\n' "$path"
            fi
        done
        find . -mindepth 1 -not -path './.git/*' -type f -print0 |
            LC_ALL=C sort -z | xargs -0 shasum
    })
}

# run HOME ARGS...: run the script against the fixture in HOME.
run() {
    local home=$1
    shift
    env -u XDG_CONFIG_HOME -u XDG_DATA_HOME -u XDG_CACHE_HOME \
        HOME="$home" EMACS_XDG_STAMP=run1 EMACS_XDG_TEST_PS_FILE="$home/ps" \
        "$migrate" "$@"
}

mode_of() {
    if stat -f %Lp "$1" >/dev/null 2>&1; then
        stat -f %Lp "$1"
    else
        stat -c %a "$1"
    fi
}

actions() {
    grep -E '^  (mv|rmdir|same|keep|stays|clash) ' || true
}

# ---------------------------------------------------------------- preview
home=$scratch/preview
fixture "$home"
before=$(snapshot "$home")
output=$(run "$home" 2>&1)
status=$?
check 'preview exits 0' test "$status" -eq 0
check 'preview changes nothing' test "$before" = "$(snapshot "$home")"
check 'preview says so' grep -q 'Preview only' <<<"$output"
check 'preview shows a destination that holds a different file' \
    grep -q "^  clash  $home/.config/emacs/data/history <> $home/.local/share/emacs/history\$" <<<"$output"
check 'preview says that apply will need a preference' \
    grep -q -- '--apply will need --prefer=source or --prefer=destination' <<<"$output"
check 'preview keeps a directory that still holds a clashing file' \
    grep -q "^  stays  $home/.config/emacs/data (not empty)\$" <<<"$output"
output=$(run "$home" --prefer=source 2>&1)
check 'a preview with a preference changes nothing' test "$before" = "$(snapshot "$home")"
preview_actions=$(actions <<<"$output")
preview_leftovers=$(sed -n '/^Left in /,/^Done\./p' <<<"$output" | sed '1d;$d')

# ------------------------------------------------------------------ apply
home=$scratch/apply
fixture "$home"
config=$home/.config/emacs
data=$home/.local/share/emacs
cache=$home/.cache/emacs
run_dir=$data/migration/run1
original=$(snapshot "$config")
original_data=$(snapshot "$data")
before=$(snapshot "$home")
output=$(run "$home" --apply 2>&1)
status=$?
check 'apply refuses to choose between two different files' \
    test "$status" -ne 0 -a "${output#*already hold a different file}" != "$output"
check 'a refused apply changes nothing' test "$before" = "$(snapshot "$home")"
output=$(run "$home" --apply --prefer=source 2>&1)
status=$?
check 'apply exits 0' test "$status" -eq 0
apply_actions=$(actions <<<"$output")
check 'preview printed the same actions as apply' \
    test "${preview_actions//preview/apply}" = "$apply_actions"

check 'history arrives with the legacy content' \
    grep -qx 'legacy history' "$data/history"
check 'the history that was there is kept' \
    grep -qx 'a history written by a premature start' "$run_dir/collisions$data/history"
check 'an identical file is merged silently' \
    grep -qx 'recent files' "$data/recentf"
check 'an identical file leaves no kept copy' \
    test ! -e "$run_dir/collisions$data/recentf" -a ! -e "$run_dir/collisions$config/data/recentf"
check 'an identical file is logged as a duplicate' \
    grep -q "^DUP	$config/data/recentf	$data/recentf\$" "$run_dir/moves.tsv"
check 'a dot file inside a merged directory moves' \
    grep -qx 'a dot file' "$data/.hidden"
check 'the database moves' test -f "$data/org-roam.db"
check 'nested state moves' test -f "$data/transient/values.el"
check 'cookies move' test -f "$data/url/cookies"
check 'auto-save index moves' test -f "$data/auto-save-list/.saves-1-host~"
check 'old state rides along' test -f "$data/workgroups"
check 'eshell history moves' test -f "$data/eshell/history"
check 'eshell lastdir moves' test -f "$data/eshell/lastdir"
check 'project list moves' test -f "$data/projects"
check 'frecency moves' test -f "$data/projectile-frecency.eld"
check 'multisession moves' test -f "$data/multisession/files/emoji/emoji--recent.value"
check 'persist moves' test -f "$data/persist/listen-queues"
check 'cookie jar moves to data' test -f "$data/request/curl-cookie-jar"
check 'grammars move to data' test -f "$data/tree-sitter/libtree-sitter-c.dylib"
check 'existing backups are untouched' grep -qx 'a backup' "$data/backups/keep.txt"

check 'native cache moves' test -f "$cache/eln-cache/31/x.eln"
check 'emoji images move' test -f "$cache/emojis/set/1.png"
check 'pcache moves' test -f "$cache/pcache/fonts"
check 'url cache from data/ moves' test -f "$cache/url/johnw/a"
check 'stray url cache merges' test -f "$cache/url/johnw/b"
check 'lsp servers move' test -f "$cache/lsp/server"
check 'projectile index moves' test -f "$cache/projectile.cache"
check 'stray cache file is untouched' test -f "$cache/tramp.abc"

attic=$run_dir/attic
check 'stale instance goes to the attic' test -f "$attic/data-MacPort/auto-save-list/.saves-2-host~"
check 'stray compiled file goes to the attic' test -f "$attic/data/mc-lists.elc"
check 'dead tile cache goes to the attic' test -f "$attic/var/osm/default/1.png"
check 'stray transient goes to the attic' test -f "$attic/transient/history.el"
check 'stray auto-save-list goes to the attic' test -f "$attic/auto-save-list/.saves-3-host~"
check 'broken venv goes to the attic' test -L "$attic/elpy/rpc-venv/bin/python"
check 'database and its WAL files stay together' \
    test -f "$attic/gptel-agent/sessions.db" -a -f "$attic/gptel-agent/sessions.db-wal" \
    -a -f "$attic/gptel-agent/sessions.db-shm"
check 'dot files go to the attic' test -f "$attic/.lsp-session-v1" -a -f "$attic/.org-generic-id-locations"
check 'a name with odd characters goes to the attic' \
    grep -qx 'emergency backup' "$attic/%backup%~"

for gone in data data-MacPort projects projectile-frecency.eld multisession persist \
    request tree-sitter eln-cache emojis var url transient auto-save-list elpy \
    gptel-agent .lsp-session-v1 .org-generic-id-locations anvil-worker.log \
    '%backup%~' hash-store agent eshell/history eshell/lastdir; do
    check "$gone has left the configuration directory" test ! -e "$config/$gone"
done
for stays in init.org init.el lisp/a.el eshell/alias eshell/login mystery.txt; do
    check "$stays stays" test -f "$config/$stays"
done
leftovers() {
    sed -n '/^Left in /,/^Done\./p' | sed '1d;$d'
}
check 'only the unknown file is reported as left behind' \
    test "$(leftovers <<<"$output")" = "  $config/mystery.txt"
check 'preview reports the same leftovers as apply' \
    test "${preview_leftovers//preview/apply}" = "$(leftovers <<<"$output")"

check 'data root is private' test "$(mode_of "$data")" = 700
check 'cache root is private' test "$(mode_of "$cache")" = 700
check 'run directory is private' test "$(mode_of "$run_dir")" = 700
check 'token file is private' test "$(mode_of "$data/oauth2-auto.plist")" = 600
check 'cookie jar is private' test "$(mode_of "$data/request/curl-cookie-jar")" = 600
check 'sync tokens are private' test "$(mode_of "$data/persist/org-gcal--sync-tokens")" = 600
check 'cookies are private' test "$(mode_of "$data/url/cookies")" = 600

check 'the archive holds the legacy history' \
    test "$(tar -xOf "$run_dir/pre-migration.tar" data/history)" = 'legacy history'
check 'the archive holds attic items' \
    test "$(tar -xOf "$run_dir/pre-migration.tar" '%backup%~')" = 'emergency backup'
check 'the archive leaves caches out' \
    test -z "$(tar -tf "$run_dir/pre-migration.tar" | grep -E '^(eln-cache|emojis|var/pcache)' || true)"
check 'every rename is logged' test "$(grep -c '^MV' "$run_dir/moves.tsv")" -ge 30

# ------------------------------------------------------------- idempotent
after_first=$(snapshot "$home")
output=$(EMACS_XDG_STAMP=run2 run "$home" --apply 2>&1)
status=$?
check 'a second apply exits 0' test "$status" -eq 0
check 'a second apply moves nothing' test -z "$(actions <<<"$output")"
check 'a second apply changes only its own run directory' \
    test "$after_first" = "$(snapshot "$home" | grep -v 'migration/run2')"

# --------------------------------------------------------------- rollback
# A file that has come back at its old path stops the rollback, which can
# be run again once the file is out of the way.
put "$config/data/history" 'written after the move'
put "$config/data/recentf" 'written after the move'
output=$(run "$home" --rollback "$run_dir" 2>&1)
status=$?
check 'rollback refuses to overwrite a file that came back' \
    test "$status" -ne 0 -a "${output#*cannot undo: "$config"/data/}" != "$output"
check 'the file that came back is untouched' \
    grep -qx 'written after the move' "$config/data/history"
check 'a duplicate that came back is untouched' \
    grep -qx 'written after the move' "$config/data/recentf"
rm "$config/data/history" "$config/data/recentf"
output=$(run "$home" --rollback "$run_dir" 2>&1)
status=$?
check 'rollback exits 0' test "$status" -eq 0
check 'rollback restores every name and its contents' \
    test "$original" = "$(snapshot "$config")"
check 'rollback restores the data root' \
    test "$original_data" = "$(snapshot "$data" | grep -v ' \./migration')"
check 'rollback leaves the cache root as it was' \
    test "$(cd "$cache" && find . -mindepth 1 | LC_ALL=C sort)" = ./tramp.abc
check 'rollback retires the log' test -f "$run_dir/moves.tsv.rolled-back"

# ------------------------------------------------- the destination wins
home=$scratch/destination
fixture "$home"
config=$home/.config/emacs
data=$home/.local/share/emacs
run_dir=$data/migration/run1
original=$(snapshot "$config")
preview=$(run "$home" --prefer=destination 2>&1 | actions)
output=$(run "$home" --apply --prefer=destination 2>&1)
status=$?
check 'apply with the destination preferred exits 0' test "$status" -eq 0
check 'its preview printed the same actions' \
    test "${preview//destination/X}" = "$(actions <<<"$output" | sed 's/destination/X/g')"
check 'the file at the destination stays' \
    grep -qx 'a history written by a premature start' "$data/history"
check 'the copy from the configuration directory is kept' \
    grep -qx 'legacy history' "$run_dir/collisions$config/data/history"
check 'everything else still moves' test -f "$data/org-roam.db" -a ! -e "$config/data"
output=$(run "$home" --rollback "$run_dir" 2>&1)
check 'rollback restores every name and its contents again' \
    test "$original" = "$(snapshot "$config")"
check 'rollback leaves the destination file alone' \
    grep -qx 'a history written by a premature start' "$data/history"

# ------------------------------------------------------------ a new host
# No data root and no cache root yet: the preview must still match.
home=$scratch/fresh
fixture "$home"
case $home in
"$scratch"/fresh) rm -r "$home/.local" "$home/.cache" ;;
esac
preview=$(run "$home" 2>&1 | actions)
output=$(run "$home" --apply 2>&1)
status=$?
check 'apply on a host without the roots exits 0' test "$status" -eq 0
check 'its preview printed the same actions' test "$preview" = "$(actions <<<"$output")"
check 'the state arrives' grep -qx 'legacy history' "$home/.local/share/emacs/history"

# -------------------------------------------- two sources, one destination
home=$scratch/twice
fixture "$home"
put "$home/.config/emacs/data/url/cache/johnw/a" 'a newer copy'
put "$home/.cache/emacs/url/johnw/a" 'a third copy'
before=$(snapshot "$home")
output=$(run "$home" --apply --prefer=source 2>&1)
status=$?
check 'apply refuses when two sources clash at one destination' \
    test "$status" -ne 0 -a "${output#*two sources clash}" != "$output"
check 'that refusal changes nothing' test "$before" = "$(snapshot "$home")"

# ---------------------------------------------------------------- refusals
refuses() {
    local description=$1 expect=$2 home=$3 before output status
    shift 3
    before=$(snapshot "$home")
    output=$(run "$home" "$@" 2>&1)
    status=$?
    if [[ $status -ne 0 && $output == *"$expect"* && $before == "$(snapshot "$home")" ]]; then
        ok "$description"
    else
        not_ok "$description" "status=$status output=$output"
    fi
}

home=$scratch/running
fixture "$home"
printf '/Applications/Emacs.app/Contents/MacOS/Emacs\n' >>"$home/ps"
refuses 'refuses while the macOS application runs' 'quit every Emacs' "$home" --apply
printf '/bin/zsh\n/nix/store/abc-emacs/bin/.emacs-wrapped\n' >"$home/ps"
refuses 'refuses while a Nix-wrapped Emacs runs' 'quit every Emacs' "$home" --apply
printf '/bin/zsh\n/nix/store/abc-emacs/bin/emacs-31.1\n' >"$home/ps"
refuses 'refuses while a versioned Emacs binary runs' 'quit every Emacs' "$home" --apply
before=$(snapshot "$home")
output=$(run "$home" 2>&1)
status=$?
check 'a preview still runs while Emacs does' test "$status" -eq 0
check 'a preview warns that Emacs is running' grep -q 'Emacs is running' <<<"$output"
check 'a preview while Emacs runs changes nothing' test "$before" = "$(snapshot "$home")"
mkdir -p "$home/.local/share/emacs/migration/run9"
printf 'MV\t/nonexistent/a\t/nonexistent/b\n' >"$home/.local/share/emacs/migration/run9/moves.tsv"
refuses 'rollback refuses while Emacs runs' 'quit every Emacs' "$home" \
    --rollback "$home/.local/share/emacs/migration/run9"
printf '/bin/zsh\n/opt/bin/emacsclient\n/usr/bin/emacs-mcp-stdio.sh\n' >"$home/ps"
check 'emacsclient and helpers do not count as Emacs' run "$home"

home=$scratch/legacy
fixture "$home"
mkdir "$home/.emacs.d"
refuses 'refuses when ~/.emacs.d exists' 'would outrank' "$home" --apply

home=$scratch/noinit
fixture "$home"
rm "$home/.config/emacs/init.org"
refuses 'refuses a directory that is not the checkout' 'no init.org' "$home" --apply

home=$scratch/symlink
fixture "$home"
mv "$home/.config/emacs/data" "$home/elsewhere"
ln -s "$home/elsewhere" "$home/.config/emacs/data"
refuses 'refuses a symbolic link in place of a source' 'symbolic link' "$home" --apply

home=$scratch/nested
fixture "$home"
output=$(env -u XDG_CONFIG_HOME -u XDG_CACHE_HOME HOME="$home" \
    XDG_DATA_HOME="$home/.config/emacs/data" EMACS_XDG_TEST_PS_FILE="$home/ps" \
    "$migrate" --apply 2>&1)
status=$?
check 'refuses a data root inside the configuration directory' \
    test "$status" -ne 0 -a "${output#*must lie outside}" != "$output"

home=$scratch/oddname
fixture "$home"
put "$home/.config/emacs/data/odd$(printf '\t')name" 'x'
refuses 'refuses a name that holds a tab' 'tab or a newline' "$home" --apply

home=$scratch/slashes
fixture "$home"
output=$(env -u XDG_DATA_HOME -u XDG_CACHE_HOME HOME="$home" \
    XDG_CONFIG_HOME="$home//.config/" EMACS_XDG_TEST_PS_FILE="$home/ps" \
    "$migrate" 2>&1)
check 'repeated and trailing slashes in a root are dropped' \
    grep -q "^Configuration: $home/.config/emacs\$" <<<"$output"
output=$(env -u XDG_CACHE_HOME HOME="$home" XDG_CONFIG_HOME="$home/.config/" \
    XDG_DATA_HOME="$home/.config//emacs/data" EMACS_XDG_TEST_PS_FILE="$home/ps" \
    "$migrate" --apply 2>&1)
status=$?
check 'a data root inside the configuration directory is refused however it is spelt' \
    test "$status" -ne 0 -a "${output#*must lie outside}" != "$output"

home=$scratch/usage
fixture "$home"
refuses 'rejects an unknown option' 'usage:' "$home" --force
refuses 'rejects an unknown preference' 'usage:' "$home" --apply --prefer=newest
refuses 'rollback needs a directory' 'usage:' "$home" --rollback
refuses 'rollback needs a log' 'no moves.tsv' "$home" --rollback "$home"

# ------------------------------------------------------------ environment
home=$scratch/xdg
fixture "$home"
output=$(env -u XDG_CONFIG_HOME HOME="$home" XDG_DATA_HOME=relative/share \
    XDG_CACHE_HOME= EMACS_XDG_TEST_PS_FILE="$home/ps" "$migrate" 2>&1)
check 'a relative XDG_DATA_HOME falls back to the default' \
    grep -q "^Data:  *$home/.local/share/emacs\$" <<<"$output"
check 'an empty XDG_CACHE_HOME falls back to the default' \
    grep -q "^Cache:  *$home/.cache/emacs\$" <<<"$output"
mkdir -p "$home/elsewhere"
output=$(env -u XDG_CONFIG_HOME -u XDG_CACHE_HOME HOME="$home" \
    XDG_DATA_HOME="$home/elsewhere" EMACS_XDG_TEST_PS_FILE="$home/ps" "$migrate" 2>&1)
check 'an absolute XDG_DATA_HOME is honoured' \
    grep -q "^Data:  *$home/elsewhere/emacs\$" <<<"$output"

printf '\n%d passed, %d failed\n' "$passed" "$failed"
[[ $failed -eq 0 ]]
```

- [ ] **Step 2: Run the tests to verify they fail**

Run: `chmod +x xdg/migrate-test.sh && xdg/migrate-test.sh 2>/dev/null | tail -1`

Expected: `29 passed, 107 failed`. The script under test does not exist yet; the checks that pass hold vacuously, such as a configuration file staying where it is.

- [ ] **Step 3: Write the mover**

Create `xdg/migrate.sh`:

```bash
#!/usr/bin/env bash
# migrate.sh --- move Emacs runtime state out of the configuration checkout
#
# Usage:
#   xdg/migrate.sh                  preview: print every action, change nothing
#   xdg/migrate.sh --apply          perform the moves
#   xdg/migrate.sh --rollback DIR   undo the moves recorded in DIR/moves.tsv
#
# When a destination already holds a different file, --apply refuses until
# you say which copy wins: add --prefer=source for the copy in the
# configuration directory, or --prefer=destination for the copy that is
# already there.  The other copy is kept in the run directory either way.
# A preview takes the same option and shows the result.
#
# Durable state goes to $XDG_DATA_HOME/emacs, caches go to
# $XDG_CACHE_HOME/emacs, and leftovers of packages that are gone go to an
# attic inside the run directory for a person to review.  Nothing is
# deleted, except a source file that is byte-identical to its destination
# and directories that the moves have emptied.
#
# Every rename is recorded in <data>/migration/<stamp>/moves.tsv, and a tar
# archive of everything that is not a cache is written there first.  The
# script is safe to run again: sources that are already gone are skipped.
#
# Quit every Emacs first.  A running session rewrites its history files at
# their old paths, on timers as well as on exit.

set -euo pipefail
umask 077

die() {
    printf 'migrate: %s\n' "$*" >&2
    exit 1
}

# An unset, empty or relative XDG value counts as unset, as it does in
# lisp/user-paths.el.  Repeated and trailing slashes are dropped, so that
# two spellings of one directory compare equal.
xdg_home() {
    local value=${!1:-}
    case $value in
    /*) ;;
    *) value=$2 ;;
    esac
    while [[ $value == *//* ]]; do
        value=${value//\/\//\/}
    done
    printf '%s\n' "${value%/}"
}

[[ -n ${HOME:-} ]] || die 'HOME is not set'

CONFIG_DIR=$(xdg_home XDG_CONFIG_HOME "$HOME/.config")/emacs
DATA_DIR=$(xdg_home XDG_DATA_HOME "$HOME/.local/share")/emacs
CACHE_DIR=$(xdg_home XDG_CACHE_HOME "$HOME/.cache")/emacs
STAMP=${EMACS_XDG_STAMP:-$(date +%Y%m%d-%H%M%S)}
RUN_DIR=$DATA_DIR/migration/$STAMP

# KIND|SOURCE|DESTINATION.  SOURCE is relative to the configuration
# directory.  DESTINATION is relative to the root that KIND names: `data',
# `cache', or `attic' (leftovers kept for review).  `prune' removes SOURCE
# if the moves above it left it empty.  Order matters: an entry that takes
# part of a directory must precede the entry that takes the rest.
manifest() {
    cat <<'EOF'
cache|url/cache|url
prune|url|-
cache|data/url/cache|url
cache|data/projectile.cache|projectile.cache
cache|data/.cache/lsp|lsp
prune|data/.cache|-
attic|data/mc-lists.elc|data/mc-lists.elc
data|data|.
attic|data-MacPort|data-MacPort
data|eshell/history|eshell/history
data|eshell/lastdir|eshell/lastdir
data|projects|projects
data|projectile-frecency.eld|projectile-frecency.eld
data|multisession|multisession
data|persist|persist
data|request|request
data|tree-sitter|tree-sitter
cache|eln-cache|eln-cache
cache|emojis|emojis
cache|var/pcache|pcache
attic|var/osm|var/osm
prune|var|-
attic|transient|transient
attic|auto-save-list|auto-save-list
attic|elpy|elpy
attic|gptel-agent|gptel-agent
attic|.lsp-session-v1|.lsp-session-v1
attic|.org-generic-id-locations|.org-generic-id-locations
attic|anvil-worker.log|anvil-worker.log
attic|%backup%~|%backup%~
prune|hash-store|-
prune|agent|-
EOF
}

# Files that hold tokens or cookies; they end up owner-only.
private_files() {
    cat <<EOF
$DATA_DIR/oauth2-auto.plist
$DATA_DIR/request/curl-cookie-jar
$DATA_DIR/persist/org-gcal--sync-tokens
$DATA_DIR/url/cookies
EOF
}

destination_of() {
    local root
    case $1 in
    data) root=$DATA_DIR ;;
    cache) root=$CACHE_DIR ;;
    attic) root=$RUN_DIR/attic ;;
    *) die "unknown manifest kind: $1" ;;
    esac
    if [[ $2 == . ]]; then
        printf '%s\n' "$root"
    else
        printf '%s\n' "$root/$2"
    fi
}

APPLY=0
PREFER=
CONFLICTS=0

# A preview must print exactly the commands that --apply runs, so it keeps
# a list of the renames and removals it has printed and answers every
# question about the file system as if they had happened.  A removal has
# an empty VIRT_TO.
VIRT_FROM=()
VIRT_TO=()
RESOLVED=

# Succeed if --apply creates directory $1 before it moves anything.
made_first() {
    case $1 in
    "$DATA_DIR" | "$CACHE_DIR" | "$DATA_DIR/migration" | "$RUN_DIR" | "$RUN_DIR/attic")
        return 0
        ;;
    esac
    return 1
}

# Set RESOLVED to the path that holds, on disk today, what a preview has
# put at $1.  Fail if the preview has moved or removed $1.
resolve() {
    local path=$1 index from to
    RESOLVED=$path
    [[ $APPLY == 0 ]] || return 0
    index=${#VIRT_FROM[@]}
    while ((index > 0)); do
        index=$((index - 1))
        from=${VIRT_FROM[index]}
        to=${VIRT_TO[index]}
        if [[ -n $to && ($path == "$to" || $path == "$to"/*) ]]; then
            path=$from${path#"$to"}
        elif [[ $path == "$from" || $path == "$from"/* ]]; then
            return 1
        fi
    done
    RESOLVED=$path
}

present() {
    resolve "$1" || return 1
    if [[ -e $RESOLVED || -L $RESOLVED ]]; then
        return 0
    fi
    [[ $APPLY == 0 ]] && made_first "$1"
}

is_directory() {
    resolve "$1" || return 1
    if [[ -d $RESOLVED && ! -L $RESOLVED ]]; then
        return 0
    fi
    [[ $APPLY == 0 && ! -e $RESOLVED && ! -L $RESOLVED ]] && made_first "$1"
}

is_file() {
    resolve "$1" || return 1
    [[ -f $RESOLVED && ! -L $RESOLVED ]]
}

same_bytes() {
    local first
    resolve "$1" || return 1
    first=$RESOLVED
    resolve "$2" || return 1
    cmp -s -- "$first" "$RESOLVED"
}

# Print the children of directory $1 under the names they have there.
children_of() {
    local child
    resolve "$1" || return 0
    [[ -d $RESOLVED ]] || return 0
    find "$RESOLVED" -mindepth 1 -maxdepth 1 -print | LC_ALL=C sort |
        while IFS= read -r child; do
            printf '%s\n' "$1/${child##*/}"
        done
}

has_children() {
    local child
    while IFS= read -r child; do
        if present "$child"; then
            return 0
        fi
    done < <(children_of "$1")
    return 1
}

record() {
    if [[ $APPLY == 1 ]]; then
        printf '%s\n' "$1" >>"$RUN_DIR/moves.tsv"
    fi
}

rename_to() {
    local src=$1 dest=$2
    printf '  mv     %s -> %s\n' "$src" "$dest"
    if [[ $APPLY == 1 ]]; then
        mkdir -p "$(dirname "$dest")"
        # Log first.  If the run stops between the two commands, the
        # rollback sees a move that never happened and skips it.
        record "$(printf 'MV\t%s\t%s' "$src" "$dest")"
        mv -- "$src" "$dest"
    else
        VIRT_FROM+=("$src")
        VIRT_TO+=("$dest")
    fi
}

remove_directory() {
    printf '  rmdir  %s\n' "$1"
    if [[ $APPLY == 1 ]]; then
        record "$(printf 'RMDIR\t%s' "$1")"
        rmdir -- "$1"
    else
        VIRT_FROM+=("$1")
        VIRT_TO+=("")
    fi
}

move_entry() {
    local src=$1 dest=$2 child saved
    present "$src" || return 0
    if ! present "$dest"; then
        rename_to "$src" "$dest"
        return 0
    fi
    # Both are directories: merge child by child, then drop the source.
    if is_directory "$src" && is_directory "$dest"; then
        while IFS= read -r child; do
            move_entry "$child" "$dest/${child##*/}"
        done < <(children_of "$src")
        if has_children "$src"; then
            printf '  stays  %s (not empty)\n' "$src"
        else
            remove_directory "$src"
        fi
        return 0
    fi
    # The same bytes on both sides: the source is redundant.
    if is_file "$src" && is_file "$dest" && same_bytes "$src" "$dest"; then
        printf '  same   %s == %s\n' "$src" "$dest"
        if [[ $APPLY == 1 ]]; then
            record "$(printf 'DUP\t%s\t%s' "$src" "$dest")"
            rm -f -- "$src"
        else
            VIRT_FROM+=("$src")
            VIRT_TO+=("")
        fi
        return 0
    fi
    # A real conflict: both sides hold something, and it differs.  Which
    # copy is right depends on how the destination came to exist, so a
    # person decides.  The copy that loses is kept beside the log.
    CONFLICTS=$((CONFLICTS + 1))
    case $PREFER in
    source)
        if inside "$RUN_DIR" "$dest"; then
            die "cannot set $dest aside: it holds the migration records"
        fi
        saved=$RUN_DIR/collisions$dest
        if present "$saved"; then
            die "two sources clash at $dest; settle that one by hand"
        fi
        printf '  keep   %s (it was at the destination)\n' "$saved"
        rename_to "$dest" "$saved"
        rename_to "$src" "$dest"
        ;;
    destination)
        saved=$RUN_DIR/collisions$src
        printf '  keep   %s (the destination stays as it is)\n' "$saved"
        rename_to "$src" "$saved"
        ;;
    *)
        printf '  clash  %s <> %s\n' "$src" "$dest"
        ;;
    esac
}

prune_entry() {
    local dir=$1
    is_directory "$dir" || return 0
    if has_children "$dir"; then
        printf '  stays  %s (not empty)\n' "$dir"
    else
        remove_directory "$dir"
    fi
}

# The tests name a file of process names in EMACS_XDG_TEST_PS_FILE.
emacs_processes() {
    if [[ -n ${EMACS_XDG_TEST_PS_FILE:-} ]]; then
        cat -- "$EMACS_XDG_TEST_PS_FILE"
    else
        ps -u "$(id -u)" -o comm=
    fi | awk '{ count = split($0, part, "/"); name = part[count]
                if (name ~ /^(Emacs|emacs|emacs-[0-9][0-9.]*|\.emacs-wrapped)$/)
                    print $0 }'
}

inside() {
    [[ $1 == "$2" || $1 == "$2"/* ]]
}

preflight() {
    local legacy running kind src odd
    [[ -d $CONFIG_DIR ]] || die "no configuration directory at $CONFIG_DIR"
    [[ -f $CONFIG_DIR/init.org ]] ||
        die "$CONFIG_DIR does not look like the Emacs checkout (no init.org)"
    for legacy in "$HOME/.emacs.d" "$HOME/.emacs" "$HOME/.emacs.el"; do
        if [[ -e $legacy || -L $legacy ]]; then
            die "$legacy exists and would outrank $CONFIG_DIR at startup; move it away first"
        fi
    done
    if inside "$DATA_DIR" "$CONFIG_DIR" || inside "$CACHE_DIR" "$CONFIG_DIR" ||
        inside "$CONFIG_DIR" "$DATA_DIR" || inside "$CONFIG_DIR" "$CACHE_DIR"; then
        die 'the data and cache roots must lie outside the configuration directory'
    fi
    while IFS='|' read -r kind src _; do
        if [[ -L $CONFIG_DIR/$src ]]; then
            die "$CONFIG_DIR/$src is a symbolic link; resolve it by hand first"
        fi
        # The log holds one tab-separated record per line.
        if [[ -d $CONFIG_DIR/$src ]]; then
            odd=$(find "$CONFIG_DIR/$src" \( -name $'*\t*' -o -name $'*\n*' \) -print | head -n 1)
            if [[ -n $odd ]]; then
                die "a name under $CONFIG_DIR/$src contains a tab or a newline; rename it first"
            fi
        fi
    done < <(manifest)
    running=$(emacs_processes) || die 'cannot list running processes'
    if [[ -n $running ]]; then
        printf 'migrate: Emacs is running:\n%s\n' "$running" >&2
        if [[ $APPLY == 1 ]]; then
            die 'quit every Emacs, then run this again'
        fi
        printf 'migrate: this preview can go stale; --apply will refuse until Emacs has quit\n' >&2
    fi
}

backup_sources() {
    local kind src dest
    local -a sources=()
    while IFS='|' read -r kind src dest; do
        if [[ $kind == data || $kind == attic ]] &&
            [[ -e $CONFIG_DIR/$src || -L $CONFIG_DIR/$src ]]; then
            sources+=("$src")
        fi
    done < <(manifest)
    if [[ ${#sources[@]} -gt 0 ]]; then
        printf 'Archiving %d sources to %s\n' "${#sources[@]}" "$RUN_DIR/pre-migration.tar"
        tar -cpf "$RUN_DIR/pre-migration.tar" -C "$CONFIG_DIR" -- "${sources[@]}"
    fi
}

leftovers() {
    local entry name
    while IFS= read -r entry; do
        present "$entry" || continue
        name=${entry##*/}
        case $name in
        .git | .gitignore | .gitmodules | .gitea | .github | .claude | .superpowers) continue ;;
        init.el | settings.el | nix-packages | nix-packages.el | certs | eshell) continue ;;
        esac
        if [[ -n $(git -C "$CONFIG_DIR" ls-files -- ":(literal)$name" 2>/dev/null | head -n 1) ]]; then
            continue
        fi
        printf '  %s\n' "$entry"
    done < <(children_of "$CONFIG_DIR")
}

walk_manifest() {
    local kind src dest
    while IFS='|' read -r kind src dest; do
        if [[ $kind == prune ]]; then
            prune_entry "$CONFIG_DIR/$src"
        else
            move_entry "$CONFIG_DIR/$src" "$(destination_of "$kind" "$dest")"
        fi
    done < <(manifest)
}

migrate() {
    local file
    preflight
    printf 'Configuration: %s\nData:          %s\nCache:         %s\n' \
        "$CONFIG_DIR" "$DATA_DIR" "$CACHE_DIR"
    if [[ $APPLY == 1 ]]; then
        # Rehearse first: a conflict must stop the run before anything moves.
        APPLY=0
        walk_manifest >/dev/null
        APPLY=1
        VIRT_FROM=()
        VIRT_TO=()
        if [[ $CONFLICTS -gt 0 && -z $PREFER ]]; then
            die "$CONFLICTS destinations already hold a different file; preview to see them, then add --prefer=source or --prefer=destination"
        fi
        CONFLICTS=0
        mkdir -p "$DATA_DIR" "$CACHE_DIR" "$RUN_DIR/attic"
        chmod 700 "$DATA_DIR" "$CACHE_DIR" "$RUN_DIR"
        : >>"$RUN_DIR/moves.tsv"
        backup_sources
        printf 'Moving; the log is %s\n' "$RUN_DIR/moves.tsv"
    else
        printf 'Preview only: nothing is changed.  Run with --apply to move.\n'
    fi
    walk_manifest
    if [[ $APPLY == 1 ]]; then
        while IFS= read -r file; do
            if [[ -f $file && ! -L $file ]]; then
                chmod 600 "$file"
            fi
        done < <(private_files)
        rmdir "$RUN_DIR/attic" 2>/dev/null || true
    fi
    if [[ $CONFLICTS -gt 0 && -z $PREFER ]]; then
        printf '%d destinations already hold a different file (the clash lines).\n' "$CONFLICTS"
        printf -- '--apply will need --prefer=source or --prefer=destination.\n'
    fi
    printf 'Left in %s, neither tracked nor expected:\n' "$CONFIG_DIR"
    leftovers
    printf 'Done.\n'
}

rollback() {
    local run=$1 log line op first second
    log=$run/moves.tsv
    [[ -f $log ]] || die "no moves.tsv in $run"
    APPLY=1
    preflight
    # Undo in reverse order.  awk reverses the file: tac is not on macOS.
    # A record whose move is already undone, or never happened, is skipped,
    # so a rollback that stopped can be run again.
    while IFS= read -r line; do
        IFS=$'\t' read -r op first second <<<"$line"
        case $op in
        MV)
            if [[ ! -e $second && ! -L $second ]]; then
                if [[ -e $first || -L $first ]]; then
                    continue
                fi
                die "cannot undo: both $first and $second are missing"
            fi
            if [[ -e $first || -L $first ]]; then
                die "cannot undo: $first exists; move it away and run the rollback again"
            fi
            mkdir -p "$(dirname "$first")"
            mv -- "$second" "$first"
            printf '  mv     %s -> %s\n' "$second" "$first"
            ;;
        RMDIR)
            mkdir -p "$first"
            printf '  mkdir  %s\n' "$first"
            ;;
        DUP)
            if [[ -e $first || -L $first ]]; then
                if [[ -f $first && ! -L $first ]] && cmp -s -- "$first" "$second"; then
                    continue
                fi
                die "cannot undo: $first exists; move it away and run the rollback again"
            fi
            mkdir -p "$(dirname "$first")"
            cp -p -- "$second" "$first"
            printf '  copy   %s -> %s\n' "$second" "$first"
            ;;
        *) die "unreadable line in $log: $line" ;;
        esac
    done < <(awk '{ line[NR] = $0 } END { for (i = NR; i > 0; i--) print line[i] }' "$log")
    mv -- "$log" "$log.rolled-back"
    printf 'Rolled back: every file is where it was.  File modes that the move\n'
    printf 'tightened stay tight.  The archive and the log remain in %s\n' "$run"
}

usage() {
    die 'usage: migrate.sh [--apply] [--prefer=source|--prefer=destination] | --rollback DIR'
}

if [[ ${1:-} == --rollback ]]; then
    [[ $# -eq 2 && -n $2 ]] || usage
    rollback "$2"
    exit 0
fi
for argument in "$@"; do
    case $argument in
    --apply) APPLY=1 ;;
    --prefer=source | --prefer=destination) PREFER=${argument#--prefer=} ;;
    *) usage ;;
    esac
done
migrate
```

- [ ] **Step 4: Run the tests to verify they pass**

Run: `chmod +x xdg/migrate.sh && xdg/migrate-test.sh | tail -1`

Expected: `136 passed, 0 failed`

- [ ] **Step 5: Run the tests under the system bash**

Putting `/bin` first makes `env bash` in the script find the system bash as well, together with the system's `mv`, `cp` and `rm`.

Run: `PATH="/bin:$PATH" /bin/bash xdg/migrate-test.sh 2>/dev/null | tail -1`

Expected: `136 passed, 0 failed`

- [ ] **Step 6: Lint both scripts**

Run: `shellcheck xdg/migrate.sh xdg/migrate-test.sh; echo "exit=$?"`

Expected: `exit=0` and no other output.

- [ ] **Step 7: Preview the move on the real tree**

A preview reads and prints; it changes nothing.

Run: `xdg/migrate.sh >/tmp/emacs-xdg-preview.txt 2>&1; echo "exit=$?"; grep -E '^  (clash|stays)' /tmp/emacs-xdg-preview.txt; head -3 /tmp/emacs-xdg-preview.txt; tail -8 /tmp/emacs-xdg-preview.txt`

Expected, with `<stamp>` a date and time:

```text
exit=0
migrate: Emacs is running:
/Applications/Emacs.app/Contents/MacOS/Emacs
migrate: this preview can go stale; --apply will refuse until Emacs has quit
  mv     /Users/johnw/.config/emacs/.lsp-session-v1 -> /Users/johnw/.local/share/emacs/migration/<stamp>/attic/.lsp-session-v1
  mv     /Users/johnw/.config/emacs/.org-generic-id-locations -> /Users/johnw/.local/share/emacs/migration/<stamp>/attic/.org-generic-id-locations
  mv     /Users/johnw/.config/emacs/anvil-worker.log -> /Users/johnw/.local/share/emacs/migration/<stamp>/attic/anvil-worker.log
  mv     /Users/johnw/.config/emacs/%backup%~ -> /Users/johnw/.local/share/emacs/migration/<stamp>/attic/%backup%~
  rmdir  /Users/johnw/.config/emacs/hash-store
  rmdir  /Users/johnw/.config/emacs/agent
Left in /Users/johnw/.config/emacs, neither tracked nor expected:
Done.
```

The three `migrate:` lines say that Emacs is running; that is expected here. The whole preview at the time of writing is in Appendix C. Three things must hold: `exit=0`, no `clash` or `stays` line, and nothing listed between `Left in` and `Done.`

- [ ] **Step 8: Remove the earlier script**

`migrate-emacs-xdg.sh` was written for a checkout at `~/src/dot-emacs` exposed as `~/.emacs.d`. It was never run. On the current layout it stops at its first check, and its embedded patches no longer apply.

Run: `git rm migrate-emacs-xdg.sh`

Expected: `rm 'migrate-emacs-xdg.sh'`

- [ ] **Step 9: Commit**

```bash
git add xdg/migrate.sh xdg/migrate-test.sh
git commit -m "xdg: Replace the stale migration script with a tested mover"
```

---

### Task 5: The litter report, ignore rules, make targets and README

**Files:**
- Create: `xdg/check-litter.sh` (executable)
- Test: `xdg/check-litter-test.sh` (executable)
- Modify: `.gitignore` (append after line 35)
- Modify: `Makefile:22` and `Makefile:67`
- Modify: `README.md:8`

**Interfaces:**
- Consumes: the test scripts of Tasks 1, 2 and 4, and `xdg/audit/run.sh` of Task 3, by path.
- Produces:
  - `xdg/check-litter.sh [CHECKOUT]`: prints one line per finding; exit 0 if there is none, 1 if there is one, 2 if CHECKOUT is not a git checkout. CHECKOUT defaults to the checkout the script is in.
  - `make check-litter`, `make test-xdg`, `make audit-xdg`.

- [ ] **Step 1: Write the failing tests**

Create `xdg/check-litter-test.sh`:

```bash
#!/usr/bin/env bash
# check-litter-test.sh --- exercise xdg/check-litter.sh on a throw-away checkout
#
# Usage: xdg/check-litter-test.sh

set -uo pipefail

here=$(cd "$(dirname "$0")" && pwd -P)
scratch=$(mktemp -d "${TMPDIR:-/tmp}/check-litter-test.XXXXXX")
if [[ -z $scratch || ! -d $scratch ]]; then
    printf 'check-litter-test: cannot create a scratch directory\n' >&2
    exit 2
fi
scratch=$(cd "$scratch" && pwd -P)

# Remove the scratch directory on exit, and nothing that is not one.
cleanup() {
    case $scratch in
    */check-litter-test.??????) rm -rf "$scratch" ;;
    esac
}
trap cleanup EXIT

passed=0
failed=0
home=$scratch/home
repo=$home/.config/emacs

# clean DESCRIPTION: the check must pass.
clean() {
    local output
    if output=$(HOME="$home" "$here/check-litter.sh" "$repo" 2>&1); then
        passed=$((passed + 1))
        printf 'ok    %s\n' "$1"
    else
        failed=$((failed + 1))
        printf 'FAIL  %s\n%s\n' "$1" "$output"
    fi
}

# litter DESCRIPTION EXPECTED: the check must fail and name EXPECTED.
litter() {
    local output
    if output=$(HOME="$home" "$here/check-litter.sh" "$repo" 2>&1); then
        failed=$((failed + 1))
        printf 'FAIL  %s (the check passed)\n' "$1"
    elif [[ $output == *"$2"* ]]; then
        passed=$((passed + 1))
        printf 'ok    %s\n' "$1"
    else
        failed=$((failed + 1))
        printf 'FAIL  %s\n%s\n' "$1" "$output"
    fi
}

put() {
    mkdir -p "$(dirname "$1")"
    printf 'x\n' >"$1"
}

# A checkout after migration: tracked files, plus the untracked
# configuration and build products that are allowed to be there.
mkdir -p "$repo"
git -C "$repo" init -q
cp "$here/../.gitignore" "$repo/.gitignore"
put "$repo/init.org"
put "$repo/lisp/a.el"
git -C "$repo" add .gitignore init.org lisp
put "$repo/init.el"
put "$repo/settings.el"
put "$repo/lisp/a.elc"
put "$repo/certs/ca.pem"
put "$repo/eshell/alias"
put "$repo/eshell/login"
put "$repo/eln-cache/31/x.eln"
put "$repo/.claude/settings.local.json"
ln -s /nix/store/none "$repo/nix-packages"
ln -s /nix/store/none.el "$repo/nix-packages.el"
clean 'a migrated checkout is clean'

put "$repo/notes.txt"
clean 'an untracked file that git already shows is not litter'
rm "$repo/notes.txt"

for path in data/history var/pcache/fonts url/cache/a transient/history.el \
    auto-save-list/.saves-1-host~ multisession/files/emoji/x persist/queues \
    request/curl-cookie-jar tree-sitter/libtree-sitter-c.dylib projects \
    projects.eld projectile-frecency.eld elpy/rpc-venv/pyvenv.cfg \
    emojis/set/1.png gptel-agent/sessions.db '%backup%~' .lsp-session-v1; do
    put "$repo/$path"
    litter "${path%%/*} is reported" "$repo/${path%%/*}"
    rm -rf "${repo:?}/${path%%/*}"
done

put "$repo/eshell/history"
litter 'eshell history is reported' "$repo/eshell/history"
rm "$repo/eshell/history"

mkdir "$repo/hash-store"
litter 'an empty directory is reported' "$repo/hash-store (empty directory)"
rmdir "$repo/hash-store"

mkdir "$home/.emacs.d"
litter 'a .emacs.d in the home directory is reported' "$home/.emacs.d exists"
rmdir "$home/.emacs.d"

put "$home/.emacs"
litter 'a .emacs in the home directory is reported' "$home/.emacs exists"
rm "$home/.emacs"

clean 'the checkout is clean again afterwards'

HOME="$home" "$here/check-litter.sh" "$scratch" >/dev/null 2>&1
if [[ $? -eq 2 ]]; then
    passed=$((passed + 1))
    printf 'ok    a directory that is not a checkout is an error\n'
else
    failed=$((failed + 1))
    printf 'FAIL  a directory that is not a checkout is an error\n'
fi

printf '\n%d passed, %d failed\n' "$passed" "$failed"
[[ $failed -eq 0 ]]
```

- [ ] **Step 2: Run the tests to verify they fail**

Run: `chmod +x xdg/check-litter-test.sh && xdg/check-litter-test.sh | tail -1`

Expected: `0 passed, 25 failed`

- [ ] **Step 3: Write the report**

Create `xdg/check-litter.sh`:

```bash
#!/usr/bin/env bash
# check-litter.sh --- report Emacs runtime state that is back in the checkout
#
# Usage: xdg/check-litter.sh [CHECKOUT]
#
# State and caches belong under $XDG_DATA_HOME/emacs and
# $XDG_CACHE_HOME/emacs; see lisp/user-paths.el.  .gitignore hides most of
# the places a package would litter, so that a stray cookie jar is never
# committed by accident.  This script is what makes such litter visible.
# It lists
#
#   - ~/.emacs.d, ~/.emacs and ~/.emacs.el, any of which makes Emacs
#     ignore this checkout altogether;
#   - every ignored path in the checkout that is not known configuration
#     or a build product;
#   - every empty directory at the top of the checkout.
#
# An Emacs started with -Q or -q reads no init file and writes to the
# built-in defaults, so an auto-save-list/, transient/ or url/ directory
# can appear here after such a run; delete it.  eln-cache/ appears for the
# same reason, cannot be prevented, and is not reported.
#
# The exit status is 0 when nothing is listed.

set -euo pipefail

checkout=${1:-$(cd "$(dirname "$0")/.." && pwd -P)}
status=0

if ! git -C "$checkout" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
    printf 'check-litter: %s is not a git checkout\n' "$checkout" >&2
    exit 2
fi

report() {
    printf '%s\n' "$1"
    status=1
}

for legacy in "$HOME/.emacs.d" "$HOME/.emacs" "$HOME/.emacs.el"; do
    if [[ -e $legacy || -L $legacy ]]; then
        report "$legacy exists: Emacs uses it instead of $checkout"
    fi
done

while IFS= read -r -d '' entry; do
    [[ $entry == '!! '* ]] || continue
    path=${entry#'!! '}
    case $path in
    init.el | settings.el | nix-packages | nix-packages.el) continue ;;
    certs/ | eln-cache/ | .claude/ | .superpowers/) continue ;;
    prompts/.prompt-deploy-manifest.json) continue ;;
    lisp/* | *.elc | .DS_Store | */.DS_Store) continue ;;
    eshell/)
        # alias, login and profile are configuration; history is not.
        while IFS= read -r name; do
            case $name in
            alias | login | profile) ;;
            *) report "$checkout/eshell/$name" ;;
            esac
        done < <(ls -A "$checkout/eshell")
        continue
        ;;
    esac
    report "$checkout/${path%/}"
done < <(git --no-optional-locks -C "$checkout" status --porcelain --ignored -z)

while IFS= read -r directory; do
    report "$directory (empty directory)"
done < <(find "$checkout" -mindepth 1 -maxdepth 1 -type d -empty | LC_ALL=C sort)

if [[ $status -eq 0 ]]; then
    printf 'No litter in %s\n' "$checkout"
fi
exit "$status"
```

- [ ] **Step 4: Add the safety-net ignore rules**

The test copies the checkout's `.gitignore`, so the rules come before the test can pass. Append to `.gitignore`:

```gitignore

# State and caches live under $XDG_DATA_HOME/emacs and $XDG_CACHE_HOME/emacs
# (lisp/user-paths.el).  The rules in this file for such paths are a safety
# net: an Emacs started with -Q still writes to its built-in defaults here,
# and `git add -A' must never pick that up.  `make check-litter' shows what
# these rules hide.
/auto-save-list/
/multisession/
/projects.eld
/tree-sitter/
/%backup%~
```

- [ ] **Step 5: Run the tests to verify they pass**

Run: `chmod +x xdg/check-litter.sh && xdg/check-litter-test.sh | tail -1 && shellcheck xdg/check-litter.sh xdg/check-litter-test.sh; echo "exit=$?"`

Expected:

```text
25 passed, 0 failed
exit=0
```

- [ ] **Step 6: Add the make targets**

In `Makefile`, replace line 22

```make
.PHONY: test build clean
```

with

```make
.PHONY: test build clean check-litter test-xdg audit-xdg
```

and replace the last line

```make
### Makefile ends here
```

with the following. The recipe lines begin with a tab.

```make
# State and caches live outside this checkout; see lisp/user-paths.el.

# Report runtime state that has come back into the checkout.
check-litter:
	@xdg/check-litter.sh

# Unit tests for the path library and the migration tools.
test-xdg:
	@$(EMACS_BATCH) -Q -l lisp/user-paths-test.el -f ert-run-tests-batch-and-exit
	@$(EMACS_BATCH) -Q -l xdg/apply-init-edits-test.el -f ert-run-tests-batch-and-exit
	@xdg/migrate-test.sh
	@xdg/check-litter-test.sh

# Load the whole init in a sealed copy and report paths that still point here.
audit-xdg:
	@xdg/audit/run.sh

### Makefile ends here
```

- [ ] **Step 7: Describe the layout in the README**

In `README.md`, after the paragraph that ends on line 8 with ``source before rebuilding `init.el`.``, add a blank line and this paragraph:

```markdown
Only configuration lives in this checkout. Durable state (histories, the
Org-roam database, tokens, tree-sitter grammars) lives under
`$XDG_DATA_HOME/emacs`, and caches live under `$XDG_CACHE_HOME/emacs`.
`lisp/user-paths.el` defines both roots and `early-init.el` loads it first.
Run `make check-litter` to see whether anything has crept back.
```

- [ ] **Step 8: Run every test through make**

Run: `make test-xdg 2>&1 | grep -E 'Ran |passed, '`

Expected:

```text
Ran 15 tests, 15 results as expected, 0 unexpected (...)
Ran 5 tests, 5 results as expected, 0 unexpected (...)
136 passed, 0 failed
25 passed, 0 failed
```

- [ ] **Step 9: Run the report on the worktree and on the real checkout**

Run: `make check-litter`

Expected: `No litter in <WT>`

Run: `xdg/check-litter.sh ~/.config/emacs; echo "exit=$?"`

Expected: `exit=1` and, above it, the state the cutover removes: 22 lines at the time of writing, from `/Users/johnw/.config/emacs/%backup%~` to `/Users/johnw/.config/emacs/hash-store (empty directory)`. Appendix C has the list. After Task 7 this command must print `No litter in /Users/johnw/.config/emacs`.

- [ ] **Step 10: Commit**

```bash
git add xdg/check-litter.sh xdg/check-litter-test.sh .gitignore Makefile README.md
git commit -m "xdg: Report runtime state that returns to the checkout"
```

---

### Task 6: Preflight on Clio

Nothing in this task writes outside the worktree, apart from one `git push` of the branch. It produces the evidence John needs to say go.

**Files:** none.

**Interfaces:**
- Consumes: `make test-xdg`, `make audit-xdg`, `xdg/migrate.sh`, `xdg/check-litter.sh`, `xdg-init-edits-batch --check`.
- Produces: a short report for John, and the branch `xdg-layout` on `origin`.

- [ ] **Step 1: Run the unit tests**

Run: `make test-xdg 2>&1 | grep -E 'Ran |passed, |FAILED'`

Expected: the four lines of Task 5 Step 8, and no `FAILED`.

- [ ] **Step 2: Run the audit against today's init.org**

Run: `make audit-xdg; echo "exit=$?"`

Expected: `PASS` and `exit=0`. If it reports an offender or a failed form, follow Task 3 Step 7, commit the fix, and run this step again.

- [ ] **Step 3: Check the edits against today's init.org**

Run: `emacs --batch -Q -l xdg/apply-init-edits.el -f xdg-init-edits-batch --check ~/org/init.org; echo "exit=$?"`

Expected: ten `pending` lines and `exit=0`. For an `ERROR`, follow Task 2 Step 5.

- [ ] **Step 4: Save the preview of the move**

Run: `xdg/migrate.sh >/tmp/emacs-xdg-preview-clio.txt 2>&1; echo "exit=$?"; grep -c '^  ' /tmp/emacs-xdg-preview-clio.txt; grep -E '^  (clash|stays)' /tmp/emacs-xdg-preview-clio.txt; sed -n '/^Left in /,/^Done\./p' /tmp/emacs-xdg-preview-clio.txt`

Expected: `exit=0`; a count near 45; no `clash` or `stays` line; and

```text
Left in /Users/johnw/.config/emacs, neither tracked nor expected:
Done.
```

A `clash` line is a different file that already exists at a destination. A name between `Left in` and `Done.` is something in the checkout that this plan does not know. Report either to John before going on.

- [ ] **Step 5: Check that the merge will not collide with work in progress**

Run:

```bash
comm -12 <(git -C ~/.config/emacs diff --name-only HEAD...xdg-layout | sort) \
         <(git -C ~/.config/emacs status --porcelain | cut -c4- | sort)
```

Expected: no output. A name here is a file that this branch changes and that also has uncommitted changes in the main checkout. Tell John.

- [ ] **Step 6: Push the branch**

Hera fetches it in Task 8.

Run: `git push -u origin xdg-layout`

Expected: `branch 'xdg-layout' set up to track 'origin/xdg-layout'.`

- [ ] **Step 7: Report to John and wait**

Give John the results of Steps 1 to 5, the file `/tmp/emacs-xdg-preview-clio.txt`, and these questions. Do not start Task 7 without his answers.

1. Do the departures in Appendix B stand? The ones that matter: tree-sitter grammars and transient files go to the data root; dead leftovers go to an attic, not to the data root.
2. In ChronoSync, does the task `Home` include `.local/share/emacs` and `.cache`? Should Hera and Clio go on sharing Emacs history files as they do today? Task 9 sets the rule.
3. Can Hera be reached now, and is Emacs closed there? Tasks 7 and 8 belong in one sitting.

---

### Task 7: Cutover on Clio

**John runs this, or is present while an agent does.** It takes about twenty minutes. Do Task 8 in the same sitting. From Step 7 until Task 8 is done, do not start Emacs on Hera: the new `init.org` arrives there at once, and Hera's state has not moved yet.

The order matters. The new init goes in first and is built once on purpose while the old state is still in place, so that it stops at its guard (Step 8). From then on an Emacs started by mistake stops at the same error, where the old init would have started on empty history and written new files.

**Files:**
- Modify: `~/org/init.org` (ten edits, by `xdg/apply-init-edits.el`)
- Modify: `~/.config/emacs/init.org`, `~/.config/emacs/init.el` (by `make`)
- Move: everything in the Task 4 table

**Interfaces:**
- Consumes: the branch `xdg-layout` with Tasks 1 to 5; John's go from Task 6.
- Produces: Clio running on the new layout; `master` holding the branch; the run directory under `~/.local/share/emacs/migration/`.

- [ ] **Step 1: Pause ChronoSync**

In ChronoSync on Clio, suspend the schedule of the task `Home` and confirm that no run is in progress. While it runs it would copy Hera's `data/` back, or delete Hera's while Emacs there still uses it.

- [ ] **Step 2: Quit Emacs on Clio and on Hera**

Quit both. Until Step 12, do not start Emacs on Clio, and stop anything else that runs `make` or `emacs` in this checkout, such as another agent's session.

Then on each host run the test the mover itself uses:

```bash
ps -u "$(id -u)" -o comm= |
  awk -F/ '$NF ~ /^(Emacs|emacs|emacs-[0-9][0-9.]*|\.emacs-wrapped)$/'
```

Expected: no output.

- [ ] **Step 3: Find the worktree**

Run: `WT=~/src/emacs-xdg-layout; ls "$WT/xdg/migrate.sh"`

Expected: the file name. Later steps use `$WT`; set it again in a new shell.

- [ ] **Step 4: Preview once more, now that Emacs has quit**

Run: `"$WT/xdg/migrate.sh" 2>&1 | grep -E '^  (clash|keep|stays)|^migrate:'; "$WT/xdg/migrate.sh" 2>&1 | sed -n '/^Left in /,/^Done\./p'`

Expected: no `clash`, `keep`, `stays` or `migrate:` line, then

```text
Left in /Users/johnw/.config/emacs, neither tracked nor expected:
Done.
```

- [ ] **Step 5: Keep a copy of init.org, and note where master is**

```bash
cp -p ~/org/init.org ~/.local/share/emacs/init.org.before-xdg
PRE=$(git -C ~/.config/emacs rev-parse HEAD); echo "$PRE"
```

Expected: a commit hash. Write it down: the rollback at the end of this task needs it, and the copy.

- [ ] **Step 6: Bring the branch into master**

```bash
comm -12 <(git -C ~/.config/emacs diff --name-only HEAD...xdg-layout | sort) \
         <(git -C ~/.config/emacs status --porcelain | cut -c4- | sort)
git -C ~/.config/emacs merge --ff-only xdg-layout
ls ~/.config/emacs/early-init.el ~/.config/emacs/xdg/migrate.sh
```

Expected: nothing from `comm`; then `Updating <old>..<new>`, `Fast-forward` and a list of files; then the two file names.

If `comm` prints a name, that file has uncommitted changes and the branch changes it too. Commit that change or set it aside before merging.

If git answers that the branches have diverged and it cannot fast-forward, `master` has moved since the branch was cut. In `$WT` run `git rebase master`, then `make test-xdg`, then repeat this step.

- [ ] **Step 7: Apply the ten edits to the canonical init.org**

Run: `emacs --batch -Q -l ~/.config/emacs/xdg/apply-init-edits.el -f xdg-init-edits-batch ~/org/init.org; echo "exit=$?"`

Expected: ten lines that begin with `applied`, and `exit=0`.

- [ ] **Step 8: Build init.el once; it must stop at the guard**

This copies the canonical file into the checkout, tangles `init.el`, and loads it in batch. The load must fail, because the state has not moved yet.

Run: `make -C ~/.config/emacs init.el 2>&1 | grep -E 'Emacs state is still in|\*\*\*'; ls -l ~/.config/emacs/init.el`

Expected: a line that contains `Emacs state is still in /Users/johnw/.config/emacs/data; quit Emacs and run /Users/johnw/.config/emacs/xdg/migrate.sh --apply`, a line from make that ends in `Error 255`, and a new `init.el`.

If make succeeds instead, there is no `~/.config/emacs/data` on this host. Stop and find out why before going on.

- [ ] **Step 9: Move the files**

Run: `~/.config/emacs/xdg/migrate.sh --apply 2>&1 | tee /tmp/emacs-xdg-apply-clio.txt | tail -4`

Expected:

```text
  rmdir  /Users/johnw/.config/emacs/hash-store
  rmdir  /Users/johnw/.config/emacs/agent
Left in /Users/johnw/.config/emacs, neither tracked nor expected:
Done.
```

Then: `RUN=$(sed -n 's/^Moving; the log is \(.*\)\/moves.tsv$/\1/p' /tmp/emacs-xdg-apply-clio.txt); echo "$RUN"; ls "$RUN"`

Expected: a directory `/Users/johnw/.local/share/emacs/migration/<stamp>` containing `attic`, `moves.tsv` and `pre-migration.tar`.

If the script instead refuses with `destinations already hold a different file`, Emacs was started between Step 6 and Step 8 and wrote new files under the new roots. The copies in the configuration directory are the real ones: run the command again with `--apply --prefer=source`.

- [ ] **Step 10: Confirm that the state arrived**

Run: `ls -d ~/.config/emacs/data 2>&1; ls ~/.local/share/emacs; ls ~/.cache/emacs`

Expected: `No such file or directory` for the first; then a listing that includes `auto-save-list backups eshell history migration org-id-locations org-roam.db projects recentf transient tree-sitter url`; then one that includes `eln-cache emojis pcache url`.

- [ ] **Step 11: Build init.el again; now it must succeed**

`-B` makes `make` rebuild a file it considers up to date.

Run: `make -C ~/.config/emacs -B init.el; echo "exit=$?"; ls -l ~/.config/emacs/init.el`

Expected: `exit=0`, and `init.el` with mode `-r--r--r--` and the current time.

- [ ] **Step 12: Start Emacs**

Start Emacs the usual way.

- [ ] **Step 13: Check the paths in the running session**

Run:

```bash
emacsclient -s /tmp/johnw-emacs/server --eval \
  '(list user-data-directory user-cache-directory (car native-comp-eln-load-path)
         savehist-file transient-values-file tramp-persistency-file-name
         project-list-file url-cache-directory)'
```

Expected:

```text
("/Users/johnw/.local/share/emacs/" "/Users/johnw/.cache/emacs/" "/Users/johnw/.cache/emacs/eln-cache/" "/Users/johnw/.local/share/emacs/history" "/Users/johnw/.local/share/emacs/transient/values.el" "/Users/johnw/.local/share/emacs/tramp" "/Users/johnw/.local/share/emacs/projects" "/Users/johnw/.cache/emacs/url/")
```

- [ ] **Step 14: Scan the running session for stray paths**

Run:

```bash
emacsclient -s /tmp/johnw-emacs/server --eval \
  '(progn (load "~/.config/emacs/xdg/audit/audit.el" nil t)
          (xdg-audit-offenders user-emacs-directory))'
```

Expected: `nil`. A variable that only records which buffers or projects the session has visited is not an offender. For anything else, apply the three rules of Task 3 Step 7, commit, and restart Emacs.

- [ ] **Step 15: Check the checkout**

Run: `make -C ~/.config/emacs check-litter`

Expected: `No litter in /Users/johnw/.config/emacs`

- [ ] **Step 16: Use it**

John checks, in Emacs: `M-x` offers earlier commands; the recent-files list is populated; `org-roam-node-find` finds notes; `M-p` in a new eshell recalls earlier commands; a magit transient opens. Then:

Run: `emacsclient -s /tmp/johnw-emacs/server --eval "(treesit-language-available-p 'python)"`

Expected: `t`

One change to expect: transient now reads the values it saved. `~/.local/share/emacs/transient/values.el` dates from August 2025 and has not been read since, so a transient command may show a default that was saved then.

- [ ] **Step 17: Commit and push**

The commit of `init.org` carries whatever else changed in the canonical file since it was last copied here, as every such commit does.

`git status` now shows `multisession/files/emoji/emoji--recent.value` as deleted, because the mover took it to the data root. Leave that uncommitted until Task 9, and do not run `changes` on this checkout before Task 8 is done. Hera must pull a `master` that still tracks the file, or the pull would delete Hera's copy before Hera's mover has moved it.

```bash
git -C ~/.config/emacs add init.org
git -C ~/.config/emacs commit -m "init: Keep state and caches out of the configuration directory"
git -C ~/.config/emacs push
```

Expected: the push reports `master -> master`.

**Rollback, if a step from 6 to 16 fails and cannot be fixed on the spot.** Do it before Step 17. If Step 17 has already pushed, do not reset `master`; fix forward.

```bash
# Quit Emacs first.  Set WT as in Step 3, and PRE to the hash Step 5 printed.
for log in $(ls -d ~/.local/share/emacs/migration/*/moves.tsv 2>/dev/null | sort -r); do
  "$WT/xdg/migrate.sh" --rollback "$(dirname "$log")"
done
cp ~/.local/share/emacs/init.org.before-xdg ~/org/init.org
git -C ~/.config/emacs reset --keep "$PRE"
make -C ~/.config/emacs -B init.el
```

The loop undoes every run of the mover, newest first, and does nothing if Step 9 never ran. Each run puts its files back where they were. If one stops with `cannot undo: ... exists`, a file has come back at its old path: move that file away and run the loop again. The copy is made without `-p` on purpose: the restored `init.org` must be newer than the checkout's copy, or `make` will not take it. `reset --keep` moves `master` back and leaves uncommitted work alone. The order matters: the mover has to restore the tracked file under `multisession/` before git looks at it. File modes that the move tightened stay tight, and directories that the new init created under the two roots stay; neither does harm.

This sequence was rehearsed in a scratch home with the real mover and the real Makefile. It ended with the tree and `git status` exactly as they began.

---

### Task 8: Cutover on Hera

**John runs this**, in the same sitting as Task 7, with ChronoSync still paused and Emacs closed on Hera. All commands run on Hera. Nothing about Hera could be checked while this plan was written, so each step says what to do when Hera differs.

Hera can only go forward. The edited `init.org` is shared with Clio through Syncthing, so Hera cannot return to the old init by itself. If a step here fails, fix it here; the files the mover moved can still be put back with `xdg/migrate.sh --rollback`.

**Files:** the same as Task 7, on Hera. `~/org/init.org` is already edited: Syncthing delivered it.

**Interfaces:**
- Consumes: `master` as pushed in Task 7 Step 17.
- Produces: Hera running on the new layout.

- [ ] **Step 1: Check for a legacy init directory**

Run: `ls -d ~/.emacs.d ~/.emacs ~/.emacs.el 2>&1`

Expected: three lines ending in `No such file or directory`. If one exists, stop: Emacs on Hera uses it instead of `~/.config/emacs`. Find out why it is there before moving anything.

- [ ] **Step 2: Bring the checkout up to date**

```bash
cd ~/.config/emacs
git status --short
git checkout -- init.org
git pull --ff-only --no-rebase --no-autostash
git log --oneline -1
git status --short | grep '^UU'
```

Expected: the commit of Task 7 Step 17 from `git log`, and nothing from the last command.

`init.org` in the checkout is a copy that `make` writes, so discarding its local state loses nothing; left alone, it would block the pull. The two options make the pull refuse when another local change is in the way. Without them John's git configuration stashes local changes, pulls, and reapplies them, which can leave a conflict behind while reporting success.

If the pull refuses, it names the files in the way. Do not force it. This checkout may hold a copy of Clio's working tree that ChronoSync made, including another agent's unfinished edits. The requirement is only that `~/.config/emacs` on Hera is at Task 7's commit, with `xdg/` and `early-init.el` present.

- [ ] **Step 3: Confirm that the edited init.org has arrived**

Run: `emacs --batch -Q -l xdg/apply-init-edits.el -f xdg-init-edits-batch --check ~/org/init.org; echo "exit=$?"`

Expected: ten lines that begin with `done`, and `exit=0`. Lines that say `pending` mean Syncthing has not delivered the file yet. Wait for it. Do not apply the edits here: two hosts editing the same file make a Syncthing conflict.

- [ ] **Step 4: Build init.el once; it must stop at the guard**

Run: `make init.el 2>&1 | grep -E 'Emacs state is still in|\*\*\*'`

Expected: the same two lines as in Task 7 Step 8, with Hera's paths.

If make succeeds, Hera has no `~/.config/emacs/data`. Either it never had one or ChronoSync has removed it. Go on: the preview in the next step shows what is left to move.

- [ ] **Step 5: Preview**

Run: `xdg/migrate.sh 2>&1 | tee /tmp/emacs-xdg-preview-hera.txt | grep -E '^  (clash|stays)|^migrate:'; sed -n '/^Left in /,/^Done\./p' /tmp/emacs-xdg-preview-hera.txt`

Expected: Hera's list differs from Clio's in its details. Read each name between `Left in` and `Done.` before going on.

A `clash` line means a destination already holds a different file. ChronoSync was paused before Clio's files moved, so this should not happen. If it does, either the pause did not hold and Clio's moved state has reached Hera, or the new init ran on Hera early. Stop and check ChronoSync before going on. Then John chooses, for all of them at once: `--prefer=source` puts Hera's own file in place, and `--prefer=destination` keeps the one that is there. The other copy is kept under `migration/<stamp>/collisions/` either way. Hera's own files are what Emacs on Hera last saw, so `--prefer=source` changes least.

- [ ] **Step 6: Move the files**

Run: `xdg/migrate.sh --apply 2>&1 | tee /tmp/emacs-xdg-apply-hera.txt | tail -3`, adding the preference chosen in Step 5 if there was a `clash` line.

Expected: the last line is `Done.`

- [ ] **Step 7: Build again and start**

Run: `make -B init.el; echo "exit=$?"`

Expected: `exit=0`. Then start Emacs.

- [ ] **Step 8: Verify**

Run Task 7 Steps 13, 14, 15 and 16 on Hera. The expected output is the same.

---

### Task 9: Resume sync and confirm the backup

**John runs this.**

**Files:**
- Untrack: `multisession/files/emoji/emoji--recent.value`

**Interfaces:**
- Consumes: both hosts on the new layout.
- Produces: ChronoSync running with rules that fit the layout; evidence that the nightly backup holds the moved state; `master` no longer tracking the runtime file.

- [ ] **Step 1: Record that the runtime file is no longer tracked**

Both movers have taken `multisession/` to the data root, so the file can leave the index. On Clio:

```bash
git -C ~/.config/emacs rm -q --cached multisession/files/emoji/emoji--recent.value
git -C ~/.config/emacs commit -m "xdg: Stop tracking the emoji picker's state"
git -C ~/.config/emacs push
```

Then on Hera: `git -C ~/.config/emacs pull --ff-only --no-rebase --no-autostash`

Expected: the push reports `master -> master`, and the pull fast-forwards.

- [ ] **Step 2: Set the ChronoSync rules**

In the task `Home`, decide these three, and note the decision in the task's description:

1. `.cache`: exclude. Caches are rebuilt on each host.
2. `.local/share/emacs`: include it to keep sharing history, recent files and org-id locations between the hosts as today, conflicts and all. Exclude it to give each host its own. Either way, exclude `.local/share/emacs/backups` and `.local/share/emacs/migration`.
3. `.config/emacs`: unchanged.

Note that Hera's home reaches the backup only through this sync. If `.local/share/emacs` is excluded, Hera's Emacs state is backed up nowhere.

- [ ] **Step 3: Resume the schedule and watch the first run**

Expected: no deletion under `.local/share/emacs` on either host, and no `data` directory reappearing under `.config/emacs`.

If `~/.config/emacs/data` comes back on a host, Emacs refuses to start there with `Emacs state is still in ...`. What came back is the stale copy; the files under the data root are the ones in use. Quit Emacs and run `xdg/migrate.sh --apply --prefer=destination`. It keeps every file that is in use, moves across only what the data root lacks, and puts the stale copies under `migration/<stamp>/collisions/`. Never use `--prefer=source` for this. Then find the ChronoSync rule that brought the directory back.

- [ ] **Step 4: Check the checkout on both hosts**

Run on each: `make -C ~/.config/emacs check-litter`

Expected: `No litter in ...`

- [ ] **Step 5: After the 03:00 backup, confirm the state is on tank**

Run on Clio, the morning after: `ssh vulcan 'ls -l /tank/Home/.local/share/emacs/history /tank/Home/.local/share/emacs/org-id-locations; ls -d /tank/Home/.config/emacs/data /tank/Home/.cache/emacs 2>&1'`

Expected: the first two files exist with yesterday's or today's date, and the last two paths do not exist.

If the files are missing, first check that the job ran: it is the LaunchAgent `org.nixos.push-tank`. The filters are unlikely to be the cause. The `tank` store in `~/.config/pushme/filesets/Home.yaml` has its own filter list, and nothing in it excludes `.local/share/emacs`. The rule on line 197 that does belongs to the list shared between hosts, which does not apply to `tank`.

---

### Task 10: Remove the one-time tools

Do this two weeks after Task 9, once John has looked through the attic and the collisions on both hosts. Run it on Clio; Hera receives the result by `git pull`. The mover, its tests, the guard and the litter report stay: they are what puts a host right if state ever comes back.

**Files:**
- Delete: `xdg/apply-init-edits.el`, `xdg/apply-init-edits-test.el`, `xdg/audit/`
- Modify: `Makefile` (the lines added in Task 5 Step 6)
- Delete on each host, by John: `~/.local/share/emacs/migration/`, `~/.local/share/emacs/init.org.before-xdg`

**Interfaces:**
- Consumes: both hosts migrated, `make check-litter` clean on both.
- Produces: a checkout with only the permanent files of the File Structure table.

- [ ] **Step 1: Remove the editor and the audit**

Run: `git -C ~/.config/emacs rm -r xdg/apply-init-edits.el xdg/apply-init-edits-test.el xdg/audit`

Expected: six `rm '...'` lines.

- [ ] **Step 2: Trim the make targets**

In `Makefile`, replace

```make
.PHONY: test build clean check-litter test-xdg audit-xdg
```

with

```make
.PHONY: test build clean check-litter test-xdg
```

and replace

```make
# Unit tests for the path library and the migration tools.
test-xdg:
	@$(EMACS_BATCH) -Q -l lisp/user-paths-test.el -f ert-run-tests-batch-and-exit
	@$(EMACS_BATCH) -Q -l xdg/apply-init-edits-test.el -f ert-run-tests-batch-and-exit
	@xdg/migrate-test.sh
	@xdg/check-litter-test.sh

# Load the whole init in a sealed copy and report paths that still point here.
audit-xdg:
	@xdg/audit/run.sh
```

with

```make
# Unit tests for the path library, the mover and the litter report.
test-xdg:
	@$(EMACS_BATCH) -Q -l lisp/user-paths-test.el -f ert-run-tests-batch-and-exit
	@xdg/migrate-test.sh
	@xdg/check-litter-test.sh
```

- [ ] **Step 3: Run the remaining tests**

Run: `make -C ~/.config/emacs test-xdg 2>&1 | grep -E 'Ran |passed, '`

Expected:

```text
Ran 15 tests, 15 results as expected, 0 unexpected (...)
136 passed, 0 failed
25 passed, 0 failed
```

- [ ] **Step 4: Commit and push**

```bash
git -C ~/.config/emacs add Makefile
git -C ~/.config/emacs commit -m "xdg: Remove the one-time editor and audit"
git -C ~/.config/emacs push
```

- [ ] **Step 5: Remove the worktree and the branch**

```bash
git -C ~/.config/emacs push origin --delete xdg-layout
git -C ~/.config/emacs worktree remove ~/src/emacs-xdg-layout
git -C ~/.config/emacs branch -d xdg-layout
```

Expected: the first command reports `- [deleted]         xdg-layout`, and the last `Deleted branch xdg-layout`. The remote branch goes first: if the branch was rebased in Task 7, git would otherwise refuse to delete it for not matching its upstream.

- [ ] **Step 6: John deletes the migration records, on each host**

This is the only step in the plan that deletes state, and it is John's to run. Look first: `ls -R ~/.local/share/emacs/migration | head -60`. The attic holds, among other things, `gptel-agent/sessions.db` with its WAL file, and `%backup%~`, an emergency backup of `/etc/hosts` from September 2026.

```bash
rm -r ~/.local/share/emacs/migration ~/.local/share/emacs/init.org.before-xdg
```

- [ ] **Step 7: Optionally drop stale native code**

Three of the four directories under `~/.cache/emacs/eln-cache/` belong to older builds. In Emacs: `M-x native-compile-prune-cache`.

---

## Follow-ups

None of these is needed for the reorganization. Each was found on the way and is worth its own decision.

1. **`make init.el` may erase bm bookmarks.** In a sealed copy, the batch load of the init wrote an empty `bm-repository` over a populated one: bm's save runs on exit, and its load never runs in batch. The real `bm-repository` is empty today. Whether bookmarks were lost this way is not known. A build that only tangles, or that loads with the data root pointed at a scratch directory, would stop it.
2. **`~/src/scripts/syncup` is broken.** Line 24 calls `load-env-emacs$EMACSVER`, which is no longer on `PATH`, so the script stops there.
3. **`~/src/scripts/changes-all` commits the whole checkout** from `~/.config/emacs/lisp`, which is not a repository of its own.
4. **Five MCP entries in `~/.config/claude/personal/.claude.json`** name `/Users/johnw/.emacs.d/emacs-mcp-stdio.sh`, which does not exist. The tracked `emacs-mcp-stdio.sh` is stale as well.
5. **`~/.config/forge` holds 482 MB** of SQLite for a package whose block is disabled.
6. **Small defects in `init.org`:** the yasnippet `:mode` pattern still names `.emacs.d`; `load-path` has an entry for a `use-package` directory that does not exist; `tramp-remote-path` gains `<cwd>/bin` when `PROFILE_DIR` is unset; `eshell-z-exclude-dirs` names `~/.emacs.d/elpa`.
7. **`eshell/alias`, `eshell/login` and `certs/vulcan-ca-bundle.pem` are configuration that is not versioned.** Tracking them needs a look at their contents first. The certificate has the same fingerprint as one the Nix configuration already installs.
8. **The gptel package built by Nix** has `/homeless-shelter/.cache` compiled in as the default for `gptel-crowdsourced-prompts-file`. The table in `lisp/user-paths.el` overrides it; the build is still wrong.
9. **The tree-sitter grammars could come from Nix**, into the bundle's `lib/` directory, which `nix-packages.el` already adds to the load path and which is empty today.
10. **`~/.config/pushme/filesets/Home.yaml` line 197** excludes `/.local/share/emacs/` in the filters shared between hosts. It has no effect while host sync is off, and would block the moved state if it were turned on again.

---

## Appendix A: The spec

The audit report as John supplied it, verbatim.

````markdown
Report — `~/.config/emacs` audit vs `~/.local/share/emacs` (currently only `backups/` = 201M correct):

Your `init.el` already does partial XDG: `user-data` → `~/.config/emacs/data` + `backup-directory-alist`/`tramp-auto-save-directory` → `~/.local/share/emacs/backups`. Rest still lives under `~/.config/emacs` — violates XDG.

No changes made. Recommendations:

**STAY in `~/.config/emacs` (config, versioned):**
- `init.el`, `init.org`, `settings.el`, `abbrevs.el`, `nix-packages.el` (symlink)
- `lisp/*.el` + `.elc` (39M — source), `lisp/badi-calendar`, `dired-filetags`, `llm-setup`, `org-agents`
- `snippets/`, `prompts/`, `doc/`, `emojis/`, `certs/vulcan-ca-bundle.pem`, `sits/`? specs/
- `.gitignore`, `.gitmodules`, `.gitea/`, `.github/FUNDING.yml`

**MOVE to `~/.local/share/emacs` (XDG_DATA_HOME — persistent state/data, host-writable, not config):**
- `data/` (44M total): `history` (308K), `org-roam.db` (43M!), `org-id-locations` (855K), `places`, `recentf`, `mc-lists.el`, `network-security.data`, `oauth2-auto.plist`, `persistent-scratch`, `projectile-bookmarks.eld`, `prescient-save.el`, `workgroups`, `tramp`, `url/cookies`
- `data-MacPort/` (same shape — merge or keep `alt` suffix logic, but move under share)
- `var/` (21M): `var/osm/default/*.png` (tile cache), `var/pcache/`
- `persist/`, `multisession/files/`, `eshell/history+lastdir` (52K)
- `gptel-agent/sessions.db*` (112K), `bookmarks` already external (`~/doc/bookmarks` OK), `bookmark` backups
- `auto-save-list/` (both `auto-save-list/` and `data/auto-save-list/` — currently 30+ `.saves-*` files)
- dotfiles at top-level: `.lsp-session-v1`, `.org-generic-id-locations`

**MOVE to `~/.cache/emacs` (XDG_CACHE_HOME — regenerable, deletable):**
- `eln-cache/` (15M, 4 versions) — native-compilation cache
- `tree-sitter/*.dylib` (34M) — compiled grammars
- `url/cache/` (716K, `https://...` tree) + `data/url/cache` duplicate
- `request/curl-cookie-jar`, `cache/` (if any), `transient/history.el` (3B stub vs `data/transient/`)

**MIXED / FIX:**
- `transient/` split: merge into `~/.cache/emacs/transient` (history is cache-like, `values.el` is state — either share or cache, not config)
- `url/` vs `data/url/` vs `url/cache` triple: consolidate to `~/.cache/emacs/url/` and `~/.local/share/emacs/url/cookies`
- `.#*` lockfiles, `%backup%~` (already duplicated in share/backups), `anvil-worker.log`, `auto-save-list` stray files → `state` or `cache`, not config
- `elpy/rpc-venv` (24M, python env) → `~/.cache/emacs/elpy` or `~/.local/share/emacs/elpy` (not config)

**Why:** `~/.config` should be small, versioned, host-portable. Your `data/org-roam.db` + `var/osm` + `eln-cache` + `tree-sitter` = ~113M trash in config that breaks `git status`, backups, and Nix `home-manager` purity. XDG split fixes `dot-emacs` repo weight and matches `backup-directory-alist` you already set.

Want plan to wire `user-data-directory` → `$XDG_DATA_HOME/emacs`, `cache` → `$XDG_CACHE_HOME/emacs`, plus symlinks for transition?
````

---

## Appendix B: Where this plan departs from the report

| Item | The report says | This plan does | Why |
|---|---|---|---|
| `tree-sitter/` | cache | data, `tree-sitter/` | These 30 grammars are the only copy: the Nix bundle supplies none and `init.org` records no sources. Rebuilding needs git, a C compiler and the network. `~/.cache` is excluded from the backups. |
| `emojis/` | stay, as versioned configuration | cache | It is git-ignored, and it is the image set emojify downloaded. |
| `var/` | data | `var/pcache/` to cache; `var/osm/` to the attic | pcache is a font cache that is rebuilt. The osm package is not installed; its tiles date from 2024. |
| `request/curl-cookie-jar` | cache | data, mode 600 | Cookies are credentials. |
| `transient/` | cache, merged into one directory | data: history, values and levels together | Values and levels are choices a person saved. The report itself allows "either share or cache". |
| `url/cache` and "`data/url/cache` duplicate" | consolidate both | the stray top-level `url/cache/` goes to cache | There is no `data/url/cache`. `data/url/` holds only `cookies`. |
| `data-MacPort/` | "same shape" as `data/`; merge, or keep the alt logic | attic; the alternate instance, if ever revived, uses `emacs-alt` | It holds one auto-save index from May 2025. Nothing has set `emacsERC` since 2024. |
| `.lsp-session-v1`, `.org-generic-id-locations`, `gptel-agent/` | data | attic, which is under the data root | Their packages are disabled or gone. |
| `elpy/rpc-venv` | cache or data | attic; elpy builds its next one under the cache root | The virtualenv is broken: its Python has left the Nix store and its scripts name `~/.emacs.d`. A virtualenv cannot be moved in any case. |
| `auto-save-list/` | both directories to data, and elsewhere "state or cache" | `data/auto-save-list/` to data; the stray top-level directory to the attic | It is the index `recover-session` needs after a crash, and the state root is excluded from every backup. The top-level directory holds one empty file, written by an Emacs that read no init. |
| `.#*` lockfiles | state or cache | nothing | None exist: `create-lockfiles` is nil. |
| `%backup%~` | "already duplicated in share/backups" | attic | It is not a duplicate. It is a 578-byte emergency backup of `/etc/hosts`. |
| `anvil-worker.log` | state or cache | attic | Anvil has been removed; the log is from July 2026. |
| `bookmarks`, "bookmark backups" | already external | nothing | `~/doc/bookmarks` is in a Syncthing folder and stays. Its backups are already under `~/.local/share/emacs/backups`. |
| `eln-cache/` | cache | cache, moved whole | Agreed. Moving keeps the 71 native files the running Emacs uses; `native-comp-jit-compilation` is nil, so they would not be rebuilt. |
| symlinks for the transition | offered | none | Nothing outside Emacs reads the old paths. A link named `data` is not matched by the rule `/data*/`, so `changes` would commit it. |
| `sits/`, `cache/` | listed with a question mark | nothing | Neither exists. |
| `certs/`, `init.el`, `settings.el`, `nix-packages.el` | versioned | unchanged | They stay, but they are git-ignored, not versioned. |
| the reason given: "breaks git status", repository weight, Home Manager purity | | | All of this state is already ignored, none of it is in the repository, and Home Manager owns only two symlinks. The real costs are backup churn and sync conflicts between the hosts. |

Not in the report, and handled here: `projects` and `projectile-frecency.eld`; the split of `eshell/` into configuration and state; `transient-levels-file`; `pcache-directory`, `persist--directory-location`, `multisession-directory` and `request-storage-directory`; the two defaults that point at `~/.emacs.d`; the load-order defects in the tramp and transient settings; the tracked runtime file under `multisession/`; and Hera.

---

## Appendix C: What was run while writing this plan

Every file in this plan was built and run before it was written down. The tests and the audit ran against throw-away copies, with Emacs under `sandbox-exec` and writes to the home directory denied.

| Check | Result |
|---|---|
| `lisp/user-paths-test.el` | 15 of 15 pass |
| `xdg/apply-init-edits-test.el` | 5 of 5 pass |
| `--check` against `~/org/init.org` | all ten edits match exactly once |
| `xdg/migrate-test.sh` | 136 of 136 pass, under bash 5.3 and with `/bin/bash` 3.2 and the system tools first on `PATH` |
| `xdg/check-litter-test.sh` | 25 of 25 pass |
| `shellcheck` on all five scripts | clean |
| `xdg/audit/run.sh` on the full init, from a checkout that holds only this plan's files | 580 forms, 0 failed; 1,674 features; 0 offenders; nothing written inside the configuration directory |
| the same with `XDG_AUDIT_SELFTEST=1` | fails on the planted variable and the planted file, as it must |
| the sandbox profile | refuses a write to the home directory, to `~/.config/emacs` and to `/tmp/johnw-emacs`, and refuses the network |
| every variable in `user-paths-table`, checked against the installed sources | each exists under that name and takes a single path; the one constant, `web-cookie-jar-file`, is handled separately |
| Tasks 1 to 6, executed from this document's text in a clone, by an agent that had seen nothing else | every extracted file was byte-identical to the tested one and every expected output matched; that was before the last revision, after which all files were extracted and run once more |
| Task 7 forward and back, rehearsed in a scratch home with the real mover, the real Makefile and a stand-in for Emacs | the first build stops at the guard, the second succeeds after the move, and the rollback restores the tree and `git status` exactly |

Not run: the cutover itself, a real GUI start on the new layout, and anything on Hera.

Five reviewers then attacked the plan, and a second agent had to reproduce each finding before it counted. Forty-seven held up. The serious ones were in the rollback, in the advice for a `data/` directory that reappears, in the pull on Hera, and in the mover's own rollback; this text has them fixed. One reviewer's hand-made fixture set `HOME` but left `XDG_CACHE_HOME` pointing at the real `~/.cache`, so the mover it ran set `~/.cache/emacs` to mode 700. The mode was put back to 755, and nothing else was touched. Anyone who runs the mover against a fake home by hand must unset the three XDG variables, as `xdg/migrate-test.sh` does.

The preview of the move on Clio on 2026-11-17:

```text
migrate: Emacs is running:
/Applications/Emacs.app/Contents/MacOS/Emacs
migrate: this preview can go stale; --apply will refuse until Emacs has quit
Configuration: /Users/johnw/.config/emacs
Data:          /Users/johnw/.local/share/emacs
Cache:         /Users/johnw/.cache/emacs
Preview only: nothing is changed.  Run with --apply to move.
  mv     /Users/johnw/.config/emacs/url/cache -> /Users/johnw/.cache/emacs/url
  rmdir  /Users/johnw/.config/emacs/url
  mv     /Users/johnw/.config/emacs/data/mc-lists.elc -> /Users/johnw/.local/share/emacs/migration/20261117-112233/attic/data/mc-lists.elc
  mv     /Users/johnw/.config/emacs/data/auto-save-list -> /Users/johnw/.local/share/emacs/auto-save-list
  mv     /Users/johnw/.config/emacs/data/bm-repository -> /Users/johnw/.local/share/emacs/bm-repository
  mv     /Users/johnw/.config/emacs/data/history -> /Users/johnw/.local/share/emacs/history
  mv     /Users/johnw/.config/emacs/data/mc-lists.el -> /Users/johnw/.local/share/emacs/mc-lists.el
  mv     /Users/johnw/.config/emacs/data/network-security.data -> /Users/johnw/.local/share/emacs/network-security.data
  mv     /Users/johnw/.config/emacs/data/oauth2-auto.plist -> /Users/johnw/.local/share/emacs/oauth2-auto.plist
  mv     /Users/johnw/.config/emacs/data/org-id-locations -> /Users/johnw/.local/share/emacs/org-id-locations
  mv     /Users/johnw/.config/emacs/data/org-roam.db -> /Users/johnw/.local/share/emacs/org-roam.db
  mv     /Users/johnw/.config/emacs/data/persistent-scratch -> /Users/johnw/.local/share/emacs/persistent-scratch
  mv     /Users/johnw/.config/emacs/data/places -> /Users/johnw/.local/share/emacs/places
  mv     /Users/johnw/.config/emacs/data/prescient-save.el -> /Users/johnw/.local/share/emacs/prescient-save.el
  mv     /Users/johnw/.config/emacs/data/projectile-bookmarks.eld -> /Users/johnw/.local/share/emacs/projectile-bookmarks.eld
  mv     /Users/johnw/.config/emacs/data/recentf -> /Users/johnw/.local/share/emacs/recentf
  mv     /Users/johnw/.config/emacs/data/tramp -> /Users/johnw/.local/share/emacs/tramp
  mv     /Users/johnw/.config/emacs/data/transient -> /Users/johnw/.local/share/emacs/transient
  mv     /Users/johnw/.config/emacs/data/url -> /Users/johnw/.local/share/emacs/url
  mv     /Users/johnw/.config/emacs/data/workgroups -> /Users/johnw/.local/share/emacs/workgroups
  rmdir  /Users/johnw/.config/emacs/data
  mv     /Users/johnw/.config/emacs/data-MacPort -> /Users/johnw/.local/share/emacs/migration/20261117-112233/attic/data-MacPort
  mv     /Users/johnw/.config/emacs/eshell/history -> /Users/johnw/.local/share/emacs/eshell/history
  mv     /Users/johnw/.config/emacs/eshell/lastdir -> /Users/johnw/.local/share/emacs/eshell/lastdir
  mv     /Users/johnw/.config/emacs/projects -> /Users/johnw/.local/share/emacs/projects
  mv     /Users/johnw/.config/emacs/projectile-frecency.eld -> /Users/johnw/.local/share/emacs/projectile-frecency.eld
  mv     /Users/johnw/.config/emacs/multisession -> /Users/johnw/.local/share/emacs/multisession
  mv     /Users/johnw/.config/emacs/persist -> /Users/johnw/.local/share/emacs/persist
  mv     /Users/johnw/.config/emacs/request -> /Users/johnw/.local/share/emacs/request
  mv     /Users/johnw/.config/emacs/tree-sitter -> /Users/johnw/.local/share/emacs/tree-sitter
  mv     /Users/johnw/.config/emacs/eln-cache -> /Users/johnw/.cache/emacs/eln-cache
  mv     /Users/johnw/.config/emacs/emojis -> /Users/johnw/.cache/emacs/emojis
  mv     /Users/johnw/.config/emacs/var/pcache -> /Users/johnw/.cache/emacs/pcache
  mv     /Users/johnw/.config/emacs/var/osm -> /Users/johnw/.local/share/emacs/migration/20261117-112233/attic/var/osm
  rmdir  /Users/johnw/.config/emacs/var
  mv     /Users/johnw/.config/emacs/transient -> /Users/johnw/.local/share/emacs/migration/20261117-112233/attic/transient
  mv     /Users/johnw/.config/emacs/auto-save-list -> /Users/johnw/.local/share/emacs/migration/20261117-112233/attic/auto-save-list
  mv     /Users/johnw/.config/emacs/elpy -> /Users/johnw/.local/share/emacs/migration/20261117-112233/attic/elpy
  mv     /Users/johnw/.config/emacs/gptel-agent -> /Users/johnw/.local/share/emacs/migration/20261117-112233/attic/gptel-agent
  mv     /Users/johnw/.config/emacs/.lsp-session-v1 -> /Users/johnw/.local/share/emacs/migration/20261117-112233/attic/.lsp-session-v1
  mv     /Users/johnw/.config/emacs/.org-generic-id-locations -> /Users/johnw/.local/share/emacs/migration/20261117-112233/attic/.org-generic-id-locations
  mv     /Users/johnw/.config/emacs/anvil-worker.log -> /Users/johnw/.local/share/emacs/migration/20261117-112233/attic/anvil-worker.log
  mv     /Users/johnw/.config/emacs/%backup%~ -> /Users/johnw/.local/share/emacs/migration/20261117-112233/attic/%backup%~
  rmdir  /Users/johnw/.config/emacs/hash-store
  rmdir  /Users/johnw/.config/emacs/agent
Left in /Users/johnw/.config/emacs, neither tracked nor expected:
Done.
```

`xdg/check-litter.sh ~/.config/emacs` on the same day:

```text
/Users/johnw/.config/emacs/%backup%~
/Users/johnw/.config/emacs/.lsp-session-v1
/Users/johnw/.config/emacs/.org-generic-id-locations
/Users/johnw/.config/emacs/anvil-worker.log
/Users/johnw/.config/emacs/auto-save-list
/Users/johnw/.config/emacs/data-MacPort
/Users/johnw/.config/emacs/data
/Users/johnw/.config/emacs/elpy
/Users/johnw/.config/emacs/emojis
/Users/johnw/.config/emacs/eshell/history
/Users/johnw/.config/emacs/eshell/lastdir
/Users/johnw/.config/emacs/gptel-agent
/Users/johnw/.config/emacs/persist
/Users/johnw/.config/emacs/projectile-frecency.eld
/Users/johnw/.config/emacs/projects
/Users/johnw/.config/emacs/request
/Users/johnw/.config/emacs/transient
/Users/johnw/.config/emacs/tree-sitter
/Users/johnw/.config/emacs/url
/Users/johnw/.config/emacs/var
/Users/johnw/.config/emacs/agent (empty directory)
/Users/johnw/.config/emacs/hash-store (empty directory)
```
