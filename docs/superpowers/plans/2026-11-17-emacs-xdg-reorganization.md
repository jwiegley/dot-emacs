# Emacs XDG Reorganization Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Leave only configuration in `~/.config/emacs`, and put everything Emacs writes while it runs where the XDG Base Directory specification says its kind belongs: data under `$XDG_DATA_HOME/emacs`, state under `$XDG_STATE_HOME/emacs`, caches under `$XDG_CACHE_HOME/emacs`. On Clio and Hera, without losing a file.

**Architecture:** A small library, `lisp/user-paths.el`, computes the three roots from the XDG variables and sets every path that has to be in place before its package loads. A new `early-init.el` loads it first, and the first block of `init.org` loads it again for batch runs and refuses to run on state that has not been moved. The files themselves are moved once per host by `xdg/migrate.sh`, which previews by default, records every rename and can roll back. The `init.org` edit is applied by an anchored edit script inside the cutover window, because the canonical file reaches Hera through Syncthing the moment it changes.

**Tech Stack:** Emacs Lisp (GNU Emacs 31.1.50) with ERT, bash (must also run under the system bash 3.2), git, make, `sandbox-exec`, `shellcheck`.

**Spec:** Appendix A of this document: the audit report, verbatim, and John's four amendments of 2026-11-17, which add `~/.local/state`, rule out backup coverage as a reason for placing a file, and ask for the placement to rest on research. Appendix B lists every place where this plan departs from the report, and why. Appendix D gives the sources the placement rests on.

## Global Constraints

- The canonical `init.org` is `~/org/init.org` (it resolves to `~/Documents/org/init.org`). `~/.config/emacs/init.org` is a copy that `make` overwrites. Never edit the copy.
- `user-emacs-directory` stays `~/.config/emacs`. Redirection is per variable.
- Four directories, each used for what it is for: `~/.config/emacs` for configuration; `$XDG_DATA_HOME/emacs` (`~/.local/share/emacs`) for data; `$XDG_STATE_HOME/emacs` (`~/.local/state/emacs`) for state; `$XDG_CACHE_HOME/emacs` (`~/.cache/emacs`) for caches.
- A file's place follows from what the file is, by the XDG Base Directory specification and the practice of the projects that apply it most carefully (Appendix D), and from nothing else. Data is what is worth carrying to another machine, and what was installed on request: saved choices, tokens, learned parameters, tree-sitter grammars, language servers, downloaded artwork. State is what Emacs records about its own use on this machine and keeps between restarts: histories, recent files, positions, sessions, cookies, backups, crash-recovery indexes, logs. A cache is what Emacs can make again from what is on this machine, or fetches again unasked: compiled code, indexes, web responses. What comes back only when John agrees to a download or a build is installed, not cached. Whether a directory is backed up plays no part.
- An unset, empty or relative XDG value means the default (`~/.local/share`, `~/.local/state`, `~/.cache`). A GUI Emacs started from the Dock has no XDG variables at all.
- No compatibility symlinks.
- `xdg/migrate.sh --apply` runs only while no Emacs is running on that host.
- A hand-made trial of `xdg/migrate.sh` or of `lisp/user-paths.el` against a throw-away home must start from an empty environment (`env -i`), as `xdg/migrate-test.sh` does, or set `XDG_CONFIG_HOME`, `XDG_DATA_HOME`, `XDG_STATE_HOME` and `XDG_CACHE_HOME` as well as `HOME`. John's shell exports all four, and they take precedence over `HOME`.
- The mover never deletes state. A leftover with no owner goes to an attic for a person to review.
- The existing `.gitignore` rules for runtime paths stay, as a safety net: `~/src/scripts/changes` runs `git add -A` and pushes.
- Tasks 1 to 6 change nothing outside the worktree, apart from git's own record of the worktree and its branch, and the push of that branch to `origin` in Task 6 Step 6: not `~/org/init.org`, not the working tree of `master`, not a single file of state.
- Every edit text in `xdg/apply-init-edits.el` is plain ASCII.
- Every shell script passes `shellcheck` and runs under `/bin/bash` 3.2.
- Commit subjects follow the repository's style, `area: Sentence`. Add whatever attribution trailer your own instructions require.

## Review Focus

Each line names a condition the report implies but does not state, the behaviour a reasonable person expects, and the test that pins it.

1. **A GUI Emacs started from the Dock has no XDG variables.** All three roots must equal the directories the shell's values name. Pinned by `user-paths-test-defaults-without-xdg-variables` and `user-paths-test-unusable-xdg-values-fall-back` (Task 1).
2. **A library that loads after the redirect reads or restores its own default.** Tramp and transient read their files while they load; today both write files they never read back. Pinned by `user-paths-test-values-survive-loading-their-libraries` (Task 1) for built-in libraries and by the sealed audit (Task 3) for the whole init.
3. **Emacs is still running when the files move.** A running session rewrites its history at the old paths, on timers as well as on exit. Pinned by the `refuses while ... runs` checks in `xdg/migrate-test.sh` (Task 4).
4. **A destination already holds a different file**, because Emacs started at the wrong moment or the other host's copy arrived by sync. The mover must not guess which is right: it refuses until told, and keeps the copy that loses. Pinned by the checks `apply refuses to choose between two different files`, `the history that was there is kept` and `the copy from the configuration directory is kept` (Task 4).
5. **A host starts the new init before its own state has moved.** `init.org` reaches Hera through Syncthing within seconds. Emacs must refuse rather than start on empty history. Pinned by `user-paths-test-guard-rejects-unmigrated-state` (Task 1).

Four more, lower on the list. An interrupted move must be safe to run again (`a second apply moves nothing`, Task 4). Token and cookie files must end up owner-only (`token file is private`, Task 4). A file that clashes with a copy already at its destination must stay where it is, without the entry for the rest of `data/` carrying it to another root (`preview sends a clashing file to no other root` and the checks under `a clash inside a directory`, Task 4). And the three roots must be three separate directories: with two of them in one place, the move of `backups/` from the data root to the state root would take every file for a duplicate of itself and delete it (`refuses XDG_STATE_HOME at or inside another root`, Task 4).

## What the investigation found

An executor needs these facts; none of them is in the report.

- **`make init.el` loads the whole init.** The Makefile runs `org-babel-load-file`, which tangles and then loads `init.el` in batch Emacs. `~/src/nix/bin/runemacs` runs `make init.el` at every launch, and `make` rebuilds only when `~/org/init.org` is newer than the checkout's copy: the batch load happens after each change to `init.org`. Batch Emacs never reads `early-init.el`.
- **`init.org` travels by Syncthing; everything else by ChronoSync.** `~/Documents` is a Syncthing folder shared by Clio, Hera and Vulcan. A ChronoSync task named `Home` synchronizes the whole home directory between Hera and Clio every hour, in both directions, and already reports conflicts on `.config/emacs/data/recentf`. Its include and exclude rules could not be read from disk. Only John can inspect them.
- **`~/src/scripts/changes` runs `git add -A`, commits and pushes** this repository. That is how `multisession/files/emoji/emoji--recent.value`, a runtime file, came to be tracked.
- **An Emacs started with `-Q` or `-q` reads no init file** and writes to the built-in defaults under `~/.config/emacs`: `eln-cache/`, `auto-save-list/`, `transient/`, `url/`, and depending on what is done in it `tramp`, `bookmarks`, `network-security.eld`, `elpa/` and more. No init setting can prevent that. The stray top-level `transient/`, `url/` and `auto-save-list/` most likely come from such runs, or from an init that stopped early. Task 5 adds an ignore rule for each built-in name, so that `changes` cannot commit one, and `make check-litter` shows them.
- **Two package defaults point at `~/.emacs.d`:** `hash-store-directory` and `pandoc-data-dir`. If either package creates that directory, Emacs prefers it to `~/.config/emacs` at the next start and comes up with no configuration.
- **Two settings do not work today.** `tramp-persistency-file-name` is set in `:config`, after tramp has read the file. The transient files are set in a `:custom` that runs after another package has loaded transient. Going by the order in which the init loads them, both are written on exit and never read back.
- **The alternate instance is dead code.** Nothing sets `NIX_MYENV_NAME=emacsERC` since 2024. The plan keeps the one line that separates its state and leaves the uses of `alternate-emacs` elsewhere in `init.org` alone. An Emacs started that way gets three roots of its own, named `emacs-alt` and empty at first: it shares neither history nor grammars with the main instance, and the mover fills only the main one.
- **Nothing in the Nix configuration or the scripts repository has to change** for this move. No script reads `data/`, `org-roam.db` or `org-id-locations`, and the Nix tests run Emacs with `-Q` in a scratch home.
- **The old `data/` directory holds all three kinds.** The current init sends everything through `(user-data ...)`: the minibuffer history, the recent-files list, tokens, saved choices, the Org-roam index. Splitting it is most of the work in this plan: each setting in `init.org` has to name its root, and the mover has to take each file to the root its setting names.
- **Eight blocks of `init.org` that set a path are commented out:** saveplace, prescient, bookmark+, lsp-mode, xeft, oauth2-auto, org-gcal and org-caldav. They are not tangled, so the sealed audit cannot see them. The first five get an edit all the same, so that a revived block names the right root, and the mover takes their old files (`data/places` and `data/prescient-save.el` on Clio) to the place the edited text names. The other three are left alone; see the Follow-ups.
- **Tree-sitter grammars are installed, not cached.** In Emacs 31 `treesit-auto-install-grammar` defaults to `ask`, and the built-in modes register their grammar sources themselves. A missing grammar therefore comes back only after a prompt, and needs git, a C compiler and the network. That covers 26 of the 30 grammars on Clio. The other four (clojure, haskell, kotlin, scala) have no registered source, and no mode that would use them is installed. `init.org` records no sources of its own. `treesit-ensure-installed` installs into the first writable directory on `treesit-extra-load-path`, which the library sets.
- **One directory to move is not in the checkout.** The init already keeps numbered backups and tramp auto-saves in `~/.local/share/emacs/backups` (201 MB on Clio). They are state, so the mover takes that directory to the state root. It is the only source outside `~/.config/emacs`.
- **Three caches already followed XDG, each under a name of its own:** Org's `org-persist` at `~/.cache/org-persist`, and the defaults of John's `coq-lookup` and `dired-filetags` at `~/.cache/coq-lookup` and `~/.cache/dired-filetags`. The table brings all three under `~/.cache/emacs`, so that the four directories hold everything Emacs keeps. Only the first exists on Clio (776 KB); being a cache it is rebuilt at the new place, and Task 10 removes the old directory. Org's default also has a trap that the table closes: on a host where `~/.cache` does not exist yet, it falls back to the configuration directory.
- **One package writes a dotfile into the home directory.** `chess-autosave-file` defaults to `~/.chess-save`. It is crash-recovery state, and the table sends it to the state root. No such file exists on Clio.

## File Structure

### What changes, by location

John asked for every configuration file under `~/org`, `~/.config/emacs` and `~/.config/emacs/lisp` that needs a change. Each of the three trees was searched for the paths that move, for code that builds a path at run time, and for the names the old init defined; three critics then hunted for anything missed (Appendix C).

| Where | Changes | Needs no change |
|---|---|---|
| `~/org` | `init.org`: 26 exact-text edits (Task 2), applied at the cutover (Task 7 Step 7). One adds the section that loads the library and the guard; one drops the block that defined `user-data`; nineteen give a setting its root (fifteen to state, three to the cache, and one that sends the lsp servers to data and the lsp session to state); five remove a setting that the library now makes early enough | Everything else. Of about 14,750 files, `init.org` is the only one Emacs loads as configuration: no other Org file tangles or evaluates Emacs Lisp, and `Makefile`, `org.yaml`, `.gitea/` and `.claude/` there do not name the Emacs configuration. A handful of notes mention the old paths in prose |
| `~/.config/emacs` | New: `early-init.el`, `xdg/migrate.sh`, `xdg/check-litter.sh` and their tests; for the cutover only, `xdg/apply-init-edits.el` and `xdg/audit/`. Modified: `.gitignore` (22 rules), `Makefile` (three targets), `README.md` (one paragraph). Deleted: `migrate-emacs-xdg.sh`. Untracked: `multisession/files/emoji/emoji--recent.value` | `settings.el` (the Custom file sets no path), `abbrevs.el`, `eshell/alias`, `eshell/login`, `runshell`, `test-emacs`, `emacs-mcp-stdio.sh`, `.claude/`, `prompts/`, `snippets/`, `doc/`. The Makefile's build rules stay as they are: `make init.el`, run in a sealed copy with its own command line, put its native code under the cache root and wrote nothing inside the configuration directory |
| `~/.config/emacs/lisp` | New: `user-paths.el`, `user-paths-test.el` | Every existing file. None of the 66 tracked `.el` files or the three submodules uses `user-emacs-directory`, `locate-user-emacs-file`, `emacs-path`, `user-data` or `user-data-directory`, and none writes beside itself. Two of them have a cache directory of their own, which the library's table redirects without touching the packages |
| Directories | Created: `~/.local/state/emacs`. `~/.local/share/emacs` and `~/.cache/emacs` exist already; the first gives up `backups/`. Emptied out of the checkout: `data/`, `data-MacPort/`, `var/`, `persist/`, `multisession/`, `request/`, `transient/`, `url/`, `auto-save-list/`, `tree-sitter/`, `eln-cache/`, `emojis/`, `elpy/`, `gptel-agent/`, `hash-store/`, `agent/`, and eight single files (Task 4 has the destination of each) | `~/.local/share/gnus`, where Gnus keeps its own home (Follow-up 16); `~/.cache/org-persist`, which is abandoned for `~/.cache/emacs/org-persist` and deleted in Task 10 |
| Elsewhere | Nothing | `~/src/nix`, `~/src/scripts` and `~/Library/LaunchAgents` were searched for every path that moves; none names one |

### The files

| File | Status | Responsibility |
|---|---|---|
| `lisp/user-paths.el` | new, permanent | The three roots; `user-data`, `user-state` and `user-cache`; the table of early path settings; the directory set-up; the native-cache redirect; the guard |
| `lisp/user-paths-test.el` | new, permanent | ERT tests for the library and for `early-init.el` |
| `early-init.el` | new, permanent | Loads the library before anything else; disables package.el |
| `xdg/check-litter.sh` | new, permanent | Reports runtime state that has come back into the checkout |
| `xdg/check-litter-test.sh` | new, permanent | Tests for the report |
| `xdg/migrate.sh` | new, permanent | Moves state out of the checkout; previews, logs, rolls back |
| `xdg/migrate-test.sh` | new, permanent | Tests for the mover against throw-away trees |
| `xdg/apply-init-edits.el` | new, removed in Task 10 | Applies the 26 `init.org` edits by exact text |
| `xdg/apply-init-edits-test.el` | new, removed in Task 10 | Tests for the editor |
| `xdg/audit/run.sh`, `sandbox.sb`, `guards.el`, `audit.el` | new, removed in Task 10 | Loads the whole init in a sealed copy and reports paths that still point into the checkout |
| `.gitignore` | modified | 22 more safety-net rules |
| `Makefile` | modified | Targets `check-litter`, `test-xdg`, `audit-xdg` |
| `README.md` | modified | One paragraph on the layout |
| `migrate-emacs-xdg.sh` | deleted | The earlier script; it was never run and cannot run on the current layout |
| `multisession/files/emoji/emoji--recent.value` | untracked in Task 9 | Runtime state that was committed by accident; the mover takes it to the state root |
| `~/org/init.org` | modified at cutover | 26 edits, applied by `xdg/apply-init-edits.el` |

### The four directories after the cutover

| Directory | Holds | On Clio |
|---|---|---|
| `~/.config/emacs` | Configuration: what is versioned, and what is set up once per host | the tracked files, `init.el`, `settings.el`, `nix-packages`, `nix-packages.el`, `certs/`, `eshell/alias`, `eshell/login`, the `*.elc` files under `lisp/`, `.claude/`, `.superpowers/` |
| `~/.local/share/emacs` | Data: worth carrying to another machine, or installed on request | `mc-lists.el`, `oauth2-auto.plist`, `persist/` (org-drill's learned matrix, play queues), `transient/values.el`, `tree-sitter/`, `emojis/` |
| `~/.local/state/emacs` | State: what Emacs records about its own use on this machine | `history`, `recentf`, `org-id-locations`, `persistent-scratch`, `places`, `prescient-save.el`, `projects`, `projectile-bookmarks.eld`, `projectile-frecency.eld`, `tramp`, `bm-repository`, `network-security.data`, `eshell/history`, `eshell/lastdir`, `transient/history.el`, `url/cookies`, `request/curl-cookie-jar`, `auto-save-list/`, `multisession/`, `backups/`, and for a while `migration/` |
| `~/.cache/emacs` | Caches: what Emacs can make again from what is on this machine, or fetches again unasked | `eln-cache/`, `org-roam.db`, `url/`, `pcache/`, and once Org writes there `org-persist/` |

Each later variable goes to its root by the same rule. `user-paths-table` and `user-paths-apply-special` in Task 1 and the edit table in Task 2 list them all; the special cases are `TeX-auto-private` (cache), elpy's virtualenv (data), `web-cookie-jar-file` (state) and the tree-sitter directory (data).

## Before you start

- Work on branch `xdg-layout` in a git worktree outside the checkout. Create it with exactly this command, and do not let superpowers:using-git-worktrees choose the place. Its default is a directory inside the checkout, which the mover and the litter report would then list.

  ```bash
  git -C ~/.config/emacs worktree add ~/src/emacs-xdg-layout -b xdg-layout
  ```

  In this plan `WT` is `~/src/emacs-xdg-layout`, and the commands of Tasks 1 to 6 run from there. Where an expected output shows `<WT>`, Emacs prints that directory's full path. Another agent edits `init.org` and `lisp/` in the main checkout; stay out of it.
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
- Consumes: nothing from other tasks. Reads the environment variables `XDG_DATA_HOME`, `XDG_STATE_HOME` and `XDG_CACHE_HOME` through Emacs's own `xdg.el`, and `NIX_MYENV_NAME`.
- Produces:
  - `user-data-directory`, `user-state-directory` and `user-cache-directory`: strings, absolute, each ending in `/`.
  - `(user-data PATH)`, `(user-state PATH)` and `(user-cache PATH)`: return PATH expanded under the matching root.
  - `emacs-environment` (string or nil) and `alternate-emacs` (boolean), which `init.org` goes on using.
  - `user-paths-table`: a list of `(VARIABLE ROOT NAME)` with ROOT `data`, `state` or `cache`.
  - `(user-paths-check-migrated)`: signals `error` if `<user-emacs-directory>/data` is a directory, and otherwise returns nil.
  - The feature `user-paths`. Loading the file creates the directories, applies the table and redirects the native-compilation cache.

- [x] **Step 1: Write the failing tests**

Create `lisp/user-paths-test.el`:

```elisp
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
```

- [x] **Step 2: Run the tests to verify they fail**

Run: `emacs --batch -Q -l lisp/user-paths-test.el -f ert-run-tests-batch-and-exit; echo "exit=$?"`

Expected: `exit=255`, and above it

```text
Cannot open load file: No such file or directory, <WT>/lisp/user-paths.el
```

- [x] **Step 3: Write the library**

Create `lisp/user-paths.el`:

```elisp
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
```

- [x] **Step 4: Run the tests; all but one pass**

Run: `emacs --batch -Q -l lisp/user-paths-test.el -f ert-run-tests-batch-and-exit 2>&1 | grep -E 'FAILED|Ran '`

Expected:

```text
   FAILED   5/17  user-paths-test-early-init-loads-the-library (...)
Ran 17 tests, 16 results as expected, 1 unexpected (...)
   FAILED  user-paths-test-early-init-loads-the-library
```

The one failure is the test for the file the next step creates.

- [x] **Step 5: Write early-init.el**

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

- [x] **Step 6: Run the tests to verify they pass**

Run: `emacs --batch -Q -l lisp/user-paths-test.el -f ert-run-tests-batch-and-exit 2>&1 | grep -E 'FAILED|Ran '`

Expected: `Ran 17 tests, 17 results as expected, 0 unexpected (...)`

- [x] **Step 7: Check that the library compiles without warnings**

The library is always loaded as source, so compile a copy elsewhere and leave no `.elc` in the worktree.

```bash
copy=$(mktemp -d) && cp lisp/user-paths.el "$copy/" &&
  (cd "$copy" && emacs --batch -Q -f batch-byte-compile user-paths.el)
```

Expected: no output.

- [x] **Step 8: Commit**

```bash
git add lisp/user-paths.el lisp/user-paths-test.el early-init.el
git commit -m "user-paths: Compute the XDG data, state and cache roots in one library"
```

---

### Task 2: The anchored init.org editor

**Files:**
- Create: `xdg/apply-init-edits.el`
- Test: `xdg/apply-init-edits-test.el`

**Interfaces:**
- Consumes: the names Task 1 defines, but only as text inside the edits: `user-paths`, `user-paths-check-migrated`, `user-data`, `user-state`, `user-cache`.
- Produces:
  - `xdg-init-edits`: a list of plists with `:name`, `:old`, `:new`, an optional `:removes` (a string that must be absent once the edit is done) and an optional `:marker` (a string whose presence alone means done).
  - `(xdg-init-edits-apply FILE &optional CHECK)`: returns non-nil if every edit is done or can be made. It writes FILE only when all can and something changed, and never when CHECK is non-nil.
  - `xdg-init-edits-batch`: the command-line entry. Arguments `[--check] FILE`. Exit status 0, 1 if an edit cannot be made, or 2 if no file is named.

The 26 edits, in the order of the file. "Commented out" marks a block under a `COMMENT` heading, which is not tangled today.

| # | Edit | Effect on `init.org` |
|---|---|---|
| 1 | load user-paths before anything else | New section before the Nix package loader, which is the first block that loads anything: requires `lisp/user-paths.el`, then calls the guard |
| 2 | drop the old data-environment block | The library now defines `emacs-environment`, `alternate-emacs`, the three roots and their three functions |
| 3 | auto-save-list prefix | Removed from `use-package emacs`; the table sets it, under state |
| 4 | backups | `backup-directory-alist` moves from the literal `~/.local/share/emacs/backups` to `(user-state "backups")` |
| 5 | network security decisions | `nsm-settings-file` moves to `(user-state ...)` |
| 6 | line bookmarks | `bm-repository-file` moves to `(user-state ...)` |
| 7 | bookmark-list display state | `bmkp-bmenu-state-file` moves to `(user-state ...)`. Commented out |
| 8 | nov reading positions | `nov-save-place-file` moves to `(user-state ...)` |
| 9 | persistent scratch | `persistent-scratch-save-file` moves to `(user-state ...)` |
| 10 | prescient usage counts | `prescient-save-file` moves to `(user-state ...)`. Commented out |
| 11 | projectile index | `projectile-cache-file` moves to `(user-cache ...)` |
| 12 | projectile known projects | `projectile-known-projects-file` moves to `(user-state ...)` |
| 13 | recent files | `recentf-save-file` moves to `(user-state ...)` |
| 14 | minibuffer history | `savehist-file` moves to `(user-state ...)` |
| 15 | saved positions | `save-place-file` moves to `(user-state ...)`. Commented out |
| 16 | tramp auto-saves | `tramp-auto-save-directory` moves from the same literal to `(user-state "backups")` |
| 17 | tramp persistency | The `setq` in `:config` is removed; the table sets it, under state, before tramp loads |
| 18 | transient files | The `:custom` is removed; the table sets the history under state and the saved values and levels under data |
| 19 | url directory | The `:custom` is removed; the table sets it, under state: it holds cookies and the history of visited URLs |
| 20 | url cache directory | The `:custom` is removed; the table sets it under the cache root |
| 21 | slime history | `slime-repl-history-file` moves to `(user-state ...)` |
| 22 | lsp servers and session | `lsp-server-install-dir` becomes `(user-data "lsp/")` and `lsp-session-file` moves to `(user-state "lsp-session-v1")`, the names the table uses. Commented out |
| 23 | org clock persistence | `org-clock-persist-file` moves to `(user-state ...)` |
| 24 | org-id locations | `org-id-locations-file` moves to `(user-state ...)` |
| 25 | org-roam database | `org-roam-db-location` moves to `(user-cache ...)` |
| 26 | xeft index | `xeft-database` moves to `(user-cache ...)`. Commented out |

The settings this list leaves at `(user-data ...)` are data and stay so: `mc/list-file`, and in commented-out blocks `bmkp-bmenu-commands-file`, `oauth2-auto-plstore` and `org-gcal-dir`.

The first edit carries a `:marker`. Its inserted block sits before a heading that stays in the file, so without the marker a later rewording of the block would make the next run insert a second copy.

- [x] **Step 1: Write the failing tests**

The checkout has no `xdg/` directory yet. Make it, with the one Task 3 needs: `mkdir -p xdg/audit`

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

(ert-deftest xdg-init-edits-test-each-path-names-its-root ()
  ;; Which root a file belongs to is the point of most edits, so pin it.
  (let ((file (xdg-init-edits-test--fixture)))
    (unwind-protect
        (let (text)
          (should (xdg-init-edits-apply file))
          (setq text (xdg-init-edits-test--bytes file))
          (dolist (name '("backups" "network-security.data" "bm-repository"
                          "bmk-bmenu-state.el" "nov-places"
                          "persistent-scratch" "prescient-save.el"
                          "projectile-bookmarks.eld" "recentf" "history"
                          "places" "slime-history.eld" "lsp-session-v1"
                          "org-clock-save.el" "org-id-locations"))
            (should (string-search (format "(user-state %S)" name) text))
            (should-not (string-search (format "(user-data %S)" name) text)))
          (should (string-search "(user-data \"lsp/\")" text))
          (dolist (name '("projectile.cache" "org-roam.db" "xeft.db"))
            (should (string-search (format "(user-cache %S)" name) text))
            (should-not (string-search (format "(user-data %S)" name) text)))
          ;; The old names of the lsp files are gone with their old root.
          (should-not (string-search ".lsp-session-v1" text))
          (should-not (string-search ".cache/lsp" text))
          (should-not (string-search "~/.local/share/emacs/backups" text)))
      (delete-file file))))

(ert-deftest xdg-init-edits-test-a-touched-block-is-not-inserted-twice ()
  ;; The first edit inserts a block before a heading that stays in the
  ;; file.  Someone who later rewords that block must not get a second
  ;; copy on the next run.
  (let ((file (xdg-init-edits-test--fixture)))
    (unwind-protect
        (let (text)
          (should (xdg-init-edits-apply file))
          (setq text (xdg-init-edits-test--bytes file))
          (with-temp-file file
            (set-buffer-multibyte nil)
            (insert (string-replace ";; Refuse to run on state"
                                    ";; Do not run on state" text)))
          (should (xdg-init-edits-apply file))
          (setq text (xdg-init-edits-test--bytes file))
          (should (= 1 (with-temp-buffer
                         (insert text)
                         (how-many "(user-paths-check-migrated)"
                                   (point-min) (point-max))))))
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

- [x] **Step 2: Run the tests to verify they fail**

Run: `emacs --batch -Q -l xdg/apply-init-edits-test.el -f ert-run-tests-batch-and-exit; echo "exit=$?"`

Expected: `exit=255`, and above it

```text
Cannot open load file: No such file or directory, <WT>/xdg/apply-init-edits.el
```

- [x] **Step 3: Write the editor**

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
```

- [x] **Step 4: Run the tests to verify they pass**

Run: `emacs --batch -Q -l xdg/apply-init-edits-test.el -f ert-run-tests-batch-and-exit 2>&1 | grep -E 'FAILED|Ran '`

Expected: `Ran 7 tests, 7 results as expected, 0 unexpected (...)`

- [x] **Step 5: Check every edit against the canonical file, without writing it**

Run: `emacs --batch -Q -l xdg/apply-init-edits.el -f xdg-init-edits-batch --check ~/org/init.org; echo "exit=$?"`

Expected:

```text
pending   load user-paths before anything else
pending   drop the old data-environment block
pending   auto-save-list prefix is set in user-paths
pending   backups are state
pending   network security decisions are state
pending   line bookmarks are state
pending   bookmark-list display state is state
pending   nov reading positions are state
pending   persistent scratch is state
pending   prescient usage counts are state
pending   projectile index is a cache
pending   projectile known projects are state
pending   recent files are state
pending   minibuffer history is state
pending   saved positions are state
pending   tramp auto-saves are state
pending   tramp persistency is set in user-paths
pending   transient files are set in user-paths
pending   url directory is set in user-paths
pending   url cache directory is set in user-paths
pending   slime history is state
pending   lsp servers are data and the lsp session is state
pending   org clock persistence is state
pending   org-id locations are state
pending   org-roam database is a cache
pending   xeft index is a cache
exit=0
```

If a line says `ERROR`, that block of `init.org` has changed since this plan was written. Open `~/org/init.org`, find the block the edit's name describes, and change that edit's `:old` in `xdg/apply-init-edits.el` to the block's current text, byte for byte. Change `:new` to match, keeping what the table above says the edit does. Then repeat Steps 4 and 5.

- [x] **Step 6: Commit**

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

- [x] **Step 1: Write the sandbox profile**

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

- [x] **Step 2: Write the guards**

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

;; The init makes the directory of its server socket when that is missing,
;; as it is while no Emacs runs.  run.sh denies every write there, so the
;; attempt is skipped as well.
(defconst xdg-audit-server-directory
  (format "/tmp/%s-emacs" (user-login-name))
  "Directory of the live server socket, which the sandbox denies.")

(dolist (function '(make-directory set-file-modes))
  (advice-add function :around
              (lambda (original file &rest arguments)
                (if (equal (directory-file-name (expand-file-name file))
                           xdg-audit-server-directory)
                    (progn (message "guards: left %s alone" file) nil)
                  (apply original file arguments)))
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

- [x] **Step 3: Write the audit**

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

- [x] **Step 4: Write the runner**

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
mkdir -p "$config" "$home/.local/share" "$home/.local/state" "$home/.cache" "$scratch/tmp"

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
printf 'Written under the data, state and cache roots:\n'
(cd "$home" && find .local/share .local/state .cache -newer "$scratch/stamp" ! -type d |
    sed 's|\(eln-cache/[^/]*\)/.*|\1/*.eln|' | LC_ALL=C sort -u | sed 's/^/  /')

if [[ $status -eq 0 ]]; then
    printf 'PASS\n'
else
    printf 'FAIL (the log is %s; set XDG_AUDIT_KEEP=1 to keep it)\n' "$scratch/audit.log"
fi
exit "$status"
```

- [x] **Step 5: Make it executable and lint it**

Run: `chmod +x xdg/audit/run.sh && shellcheck xdg/audit/run.sh; echo "exit=$?"`

Expected: `exit=0` and no other output.

- [x] **Step 6: Run the self-test; it must fail**

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

- [x] **Step 7: Run the audit; it must pass**

Run: `xdg/audit/run.sh; echo "exit=$?"`

Expected:

```text
Applying the init.org edits to the copy
  applied   load user-paths before anything else
  ... 25 more "applied" lines ...
Tangling init.el
Loading the init; this takes about half a minute
  audit: emacs-startup-hook: (user-error "Not a directory: .../home/Desktop")
  audit: window-setup-hook: (file-error "guards: subprocesses disabled" (".../epdfinfo"))
  audit: 580 forms, 0 failed; 300 more features loaded, 30 would not; 1674 features in all
audit: 0 offenders, 0 failed forms
Written inside the configuration directory:
Written under the data, state and cache roots:
  .cache/emacs/eln-cache/31_1_50-ed4578ca/*.eln
  .cache/emacs/org-roam.db
  .local/state/emacs/bm-repository
  .local/state/emacs/history
  .local/state/emacs/persistent-scratch
  .local/state/emacs/recentf
  .local/state/emacs/tramp
PASS
exit=0
```

The two hook lines are expected: the scratch home has no `~/Desktop`, and the guards refuse to start `epdfinfo`. The counts drift as the init and the packages change. What must hold is `0 offenders, 0 failed forms`, an empty list under `Written inside the configuration directory`, and `PASS`. The last list shows each kind landing in its own root: the history, the recent files, the scratch buffer, the line bookmarks and tramp's connection history under state; the Org-roam index and native code under the cache. Nothing in this run writes data: that root changes only when John saves a choice or installs something.

If the run reports an offender, `init.org` has gained a package since this plan was written. Decide as follows, then run `make test-xdg` (after Task 5) or the Task 1 tests, and this step again.

1. The value is configuration that a person writes, such as a snippets directory or a settings file: add the variable to `xdg-audit-allowed-variables` in `xdg/audit/audit.el`, under the comment that fits.
2. Otherwise add `(VARIABLE data "name")`, `(VARIABLE state "name")` or `(VARIABLE cache "name")` to `user-paths-table` in `lisp/user-paths.el`, in alphabetical order within its part. Choose `data` if the file is worth carrying to another machine or was installed on request, such as a saved choice, a token or a grammar; `state` if it records what Emacs did on this machine, such as a history, a position, a session, a cookie or a backup; and `cache` if Emacs can make it again from what is on this machine, or fetches it again unasked. Keep a trailing slash if the package's default has one.
3. The variable is a `defconst`, or its value is not a single string: set it in `user-paths-apply-special`.

If a form of `init.el` fails, the log names it. A form that needs one of John's documents can be tolerated the way `guards.el` tolerates `org-ext-update-team`.

- [x] **Step 8: Commit**

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
- Consumes: nothing from other tasks. Reads `HOME`, `XDG_CONFIG_HOME`, `XDG_DATA_HOME`, `XDG_STATE_HOME`, `XDG_CACHE_HOME`, and for tests `EMACS_XDG_STAMP` and `EMACS_XDG_TEST_PS_FILE`.
- Produces:
  - `xdg/migrate.sh`: preview, exit 0, changes nothing. A running Emacs is only a warning.
  - `xdg/migrate.sh --apply`: moves, exit 0. Refuses with exit 1 if Emacs runs, if `~/.emacs.d`, `~/.emacs` or `~/.emacs.el` exists, if the configuration directory has no `init.org`, or if a source is a symbolic link. A preview refuses as well, and so does `--apply`, if two of the three roots are the same directory or one lies inside another, or if a root or the place for the records exists and is not a directory.
  - `--prefer=source` or `--prefer=destination`, with or without `--apply`: says which copy wins where a destination already holds a different file. Without it, a preview marks each such pair with `clash` and `--apply` refuses before moving anything. The copy that loses is kept under `<run directory>/collisions/`.
  - `xdg/migrate.sh --rollback DIR`: undoes the renames listed in `DIR/moves.tsv`. It refuses to overwrite a file that has come back at an old path, and it can be run again after it stops. If a moved file has since vanished from both places, it says so on a line that begins with `  lost` (two spaces first, like every action line), restores everything else, exits 1 and keeps the log.
  - The run directory `<state>/migration/<stamp>/` holding `moves.tsv`, `pre-migration.tar`, `attic/` and, if anything collided, `collisions/`.
  - Every file at exactly the root and name that `user-paths-table` (Task 1) or the edited `init.org` (Task 2) gives it: `<state>/eshell/history`, `<state>/history`, `<data>/transient/values.el`, `<cache>/org-roam.db` and so on.

Where each thing goes. The old init kept all three kinds under `data/`, so that directory is split:

| Source in `~/.config/emacs` | Destination | Kind |
|---|---|---|
| `data/history`, `data/recentf`, `data/org-id-locations`, `data/persistent-scratch`, `data/places`, `data/prescient-save.el`, `data/projectile-bookmarks.eld`, `data/tramp`, `data/bm-repository`, `data/network-security.data`, `data/auto-save-list/`, `data/url/` (cookies), `data/transient/history.el` | `~/.local/state/emacs/` under the same names | state |
| where a host has them: `data/nov-places`, `data/org-clock-save.el`, `data/slime-history.eld`, `data/bmk-bmenu-state.el`, `data/backups/` | `~/.local/state/emacs/` under the same names | state |
| where a host has one: `data/.lsp-session-v1` | `~/.local/state/emacs/lsp-session-v1` | state |
| `eshell/history`, `eshell/lastdir` | `~/.local/state/emacs/eshell/` | state |
| `projects`, `projectile-frecency.eld`, `multisession/`, `request/` | `~/.local/state/emacs/` | state |
| `~/.local/share/emacs/backups/`, which is outside the checkout already | `~/.local/state/emacs/backups/` | state |
| the rest of `data/`: `mc-lists.el`, `oauth2-auto.plist`, `transient/values.el`, and any file this list does not know | `~/.local/share/emacs/` under the same names | data |
| `persist/`, `tree-sitter/`, `emojis/`, `hash-store/` | `~/.local/share/emacs/` | data |
| where a host has it: `data/.cache/lsp/` | `~/.local/share/emacs/lsp/` | data |
| `data/org-roam.db`, with any `-journal`, `-wal` or `-shm` file a crash left beside it; `data/projectile.cache`; `data/xeft.db` | `~/.cache/emacs/` under the same names | cache |
| `eln-cache/` | `~/.cache/emacs/` | cache |
| `var/pcache/` | `~/.cache/emacs/pcache/` | cache |
| `url/cache/` (stray), `data/url/cache/` | `~/.cache/emacs/url/` | cache |
| `data-MacPort/`, `data/mc-lists.elc`, `data/workgroups`, `var/osm/`, `transient/` (stray), `auto-save-list/` (stray), `elpy/`, `gptel-agent/`, `.lsp-session-v1`, `.org-generic-id-locations`, `anvil-worker.log`, `%backup%~` | `<run directory>/attic/` under the same names | attic |
| `agent/`, and `var/`, `url/`, `data/` once emptied | removed if empty | prune |
| `eshell/alias`, `eshell/login`, `certs/`, `settings.el`, `init.el`, `nix-packages*` | stay | configuration |

The tests start the script with an empty environment (`env -i`). That is deliberate: John's shell exports `XDG_STATE_HOME` and its three siblings, and a test that left one of them in place would move its fixture into a real directory.

- [x] **Step 1: Write the failing tests**

Create `xdg/migrate-test.sh`:

```bash
#!/usr/bin/env bash
# migrate-test.sh --- exercise xdg/migrate.sh against throw-away trees
#
# Usage: xdg/migrate-test.sh
#
# Every test builds its own home directory under a scratch directory and
# points the script at it, so no real state is read or written.  The script
# is always started with an empty environment: an XDG variable exported by
# the shell that runs these tests would otherwise outrank the scratch HOME
# and send the moves to real directories.

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
    local home=$1 config data state cache name
    config=$home/.config/emacs
    data=$home/.local/share/emacs
    state=$home/.local/state/emacs
    cache=$home/.cache/emacs
    mkdir -p "$config" "$data/backups" "$state" "$cache"

    # Configuration that must stay.
    put "$config/init.org" 'init'
    put "$config/init.el" 'generated'
    put "$config/lisp/a.el" 'lisp'
    put "$config/eshell/alias" 'alias ll ls -l'
    put "$config/eshell/login" 'login'
    put "$config/mystery.txt" 'nobody knows this file'

    # What the old init kept under data/: data, state and caches together.
    put "$config/data/history" 'legacy history'
    put "$config/data/recentf" 'recent files'
    put "$config/data/org-roam.db" 'database'
    put "$config/data/org-roam.db-journal" 'a journal left by a crash'
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
    put "$config/data/url/cache/johnw/c" 'cached c'
    put "$config/data/.cache/lsp/server" 'server'
    put "$config/data/projectile.cache" 'index'
    for name in bm-repository bmk-bmenu-state.el network-security.data nov-places \
        org-clock-save.el org-id-locations persistent-scratch places \
        prescient-save.el projectile-bookmarks.eld slime-history.eld tramp; do
        put "$config/data/$name" "state: $name"
    done
    put "$config/data/.lsp-session-v1" 'state: lsp session'
    put "$config/data/xeft.db" 'index'

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
    put "$config/hash-store/ab/cdef" 'a stored object'
    mkdir -p "$config/agent"

    # What is already at the destinations.
    put "$data/backups/keep.txt" 'a backup'
    put "$data/keep.txt" 'kept'
    put "$state/history" 'a history written by a premature start'
    put "$state/recentf" 'recent files'
    mkdir -p "$state/url" "$state/eshell" "$data/tree-sitter"
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

# sealed HOME [VAR=value...] [ARGS...]: run the script against the fixture
# in HOME, with nothing else in its environment but PATH and the list of
# processes the fixture supplies.
sealed() {
    local home=$1
    shift
    env -i PATH="$PATH" HOME="$home" EMACS_XDG_TEST_PS_FILE="$home/ps" "$@"
}

# run HOME ARGS...: the usual case, with the default roots below HOME.
run() {
    local home=$1
    shift
    sealed "$home" EMACS_XDG_STAMP="${EMACS_XDG_STAMP:-run1}" "$migrate" "$@"
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
    grep -q "^  clash  $home/.config/emacs/data/history <> $home/.local/state/emacs/history\$" <<<"$output"
check 'preview says that apply will need a preference' \
    grep -q -- '--apply will need --prefer=source or --prefer=destination' <<<"$output"
check 'preview keeps a directory that still holds a clashing file' \
    grep -q "^  stays  $home/.config/emacs/data (not empty)\$" <<<"$output"
check 'preview sends a clashing file to no other root' \
    test -z "$(grep "^  mv     $home/.config/emacs/data/history -> " <<<"$output")"
output=$(run "$home" --prefer=source 2>&1)
check 'a preview with a preference changes nothing' test "$before" = "$(snapshot "$home")"
preview_actions=$(actions <<<"$output")
preview_leftovers=$(sed -n '/^Left in /,/^Done\./p' <<<"$output" | sed '1d;$d')

# ------------------------------------------------------------------ apply
home=$scratch/apply
fixture "$home"
config=$home/.config/emacs
data=$home/.local/share/emacs
state=$home/.local/state/emacs
cache=$home/.cache/emacs
run_dir=$state/migration/run1
original=$(snapshot "$config")
original_data=$(snapshot "$data")
original_state=$(snapshot "$state")
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

# State: what Emacs records about its own use.
check 'history arrives in the state root with the legacy content' \
    grep -qx 'legacy history' "$state/history"
check 'the history that was there is kept' \
    grep -qx 'a history written by a premature start' "$run_dir/collisions$state/history"
check 'an identical file is merged silently' \
    grep -qx 'recent files' "$state/recentf"
check 'an identical file leaves no kept copy' \
    test ! -e "$run_dir/collisions$state/recentf" -a ! -e "$run_dir/collisions$config/data/recentf"
check 'an identical file is logged as a duplicate' \
    grep -q "^DUP	$config/data/recentf	$state/recentf\$" "$run_dir/moves.tsv"
for name in bm-repository bmk-bmenu-state.el network-security.data nov-places \
    org-clock-save.el org-id-locations persistent-scratch places \
    prescient-save.el projectile-bookmarks.eld slime-history.eld tramp; do
    check "data/$name goes to state" grep -qx "state: $name" "$state/$name"
    check "data/$name does not go to data" test ! -e "$data/$name"
done
check 'the lsp session goes to state under its new name' \
    grep -qx 'state: lsp session' "$state/lsp-session-v1"
check 'transient history goes to state' test -f "$state/transient/history.el"
check 'cookies go to state' test -f "$state/url/cookies"
check 'auto-save index goes to state' test -f "$state/auto-save-list/.saves-1-host~"
check 'eshell history goes to state' test -f "$state/eshell/history"
check 'eshell lastdir goes to state' test -f "$state/eshell/lastdir"
check 'project list goes to state' test -f "$state/projects"
check 'frecency goes to state' test -f "$state/projectile-frecency.eld"
check 'multisession goes to state' test -f "$state/multisession/files/emoji/emoji--recent.value"
check 'cookie jar goes to state' test -f "$state/request/curl-cookie-jar"

# Data: what a person made or accumulated.
check 'a file the list does not know goes to data, dot file or not' \
    grep -qx 'a dot file' "$data/.hidden"
check 'the token file goes to data' test -f "$data/oauth2-auto.plist"
check 'saved transient values go to data' test -f "$data/transient/values.el"
check 'transient history does not go to data' test ! -e "$data/transient/history.el"
check 'persist goes to data' test -f "$data/persist/listen-queues"
check 'saved choices go to data' test -f "$data/mc-lists.el" -a ! -e "$state/mc-lists.el"
check 'grammars are installed things and go to data' \
    test -f "$data/tree-sitter/libtree-sitter-c.dylib" -a ! -e "$cache/tree-sitter"
check 'language servers are installed things and go to data' \
    test -f "$data/lsp/server" -a ! -e "$cache/lsp"
check 'downloaded artwork goes to data' \
    test -f "$data/emojis/set/1.png" -a ! -e "$cache/emojis"
check 'the object store goes to data' grep -qx 'a stored object' "$data/hash-store/ab/cdef"
check 'data that no entry names is untouched' grep -qx 'kept' "$data/keep.txt"

# Backups already live outside the checkout, under the data root.
check 'backups move from the data root to state' grep -qx 'a backup' "$state/backups/keep.txt"
check 'no backups directory is left under data' test ! -e "$data/backups"
check 'the move between roots is logged' \
    grep -q "^MV	$data/backups	$state/backups\$" "$run_dir/moves.tsv"

# Caches: what Emacs rebuilds.
check 'the note index goes to the cache' test -f "$cache/org-roam.db"
check 'the note index does not go to data' test ! -e "$data/org-roam.db"
check 'a journal left beside the note index goes with it' \
    test -f "$cache/org-roam.db-journal" -a ! -e "$data/org-roam.db-journal"
check 'the search index goes to the cache' test -f "$cache/xeft.db"
check 'native cache moves' test -f "$cache/eln-cache/31/x.eln"
check 'pcache moves' test -f "$cache/pcache/fonts"
check 'url cache from data/ moves' grep -qx 'cached c' "$cache/url/johnw/c"
check 'url cache from data/ does not go to state' test ! -e "$state/url/cache"
check 'the emptied data/.cache is not carried along' test ! -e "$data/.cache"
check 'stray url cache merges' test -f "$cache/url/johnw/b"
check 'projectile index moves' test -f "$cache/projectile.cache"
check 'stray cache file is untouched' test -f "$cache/tramp.abc"

attic=$run_dir/attic
check 'stale instance goes to the attic' test -f "$attic/data-MacPort/auto-save-list/.saves-2-host~"
check 'stray compiled file goes to the attic' test -f "$attic/data/mc-lists.elc"
check 'a file that no setting names goes to the attic' \
    test -f "$attic/data/workgroups" -a ! -e "$data/workgroups"
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
check 'state root is private' test "$(mode_of "$state")" = 700
check 'cache root is private' test "$(mode_of "$cache")" = 700
check 'run directory is private' test "$(mode_of "$run_dir")" = 700
check 'token file is private' test "$(mode_of "$data/oauth2-auto.plist")" = 600
check 'cookie jar is private' test "$(mode_of "$state/request/curl-cookie-jar")" = 600
check 'sync tokens are private' test "$(mode_of "$data/persist/org-gcal--sync-tokens")" = 600
check 'cookies are private' test "$(mode_of "$state/url/cookies")" = 600

check 'the archive holds the legacy history' \
    test "$(tar -xOf "$run_dir/pre-migration.tar" data/history)" = 'legacy history'
check 'the archive holds attic items' \
    test "$(tar -xOf "$run_dir/pre-migration.tar" '%backup%~')" = 'emergency backup'
check 'the archive holds each file once' \
    test -z "$(tar -tf "$run_dir/pre-migration.tar" | LC_ALL=C sort | uniq -d)"
check 'the archive leaves caches out' \
    test -z "$(tar -tf "$run_dir/pre-migration.tar" | grep -E '^(eln-cache|var/pcache)' || true)"
check 'the archive holds what was installed' \
    test -n "$(tar -tf "$run_dir/pre-migration.tar" | grep -x 'tree-sitter/libtree-sitter-c.dylib')"
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
    test "$original_data" = "$(snapshot "$data")"
# The move made one directory in the state root, for the transient history.
# A rollback leaves it there, empty.
check 'rollback restores every file in the state root' \
    test "$(grep -v '^D ' <<<"$original_state")" = \
    "$(snapshot "$state" | grep -v -e '^D ' -e ' \./migration/')"
check 'rollback leaves the cache root as it was' \
    test "$(cd "$cache" && find . -mindepth 1 | LC_ALL=C sort | tr '\n' ' ')" = './tramp.abc '
check 'rollback retires the log' test -f "$run_dir/moves.tsv.rolled-back"

# ------------------------------------- a rollback with something missing
# A moved directory has vanished since.  The rollback restores everything
# else, says what it could not restore, and keeps the log for another try.
home=$scratch/vanished
fixture "$home"
config=$home/.config/emacs
state=$home/.local/state/emacs
run_dir=$state/migration/run1
run "$home" --apply --prefer=source >/dev/null 2>&1
case $state in
"$scratch"/vanished/.local/state/emacs) rm -r "$state/request" ;;
esac
output=$(run "$home" --rollback "$run_dir" 2>&1)
status=$?
check 'a rollback that cannot restore everything exits non-zero' test "$status" -ne 0
check 'it names what it could not restore' \
    grep -q "^  lost   $config/request " <<<"$output"
check 'it restores everything else' \
    test -f "$config/data/history" -a -f "$config/eshell/history" -a -f "$config/persist/listen-queues"
check 'it keeps the log for another try' \
    test -f "$run_dir/moves.tsv" -a ! -e "$run_dir/moves.tsv.rolled-back"
output=$(run "$home" --rollback "$run_dir" 2>&1)
status=$?
check 'a second try reports the same loss and changes nothing else' \
    test "$status" -ne 0 -a -f "$config/data/history"

# -------------------------------------- backups in three places at once
# The checkout, the data root and the state root each hold a backups
# directory, and one file differs.  The clash must show in the preview and
# stop --apply before anything moves.
home=$scratch/backups
fixture "$home"
config=$home/.config/emacs
data=$home/.local/share/emacs
state=$home/.local/state/emacs
put "$config/data/backups/a" 'from the checkout'
put "$data/backups/b" 'already under data'
put "$state/backups/a" 'a different a'
rm "$state/history" "$state/recentf"
before=$(snapshot "$home")
output=$(run "$home" 2>&1)
check 'a clash between backups directories shows in the preview' \
    grep -q "^  clash  $config/data/backups/a <> $state/backups/a\$" <<<"$output"
output=$(run "$home" --apply 2>&1)
status=$?
check 'that clash stops apply before anything moves' \
    test "$status" -ne 0 -a "$before" = "$(snapshot "$home")"
preview=$(run "$home" --prefer=source 2>&1 | actions)
output=$(run "$home" --apply --prefer=source 2>&1)
status=$?
check 'apply with three backups directories exits 0' test "$status" -eq 0
check 'its preview printed the same actions' test "$preview" = "$(actions <<<"$output")"
check 'backups from the checkout arrive in state' \
    grep -qx 'from the checkout' "$state/backups/a"
check 'backups from the data root arrive in state' \
    test "$(cat "$state/backups/b")" = 'already under data' -a -f "$state/backups/keep.txt"
check 'no backups directory is left behind' \
    test ! -e "$data/backups" -a ! -e "$config/data"

# ------------------------------------------------- the destination wins
home=$scratch/destination
fixture "$home"
config=$home/.config/emacs
data=$home/.local/share/emacs
state=$home/.local/state/emacs
run_dir=$state/migration/run1
original=$(snapshot "$config")
preview=$(run "$home" --prefer=destination 2>&1 | actions)
output=$(run "$home" --apply --prefer=destination 2>&1)
status=$?
check 'apply with the destination preferred exits 0' test "$status" -eq 0
check 'its preview printed the same actions' \
    test "${preview//destination/X}" = "$(actions <<<"$output" | sed 's/destination/X/g')"
check 'the file at the destination stays' \
    grep -qx 'a history written by a premature start' "$state/history"
check 'the copy from the configuration directory is kept' \
    grep -qx 'legacy history' "$run_dir/collisions$config/data/history"
check 'everything else still moves' test -f "$data/oauth2-auto.plist" -a ! -e "$config/data"
output=$(run "$home" --rollback "$run_dir" 2>&1)
check 'rollback restores every name and its contents again' \
    test "$original" = "$(snapshot "$config")"
check 'rollback leaves the destination file alone' \
    grep -qx 'a history written by a premature start' "$state/history"

# ------------------------------------------------------------ a new host
# None of the three roots exists yet: the preview must still match.
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
check 'the state arrives' grep -qx 'legacy history' "$home/.local/state/emacs/history"
check 'the data arrives' test -f "$home/.local/share/emacs/oauth2-auto.plist"
check 'the caches arrive' test -f "$home/.cache/emacs/org-roam.db"

# ------------------------------------------ a clash inside a directory
# One file of a directory clashes; its sibling belongs to another root.
home=$scratch/inside
fixture "$home"
config=$home/.config/emacs
data=$home/.local/share/emacs
state=$home/.local/state/emacs
put "$state/transient/history.el" 'a newer history'
output=$(run "$home" 2>&1)
check 'a clash inside a directory is shown' \
    grep -q "^  clash  $config/data/transient/history.el <> $state/transient/history.el\$" <<<"$output"
check 'its sibling is still shown as moving' \
    grep -q "^  mv     $config/data/transient/values.el -> $data/transient/values.el\$" <<<"$output"
check 'the directory that holds the clashing file stays' \
    grep -q "^  stays  $config/data/transient (not empty)\$" <<<"$output"
check 'the directory is not moved whole with the clashing file in it' \
    test -z "$(grep "^  mv     $config/data/transient -> " <<<"$output")"
preview=$(run "$home" --prefer=source 2>&1 | actions)
output=$(run "$home" --apply --prefer=source 2>&1)
status=$?
check 'apply with a clash inside a directory exits 0' test "$status" -eq 0
check 'its preview printed the same actions' test "$preview" = "$(actions <<<"$output")"
check 'the clashing file arrives in state' grep -qx 'nil' "$state/transient/history.el"
check 'the copy that was there is kept' \
    grep -qx 'a newer history' "$state/migration/run1/collisions$state/transient/history.el"
check 'the sibling arrives in data' grep -qx 'values' "$data/transient/values.el"
check 'nothing is left of the directory' test ! -e "$config/data"

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
mkdir -p "$home/.local/state/emacs/migration/run9"
printf 'MV\t/nonexistent/a\t/nonexistent/b\n' >"$home/.local/state/emacs/migration/run9/moves.tsv"
refuses 'rollback refuses while Emacs runs' 'quit every Emacs' "$home" \
    --rollback "$home/.local/state/emacs/migration/run9"
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
for variable in XDG_DATA_HOME XDG_STATE_HOME XDG_CACHE_HOME; do
    before=$(snapshot "$home")
    output=$(sealed "$home" "$variable=$home/.config/emacs/data" "$migrate" --apply 2>&1)
    status=$?
    check "refuses $variable inside the configuration directory" \
        test "$status" -ne 0 -a "${output#*must lie outside}" != "$output"
    check "that refusal of $variable changes nothing" test "$before" = "$(snapshot "$home")"
done

# The three roots must be three separate directories.  With two of them in
# one place, a move between roots would find each file "already there".
home=$scratch/sameroot
fixture "$home"
ln -s "$home/.local/share" "$home/alias"
for pair in \
    "XDG_STATE_HOME=$home/.local/share" \
    "XDG_CACHE_HOME=$home/.local/share" \
    "XDG_CACHE_HOME=$home/.local/state" \
    "XDG_STATE_HOME=$home/alias" \
    "XDG_STATE_HOME=$home/.local/share/emacs/backups" \
    "XDG_DATA_HOME=$home/.local/state/emacs"; do
    before=$(snapshot "$home")
    output=$(sealed "$home" "$pair" "$migrate" --apply --prefer=source 2>&1)
    status=$?
    check "refuses ${pair%%=*} at or inside another root (${pair##*/})" \
        test "$status" -ne 0 -a "${output#*three separate directories}" != "$output"
    check "that refusal changes nothing (${pair##*/})" test "$before" = "$(snapshot "$home")"
    output=$(sealed "$home" "$pair" "$migrate" 2>&1)
    check "a preview refuses it as well (${pair##*/})" \
        test "$?" -ne 0 -a "${output#*three separate directories}" != "$output"
done

home=$scratch/notadir
fixture "$home"
put "$home/.local/state/emacs/migration" 'a file where the records go'
refuses 'a preview refuses a file where the migration records go' \
    'is not a directory' "$home"
refuses 'apply refuses it as well' 'is not a directory' "$home" --apply --prefer=source

home=$scratch/backuplink
fixture "$home"
mv "$home/.local/share/emacs/backups" "$home/elsewhere"
ln -s "$home/elsewhere" "$home/.local/share/emacs/backups"
refuses 'refuses a symbolic link in place of the backups directory' \
    'symbolic link' "$home" --apply --prefer=source

home=$scratch/backuptab
fixture "$home"
put "$home/.local/share/emacs/backups/odd$(printf '\t')name" 'x'
refuses 'refuses a tab in a name under the backups directory' \
    'tab or a newline' "$home" --apply --prefer=source

home=$scratch/oddname
fixture "$home"
put "$home/.config/emacs/data/odd$(printf '\t')name" 'x'
refuses 'refuses a name that holds a tab' 'tab or a newline' "$home" --apply

home=$scratch/slashes
fixture "$home"
output=$(sealed "$home" XDG_CONFIG_HOME="$home//.config/" "$migrate" 2>&1)
check 'repeated and trailing slashes in a root are dropped' \
    grep -q "^Configuration: $home/.config/emacs\$" <<<"$output"
output=$(sealed "$home" XDG_CONFIG_HOME="$home/.config/" \
    XDG_DATA_HOME="$home/.config//emacs/data" "$migrate" --apply 2>&1)
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
output=$(sealed "$home" XDG_DATA_HOME=relative/share XDG_STATE_HOME=relative/state \
    XDG_CACHE_HOME= "$migrate" 2>&1)
check 'a relative XDG_DATA_HOME falls back to the default' \
    grep -q "^Data:  *$home/.local/share/emacs\$" <<<"$output"
check 'a relative XDG_STATE_HOME falls back to the default' \
    grep -q "^State:  *$home/.local/state/emacs\$" <<<"$output"
check 'an empty XDG_CACHE_HOME falls back to the default' \
    grep -q "^Cache:  *$home/.cache/emacs\$" <<<"$output"
mkdir -p "$home/elsewhere"
output=$(sealed "$home" XDG_DATA_HOME="$home/elsewhere" \
    XDG_STATE_HOME="$home/elsewhere/state" "$migrate" 2>&1)
check 'an absolute XDG_DATA_HOME is honoured' \
    grep -q "^Data:  *$home/elsewhere/emacs\$" <<<"$output"
check 'an absolute XDG_STATE_HOME is honoured' \
    grep -q "^State:  *$home/elsewhere/state/emacs\$" <<<"$output"
check 'the migration records follow the state root' \
    grep -q "$home/elsewhere/state/emacs/migration/" <<<"$output"

# The variables of the shell that runs these tests must not reach the script.
home=$scratch/ambient
fixture "$home"
mkdir -p "$scratch/ambient-leak"
output=$(XDG_DATA_HOME=$scratch/ambient-leak XDG_STATE_HOME=$scratch/ambient-leak \
    XDG_CACHE_HOME=$scratch/ambient-leak XDG_CONFIG_HOME=$scratch/ambient-leak \
    run "$home" --apply --prefer=source 2>&1)
check 'XDG variables of the calling shell do not reach the script' \
    test -z "$(find "$scratch/ambient-leak" -mindepth 1 | head -n 1)" \
    -a -f "$home/.local/state/emacs/history"

printf '\n%d passed, %d failed\n' "$passed" "$failed"
[[ $failed -eq 0 ]]
```

- [x] **Step 2: Run the tests to verify they fail**

Run: `chmod +x xdg/migrate-test.sh && xdg/migrate-test.sh 2>/dev/null | tail -1`

Expected: `65 passed, 169 failed`. The script under test does not exist yet; the checks that pass hold vacuously, such as a configuration file staying where it is.

- [x] **Step 3: Write the mover**

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
# Each file goes to the root that fits what it is, as lisp/user-paths.el
# has it: data to $XDG_DATA_HOME/emacs, state to $XDG_STATE_HOME/emacs and
# caches to $XDG_CACHE_HOME/emacs.  Leftovers of packages that are gone go
# to an attic inside the run directory for a person to review.  Nothing is
# deleted, except a source file that is byte-identical to its destination
# and directories that the moves have emptied.
#
# Every rename is recorded in <state>/migration/<stamp>/moves.tsv, and a tar
# archive of every source inside the configuration directory that is not a
# cache is written there first; the old data/ directory goes into it whole.
# The backups directory, which is outside the checkout already, is only
# renamed.  The script is safe to run again: sources that are already gone
# are skipped.
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
STATE_DIR=$(xdg_home XDG_STATE_HOME "$HOME/.local/state")/emacs
CACHE_DIR=$(xdg_home XDG_CACHE_HOME "$HOME/.cache")/emacs
STAMP=${EMACS_XDG_STAMP:-$(date +%Y%m%d-%H%M%S)}
RUN_DIR=$STATE_DIR/migration/$STAMP

# KIND|SOURCE|DESTINATION.  SOURCE is relative to the configuration
# directory, or with the prefix `@data/' to the data root, for a file that
# already lives outside the checkout and only changes roots.  DESTINATION
# is relative to the root that KIND names: `data', `state', `cache', or
# `attic' (leftovers kept for review).  `prune' removes SOURCE if the
# moves above it left it empty.  Order matters: an entry that takes part
# of a directory must precede the entry that takes the rest.  The old init
# kept all three kinds under data/, so the entries for its state and its
# caches come first and `data|data|.' takes what is left, which includes
# any file this list does not know.  No entry may move anything into a
# directory that a later entry takes as its source: a preview sees only
# what is on disk there.  That is why data/backups has an entry of its own
# ahead of `data|data|.', which would otherwise put it into <data>/backups.
manifest() {
    cat <<'EOF'
cache|url/cache|url
prune|url|-
cache|data/url/cache|url
cache|data/projectile.cache|projectile.cache
cache|data/org-roam.db|org-roam.db
cache|data/org-roam.db-journal|org-roam.db-journal
cache|data/org-roam.db-wal|org-roam.db-wal
cache|data/org-roam.db-shm|org-roam.db-shm
cache|data/xeft.db|xeft.db
data|data/.cache/lsp|lsp
prune|data/.cache|-
attic|data/mc-lists.elc|data/mc-lists.elc
attic|data/workgroups|data/workgroups
state|data/.lsp-session-v1|lsp-session-v1
state|data/auto-save-list|auto-save-list
state|data/backups|backups
state|data/bm-repository|bm-repository
state|data/bmk-bmenu-state.el|bmk-bmenu-state.el
state|data/history|history
state|data/network-security.data|network-security.data
state|data/nov-places|nov-places
state|data/org-clock-save.el|org-clock-save.el
state|data/org-id-locations|org-id-locations
state|data/persistent-scratch|persistent-scratch
state|data/places|places
state|data/prescient-save.el|prescient-save.el
state|data/projectile-bookmarks.eld|projectile-bookmarks.eld
state|data/recentf|recentf
state|data/slime-history.eld|slime-history.eld
state|data/tramp|tramp
state|data/transient/history.el|transient/history.el
state|data/url|url
data|data|.
state|@data/backups|backups
attic|data-MacPort|data-MacPort
state|eshell/history|eshell/history
state|eshell/lastdir|eshell/lastdir
state|projects|projects
state|projectile-frecency.eld|projectile-frecency.eld
state|multisession|multisession
data|persist|persist
data|hash-store|hash-store
state|request|request
data|tree-sitter|tree-sitter
cache|eln-cache|eln-cache
data|emojis|emojis
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
prune|agent|-
EOF
}

# Files that hold tokens or cookies; they end up owner-only.
private_files() {
    cat <<EOF
$DATA_DIR/oauth2-auto.plist
$DATA_DIR/persist/org-gcal--sync-tokens
$STATE_DIR/request/curl-cookie-jar
$STATE_DIR/url/cookies
EOF
}

# Print directory $1 with the symbolic links in its existing part resolved,
# so that two spellings of one place compare equal.
physical() {
    local path=$1 rest='' base
    while [[ ! -d $path ]]; do
        rest=/${path##*/}$rest
        path=${path%/*}
        if [[ -z $path ]]; then
            path=/
        fi
    done
    base=$(cd -P -- "$path" && pwd -P) || die "cannot resolve $path"
    if [[ $base == / ]]; then
        base=''
    fi
    if [[ -z $base$rest ]]; then
        printf '/\n'
    else
        printf '%s%s\n' "$base" "$rest"
    fi
}

source_of() {
    case $1 in
    @data/*) printf '%s\n' "$DATA_DIR/${1#@data/}" ;;
    *) printf '%s\n' "$CONFIG_DIR/$1" ;;
    esac
}

destination_of() {
    local root
    case $1 in
    data) root=$DATA_DIR ;;
    state) root=$STATE_DIR ;;
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

# A preview without --prefer leaves each clashing source where it is.  HELD
# lists them, so that no later entry takes one of them, or a directory that
# holds one, to another root.
HELD=()

is_held() {
    local index=${#HELD[@]}
    while ((index > 0)); do
        index=$((index - 1))
        if [[ ${HELD[index]} == "$1" ]]; then
            return 0
        fi
    done
    return 1
}

holds_held() {
    local index=${#HELD[@]}
    while ((index > 0)); do
        index=$((index - 1))
        if [[ ${HELD[index]} == "$1"/* ]]; then
            return 0
        fi
    done
    return 1
}

# Succeed if --apply creates directory $1 before it moves anything.
made_first() {
    case $1 in
    "$DATA_DIR" | "$STATE_DIR" | "$CACHE_DIR" | "$STATE_DIR/migration" | "$RUN_DIR" | "$RUN_DIR/attic")
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

# Succeed if $1 and $2 are one file or directory under two names.
same_place() {
    local first
    resolve "$1" || return 1
    first=$RESOLVED
    resolve "$2" || return 1
    [[ $first -ef $RESOLVED ]]
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
    # One place under two names: there is nothing to move, and a file must
    # never be taken for a duplicate of itself.
    if same_place "$src" "$dest"; then
        return 0
    fi
    if is_held "$src"; then
        return 0
    fi
    if ! present "$dest" && ! holds_held "$src"; then
        rename_to "$src" "$dest"
        return 0
    fi
    # Both are directories, or the source holds a file that has to stay:
    # go child by child, then drop the source if that emptied it.
    if is_directory "$src" && { ! present "$dest" || is_directory "$dest"; }; then
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
        HELD+=("$src")
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
    local legacy running kind src odd index other
    local -a roots=("$CONFIG_DIR" "$DATA_DIR" "$STATE_DIR" "$CACHE_DIR")
    local -a real=()
    [[ -d $CONFIG_DIR ]] || die "no configuration directory at $CONFIG_DIR"
    [[ -f $CONFIG_DIR/init.org ]] ||
        die "$CONFIG_DIR does not look like the Emacs checkout (no init.org)"
    for legacy in "$HOME/.emacs.d" "$HOME/.emacs" "$HOME/.emacs.el"; do
        if [[ -e $legacy || -L $legacy ]]; then
            die "$legacy exists and would outrank $CONFIG_DIR at startup; move it away first"
        fi
    done
    for src in "${roots[@]}" "$STATE_DIR/migration" "$RUN_DIR"; do
        if [[ (-e $src || -L $src) && ! -d $src ]]; then
            die "$src is not a directory"
        fi
    done
    # Compare the roots as places, not as strings: one of them may be
    # reached through a symbolic link.
    for src in "${roots[@]}"; do
        real+=("$(physical "$src")")
    done
    for index in 1 2 3; do
        if inside "${real[index]}" "${real[0]}" || inside "${real[0]}" "${real[index]}"; then
            die "the data, state and cache roots must lie outside the configuration directory; ${roots[index]} does not"
        fi
        for other in 1 2 3; do
            if [[ $other -gt $index ]] &&
                { inside "${real[index]}" "${real[other]}" || inside "${real[other]}" "${real[index]}"; }; then
                die "the data, state and cache roots must be three separate directories; ${roots[index]} and ${roots[other]} are not"
            fi
        done
    done
    while IFS='|' read -r kind src _; do
        src=$(source_of "$src")
        if [[ -L $src ]]; then
            die "$src is a symbolic link; resolve it by hand first"
        fi
        # The log holds one tab-separated record per line.
        if [[ -d $src ]]; then
            odd=$(find "$src" \( -name $'*\t*' -o -name $'*\n*' \) -print | head -n 1)
            if [[ -n $odd ]]; then
                die "a name under $src contains a tab or a newline; rename it first"
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
    local kind src dest other covered
    local -a candidates=() sources=()
    # Only what is in the checkout is archived.  A source under `@data/'
    # never matches here: it is outside the checkout already, and the move
    # only renames it.
    while IFS='|' read -r kind src dest; do
        if [[ $kind == data || $kind == state || $kind == attic ]] &&
            [[ -e $CONFIG_DIR/$src || -L $CONFIG_DIR/$src ]]; then
            candidates+=("$src")
        fi
    done < <(manifest)
    # A source inside a directory that is archived whole would go in twice.
    for src in ${candidates[@]+"${candidates[@]}"}; do
        covered=0
        for other in "${candidates[@]}"; do
            if [[ $src == "$other"/* ]]; then
                covered=1
            fi
        done
        if [[ $covered == 0 ]]; then
            sources+=("$src")
        fi
    done
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
            prune_entry "$(source_of "$src")"
        else
            move_entry "$(source_of "$src")" "$(destination_of "$kind" "$dest")"
        fi
    done < <(manifest)
}

migrate() {
    local file
    preflight
    printf 'Configuration: %s\nData:          %s\nState:         %s\nCache:         %s\n' \
        "$CONFIG_DIR" "$DATA_DIR" "$STATE_DIR" "$CACHE_DIR"
    if [[ $APPLY == 1 ]]; then
        # Rehearse first: a conflict must stop the run before anything moves.
        APPLY=0
        walk_manifest >/dev/null
        APPLY=1
        VIRT_FROM=()
        VIRT_TO=()
        HELD=()
        if [[ $CONFLICTS -gt 0 && -z $PREFER ]]; then
            die "$CONFLICTS destinations already hold a different file; preview to see them, then add --prefer=source or --prefer=destination"
        fi
        CONFLICTS=0
        mkdir -p "$DATA_DIR" "$STATE_DIR" "$CACHE_DIR" "$RUN_DIR/attic"
        chmod 700 "$DATA_DIR" "$STATE_DIR" "$CACHE_DIR" "$RUN_DIR"
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
    local run=$1 log line op first second lost=0
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
                printf '  lost   %s (neither it nor %s exists)\n' "$first" "$second"
                lost=$((lost + 1))
                continue
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
            if [[ ! -e $second && ! -L $second ]]; then
                printf '  lost   %s (neither it nor %s exists)\n' "$first" "$second"
                lost=$((lost + 1))
                continue
            fi
            mkdir -p "$(dirname "$first")"
            cp -p -- "$second" "$first"
            printf '  copy   %s -> %s\n' "$second" "$first"
            ;;
        *) die "unreadable line in $log: $line" ;;
        esac
    done < <(awk '{ line[NR] = $0 } END { for (i = NR; i > 0; i--) print line[i] }' "$log")
    if [[ $lost -gt 0 ]]; then
        printf 'Rolled back, except for the %d marked "lost": neither the moved file\n' "$lost"
        printf 'nor its original exists.  The archive in %s may hold them.\n' "$run"
        printf 'The log stays in place, so this can be run again.\n'
        exit 1
    fi
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

- [x] **Step 4: Run the tests to verify they pass**

Run: `chmod +x xdg/migrate.sh && xdg/migrate-test.sh | tail -1`

Expected: `234 passed, 0 failed`

- [x] **Step 5: Run the tests under the system bash**

Putting `/usr/bin` and `/bin` first makes `env bash` in the script find the system bash as well, together with the system's `tar`, `find`, `mv`, `cp` and `rm`, which differ from the GNU tools that Nix puts on `PATH`.

Run: `PATH="/usr/bin:/bin:$PATH" /bin/bash xdg/migrate-test.sh 2>/dev/null | tail -1`

Expected: `234 passed, 0 failed`

- [x] **Step 6: Lint both scripts**

Run: `shellcheck xdg/migrate.sh xdg/migrate-test.sh; echo "exit=$?"`

Expected: `exit=0` and no other output.

- [x] **Step 7: Preview the move on the real tree**

A preview reads and prints; it changes nothing.

Run: `xdg/migrate.sh >/tmp/emacs-xdg-preview.txt 2>&1; echo "exit=$?"; grep -E '^  (clash|stays)' /tmp/emacs-xdg-preview.txt; head -3 /tmp/emacs-xdg-preview.txt; tail -8 /tmp/emacs-xdg-preview.txt`

Expected, with `<stamp>` a date and time:

```text
exit=0
migrate: Emacs is running:
/Applications/Emacs.app/Contents/MacOS/Emacs
migrate: this preview can go stale; --apply will refuse until Emacs has quit
  mv     /Users/johnw/.config/emacs/gptel-agent -> /Users/johnw/.local/state/emacs/migration/<stamp>/attic/gptel-agent
  mv     /Users/johnw/.config/emacs/.lsp-session-v1 -> /Users/johnw/.local/state/emacs/migration/<stamp>/attic/.lsp-session-v1
  mv     /Users/johnw/.config/emacs/.org-generic-id-locations -> /Users/johnw/.local/state/emacs/migration/<stamp>/attic/.org-generic-id-locations
  mv     /Users/johnw/.config/emacs/anvil-worker.log -> /Users/johnw/.local/state/emacs/migration/<stamp>/attic/anvil-worker.log
  mv     /Users/johnw/.config/emacs/%backup%~ -> /Users/johnw/.local/state/emacs/migration/<stamp>/attic/%backup%~
  rmdir  /Users/johnw/.config/emacs/agent
Left in /Users/johnw/.config/emacs, neither tracked nor expected:
Done.
```

The three `migrate:` lines say that Emacs is running; that is expected here. The whole preview at the time of writing is in Appendix C. Three things must hold: `exit=0`, no `clash` or `stays` line, and nothing listed between `Left in` and `Done.`

- [x] **Step 8: Remove the earlier script**

`migrate-emacs-xdg.sh` was written for a checkout at `~/src/dot-emacs` exposed as `~/.emacs.d`. It was never run. On the current layout it stops at its first check, and its embedded patches no longer apply.

Run: `git rm migrate-emacs-xdg.sh`

Expected: `rm 'migrate-emacs-xdg.sh'`

- [x] **Step 9: Commit**

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

- [x] **Step 1: Write the failing tests**

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
    emojis/set/1.png gptel-agent/sessions.db '%backup%~' .lsp-session-v1 \
    tramp network-security.eld .org-id-locations history recentf bookmarks \
    places ido.last ielm-history.eld org-clock-save.el elpa/archives/x \
    package-quickstart.el server/server; do
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

- [x] **Step 2: Run the tests to verify they fail**

Run: `chmod +x xdg/check-litter-test.sh && xdg/check-litter-test.sh | tail -1`

Expected: `0 passed, 38 failed`

- [x] **Step 3: Write the report**

Create `xdg/check-litter.sh`:

```bash
#!/usr/bin/env bash
# check-litter.sh --- report Emacs runtime state that is back in the checkout
#
# Usage: xdg/check-litter.sh [CHECKOUT]
#
# Data, state and caches belong under $XDG_DATA_HOME/emacs,
# $XDG_STATE_HOME/emacs and $XDG_CACHE_HOME/emacs; see lisp/user-paths.el.
# .gitignore hides most of the places a package would litter, so that a
# stray cookie jar is never committed by accident.  This script is what
# makes such litter visible.  It lists
#
#   - ~/.emacs.d, ~/.emacs and ~/.emacs.el, any of which makes Emacs
#     ignore this checkout altogether;
#   - every ignored path in the checkout that is not known configuration
#     or a build product;
#   - every empty directory at the top of the checkout.
#
# An Emacs started with -Q or -q reads no init file and writes to the
# built-in defaults, so an auto-save-list/, transient/ or url/ directory,
# or a file such as tramp, bookmarks or network-security.eld, can appear
# here after such a run; delete it.  eln-cache/ appears for the same
# reason, cannot be prevented, and is not reported.
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

- [x] **Step 4: Add the safety-net ignore rules**

The test copies the checkout's `.gitignore`, so the rules come before the test can pass. The block below begins with an empty line, which is part of it. Append to `.gitignore`:

```gitignore

# Data, state and caches live under $XDG_DATA_HOME/emacs,
# $XDG_STATE_HOME/emacs and $XDG_CACHE_HOME/emacs (lisp/user-paths.el).
# The rules in this file for such paths are a safety net: an Emacs started
# with -Q still writes to its built-in defaults here, and `git add -A' must
# never pick that up.  `make check-litter' shows what these rules hide.
/auto-save-list/
/multisession/
/projects.eld
/tree-sitter/
/%backup%~
/.org-id-locations
/bookmarks
/bookmarks.eld
/elpa/
/history
/ido.last
/ielm-history.eld
/network-security.data
/network-security.eld
/org-clock-save.el
/package-quickstart.el
/places
/places.eld
/recentf
/recentf.eld
/server/
/tramp
```

The first four and the last seventeen are names that Emacs's built-in defaults give to files in the init directory; `%backup%~` is the one leftover with a name no pattern caught. An ignored file is exactly what `xdg/check-litter.sh` reports, so each rule also makes its file visible to `make check-litter`.

- [x] **Step 5: Run the tests to verify they pass**

Run: `chmod +x xdg/check-litter.sh && xdg/check-litter-test.sh | tail -1 && shellcheck xdg/check-litter.sh xdg/check-litter-test.sh; echo "exit=$?"`

Expected:

```text
38 passed, 0 failed
exit=0
```

- [x] **Step 6: Add the make targets**

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
# Data, state and caches live outside this checkout; see lisp/user-paths.el.

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

- [x] **Step 7: Describe the layout in the README**

In `README.md`, after the paragraph that ends on line 8 with ``source before rebuilding `init.el`.``, add a blank line and this paragraph:

```markdown
Only configuration lives in this checkout. What Emacs writes while it runs
goes to one of three places, by what it is: data (saved choices, tokens,
tree-sitter grammars) under `$XDG_DATA_HOME/emacs`, state (histories,
recent files, sessions, backups) under `$XDG_STATE_HOME/emacs`, and caches
under `$XDG_CACHE_HOME/emacs`. `lisp/user-paths.el` defines the three roots
and `early-init.el` loads it first. Run `make check-litter` to see whether
anything has crept back.
```

- [x] **Step 8: Run every test through make**

Run: `make test-xdg 2>&1 | grep -E 'Ran |passed, '`

Expected:

```text
Ran 17 tests, 17 results as expected, 0 unexpected (...)
Ran 7 tests, 7 results as expected, 0 unexpected (...)
234 passed, 0 failed
38 passed, 0 failed
```

- [x] **Step 9: Run the report on the worktree and on the real checkout**

Run: `make check-litter`

Expected: `No litter in <WT>`

Run: `xdg/check-litter.sh ~/.config/emacs; echo "exit=$?"`

Expected: `exit=1` and, above it, the state the cutover removes: 22 lines at the time of writing, from `/Users/johnw/.config/emacs/%backup%~` to `/Users/johnw/.config/emacs/hash-store (empty directory)`. Appendix C has the list. After Task 7 this command must print `No litter in /Users/johnw/.config/emacs`.

- [x] **Step 10: Commit**

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

- [x] **Step 1: Run the unit tests**

Run: `make test-xdg 2>&1 | grep -E 'Ran |passed, |FAILED'`

Expected: the four lines of Task 5 Step 8, and no `FAILED`.

- [x] **Step 2: Run the audit against today's init.org**

Run: `make audit-xdg; echo "exit=$?"`

Expected: `PASS` and `exit=0`. If it reports an offender or a failed form, follow Task 3 Step 7, commit the fix, and run this step again.

- [x] **Step 3: Check the edits against today's init.org**

Run: `emacs --batch -Q -l xdg/apply-init-edits.el -f xdg-init-edits-batch --check ~/org/init.org; echo "exit=$?"`

Expected: 26 `pending` lines and `exit=0`. For an `ERROR`, follow Task 2 Step 5.

- [x] **Step 4: Save the preview of the move**

Run: `xdg/migrate.sh >/tmp/emacs-xdg-preview-clio.txt 2>&1; echo "exit=$?"; grep -c '^  ' /tmp/emacs-xdg-preview-clio.txt; grep -E '^  (clash|stays)' /tmp/emacs-xdg-preview-clio.txt; sed -n '/^Left in /,/^Done\./p' /tmp/emacs-xdg-preview-clio.txt`

Expected: `exit=0`; a count near 47; no `clash` or `stays` line; and

```text
Left in /Users/johnw/.config/emacs, neither tracked nor expected:
Done.
```

A `clash` line is a different file that already exists at a destination. A name between `Left in` and `Done.` is something in the checkout that this plan does not know. Report either to John before going on.

- [x] **Step 5: Check that the merge will not collide with work in progress**

Run:

```bash
comm -12 <(git -C ~/.config/emacs diff --name-only HEAD...xdg-layout | sort) \
         <(git -C ~/.config/emacs status --porcelain | cut -c4- | sort)
```

Expected: no output. A name here is a file that this branch changes and that also has uncommitted changes in the main checkout. Tell John.

- [x] **Step 6: Push the branch**

This keeps a copy of the branch off Clio until the cutover. Hera never fetches it: Hera receives the work through `master` in Task 8, and Task 10 Step 5 deletes the remote branch.

Run: `git push -u origin xdg-layout`

Expected: `branch 'xdg-layout' set up to track 'origin/xdg-layout'.`

- [x] **Step 7: Report to John and wait**

Give John the results of Steps 1 to 5, the file `/tmp/emacs-xdg-preview-clio.txt`, and these questions. Do not start Task 7 without his answers.

1. Do the departures in Appendix B stand? The ones that matter: tree-sitter grammars go to the data root, as installed things, where the report said cache; `emojis/` goes there too, as downloaded artwork, where the report kept it with the configuration; `org-roam.db` goes to the cache root, as an index that Emacs rebuilds; `backups/` moves from the data root to state; cookies and the transient history go to state, not to the cache; saved transient values stay under data, though their author files them as configuration; dead leftovers go to an attic.
2. In ChronoSync, does the task `Home` include `.local/share/emacs`, `.local/state/emacs` and `.cache`? State is the per-host kind in the XDG text. Should Hera and Clio go on sharing history files as they do today? Task 9 sets the rule.
3. Can Hera be reached now, and is Emacs closed there? Tasks 7 and 8 belong in one sitting.

---

### Task 7: Cutover on Clio

**John runs this, or is present while an agent does.** It takes about twenty minutes. Do Task 8 in the same sitting. From Step 7 until Task 8 is done, do not start Emacs on Hera: the new `init.org` arrives there at once, and Hera's state has not moved yet.

The order matters. The new init goes in first and is built once on purpose while the old state is still in place, so that it stops at its guard (Step 8). From then on an Emacs started by mistake stops loading its init at the same error, where the old init would have started on empty history and written new files. `early-init.el` has by then pointed a few histories at the new roots; Step 9 says how to settle anything such a start writes there.

**Files:**
- Modify: `~/org/init.org` (26 edits, by `xdg/apply-init-edits.el`)
- Modify: `~/.config/emacs/init.org`, `~/.config/emacs/init.el` (by `make`)
- Move: everything in the Task 4 table

**Interfaces:**
- Consumes: the branch `xdg-layout` with Tasks 1 to 5; John's go from Task 6.
- Produces: Clio running on the new layout; `master` holding the branch; the run directory under `~/.local/state/emacs/migration/`.

- [x] **Step 1: Pause ChronoSync**

In ChronoSync on Clio, suspend the schedule of the task `Home` and confirm that no run is in progress. While it runs it would copy Hera's `data/` back, or delete Hera's while Emacs there still uses it.

- [x] **Step 2: Quit Emacs on Clio and on Hera**

Quit both. Until Step 12, do not start Emacs on Clio, and stop anything else that runs `make` or `emacs` in this checkout, such as another agent's session.

Then on each host run the test the mover itself uses:

```bash
ps -u "$(id -u)" -o comm= |
  awk -F/ '$NF ~ /^(Emacs|emacs|emacs-[0-9][0-9.]*|\.emacs-wrapped)$/'
```

Expected: no output.

- [x] **Step 3: Find the worktree**

Run: `WT=~/src/emacs-xdg-layout; ls "$WT/xdg/migrate.sh"`

Expected: the file name. Later steps use `$WT`; set it again in a new shell.

- [x] **Step 4: Preview once more, now that Emacs has quit**

Run: `"$WT/xdg/migrate.sh" 2>&1 | grep -E '^  (clash|keep|stays)|^migrate:'; "$WT/xdg/migrate.sh" 2>&1 | sed -n '/^Left in /,/^Done\./p'`

Expected: no `clash`, `keep`, `stays` or `migrate:` line, then

```text
Left in /Users/johnw/.config/emacs, neither tracked nor expected:
Done.
```

- [x] **Step 5: Keep a copy of init.org, and note where master is**

```bash
mkdir -p ~/.local/state/emacs/migration
cp -p ~/org/init.org ~/.local/state/emacs/migration/init.org.before-xdg
PRE=$(git -C ~/.config/emacs rev-parse HEAD); echo "$PRE"
```

Expected: a commit hash. Write it down: the rollback at the end of this task needs it, and the copy. The copy sits beside the records the mover will write, so that Task 10 removes them together.

- [x] **Step 6: Bring the branch into master**

```bash
comm -12 <(git -C ~/.config/emacs diff --name-only HEAD...xdg-layout | sort) \
         <(git -C ~/.config/emacs status --porcelain | cut -c4- | sort)
git -C ~/.config/emacs merge --ff-only xdg-layout
ls ~/.config/emacs/early-init.el ~/.config/emacs/xdg/migrate.sh
```

Expected: nothing from `comm`; then `Updating <old>..<new>`, `Fast-forward` and a list of files; then the two file names.

If `comm` prints a name, that file has uncommitted changes and the branch changes it too. Commit that change or set it aside before merging.

If git answers that the branches have diverged and it cannot fast-forward, `master` has moved since the branch was cut. In `$WT` run `git rebase master`, then `make test-xdg`, then repeat this step.

- [x] **Step 7: Apply the 26 edits to the canonical init.org**

Run: `emacs --batch -Q -l ~/.config/emacs/xdg/apply-init-edits.el -f xdg-init-edits-batch ~/org/init.org; echo "exit=$?"`

Expected: 26 lines that begin with `applied`, and `exit=0`.

- [x] **Step 8: Build init.el once; it must stop at the guard**

This copies the canonical file into the checkout, tangles `init.el`, and loads it in batch. The load must fail, because the state has not moved yet.

Run: `make -C ~/.config/emacs init.el 2>&1 | grep -E 'Emacs state is still in|\*\*\*'; ls -l ~/.config/emacs/init.el`

Expected: a line that contains `Emacs state is still in /Users/johnw/.config/emacs/data; quit Emacs and run /Users/johnw/.config/emacs/xdg/migrate.sh --apply`, a line from make that ends in `Error 255`, and a new `init.el`.

If make succeeds instead, there is no `~/.config/emacs/data` on this host. Stop and find out why before going on.

- [x] **Step 9: Move the files**

Run: `~/.config/emacs/xdg/migrate.sh --apply 2>&1 | tee /tmp/emacs-xdg-apply-clio.txt | tail -4`

Expected:

```text
  mv     /Users/johnw/.config/emacs/%backup%~ -> /Users/johnw/.local/state/emacs/migration/<stamp>/attic/%backup%~
  rmdir  /Users/johnw/.config/emacs/agent
Left in /Users/johnw/.config/emacs, neither tracked nor expected:
Done.
```

Then: `RUN=$(sed -n 's/^Moving; the log is \(.*\)\/moves.tsv$/\1/p' /tmp/emacs-xdg-apply-clio.txt); echo "$RUN"; ls "$RUN"`

Expected: a directory `/Users/johnw/.local/state/emacs/migration/<stamp>` containing `attic`, `moves.tsv` and `pre-migration.tar`.

If the script instead refuses with `destinations already hold a different file`, Emacs was started after Step 6. `early-init.el` sent a few of its histories to the new roots, even where the guard then stopped the init. The copies in the configuration directory are the real ones: run the command again with `--apply --prefer=source`.

- [x] **Step 10: Confirm that the state arrived**

Run: `ls -d ~/.config/emacs/data 2>&1; ls ~/.local/share/emacs; ls ~/.local/state/emacs; ls ~/.cache/emacs`

Expected: `No such file or directory` for the first. Then three listings:

- data, which includes `emojis hash-store mc-lists.el oauth2-auto.plist persist transient tree-sitter` and no longer has `backups`;
- state, which includes `auto-save-list backups bm-repository eshell history migration multisession network-security.data org-id-locations persistent-scratch places prescient-save.el projectile-bookmarks.eld projectile-frecency.eld projects recentf request tramp transient url`;
- cache, which includes `eln-cache org-roam.db pcache url`.

A history file under data, `backups` still under data, or `org-roam.db` anywhere but the cache, means the mover and the init disagree. Stop and compare the Task 4 table with the listing.

- [x] **Step 11: Build init.el again; now it must succeed**

`-B` makes `make` rebuild a file it considers up to date.

Run: `make -C ~/.config/emacs -B init.el; echo "exit=$?"; ls -l ~/.config/emacs/init.el`

Expected: `exit=0`, and `init.el` with mode `-r--r--r--` and the current time.

- [x] **Step 12: Start Emacs**

Start Emacs the usual way.

- [x] **Step 13: Check the paths in the running session**

Run:

```bash
emacsclient -s /tmp/johnw-emacs/server --eval \
  '(list user-data-directory user-state-directory user-cache-directory
         (car native-comp-eln-load-path)
         savehist-file (cdar backup-directory-alist)
         transient-history-file transient-values-file
         user-paths-tree-sitter-directory
         (bound-and-true-p org-roam-db-location) url-cache-directory)'
```

Expected:

```text
("/Users/johnw/.local/share/emacs/" "/Users/johnw/.local/state/emacs/" "/Users/johnw/.cache/emacs/" "/Users/johnw/.cache/emacs/eln-cache/" "/Users/johnw/.local/state/emacs/history" "/Users/johnw/.local/state/emacs/backups" "/Users/johnw/.local/state/emacs/transient/history.el" "/Users/johnw/.local/share/emacs/transient/values.el" "/Users/johnw/.local/share/emacs/tree-sitter/" "/Users/johnw/.cache/emacs/org-roam.db" "/Users/johnw/.cache/emacs/url/")
```

A `nil` in the tenth place only means that org-roam has not loaded yet; open a note and run the command again.

- [x] **Step 14: Scan the running session for stray paths**

Run:

```bash
emacsclient -s /tmp/johnw-emacs/server --eval \
  '(progn (load "~/.config/emacs/xdg/audit/audit.el" nil t)
          (xdg-audit-offenders user-emacs-directory))'
```

Expected: `nil`. A variable that only records which buffers or projects the session has visited is not an offender. For anything else, apply the three rules of Task 3 Step 7, commit, and restart Emacs.

- [x] **Step 15: Check the checkout**

Run: `make -C ~/.config/emacs check-litter`

Expected: `No litter in /Users/johnw/.config/emacs`

- [ ] **Step 16: Use it**

John checks, in Emacs: `M-x` offers earlier commands; the recent-files list is populated; `org-roam-node-find` finds notes; `M-p` in a new eshell recalls earlier commands; a magit transient opens. Then:

Run: `emacsclient -s /tmp/johnw-emacs/server --eval "(treesit-language-available-p 'python)"`

Expected: `t`

One change to expect: transient now reads the values it saved. `~/.local/share/emacs/transient/values.el` dates from August 2025 and has not been read since, so a transient command may show a default that was saved then.

- [x] **Step 17: Commit and push**

The commit of `init.org` carries whatever else changed in the canonical file since it was last copied here, as every such commit does.

`git status` now shows `multisession/files/emoji/emoji--recent.value` as deleted, because the mover took it to the state root. Leave that uncommitted until Task 9, and do not run `changes` on this checkout before Task 8 is done. Hera must pull a `master` that still tracks the file, or the pull would delete Hera's copy before Hera's mover has moved it.

```bash
git -C ~/.config/emacs add init.org
git -C ~/.config/emacs commit -m "init: Keep state and caches out of the configuration directory"
git -C ~/.config/emacs push
```

Expected: the push reports `master -> master`.

**Rollback, if a step from 6 to 16 fails and cannot be fixed on the spot.** Do it before Step 17. If Step 17 has already pushed, do not reset `master`; fix forward.

```bash
# Quit Emacs first.  Set WT as in Step 3, and PRE to the hash Step 5 printed.
for log in $(ls -d ~/.local/state/emacs/migration/*/moves.tsv 2>/dev/null | sort -r); do
  "$WT/xdg/migrate.sh" --rollback "$(dirname "$log")"
done
cp ~/.local/state/emacs/migration/init.org.before-xdg ~/org/init.org
git -C ~/.config/emacs reset --keep "$PRE"
make -C ~/.config/emacs -B init.el
```

The loop undoes every run of the mover, newest first, and does nothing if Step 9 never ran. Each run puts its files back where they were. If one stops with `cannot undo: ... exists`, a file has come back at its old path: move that file away and run the loop again. The copy is made without `-p` on purpose: the restored `init.org` must be newer than the checkout's copy, or `make` will not take it. `reset --keep` moves `master` back and leaves uncommitted work alone. The order matters: the mover has to restore the tracked file under `multisession/` before git looks at it. What the rollback leaves behind, on purpose: file modes that the move tightened stay tight; directories that the new init or the move created under the three roots stay, empty; and `~/.local/state/emacs/migration` stays, with the copy of `init.org` and each run's archive and retired log, as the record of the attempt. A file that Emacs wrote for the first time after Step 12, at a path the mover never touched, also stays under the new roots, where the old init does not look: check the three roots before deleting anything there. Then resume ChronoSync, which Step 1 paused.

This sequence was rehearsed in a scratch home with the real mover and the real Makefile, without an Emacs running in between. It ended with the checkout, `git status` and every file the mover had moved exactly as they began, the `backups/` directory included.

---

### Task 8: Cutover on Hera

**John runs this**, in the same sitting as Task 7, with ChronoSync still paused and Emacs closed on Hera. All commands run on Hera. Nothing about Hera could be checked while this plan was written, so each step says what to do when Hera differs.

Hera can only go forward. The edited `init.org` reaches Hera through Syncthing, and its guard refuses to start while `~/.config/emacs/data` exists, so `xdg/migrate.sh --rollback` on Hera leaves an Emacs that will not start. If a step here fails, fix it here and run `--apply` again. To recover one file, take it from `migration/<stamp>/pre-migration.tar` or follow its line in `moves.tsv`; do not roll the run back.

**Files:** the same as Task 7, on Hera. `~/org/init.org` is already edited: Syncthing delivered it.

**Interfaces:**
- Consumes: `master` as pushed in Task 7 Step 17.
- Produces: Hera running on the new layout.

- [x] **Step 1: Check for a legacy init directory**

Run: `ls -d ~/.emacs.d ~/.emacs ~/.emacs.el 2>&1`

Expected: three lines ending in `No such file or directory`. If one exists, stop: Emacs on Hera uses it instead of `~/.config/emacs`. Find out why it is there before moving anything. A `~/.emacs.d` is the likeliest of the three: a README in `lisp/` still gives `/ssh:hera:/Users/johnw/.emacs.d/lisp/` as the place of the sources on Hera. If `ls -l ~/.emacs.d` shows a symbolic link to `~/.config/emacs`, it is a leftover of the old layout: remove the link, and run this step again.

- [x] **Step 2: Bring the checkout up to date**

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

- [x] **Step 3: Confirm that the edited init.org has arrived**

Run: `emacs --batch -Q -l xdg/apply-init-edits.el -f xdg-init-edits-batch --check ~/org/init.org; echo "exit=$?"`

Expected: 26 lines that begin with `done`, and `exit=0`. Lines that say `pending` mean Syncthing has not delivered the file yet. Wait for it. Do not apply the edits here: two hosts editing the same file make a Syncthing conflict.

- [x] **Step 4: Build init.el once; it must stop at the guard**

Run: `rm -f init.org; make init.el 2>&1 | grep -E 'Emacs state is still in|\*\*\*'`

Expected: the same two lines as in Task 7 Step 8, with Hera's paths.

`init.org` in the checkout is a copy that `make` writes, and `make` replaces it only when the canonical file is newer. The pull in Step 2 has just written the copy, so it is the newer of the two; removing it makes `make` take the canonical file that Step 3 checked.

If make succeeds, Hera has no `~/.config/emacs/data`. It had one before the cutover: ChronoSync reported conflicts on its `recentf`. So the pause did not hold, and ChronoSync has carried Clio's deletion here. Stop, and do not start Emacs on Hera. Run `ls ~/.local/state/emacs/migration`: a run directory from Clio, or `init.org.before-xdg`, proves that ChronoSync ran after the pause. Look in ChronoSync's archive on both hosts for Hera's `data/` directory and put it back at `~/.config/emacs/data`, then run this step again.

- [x] **Step 5: Preview**

Run: `xdg/migrate.sh 2>&1 | tee /tmp/emacs-xdg-preview-hera.txt | grep -E '^  (clash|stays)|^migrate:'; sed -n '/^Left in /,/^Done\./p' /tmp/emacs-xdg-preview-hera.txt`

Expected: Hera's list differs from Clio's in its details. Read each name between `Left in` and `Done.` before going on.

A `clash` line means a destination already holds a different file. ChronoSync was paused before Clio's files moved, so this should not happen. If it does, either the pause did not hold and Clio's moved state has reached Hera, or the new init ran on Hera early. Stop and check ChronoSync before going on. Then John chooses, for all of them at once: `--prefer=source` puts Hera's own file in place, and `--prefer=destination` keeps the one that is there. The other copy is kept under `migration/<stamp>/collisions/` either way. Hera's own files are what Emacs on Hera last saw, so `--prefer=source` changes least.

- [x] **Step 6: Move the files**

Run: `xdg/migrate.sh --apply 2>&1 | tee /tmp/emacs-xdg-apply-hera.txt | tail -3`, adding the preference chosen in Step 5 if there was a `clash` line.

Expected: the last line is `Done.`

- [x] **Step 7: Build again and start**

Run: `make -B init.el; echo "exit=$?"`

Expected: `exit=0`. Then start Emacs.

- [x] **Step 8: Verify**

Run Task 7 Steps 10, 13, 14, 15 and 16 on Hera. Step 10's lists of names will differ in detail. What must hold is the same: no `~/.config/emacs/data`, no `backups` under `~/.local/share/emacs`, and `org-roam.db` only under `~/.cache/emacs`.

---

### Task 9: Resume sync

**John runs this.**

**Files:**
- Untrack: `multisession/files/emoji/emoji--recent.value`

**Interfaces:**
- Consumes: both hosts on the new layout.
- Produces: ChronoSync running with rules that fit the layout; `master` no longer tracking the runtime file.

- [x] **Step 1: Record that the runtime file is no longer tracked**

Both movers have taken `multisession/` to the state root, so the file can leave the index. On Clio:

```bash
git -C ~/.config/emacs rm -q --cached multisession/files/emoji/emoji--recent.value
git -C ~/.config/emacs commit -m "xdg: Stop tracking the emoji picker's state"
git -C ~/.config/emacs push
```

Then on Hera: `git -C ~/.config/emacs pull --ff-only --no-rebase --no-autostash`

Expected: the push reports `master -> master`, and the pull fast-forwards.

- [ ] **Step 2: Set the ChronoSync rules**

In the task `Home`, decide these four, and note the decision in the task's description:

1. `.cache`: exclude. Caches are rebuilt on each host.
2. `.local/state/emacs`: state is the kind the XDG text calls not portable enough to be data; the author of that wording meant "bound to the specific machine". A shared `recentf` is what produces the conflicts this task reports today. Exclude the directory, and each host keeps its own history, recent files, backups and org-id index. Include it, and the hosts go on sharing them as they do now, conflicts and all; then still exclude `.local/state/emacs/migration` and `.local/state/emacs/backups`, which holds 200 MB of numbered backup files.
3. `.local/share/emacs`: include it, so that both hosts have one set of saved choices and tokens. `tree-sitter/` holds compiled code; share it only if both hosts have the same processor architecture.
4. `.config/emacs`: unchanged.

- [ ] **Step 3: Resume the schedule and watch the first run**

Expected: no deletion under `.local/share/emacs` or `.local/state/emacs` on either host, and no `data` directory reappearing under `.config/emacs`.

If `~/.config/emacs/data` comes back on a host, Emacs refuses to start there with `Emacs state is still in ...`. What came back is the stale copy; the files under the three roots are the ones in use. Quit Emacs and run `xdg/migrate.sh --apply --prefer=destination`. It keeps every file that is in use, moves across only what the roots lack, and puts the stale copies under `migration/<stamp>/collisions/`. Never use `--prefer=source` for this. Then find the ChronoSync rule that brought the directory back.

- [ ] **Step 4: Check the checkout on both hosts**

Run on each: `make -C ~/.config/emacs check-litter`

Expected: `No litter in ...`

---

### Task 10: Remove the one-time tools

Do this two weeks after Task 9, once John has looked through the attic and the collisions on both hosts. Run it on Clio; Hera receives the result by `git pull`. The mover, its tests, the guard and the litter report stay: they are what puts a host right if state ever comes back.

**Files:**
- Delete: `xdg/apply-init-edits.el`, `xdg/apply-init-edits-test.el`, `xdg/audit/`
- Modify: `Makefile` (the lines added in Task 5 Step 6)
- Delete on each host, by John: `~/.local/state/emacs/migration/`, which on Clio also holds `init.org.before-xdg`

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
Ran 17 tests, 17 results as expected, 0 unexpected (...)
234 passed, 0 failed
38 passed, 0 failed
```

- [ ] **Step 4: Commit and push**

```bash
git -C ~/.config/emacs add Makefile
git -C ~/.config/emacs commit -m "xdg: Remove the one-time editor and audit"
git -C ~/.config/emacs push
```

Then on Hera: `git -C ~/.config/emacs pull --ff-only --no-rebase --no-autostash; git -C ~/.config/emacs status --short xdg Makefile`

Expected: the pull fast-forwards, or says `Already up to date` if ChronoSync carried the repository across; the second command prints nothing.

- [ ] **Step 5: Remove the worktree and the branch**

```bash
git -C ~/.config/emacs push origin --delete xdg-layout
git -C ~/.config/emacs worktree remove ~/src/emacs-xdg-layout
git -C ~/.config/emacs branch -d xdg-layout
```

Expected: the first command reports `- [deleted]         xdg-layout`, and the last `Deleted branch xdg-layout`. The remote branch goes first: if the branch was rebased in Task 7, git would otherwise refuse to delete it for not matching its upstream.

- [ ] **Step 6: John deletes the migration records, on each host**

This is the only step in the plan that deletes anything of John's, and it is John's to run. Look first: `ls -R ~/.local/state/emacs/migration | head -60`. The attic holds, among other things, `gptel-agent/sessions.db` with its WAL file, `data/workgroups` from 2015, and `%backup%~`, an emergency backup of `/etc/hosts` from September 2026.

```bash
rm -r ~/.local/state/emacs/migration
```

- [ ] **Step 7: Optionally drop what is stale**

Three of the four directories under `~/.cache/emacs/eln-cache/` belong to older builds. In Emacs: `M-x native-compile-prune-cache`.

`~/.cache/org-persist` is the old place of Org's cache, which Org has rebuilt under `~/.cache/emacs/org-persist`. On each host, John can remove it: `ls ~/.cache/emacs/org-persist | head -3; rm -r ~/.cache/org-persist`. The first command must list something before the second is run.

---

## Execution record

Tasks 1 to 8 and Task 9 Step 1 were carried out on 17 November 2026, on Clio and, over ssh, on Hera. The steps above that are ticked were done. What is left is John's: the hands-on checks of Task 7 Step 16 on each host, Task 9 Steps 2 to 4, and Task 10.

| | Clio | Hera |
|---|---|---|
| Files moved at | 19:30:33 | 19:35:49 |
| Run directory | `~/.local/state/emacs/migration/20261117-193031` | `~/.local/state/emacs/migration/20261117-193547` |
| Files compared by SHA-256 before and after | 11,622: 9,671 moved, 1,951 in place, none missing or changed | 14,502: 12,553 moved, 1,949 in place, none missing or changed |
| `make -B init.el` after the move | exit 0, no error or warning | exit 0, no error or warning |
| Task 7 Steps 13, 14 and 15 in a running session | the expected list; `nil`; no litter | the same |

Commits on `master`: `9bbb6fc6e`, `752bebebc`, `2abad7827`, `970426e80` and `446b529e3` for Tasks 1 to 5; `9728bf350` and `71fc781b6` for two corrections to this plan (below); `72d456e0b` for the 26 edits of `init.org`, and nothing else; `0f1e1e61b` for Task 9 Step 1.

Each run directory has an `evidence/` directory: the record of every step with its output, three inventories of the four directories (before the move, after it, and after the first build), the comparison, and the reports of the agents that scouted and verified that host. An independent replay of each log, by an agent that had not run the move, agreed with the comparison, and each archive was unpacked and matched its inventory member by member.

**Two corrections made to this plan while it was executed.** Both checks had only ever been run under the conditions of writing: from scratch checkouts under `/tmp`, with John's Emacs running beside them.

- The path tests failed in a checkout below the home directory. The helper that starts a child Emacs binds `HOME`, and `call-process` then expanded a `default-directory` of `~/...` against it. The helper now starts the child in the scratch root.
- The sealed audit failed while no Emacs was running. The init makes `/tmp/johnw-emacs` when it is missing, and the sandbox denies that directory. `guards.el` now skips it.

**Where the execution departed from the text.**

- Task 7 Step 17: the commit holds the 26 edits only. Two other changes in the canonical file (an Org face, and a `:custom` block for ob-agent-deck) were left uncommitted, as they had been.
- Task 8 was run over ssh. The mover ran under `nohup`. Emacs was started on Hera for the live checks and quit again 26 seconds later, because it had not been running there before. Nobody read `*Messages*` of that session.
- Task 7 Step 16 was checked only as far as a program can: counts of the restored histories, and the Python grammar. The hands-on checks are open on both hosts.
- Task 9 Step 1 was done the same evening, once both hosts had moved.
- An accident. At 19:15 an agent inspecting Hera ran `osadecompile` on `org-protocol.app`, which started Emacs.app there with the old init. Nobody used that session, and it was quit at 19:28, before Hera's move. Its start-up clean-up shortened Hera's `recentf` from 1,368 to 1,319 entries, dropping files that do not exist on Hera; Clio's list is whole. Counting that session, Gnus was started on Hera at least four times that evening (the others were the build of Step 7, a batch check and the live check); what it did on the IMAP server was not checked.

**Open, for John.**

- Commit `init.org` in the `~/org` repository; `changes` does it. Until then its `HEAD` holds the old init, and a stash or a reset there would bring it back. The old init has no guard and would start on empty state (Follow-up 21).
- Task 7 Step 16 by hand on each host. On Hera also run `emacsclient -s /tmp/johnw-emacs/server --eval '(list init-file-had-error (get-buffer "*Warnings*"))'` after the first start; it should print `(nil nil)`.
- Task 9 Steps 2 to 4. The hourly item of the task `Home` is suspended. The weekly "validate" item is not, and is next due on Monday 23 November at 05:00. The two hosts' `backups/` directories differed before the move, which suggests that the task already excludes `~/.local/share/emacs` and `~/.local/state`: look at the rules before deciding. At the first run both sides will have changed in `~/.local/share/gnus` and in `.config/emacs/.git`; going by its own log, ChronoSync has until now reported such files as conflicts and overwritten neither. Clio's copies are the ones in use.
- The backup fileset (Follow-up 26).
- Task 10, two weeks after Task 9. The worktree `~/src/emacs-xdg-layout` and the branch `xdg-layout` stay until its Step 5.

---

## Follow-ups

None of these is needed for the reorganization. Each was found on the way and is worth its own decision.

1. **`make init.el` may erase bm bookmarks.** In a sealed copy, the batch load of the init wrote an empty `bm-repository` over a populated one: bm's save runs on exit, and its load never runs in batch. The real `bm-repository` is empty today. Whether bookmarks were lost this way is not known. A build that only tangles, or that loads with the state root pointed at a scratch directory, would stop it. The execution showed more of the same: that batch load rewrites `recentf` and `projectile-frecency.eld`, and it starts Gnus far enough to open its IMAP connections and to rewrite `~/.local/share/gnus/.newsrc.eld` and the `News/*.ADAPT` files when it exits.
2. **`~/src/scripts/syncup` is broken.** Line 24 calls `load-env-emacs$EMACSVER`, which is no longer on `PATH`, so the script stops there.
3. **`~/src/scripts/changes-all` commits the whole checkout** from `~/.config/emacs/lisp`, which is not a repository of its own.
4. **Five MCP entries in `~/.config/claude/personal/.claude.json`** name `/Users/johnw/.emacs.d/emacs-mcp-stdio.sh`, which does not exist. The tracked `emacs-mcp-stdio.sh` is stale as well.
5. **`~/.config/forge` holds 482 MB** of SQLite for a package whose block is disabled.
6. **Small defects in `init.org`:** the yasnippet `:mode` pattern still names `.emacs.d`; `load-path` has an entry for a `use-package` directory that does not exist; `tramp-remote-path` gains `<cwd>/bin` when `PROFILE_DIR` is unset; `eshell-z-exclude-dirs` names `~/.emacs.d/elpa`. In the same vein, `lisp/org-agent-deck-README.org` line 41 gives `/ssh:hera:/Users/johnw/.emacs.d/lisp/` as the place to reload from; it should read `.config/emacs/lisp/`. That file has another agent's uncommitted changes, so this plan does not edit it.
7. **`eshell/alias`, `eshell/login` and `certs/vulcan-ca-bundle.pem` are configuration that is not versioned.** Tracking them needs a look at their contents first. The certificate has the same fingerprint as one the Nix configuration already installs.
8. **The gptel package built by Nix** has `/homeless-shelter/.cache` compiled in as the default for `gptel-crowdsourced-prompts-file`. The table in `lisp/user-paths.el` overrides it; the build is still wrong.
9. **The tree-sitter grammars could come from Nix**, into the bundle's `lib/` directory, which `nix-packages.el` already adds to the load path and which is empty today. Short of that, four of the thirty have no source recorded anywhere: clojure, haskell, kotlin and scala. No mode that uses them is installed. If they are wanted, an entry each in `treesit-language-source-alist` lets Emacs rebuild them; if not, they can be deleted.
10. **Three commented-out blocks of `init.org` still say `user-data`,** and this plan leaves them alone. `oauth2-auto` and `org-gcal` hold tokens, which are data. `org-caldav-save-directory` holds sync state, which belongs under the state root; it was not edited because the names of its files cannot be known in advance, so the mover could not route them, and no such file exists on Clio. Whoever revives that block should point it at `(user-state "org-caldav/")`.
11. **Saved settings that their author files as configuration.** no-littering, which is written by the author of transient, puts `transient/values.el` and `transient/levels.el` under its `etc/`, and pandoc-mode's settings directory as well. This plan keeps them under data: the report rules configuration out for the transient files, and nothing should write into the checkout unasked. If they should be versioned with the configuration after all, each is one row of `user-paths-table` and one decision about `.gitignore`.
12. **The TCP server's auth file.** The specification's place for it is `XDG_RUNTIME_DIR`, which macOS does not provide; the table sends `server-auth-dir` to state. It matters only with `server-use-tcp`, which this configuration does not set.
13. **`make clean` deletes `settings.el`,** the Custom file, together with the files it can rebuild. That is older than this plan and has nothing to do with the layout; dropping `settings.el` from the recipe is one word.
14. **org-remark can build a path inside the configuration directory.** For a buffer that visits no file it would keep its notes in `<user-emacs-directory>/marginalia.org`. With today's configuration that branch never writes: only its eww, info and nov modes supply such buffers, and none is turned on. Whoever turns one on should set `org-remark-notes-file-name` first.
15. **Directory shortcuts.** `lisp/dired-ext.el` has a shortcut for `~/.config/emacs`. The three new roots have none; adding them is a matter of taste and of free keys.
16. **Gnus keeps its own home.** `gnus-home-directory` is `~/.local/share/gnus/`: 783 MB, written every day. It is outside the checkout, and this plan does not touch it. Bringing it under the three roots would mean sorting some two dozen Gnus variables into mail and drafts (data), read marks and the registry (state) and article caches (cache), on a mail store in daily use. That is a plan of its own.
17. **The litter report lists ignored paths only.** `xdg/check-litter.sh` skips every entry of `git status` that is not ignored, so a runtime file that `.gitignore` does not name is neither reported nor kept out of `changes`. About twenty built-in default names are in that position (`abbrev_defs`, `calc.el`, `games/`, `eww-bookmarks`, `image-dired/`, `diary` and others). Either report untracked entries as well, with a list of what may be untracked, or add the names to `.gitignore`. Two smaller points in the same script: it depends on git's `status.showUntrackedFiles`, and it prints `No litter` if `git status` itself fails.
18. **Paths that are still built from the configuration directory.** `image-dired-dir` (thumbnails, a cache), `diary-file` (data), `wombag-dir` (it uses `XDG_CACHE_HOME`, and falls back to the configuration directory in an Emacs that has no such variable), and org-remark (Follow-up 14). Each is one row of `user-paths-table`. The fallback `%backup%~` in `files.el` cannot be redirected.
19. **An interrupted move can get past the guard.** The mover removes `data/` before it has moved `eshell/`, `persist/`, `tree-sitter/` and the other sources that come later in its manifest, and the guard looks only at `data/`. If `--apply` stops in between, the next start is quiet and partly empty. Nothing is lost, and `--apply --prefer=source` puts it right. Moving the `data/` entries to the end of the manifest closes it. In the same script a data root that is a symbolic link is taken for a clash, and the tests have no case for an apply that stops half-way.
20. **`early-init.el` redirects before the guard can refuse.** Between the arrival of the branch and the first build, an Emacs started from the Dock runs the old `init.el` with the new early paths. Loading the library from `early-init.el` only when `data/` is absent closes it. Also, the library requires `xdg` before it redirects the native-compilation cache, so `xdg.el` is compiled again at every interactive start.
21. **There is no guard in the other direction.** An old `init.org` on a host that has been moved starts without complaint on empty state and re-creates `data/`. It can come back from the `~/org` repository (a stash, a reset, a checkout) or from the other host. The mover could leave a marker for the library to check, or `early-init.el` could refuse an `init.el` that never calls `user-paths-check-migrated`.
22. **The one-time tools, if they are kept beyond Task 10.** The audit's reader takes a form cut short by a missing paren for the end of the file. Errors in hooks are logged and not counted. A new empty directory is not reported. `run.sh` stops with rsync's error 23 in a checkout where a tracked file is deleted from the working tree. `mcp-server-lib-install-directory` belongs on the list of allowed variables. `audit.el` runs the whole audit when it is loaded in a batch Emacs. The editor counts an edit as done when the new text is present even if the old text is too, and it overwrites the file in place.
23. **Emacs starts that bypass `runemacs`.** On Clio two Keyboard Maestro macros (Cmd-Shift-M, and Home in Firefox) and org-protocol links start Emacs.app directly. On Hera `mailto:` links and the default mail client do, and org-protocol goes through an AppleScript applet whose script names Emacs. Such a start skips the build, so it runs whatever `init.el` was tangled last. Reading that applet with `osadecompile` starts Emacs too.
24. **Other agents' test runs use this checkout as their init directory.** `emacs -Q --batch` takes `~/.config/emacs` from `XDG_CONFIG_HOME` even under a scratch `HOME`, and can leave `eln-cache/` and other default files here. Their scripts should set `XDG_CONFIG_HOME` or pass `--init-directory`.
25. **Small leftovers.** Four old `tramp.*` temporary files in `~/.cache/emacs` on Clio and six on Hera. Old numbered backups of `oauth2-auto.plist` under `backups/` have mode 0644, below a 0700 root. Inside `pre-migration.tar` three token and cookie files keep mode 0644: unpack it only into a private directory.
26. **The backup fileset.** `~/.config/pushme/filesets/Home.yaml` excludes `/.local/share/emacs/` and `/.local/state/`. The first rule was written when that directory held only numbered backups; it now holds tokens, saved choices and grammars. Whether the nightly push should carry them is John's decision, and has no bearing on where they live.
27. **Three places where this plan's text was wrong or thin.** The rollback loop of Task 7 should stop at the first run it cannot undo (`|| break`). Step 9 of Task 7 and Step 6 of Task 8 should say that Emacs must not be started if `--apply` stops with an error. The preview in Task 8 Step 5 shows about 77 actions, not Clio's 47, because Step 4 has already created three directories under the roots.

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

John's amendments, in four messages on 2026-11-17 after he had read the first version of this plan, verbatim and in order. The first quotes that version's rule of two roots.

````markdown
You wrote:

> Two roots only: $XDG_DATA_HOME/emacs and $XDG_CACHE_HOME/emacs. Nothing goes under $XDG_STATE_HOME: ~/.local/state is excluded from every backup on these hosts.

However, I want to use ~/.local/state, but do not exclude this from your plan. Apply this revision, and do not base your planning on what is and what is not backed up.
````

````markdown
You should be artfully using:

- ~/.config/emacs
- ~/.local/share/emacs
- ~/.local/state/emacs
- ~/.cache/emacs
````

````markdown
Also, do your research on the Web and find out what is the best way to arrange this data in the XDG directories, based on config vs. state vs. share vs. cache.
````

````markdown
Putting backups under ~/.local/share/emacs was just something arbitrary that I did a few years ago. If your research reveals a better choice, then do it.
````

---

## Appendix B: Where this plan departs from the report

The report sorted files into two destinations. The amendments add a third and ask for the sorting to rest on research; Appendix D has the sources named here.

| Item | The report says | This plan does | Why |
|---|---|---|---|
| `data/`, as one directory | data, whole | split file by file among state, data and cache | The old init kept all three kinds in one directory. |
| `data/history`, `recentf`, `places`, `persistent-scratch`, `projectile-bookmarks.eld`, `prescient-save.el`, `tramp` | data | state | "Actions history (logs, history, recently used files)" and "current state of the application that can be reused on a restart" are the specification's own examples of state. Neovim keeps its history, marks and views there. |
| `data/org-id-locations` | data | state | It is an index, but `org-id-update-id-locations` rebuilds it only for the files Org already knows, so it is not a cache. The sources split three ways; state is the middle. |
| `data/network-security.data` | data | state | Remembered trust decisions. The closest analogues are both under state: Neovim's `:trust` database and wget's HSTS file. |
| `bm-repository`, in `data/` | data | state | Line bookmarks are positions in files on this machine, like Vim's marks, which Neovim keeps under state. |
| `data/org-roam.db` | data | cache | An index built wholly from the note files. `org-roam-db-sync` rebuilds it, org-roam's own schema upgrade deletes and rebuilds it, and Org's related `org-persist` already defaults to the XDG cache. |
| `data/workgroups` | data | attic | No setting names it; the file is from 2015. |
| `backups/` in `~/.local/share/emacs` | "correct" | state, `backups/` | John called the old place arbitrary. Neovim and Vim keep backup files under state, and Doom's definition of state names "autosaves/backup files". Neovim itself kept backups and swap files under data until 0.8, and moved them when it adopted `XDG_STATE_HOME`. `tramp-auto-save-directory` goes with them. |
| `tree-sitter/` | cache | data | Every installer examined keeps compiled grammars with installed things: nvim-treesitter and Doom under data, Emacs itself beside the configuration. A cache may be deleted at the cost of time alone; a deleted grammar comes back only after a prompt, with git, a C compiler and the network, and four of the thirty have no recorded source. |
| `emojis/` | stay, as versioned configuration | data | It is git-ignored, not versioned. It is the image set emojify downloaded on request, and emojify asks before it downloads again, so it is installed artwork and not a cache. |
| `var/` | data | `var/pcache/` to cache; `var/osm/` to the attic | pcache is a font cache that is rebuilt. The osm package is not installed; its tiles date from 2024. |
| `request/curl-cookie-jar` | cache | state, mode 600 | A cookie jar holds sign-ins. Emacs cannot rebuild it, so it is not a cache; it belongs to one installation, so it is state. |
| `transient/` | cache, merged into one directory; values "either share or cache, not config" | history to state; values and levels to data | History is the specification's first example of state. Values and levels are choices John saved. The report rules configuration out for them, which is where their author's own no-littering puts them (Follow-up 11). |
| `url/cache`, "`data/url/cache` duplicate", cookies to share | consolidate | the stray top-level `url/cache/` to cache; `data/url/` (cookies) to state | There is no `data/url/cache`. Cookies are state, as above. |
| `persist/`, `multisession/files/` | data | `persist/` to data; `multisession/` to state | `persist/` holds org-drill's learned scheduling matrix and saved play queues. `multisession/` holds one list of recently used emoji. |
| `eshell/history`, `eshell/lastdir` | data | state | Histories. |
| `data-MacPort/` | "same shape" as `data/`; merge, or keep the alt logic | attic; the alternate instance, if ever revived, uses `emacs-alt` | It holds one auto-save index from May 2025. Nothing has set `emacsERC` since 2024. |
| `.lsp-session-v1`, `.org-generic-id-locations`, `gptel-agent/` | data | attic, which is under the state root | Their packages are disabled or gone. |
| `elpy/rpc-venv` | cache or data | attic; elpy builds its next one under the data root | The virtualenv is broken: its Python has left the Nix store and its scripts name `~/.emacs.d`. A virtualenv cannot be moved in any case. The next one is installed tooling, like a grammar: elpy asks before it fetches the packages. |
| `auto-save-list/` | both directories to data, and elsewhere "state or cache" | `data/auto-save-list/` to state; the stray top-level directory to the attic | It is the index `recover-session` reads after a crash: one host, one process. Neovim keeps its swap files under state. The top-level directory holds one empty file, written by an Emacs that read no init. |
| `.#*` lockfiles | state or cache | nothing | None exist: `create-lockfiles` is nil. |
| `%backup%~` | "already duplicated in share/backups" | attic | It is not a duplicate. It is a 578-byte emergency backup of `/etc/hosts`. |
| `anvil-worker.log` | state or cache | attic | Anvil has been removed; the log is from July 2026. |
| `bookmarks`, "bookmark backups" | already external | the backups move with `backups/` | `~/doc/bookmarks` is in a Syncthing folder and stays. |
| `eln-cache/` | cache | cache, moved whole | Agreed. Moving keeps the 71 native files the running Emacs uses; `native-comp-jit-compilation` is nil, so they would not be rebuilt. The Emacs maintainers are divided on whether the directory is a cache (bug#48543); Doom and Neovim treat compiled code as one. |
| symlinks for the transition | offered | none | Nothing outside Emacs reads the old paths. A link named `data` is not matched by the rule `/data*/`, so `changes` would commit it. |
| `sits/`, `cache/` | listed with a question mark | nothing | Neither exists. |
| `certs/`, `init.el`, `settings.el`, `nix-packages.el` | versioned | unchanged | They stay, but they are git-ignored, not versioned. |
| the reason given: "breaks git status", repository weight, Home Manager purity | | | All of this state is already ignored, none of it is in the repository, and Home Manager owns only two symlinks. What the move buys is a checkout that holds configuration and nothing else, and three directories whose names say what each file is. |

Not in the report, and handled here: `projects` and `projectile-frecency.eld`; the split of `eshell/` into configuration and state; `transient-levels-file`; `pcache-directory`, `persist--directory-location`, `multisession-directory` and `request-storage-directory`; the two defaults that point at `~/.emacs.d`; the load-order defects in the tramp and transient settings; the tracked runtime file under `multisession/`; the settings in commented-out blocks; three caches that followed XDG under names of their own, and one autosave file in the home directory; and Hera.

---

## Appendix C: What was run while writing this plan

Every file in this plan was built and run before it was written down. The tests and the audit ran against throw-away copies, from an empty environment, with writes to the home directory denied by the sandbox.

| Check | Result |
|---|---|
| `lisp/user-paths-test.el` | 17 of 17 pass |
| `xdg/apply-init-edits-test.el` | 7 of 7 pass |
| `--check` against `~/org/init.org` | all 26 edits match exactly once |
| `xdg/migrate-test.sh` | 234 of 234 pass, under bash 5.3 with the GNU tools and under `/bin/bash` 3.2 with the system's tools first on `PATH` |
| `xdg/check-litter-test.sh` | 38 of 38 pass, both ways |
| `shellcheck` on all five scripts | clean |
| `xdg/audit/run.sh` on the full init, from a checkout that holds only this plan's files | 580 forms, 0 failed; 1,674 features; 0 offenders; nothing written inside the configuration directory; every file it wrote lies under the root this plan gives it |
| the same with `XDG_AUDIT_SELFTEST=1` | fails on the planted variable and the planted file, as it must |
| the sandbox profile | refuses a write to the home directory, to `~/.config/emacs` and to `/tmp/johnw-emacs`, and refuses the network |
| every variable in `user-paths-table`, checked against the installed sources | each exists under that name and takes a single path; the one constant, `web-cookie-jar-file`, is handled separately |
| a preview of the move on the real tree | 47 actions, no clash, nothing left behind; the output is below |
| Task 7 forward and back, rehearsed in a scratch home with the real mover, the real Makefile and a stand-in for Emacs | the first build stops at the guard, the second succeeds after the move, and the rollback restores the checkout, `git status` and every file under the three roots, the `backups/` directory included |
| Tasks 1 to 5, carried out from this document's text in a scratch clone by an agent that had seen nothing else | all 43 steps gave the expected output, and every file it produced was byte-identical to the tested one; that was before the last corrections, after which the files were extracted from the final text and the tests, the audit, the preview and the rehearsal run once more |

Not run: the cutover itself, a real GUI start on the new layout, and anything on Hera.

The first version of this plan had two roots. Five reviewers attacked it, and a second agent had to reproduce each finding before it counted; forty-seven held up and were fixed. One reviewer's hand-made fixture set `HOME` but left `XDG_CACHE_HOME` pointing at the real `~/.cache`, so the mover it ran set `~/.cache/emacs` to mode 700. The mode was put back to 755, and nothing else was touched. The mover's tests start it from an empty environment for that reason.

This version follows John's amendments. Beyond rewriting the code and its tests, four things were done for it:

1. Three readers checked the placement of 58 paths against the sources of the packages that write them. They agreed on 57. The one reversal, `org-roam.db` to the cache, held up under a second reader.
2. Five researchers read what the specification, Doom Emacs, no-littering, Emacs itself, Neovim and a dozen other tools do with files of each kind, and a checker re-opened every citation: 105 of 117 were confirmed, 12 partly, none refuted. Appendix D is the result. It moved `backups/`, the tree-sitter grammars, the language servers, treemacs's workspaces, the line bookmarks and the network-security file.
3. Three reviewers attacked the revised code in sealed scratch trees, and a second agent reproduced each of their twelve findings; all were fixed. The serious one: with `XDG_STATE_HOME` and `XDG_DATA_HOME` naming one directory, the move of `backups/` compared every file with itself, took it for a duplicate and deleted it. The mover now refuses roots that are not three separate directories, and never takes one file under two names for a duplicate. The others: a preview that missed files moved into a directory earlier in the same run; a rollback that stopped at the first record it could not undo; an archive that stored files twice, which failed a test under the system's `tar`; checks that could not fail; and an edit that a later rewording would have applied twice.
4. An agent that had seen nothing but this document carried out Tasks 1 to 5 from its text in a scratch clone; the last row of the table has the result. Three more reviewers read the text for consistency, for the logic of the cutover and for fidelity to the sources, opening every URL in Appendix D again, and a second agent re-checked each of their twenty findings. Nineteen held up. The one that mattered was in the instructions for Hera: a build that succeeds there, where it should stop at the guard, means the sync has already deleted Hera's state, and the text said to go on. The rest were corrected as well. `emojis/` and the object store moved to data, a database journal now travels with its database, the rollback's description says what it leaves behind, and Appendix D records where its sources disagree with this plan.
5. John then asked for the plan to cover every configuration file under `~/org`, `~/.config/emacs` and `~/.config/emacs/lisp`. The three trees were searched, the Makefile's own build was run in a sealed copy, and three critics, one per tree, hunted for a file the plan misses. They brought seven candidates; a second agent refuted three and upheld four. Those four are in: three caches that sat beside `~/.cache/emacs` now sit inside it, the chess package's autosave file leaves the home directory for the state root, seventeen more ignore rules cover what an Emacs started without its init can write into the checkout, and a stale path in a README is recorded among the follow-ups. The section "What changes, by location" is the result.

The preview of the move on Clio on 2026-11-17:

```text
migrate: Emacs is running:
/Applications/Emacs.app/Contents/MacOS/Emacs
migrate: this preview can go stale; --apply will refuse until Emacs has quit
Configuration: /Users/johnw/.config/emacs
Data:          /Users/johnw/.local/share/emacs
State:         /Users/johnw/.local/state/emacs
Cache:         /Users/johnw/.cache/emacs
Preview only: nothing is changed.  Run with --apply to move.
  mv     /Users/johnw/.config/emacs/url/cache -> /Users/johnw/.cache/emacs/url
  rmdir  /Users/johnw/.config/emacs/url
  mv     /Users/johnw/.config/emacs/data/org-roam.db -> /Users/johnw/.cache/emacs/org-roam.db
  mv     /Users/johnw/.config/emacs/data/mc-lists.elc -> /Users/johnw/.local/state/emacs/migration/<stamp>/attic/data/mc-lists.elc
  mv     /Users/johnw/.config/emacs/data/workgroups -> /Users/johnw/.local/state/emacs/migration/<stamp>/attic/data/workgroups
  mv     /Users/johnw/.config/emacs/data/auto-save-list -> /Users/johnw/.local/state/emacs/auto-save-list
  mv     /Users/johnw/.config/emacs/data/bm-repository -> /Users/johnw/.local/state/emacs/bm-repository
  mv     /Users/johnw/.config/emacs/data/history -> /Users/johnw/.local/state/emacs/history
  mv     /Users/johnw/.config/emacs/data/network-security.data -> /Users/johnw/.local/state/emacs/network-security.data
  mv     /Users/johnw/.config/emacs/data/org-id-locations -> /Users/johnw/.local/state/emacs/org-id-locations
  mv     /Users/johnw/.config/emacs/data/persistent-scratch -> /Users/johnw/.local/state/emacs/persistent-scratch
  mv     /Users/johnw/.config/emacs/data/places -> /Users/johnw/.local/state/emacs/places
  mv     /Users/johnw/.config/emacs/data/prescient-save.el -> /Users/johnw/.local/state/emacs/prescient-save.el
  mv     /Users/johnw/.config/emacs/data/projectile-bookmarks.eld -> /Users/johnw/.local/state/emacs/projectile-bookmarks.eld
  mv     /Users/johnw/.config/emacs/data/recentf -> /Users/johnw/.local/state/emacs/recentf
  mv     /Users/johnw/.config/emacs/data/tramp -> /Users/johnw/.local/state/emacs/tramp
  mv     /Users/johnw/.config/emacs/data/transient/history.el -> /Users/johnw/.local/state/emacs/transient/history.el
  mv     /Users/johnw/.config/emacs/data/url -> /Users/johnw/.local/state/emacs/url
  mv     /Users/johnw/.config/emacs/data/mc-lists.el -> /Users/johnw/.local/share/emacs/mc-lists.el
  mv     /Users/johnw/.config/emacs/data/oauth2-auto.plist -> /Users/johnw/.local/share/emacs/oauth2-auto.plist
  mv     /Users/johnw/.config/emacs/data/transient -> /Users/johnw/.local/share/emacs/transient
  rmdir  /Users/johnw/.config/emacs/data
  mv     /Users/johnw/.local/share/emacs/backups -> /Users/johnw/.local/state/emacs/backups
  mv     /Users/johnw/.config/emacs/data-MacPort -> /Users/johnw/.local/state/emacs/migration/<stamp>/attic/data-MacPort
  mv     /Users/johnw/.config/emacs/eshell/history -> /Users/johnw/.local/state/emacs/eshell/history
  mv     /Users/johnw/.config/emacs/eshell/lastdir -> /Users/johnw/.local/state/emacs/eshell/lastdir
  mv     /Users/johnw/.config/emacs/projects -> /Users/johnw/.local/state/emacs/projects
  mv     /Users/johnw/.config/emacs/projectile-frecency.eld -> /Users/johnw/.local/state/emacs/projectile-frecency.eld
  mv     /Users/johnw/.config/emacs/multisession -> /Users/johnw/.local/state/emacs/multisession
  mv     /Users/johnw/.config/emacs/persist -> /Users/johnw/.local/share/emacs/persist
  mv     /Users/johnw/.config/emacs/hash-store -> /Users/johnw/.local/share/emacs/hash-store
  mv     /Users/johnw/.config/emacs/request -> /Users/johnw/.local/state/emacs/request
  mv     /Users/johnw/.config/emacs/tree-sitter -> /Users/johnw/.local/share/emacs/tree-sitter
  mv     /Users/johnw/.config/emacs/eln-cache -> /Users/johnw/.cache/emacs/eln-cache
  mv     /Users/johnw/.config/emacs/emojis -> /Users/johnw/.local/share/emacs/emojis
  mv     /Users/johnw/.config/emacs/var/pcache -> /Users/johnw/.cache/emacs/pcache
  mv     /Users/johnw/.config/emacs/var/osm -> /Users/johnw/.local/state/emacs/migration/<stamp>/attic/var/osm
  rmdir  /Users/johnw/.config/emacs/var
  mv     /Users/johnw/.config/emacs/transient -> /Users/johnw/.local/state/emacs/migration/<stamp>/attic/transient
  mv     /Users/johnw/.config/emacs/auto-save-list -> /Users/johnw/.local/state/emacs/migration/<stamp>/attic/auto-save-list
  mv     /Users/johnw/.config/emacs/elpy -> /Users/johnw/.local/state/emacs/migration/<stamp>/attic/elpy
  mv     /Users/johnw/.config/emacs/gptel-agent -> /Users/johnw/.local/state/emacs/migration/<stamp>/attic/gptel-agent
  mv     /Users/johnw/.config/emacs/.lsp-session-v1 -> /Users/johnw/.local/state/emacs/migration/<stamp>/attic/.lsp-session-v1
  mv     /Users/johnw/.config/emacs/.org-generic-id-locations -> /Users/johnw/.local/state/emacs/migration/<stamp>/attic/.org-generic-id-locations
  mv     /Users/johnw/.config/emacs/anvil-worker.log -> /Users/johnw/.local/state/emacs/migration/<stamp>/attic/anvil-worker.log
  mv     /Users/johnw/.config/emacs/%backup%~ -> /Users/johnw/.local/state/emacs/migration/<stamp>/attic/%backup%~
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

---

## Appendix D: What the placement rests on

John asked for the placement to rest on research. Five researchers read primary sources: the text of the specification, project source on its forge, official manuals, maintainers' own statements. A checker then re-opened every citation behind a principle or a disagreement. Whether a directory is backed up was excluded from the question throughout.

### The specification

- [XDG Base Directory Specification 0.8](https://specifications.freedesktop.org/basedir-spec/latest/): "The $XDG_STATE_HOME contains state data that should persist between (application) restarts, but that is not important or portable enough to the user that it should be stored in $XDG_DATA_HOME. It may contain: actions history (logs, history, recently used files, …) current state of the application that can be reused on a restart (view, layout, open files, undo history, …)". The cache is for "user-specific non-essential (cached) data".
- The author of that wording, [on the xdg list in February 2021](https://lists.freedesktop.org/archives/xdg/2021-February/014434.html): "With "portable", I was meaning "bound to the specific machine/installation" in the broadest sense."
- The test for a cache, in [systemd's file-hierarchy(7)](https://raw.githubusercontent.com/systemd/systemd/v255/man/file-hierarchy.xml): "Flushing this directory should have no effect on operation of programs, except for increased runtimes necessary to rebuild these caches." David Faure, who later approved the addition of `XDG_STATE_HOME`, [on the xdg list in 2016](https://lists.freedesktop.org/archives/xdg/2016-December/013805.html): a cache is "anything that only exists for performance reasons and that can be thrown away".

This plan's test for a cache is those two made concrete: what Emacs can make again from what is on this machine, or fetches again unasked. What comes back only after a prompt, a download or a build is installed, and is data.

### Practice

| Kind of file | Where the precedents put it | Sources |
|---|---|---|
| histories, recently used lists | state | the specification; Neovim's shada file; less; telescope-frecency |
| saved positions and views | state in Neovim, data in Vim | Neovim's `viewdir` is under state; Vim's `xdg.vim` puts views and undo files under data, "as they are persistent" |
| backups, swap files, crash recovery | state | Neovim, where `backupdir` defaults to `.,$XDG_STATE_HOME/nvim/backup//`; Vim's `xdg.vim`; Doom's definition of state |
| logs | state | the specification; Neovim |
| trust decisions | state | Neovim's `:trust` database; wget's HSTS file in the Arch Wiki. qutebrowser keeps permissions under data |
| sessions and layouts | state, with exceptions | the specification; persistence.nvim. auto-session and Zed use data |
| installed plugins, parsers, language servers | data | nvim-treesitter (`install_dir = vim.fn.stdpath('data') .. '/site'`); mason.nvim; lazy.nvim; Doom |
| derived indexes, bytecode, native code | cache | the test above; Neovim's Lua bytecode; Org's `org-persist`, which defaults to the XDG cache |
| sign-in tokens | configuration, in the tools that say | GitHub's `gh`; git. No source keeps them under state on purpose |
| cookies | data or configuration in browsers, which have no state directory | qutebrowser. The proposal that led to `XDG_STATE_HOME` listed cookies as state |

Doom Emacs is the one Emacs project that defines all three directories. Its definitions, from [`lisp/doom.el`](https://raw.githubusercontent.com/doomemacs/core/759fb66e33132f85e8cb7ac7f0fefeb360d1a8c0/lisp/doom.el):

- data: "Deleting them by hand will cause breakage, and require user intervention (e.g. a `doom sync`) to restore. Use this for: server binaries, package source, pulled module libraries, generated files for profiles, profiles themselves, autoloads/loaddefs, etc."
- state: "State files contain unessential, non-portable, but persistent data which, if lost won't cause breakage, but may be inconvenient as they cannot be automatically regenerated or restored. [...] Use this for: history, logs, user-saved data, autosaves/backup files, known projects, recent files, bookmarks."
- cache: "Cache files represent unessential data that shouldn't be problematic when deleted (besides, perhaps, a one-time performance hit), lack portability (and so shouldn't be copied to other systems/configs), and are regenerated when needed, without user input".

Doom's code lags these definitions: state was added in 2022, and most of its history files still sit in the cache directory. Where the two disagree, this plan follows the definitions.

### How to do it in Emacs

- The Emacs manual, [node Find Init](https://raw.githubusercontent.com/emacs-mirror/emacs/master/doc/emacs/custom.texi): "Since `user-emacs-directory`, once determined by Emacs, is used by the rest of the startup code to locate other files and directories, we do not recommend changing its value in your init files, as that could disrupt or break the correct startup of your Emacs sessions." That is the design here: `user-emacs-directory` stays, and each variable is set by name, as no-littering does it. Doom does the opposite and points `user-emacs-directory` at its cache directory; its own comment names the cost, which falls on packages "that read `user-emacs-directory' expecting to find the location of your Emacs config".
- What setting each variable cannot do is catch a package it has never heard of. The sealed audit (Task 3), the ignore rules and `make check-litter` (Task 5) are the guard for that.
- Emacs's own `xdg.el` supplies the three directories and treats an unset or relative variable as unset. `startup-redirect-eln-cache` is the supported way to move native code, and its documentation says to call it from the early-init file.

### Where the sources disagree

| File | The sources | This plan |
|---|---|---|
| installed tooling: grammars, language servers, virtualenvs, packages | data in nvim-treesitter, mason.nvim, lazy.nvim and Doom; the author of the specification's wording on state, in the same message, would rather keep software installations in the cache and only a registry of them under data | data: they come back only after a prompt and a download |
| saved positions in files | state in Neovim; data in Vim's `xdg.vim` | state, as "current state of the application that can be reused on a restart" |
| saved transient values and levels | configuration in no-littering, by transient's own author; data in Doom | data, because the report rules configuration out |
| bookmarks | state in Doom's definition; data in Doom's code | line bookmarks (`bm`) to state, as positions; eww's bookmarks to data |
| tokens | configuration in `gh` and git; cache in Doom | data |
| tramp's persistency file | a cache of connection properties, in the Tramp manual; "connection history", in its own docstring | state |
| `org-id-locations` | cache, data, or beside the Org files | state |
| `eln-cache/` | the Emacs maintainers are divided (bug#48543) | cache, as the report says |
| what an application saves for itself, as a whole | systemd reads `~/.local/share` narrowly, as "Resources shared between multiple packages, such as fonts or artwork", which would send nearly all of this plan's data to state | the specification's own line: state is what is "not important or portable enough" for data |
