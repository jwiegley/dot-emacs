# AGENTS.md

This file provides guidance to coding agents working in this repository. `CLAUDE.md` is a symlink to it.

Paths are relative to the top of the repository unless they begin with `~` or `/`.

## Repository Overview

This is John Wiegley's Emacs configuration. The checkout at `~/.config/emacs` is the directory his Emacs starts from (`user-emacs-directory`), so its working tree is what the next start of Emacs runs.

- The init file is written in Org. The `Makefile` tangles `init.org` into `init.el`; `early-init.el` runs before it.
- `lisp/` holds John's own modules and their tests, the git submodules and the local directory `badi-calendar/`.
- Every other package comes from the Nix-managed Emacs environment, through two symlinks at the top of the checkout that Home Manager owns and git ignores. `nix-packages` is the bundle of packages. `nix-packages.el` puts the bundle on `load-path`, and signals an error in any Emacs other than the build the bundle was compiled for. The sources of those packages are not below `lisp/`. To change one, work in its upstream checkout or in the source that the Nix overlay pins, with that project's own commands.
- Only configuration lives in the checkout. What Emacs writes while it runs goes to three directories outside it.

## Rules

These are the rules that are easy to break without noticing. The sections below explain each.

1. **Run no `make` target here except `make check-litter` and `make test-xdg`**, `make audit-xdg` while it exists, and `make init.org` after an edit to `~/org/init.org` that John asked for. The build targets (`make`, `make init.el`, `make -B`, `make speed`, `make slow`, `make open`, `make open-quick`) load John's whole init in a batch Emacs with his real data and state, and `make clean` deletes his Custom file. For the same reason, never load `init.el` or `init.org` yourself (`emacs -l init.el`, `org-babel-load-file`).
2. **Start every batch Emacs of your own with `--init-directory="$(mktemp -d)"`.** Without it, Emacs takes this checkout as its own directory and writes into it. The option moves that one directory and nothing else; see Running Emacs.
3. **Check your changes in a batch Emacs, not in the Emacs that is running.** That one is John's working session, with his unsaved buffers, and what is evaluated there stays in it: evaluate nothing in it unless he asks you to.
4. **Before you edit a file, or let git rewrite one, look for `#NAME#` beside it.** That is the auto-save file of a buffer with unsaved changes. If there is one, stop and ask.
5. **Edit `~/org/init.org`, not the `init.org` here, and never `init.el`.**
6. **Whatever Emacs writes on its own account gets a path under one of the three roots** for data, state and caches, never under `user-emacs-directory`. Files that John has Emacs save as configuration, such as `settings.el` and `abbrevs.el`, are the exception.
7. **Leave no file of yours untracked in the checkout, and commit no plans or specs here.** John's `changes` script commits and pushes whatever `git add -A` finds, anywhere in the tree.
8. **With git, touch only what is yours.** Commit only your own files or hunks (see Committing), and read `git status` first: a file that shows as staged though you did not stage it may be staged in reverse, so leave it alone (see A stale index). Before a pull, compare what it brings in with what is changed here. Never drop a stash that you did not make, and never check out an old commit in this checkout. See Version Control.
9. **Run `make check-litter` when you start and before you finish**, and `make test-xdg` after any change to `lisp/user-paths.el`, `xdg/`, the `Makefile` or `.gitignore`.
10. **Work on this repository on one machine at a time.** ChronoSync carries the checkout between Clio and Hera every hour, in both directions, `.git` included. Do not pull in the other host's copy to bring it up to date: ChronoSync's next run does that. See Version Control.

## Layout

| Path | What it is |
|---|---|
| `init.org` | The literate init: a read-only copy of `~/org/init.org` |
| `init.el` | Tangled from `init.org`; ignored by git |
| `early-init.el` | Loads `lisp/user-paths.el` before anything else, and keeps `package.el` from activating packages at startup |
| `Makefile` | Builds `init.el`, and runs the litter report and the tests of the layout |
| `lisp/` | John's modules, their tests and the submodules |
| `xdg/` | The litter report, the tool that moved runtime files out of the checkout, the tests behind `make test-xdg`, and the one-time tools of that move |
| `prompts/` | gptel directives, one to a file |
| `snippets/` | Yasnippet snippets by mode; `snippets/org-mode` is a symlink into `~/org` |
| `abbrevs.el` | Abbrev tables |
| `settings.el` | The Custom file; ignored by git |
| `runshell` | The shell that `M-x shell` starts |
| `certs/`, `eshell/` | Local configuration that git ignores: CA certificates, and Eshell's `alias` and `login` files |
| `nix-packages`, `nix-packages.el` | Home Manager's symlinks to the package bundle; ignored by git |
| `.gitignore` | Besides build products, the default names of runtime files, as a safety net; `make test-xdg` tests its rules |
| `README.md` | A short account of the layout, for people |
| `AGENTS.md`, `CLAUDE.md` | This guide, and the symlink through which Claude Code reads it |

The table leaves out what plays no part in building or testing the configuration.

## Where Emacs Keeps What It Writes

`~/.config/emacs` holds configuration only. Whatever Emacs writes while it runs belongs under one of three roots, chosen by what the file is:

| Root | Helper | Place | What belongs there |
|---|---|---|---|
| `user-data-directory` | `(user-data "NAME")` | `$XDG_DATA_HOME/emacs/` (`~/.local/share/emacs/`) | What is worth carrying to another machine, and what was installed on request: saved choices, tokens, learned parameters, tree-sitter grammars, language servers |
| `user-state-directory` | `(user-state "NAME")` | `$XDG_STATE_HOME/emacs/` (`~/.local/state/emacs/`) | What Emacs records about its own use on this machine: histories, recent files, positions, sessions, cookies, backups |
| `user-cache-directory` | `(user-cache "NAME")` | `$XDG_CACHE_HOME/emacs/` (`~/.cache/emacs/`) | What Emacs can make again from what is on this machine, or fetches again unasked: compiled code, indexes, web responses |

Something that comes back only when a person agrees to a download or a build is data, not cache. In the alternate instance (`NIX_MYENV_NAME=emacsERC`) each root ends in `emacs-alt/` instead of `emacs/`.

`lisp/user-paths.el` defines the roots and the helpers. `early-init.el` loads it before anything else, so that even the native-compilation cache is redirected before anything is compiled, and by its `.el` name, so that a stale `.elc` is never used. Batch Emacs never reads `early-init.el`, so the top of `init.org` requires the library again. It then calls `(user-paths-check-migrated)`, which stops the init with an error while a directory `data/` is still in the checkout.

### Giving a Package Its Path

Set the path in the package's `use-package` block in `~/org/init.org`, under `:custom`:

```elisp
(use-package recentf
  :custom
  (recentf-save-file (user-state "recentf")))
```

Add a row to `user-paths-table` in `lisp/user-paths.el` instead in two cases only. One is a variable that its library reads while it loads, when that library can be loaded before its own block runs (as a dependency of another package, say): the `:custom` would then come too late. The other is a variable that no `use-package` form mentions. A row is `(VARIABLE ROOT NAME)`, with ROOT one of `data`, `state` and `cache`. A trailing slash on NAME is kept, so give one where the library builds file names from the value with `concat`. If the library does not create its directory itself, add the directory to `user-paths-ensure-directories`. Paths that fit no row are set in `user-paths-apply-special`.

`(emacs-path "NAME")`, which `init.org` defines to expand NAME in `user-emacs-directory`, is for configuration: `abbrevs.el`, `settings.el`, `snippets/` and the like. It is never for something Emacs writes on its own account.

### What Must Stay As It Is

- **The roots cannot be assigned.** A variable watcher signals an error when a `setq`, `defconst`, `setopt` or the like would give a root a different value. A `let` binding is allowed, and that is how a test redirects a root.
- **The call `(user-paths-check-migrated)` stays at the top of `init.org`**, in a source block that is tangled. The Makefile refuses an `init.org` or an `init.el` without it; see The guards.
- **Never unload the library.** After `(unload-feature 'user-paths t)` the roots are unbound, and loading the file again fails, because the watchers still call a function that the unload removed. Loading it a second time without unloading is harmless.
- **Loading the library changes things.** It creates the three roots and a few directories below them, sets every variable in its table, adds advice and redirects the native-compilation cache. A test that loads it must first point `XDG_DATA_HOME`, `XDG_STATE_HOME`, `XDG_CACHE_HOME` and `user-emacs-directory` at a scratch directory and clear `NIX_MYENV_NAME`, as `lisp/user-paths-test.el` does.
- **`~/.emacs.d` and `~/.emacs` must not exist.** Either one makes Emacs take `~/.emacs.d` as its directory and ignore this checkout.

### The Safety Net in `.gitignore` and the Litter Report

An Emacs that runs without this init (`-Q`, `-q` or `--batch`) still writes to its built-in defaults, which are inside the checkout. `.gitignore` therefore names those default files and directories, so that `git add -A` cannot commit a cookie jar or a history. A rule hides such a file from git; it does not make the file welcome here. Settings that a person saves on request (`abbrev_defs`, `calc.el`, `eudc-options`, `shadows`, `strokes`, `viper`) have rules as well: such a file stays in the checkout and out of a commit, as `settings.el` does; unlike `settings.el`, the report lists it. Code (`user-lisp/`, a style under `auctex/style/`, a theme) has no rule on purpose, so that it stays visible.

`make check-litter` runs `xdg/check-litter.sh`, which makes the litter visible. It only reads, and it lists:

- `~/.emacs.d`, `~/.emacs` and `~/.emacs.el` (the last changes nothing alone, but Emacs loads it as the init file once `~/.emacs.d` or `~/.emacs` exists);
- every ignored path outside `lisp/` that is not known configuration (such as `init.el`, `settings.el`, the Nix symlinks, `certs/`, Eshell's files, and what agent tools and the Finder leave), a build product, or an auto-save or lock file;
- every untracked entry at the top of the checkout;
- every empty directory at the top of the checkout, and backup files (`*~`), below `lisp/` too.

It prints `No litter in DIR` and exits with 0 when it finds nothing, with 1 when it lists something, and with 2 on an error. It passes over `eln-cache/`, over `.elc` files and whatever else is ignored below `lisp/` (backup files apart), and over untracked files below a tracked directory, which it takes for John's work in progress. `git add -A` takes those all the same, so remove your own scratch files from there yourself, and leave his.

If a run of yours left something, remove it and correct how you started Emacs. Anything that was there before may hold John's data: tell him what the report listed, and let him decide.

### The Tools in `xdg/`

- `xdg/check-litter.sh` and its test: the litter report.
- `xdg/migrate.sh` and its test: the tool that moved the runtime files out of the checkout in November 2026. Without `--apply` it prints what it would do and changes nothing. `--apply` and `--rollback` move John's files and need every Emacs quit first, so do not run them; if a message calls for one, tell John.
- `xdg/make-init-test.sh`: tests the Makefile's rules for `init.org` and `init.el`, with a stand-in for Emacs.
- `xdg/apply-init-edits.el`, its test, and `xdg/audit/`, which `make audit-xdg` runs: tools of the move itself, whose removal is planned. Use `make audit-xdg` while it exists, but make nothing new depend on them.

## `init.org`, `init.el` and the Makefile

The source of the init is `~/org/init.org`, in John's Org repository, which is not this one. The `init.org` here is a tracked copy, which the Makefile replaces (`cp -p`, then `chmod 444`) whenever `~/org/init.org` is newer. `init.el` is tangled from that copy and is ignored by git.

- **To change the init, edit `~/org/init.org`.** `make init.org` then copies it here and loads nothing. It copies the whole file, and with it whatever else John has changed there since the last commit here, so run `cmp init.org ~/org/init.org` before you start and commit only your own hunks. In `~/org`, the file is committed by John's `changes` script; nothing here needs you to commit there.
- **A change takes effect when John next starts Emacs.** His launcher runs `make init.el` first, and does not open Emacs when that fails. A build that fails while it loads the init leaves its `init.el` behind, though, so the start after that opens Emacs on it, mistake and all. While `make audit-xdg` exists, it fails on a top-level form that signals an error, before he meets it; a mistake inside a deferred block may show only as one more feature that would not load.
- **Much of `init.org` is switched off.** A heading that begins with `COMMENT` is not tangled, and neither is anything below it. Look at every heading above a block before you conclude that a package is in use.
- **A `use-package` block cannot load what the Nix bundle lacks.** To see whether the bundle has a library, ask a batch Emacs that has loaded `nix-packages.el` (see Running Emacs): `(locate-library "NAME")`. What the bundle holds is decided in John's Nix configuration (`~/src/nix/config/emacs.nix`), which is another repository. The `:nix` keyword in some blocks does nothing when the init runs: `init.org` defines it to be ignored, and nothing else reads it. Where a block gives a name, it is the package's name in Nix when that differs from the feature's (`bookmark+` is `bookmark-plus`). `:nix nil` tells nothing reliable, so trust `locate-library`.

| Target | What it does | May an agent run it? |
|---|---|---|
| `make check-litter` | Lists runtime files that are back in the checkout; reads only | Yes |
| `make test-xdg` | Tests `lisp/user-paths.el`, the tools in `xdg/`, the rules in `.gitignore` and the Makefile's own rules, all in scratch directories | Yes |
| `make audit-xdg` | Copies the configuration into a scratch home, tangles a copy of `~/org/init.org` there, and loads the whole init form by form, then every feature that a `use-package` form names, under a sandbox that denies writes below the home directory and all network access. Reports the forms that failed, the variables that still name a path in `user-emacs-directory`, and the files written there, and ends in `PASS` or `FAIL`. Takes about half a minute | Yes, while it exists |
| `make init.org` | Copies `~/org/init.org` over the tracked copy if it is newer and has the call `(user-paths-check-migrated)` (see The guards); loads nothing | After an edit to `~/org/init.org` that John asked for |
| `make`, `make init.el`, `make -B` | Copy, tangle, and then **load the whole init** in a batch Emacs with John's real data and state | No |
| `make speed`, `make slow` | Build as above. `speed` also compiles an `init.elc`, which stays and is loaded in place of `init.el`. Both then load the init once more | No |
| `make open`, `make open-quick` | Build as above, then open `/Applications/Emacs.app` | No |
| `make clean` | Deletes `init.el`, `settings.el` (the Custom file, which is not in git), and the `.elc` and backup files at the top | No |
| `make lisp/NAME.elc` | Byte-compiles a module beside its source, without the Nix packages | No; see Byte-Compiling |

There is no `make test` and no `make build`: both names are declared without a rule, so they succeed and do nothing.

**The guards.** An `init.org` or an `init.el` from before this layout can still turn up, from history or from another machine of John's. Loaded, it would put Emacs's state back into the checkout. Three things stand in the way. The Makefile neither copies nor tangles an `init.org` whose text lacks `(user-paths-check-migrated` on a line with no `;` before it. It rebuilds an `init.el` that lacks that text, removes `init.elc` whenever it builds, and fails when the `init.el` it has just built and loaded still lacks the text, which means that the call stands in prose, under a `COMMENT` heading or in a block that is not tangled. And in an interactive Emacs the watcher on the roots stops an old `init.el` at its first definition of a root. Nothing guards a batch `emacs -l init.el`, and nothing guards a checkout of a commit older than the guards themselves (17 November 2026), which has neither the Makefile's rules nor the watcher. The messages of these guards advise restoring `~/org/init.org` from its history, `touch ~/org/init.org` or `make -B init.el`, and that of `(user-paths-check-migrated)` advises `xdg/migrate.sh --apply`. That advice is for John: when one of them stops you, tell him what it printed.

**Time stamps.** `make` copies `~/org/init.org` only when it is the newer of the two files, and git gives a file it rewrites the time of the rewrite. After a pull or a checkout that changes `init.org`, and after any pull while `init.org` shows as modified (the stash rewrites it), the copy here is therefore the newer one, and John's next start builds from it. Run `cmp init.org ~/org/init.org` after every pull. If the two differ, one holds changes that the other lacks: commit nothing that touches `init.org`, and tell John. If you have committed such a change already, stop and ask before you push it. `touch ~/org/init.org` makes the next build copy that file again, which is right only when it holds everything. Never overwrite `~/org/init.org` from here.

## Running Emacs

A batch Emacs for a check is started from the top of the checkout like this:

```bash
emacs --batch -Q --init-directory="$(mktemp -d)" \
  --eval '(setq load-prefer-newer t)' \
  -l ~/.config/emacs/nix-packages.el -L lisp -L lisp/llm-setup \
  ...
```

- **`--init-directory="$(mktemp -d)"`.** Every Emacs takes `~/.config/emacs` as `user-emacs-directory`: batch or not, with `-Q` or without, and, because John's shell exports `XDG_CONFIG_HOME`, even under a scratch `HOME`. A batch Emacs reads neither `early-init.el` nor `init.el`, so nothing has been redirected and the built-in defaults point into the checkout. What tests leave there in practice is `eln-cache/`, with a trampoline that the native compiler makes when a primitive is rebound (running `lisp/org-ql-semantic-test.el` does it). A scratch init directory takes such writes instead. Do not point `XDG_CONFIG_HOME` at a directory that has no `emacs/` in it: Emacs then falls back to `~/.emacs.d`.
- **`-l ~/.config/emacs/nix-packages.el`.** It puts the Nix packages on `load-path`; without it, half of the test files do not load. It also tells the native compiler where to find a library that trampolines link against: without it, and under a scratch `HOME`, a test that rebinds a primitive fails with `library 'emutls_w' not found`. Give the absolute path, because the file is ignored by git and a worktree has no copy. Use the `emacs` on `PATH`, because the file signals an error in any other build.
- **`load-prefer-newer`.** `lisp/` holds ignored `.elc` files that nothing keeps fresh. A batch Emacs loads an `.elc` in preference to a newer source, and a test then passes or fails on the old code.
- **`-L lisp -L lisp/llm-setup`.** `lisp/` is not on `load-path` until the init has run, and the tests of `gptel-backends`, `gptel-model-policy` and `org-drafts-ext` need the `llm-setup` submodule. In a worktree the submodule directories are empty: use `-L ~/.config/emacs/lisp/llm-setup` there.

This Emacs has the packages and none of John's configuration: no `use-package` block has run, and no setting of his is in effect. Load what a check needs. To learn a value in his session, read how `~/org/init.org` sets it, or ask him. The three roots still follow the real `XDG_*_HOME`, so code that loads `lisp/user-paths.el` works on John's real data and state unless those variables point elsewhere as well.

Use these commands also where another file here gives commands of its own that start Emacs without a scratch directory or compile beside the source.

### Tests

The tests of the modules are ERT files, `lisp/NAME-test.el`. Run one file with the command above, ending in:

```bash
  -l lisp/NAME-test.el -f ert-run-tests-batch-and-exit
```

Run all of them like this:

```bash
export NIX_MODEL_POLICY_FILE=$HOME/.config/ai/model-policy.json
export NIX_HOST_POLICY_FILE=$HOME/.config/ai/host-policy.json
for t in lisp/*-test.el; do
  log=$(mktemp)
  emacs --batch -Q --init-directory="$(mktemp -d)" \
    --eval '(setq load-prefer-newer t)' \
    -l ~/.config/emacs/nix-packages.el -L lisp -L lisp/llm-setup \
    -l "$t" -f ert-run-tests-batch-and-exit >"$log" 2>&1
  echo "== $t: exit $? ($log)"
  grep -e '^Ran ' -e FAILED "$log"
done
make test-xdg
```

- Each file must show one `Ran N tests` line. A file without one did not load: read its log.
- The two variables are for `lisp/gptel-model-policy-test.el`, which checks the presets and backends against the model policy that Nix generates, and does not load without them.
- To run only some tests, end with `--eval '(ert-run-tests-batch-and-exit "REGEXP")'` instead; the regexp is matched against the names of the tests. For one test, name it as a symbol, in double quotes because of the Lisp quote: `--eval "(ert-run-tests-batch-and-exit 'TEST-NAME)"`. A regexp that matches nothing runs no test and still exits with 0, so read the `Ran N tests` line.
- A suite can fail before you touch anything. Run it on the unchanged tree first, so that you know which failures are yours.
- Most modules have no test file. To show a fix in one of those, add a test as under Adding a Module, or load the module in a batch Emacs and evaluate the changed code with `--eval`.
- `lisp/ob-agent-deck.el` has no test file of its own; `lisp/org-agent-deck-test.el` tests it together with `lisp/org-agent-deck.el`.
- Without `pandoc` on `PATH`, one test of `org-drafts-ext` fails and one of `org-agent-deck` is skipped. `lisp/org-drafts-ext-test.el` also reads the `init.org` at the top of the tree.
- `make test-xdg` is the suite for `lisp/user-paths.el`, `xdg/`, the `Makefile` and `.gitignore`. It must exit with 0, and each of its summaries (`Ran N tests, N results as expected, 0 unexpected` or `N passed, 0 failed`) must report no failure. The lines that begin with `ERROR` are the output of tests that pass.
- The submodules carry tests of their own; the guidance at the top of each says how to run them.
- Nothing runs these tests for you. The workflow under `.gitea/` only checks that the submodules can be cloned.

### Byte-Compiling

```bash
o=$(mktemp -d)
emacs --batch -Q --init-directory="$(mktemp -d)" \
  --eval '(setq load-prefer-newer t)' \
  -l ~/.config/emacs/nix-packages.el -L lisp -L lisp/llm-setup \
  --eval "(setq byte-compile-dest-file-function
            (lambda (f) (expand-file-name (concat (file-name-nondirectory f) \"c\") \"$o\")))" \
  -f batch-byte-compile lisp/NAME.el
```

This writes the `.elc` into the scratch directory `$o`, not beside the source. The exit status is 0 even when there are warnings, so read the output.

- Compile the files you changed, not `lisp/*.el`. Many older modules warn already. The measure is that a file gives no warning that it did not give before your change.
- `.elc` files are not tracked: `*.elc` is the first line of `.gitignore`. In a fresh worktree the modules in `lisp/` are therefore loaded from source, while the Nix packages are compiled already.
- When a module that has an `.elc` beside it changes, by your edit or by a pull, remove that `.elc`: it is now older than its source, and nothing rebuilds it. John's init sets `load-prefer-newer`, but `john-wiegley-theme` and `org-constants` are loaded before that setting and still take a stale file. An `.elc` in `lisp/` is ignored by git and passed over by the litter report, so nothing else will point it out.

## What Is in `lisp/`

Most of it is single-file modules, and most of those are loaded by a `use-package` block of their own in `init.org`. That a file is here does not mean that it runs. Some modules are named only under a `COMMENT` heading (`erc-alert` and `c-includes`, for instance), a good number are not named in `init.org` at all, and one is loaded only by another module's `require`. Search `init.org` for the name, and look at every heading above the block.

- **Paths**: `user-paths.el`, described above.
- **Org**: `org-config.el` holds the capture templates, the agenda's custom commands and the search commands they use; Org's own settings are in the `use-package org` block of `init.org`. `org-ext.el`, the largest module, holds extra Org commands, and `org-constants.el` the paths of John's Org files. Extensions of other packages: `org-roam-ext.el`, `org-ql-ext.el`, `org-ql-semantic.el`, `vulpea-ext.el`, `org-review-ext.el`, `org-drafts-ext.el`, `org-smart-capture.el`.
- **agent-deck**: `org-agent-deck.el` sends an Org entry to a running agent-deck session and inserts a session's latest output; `ob-agent-deck.el` adds the `agent-deck` Babel language, which launches a session. `org-agent-deck-README.org` describes both. The library's default for `org-agent-deck-presets` is not what John runs with: `init.org` sets its own value under `:custom`, so a change to the default changes the tests and the README, not his session.
- **gptel**: `gptel-presets.el`, `gptel-backends.el`, `gptel-ext.el` and `gptel-tools.el`, an empty stub that `init.org` loads; gptel itself comes from Nix. When gptel loads, each file in `prompts/` becomes a directive named after the file without its extension. `gptel-presets.el` and `gptel-ext.el` refer to directives by those names, so renaming a prompt file is a change to code.
- **MCP**: `mcp-convert.el` converts MCP JSON configuration to Emacs Lisp, and `mcp-hub` comes from Nix. `mcp-server-lib` and `elisp-dev-mcp` stand under `COMMENT` headings in `init.org`, and the bundle has neither on `load-path`. `mcp-server-lib` is in use all the same: the Org-wiki MCP service that John's Nix configuration sets up brings a copy of its own and talks to the running Emacs through its server socket, and the `org-wiki-mcp` block in `init.org` waits for that library with `:after`. A block that waits for a feature which the init itself never loads is therefore not proved dead.
- **The rest**: more Org helpers, helpers for Gnus, ERC, Dired, Eshell, editing and proof assistants, John's own commands in `personal.el`, and the theme, `john-wiegley-theme.el`.
- **`badi-calendar/`**: `cal-bahai.el` and `holidays.el`, tracked here as ordinary files. Both are also the names of libraries in Emacs, and `init.org` puts this directory first on `load-path` (`:load-path`), so these are loaded in their place. The directory has a `.git` of its own inside it, so run git from the top of the checkout, not from there.

The submodules are listed in `.gitmodules`. Each is a repository of John's with guidance of its own at its top (`CLAUDE.md` or `AGENTS.md`), which governs work inside it. Search `init.org` for a submodule's name to see whether and how it is loaded: not every one is.

- A change inside a submodule is committed there, on the branch that is checked out there, and pushed there. The commit in this repository then records the new revision.
- John's git configuration sets `diff.ignoreSubmodules` to `dirty`, so `git status` at the top does not show uncommitted edits inside a submodule. Run it inside the submodule.
- A fresh worktree has the submodules as empty directories.

## Emacs Lisp Conventions

**Lexical binding.** Every new file sets `lexical-binding: t` in its first line, as in the layout below. A few old modules do not, and Emacs warns when it loads one of those from source.

**File layout.** The newer modules look like this (`lisp/dired-ext.el` is one):

```elisp
;;; NAME.el --- Brief description -*- lexical-binding: t; -*-

;; Copyright (C) YEAR John Wiegley
;; Author: John Wiegley <johnw@gnu.org>
;; Keywords: keywords

;;; Commentary:

;; How to use it.

;;; Code:

(require 'cl-lib)

(defgroup NAME nil ...)
(defcustom NAME-option t ...)

;;;###autoload
(defun NAME-command () ...)

(defun NAME--helper () ...)

(provide 'NAME)

;;; NAME.el ends here
```

**Names:**

- Public: `NAME-function`. Internal: `NAME--helper`, with a double dash.
- Predicates end in `-p`, modes in `-mode`, hooks in `-hook`.

**Autoloads.** Mark commands and modes with `;;;###autoload`, but nothing in this repository generates an autoloads file. A command becomes available because the module's `use-package` block names it (`:commands`, `:bind`, `:hook`, `:mode`) or loads the module outright.

**Dependencies:**

```elisp
(require 'cl-lib)      ; never the deprecated cl
(require 'subr-x)      ; thread-first, thread-last and the like
(require 'seq)         ; sequence operations

;; A function of a library that is not loaded when this file is compiled
(declare-function bookmark-jump "bookmark" (bookmark &optional display-func))

;; An optional feature
(with-eval-after-load 'org
  (add-hook 'org-mode-hook #'NAME-setup))
```

A module that is meant to become a package of its own also lists what it needs in a `Package-Requires` header.

## Adding a Module

1. Create `lisp/NAME.el` with the layout above. In the init, `lisp/` is the last entry on `load-path`: if NAME is also the name of a library in Emacs or in the Nix bundle, the init loads that library and never yours. The test command's `-L lisp` puts `lisp/` first, so the tests do not show such a clash. Look for one with `(locate-library "NAME")` in a batch Emacs that has loaded `nix-packages.el` and has no `-L lisp`.
2. Create `lisp/NAME-test.el`:

   ```elisp
   ;;; NAME-test.el --- Tests for NAME -*- lexical-binding: t; -*-

   (require 'ert)
   (require 'NAME)

   (ert-deftest NAME-test-basic ()
     "Describe what must hold."
     (should (equal expected actual)))

   (provide 'NAME-test)

   ;;; NAME-test.el ends here
   ```

3. Add a `use-package NAME` block to `~/org/init.org`, as the section "`init.org`, `init.el` and the Makefile" describes. A module in a subdirectory of `lisp/` needs `:load-path` there. Whatever the module writes gets its path from `user-data`, `user-state` or `user-cache`.
4. Run the test and the byte-compile check from Running Emacs.

## Interactive Development

These are for when John asks you to work in his session (rule 3). An agent's own checks run in batch.

- **Reload a module** with `M-x eval-buffer` in its buffer, or with `(load "~/.config/emacs/lisp/NAME.el")`. Functions are replaced, while a `defvar` or a `defcustom` keeps the value it has. Do not `unload-feature` first: that resets the module's variables and loses what `init.org` sets under `:custom`, and for `user-paths` it breaks the session.
- **Evaluate** with `C-x C-e` (last sexp), `C-M-x` (defun), `M-x eval-buffer` or `M-x eval-region`.
- **Debug** with `(setq debug-on-error t)`, with `debug-on-entry` and `cancel-debug-on-entry`, with `trace-function` and `untrace-function`, or with a `(debug)` form in a function body.
- **Look up** with `find-function` and `describe-function`, and expand macros with `macroexpand-1`, `macroexpand-all` or `M-x pp-macroexpand-last-sexp`.
- **Measure** with `elp-instrument-function`, `elp-results` and `elp-restore-all`, or with `(benchmark-run 1000 (FUNCTION))`.

Turn off what you turned on before you hand the session back.

## Debugging Common Issues

- **A module does not load, or a change has no effect.** `(provide 'NAME)` must match the file name. The directory must be on `load-path`: `lisp/` is, once the init has run, and a subdirectory needs `:load-path`. The `use-package` block may stand under a `COMMENT` heading, or wait with `:after` for a feature that never loads. In a session, the module may have been loaded before your change, and `require` does not load it again. In batch, an `.elc` older than its source may be loaded in its place (see Byte-Compiling). Look for circular requires.
- **Void variable.** The `defvar` or `defcustom` must come before the use. Look for a misspelt name, and for a variable that is dynamic in one file and lexical in another.
- **Byte-compilation warnings.** A warning usually marks a real fault. Use `cl-lib`, not the deprecated `cl`, and declare the functions of other libraries with `declare-function`.
- **Test failures.** A batch run prints the form that failed and a backtrace: read them before you change anything. Use `should-error` for an error that is expected. Tests must not depend on one another, and must not write to John's data, state or caches.

## Version Control

- **Subjects.** Most read `area: Sentence`, for example `user-paths: Refuse to give a root another value` or `make: Refuse to build init.el from a stale init.org`. Commits titled `changes` are made by John's script.
- **Two hosts.** This checkout exists on Clio and on Hera, and ChronoSync carries it from one to the other every hour, in both directions, `.git` included. Work only in the copy on the machine your session runs on. Do not edit, commit or pull in the other host's copy, not even to bring it up to date: ChronoSync's next run does that. If John asks for something in the other host's copy, tell him that ChronoSync's next run will bring it over, and act there only if he still wants it. If a ref moves on both hosts, or the same objects are written on both (by a commit on one and a fetch on the other), ChronoSync cannot settle it, and John has to resolve the conflict by hand.
- **A stale index.** The index is the one file under `.git` that git rewrites without an edit: a `git status` or a `git diff` refreshes it. On the machine being worked on, that is of no account, since its index changes with every commit anyway. When it happens on the other host as well, in the same hour, ChronoSync cannot reconcile the two versions and leaves the file out, in both directions, until John resolves the conflict. Each commit or pull then reaches the other host without its index, and the index there still describes the commit before. `git status` shows a file that the commit changed as `MM`, one that it added as `D ` and again as `??`, and one that it deleted as `AD`, though nobody edited them: they are staged in reverse, and a plain `git commit` would undo the commit without a warning. So before every commit, read `git status` and `git diff --cached --name-status`: nothing may be staged that you did not stage. An entry that is not yours is either such a leftover or something John has staged; for a file marked `MM`, `git diff HEAD -- FILE` prints nothing in the first case. Either way, leave the file and its index entry alone. A commit by path leaves them out, so commit your own files that way, and tell John which files show it. If you must change such a file, or pull while one is there, stop and ask first: over such entries a pull either fails, with its stash left inside `.git`, or puts back the wrong thing, such as a deleted file staged as new. `git reset -q -- FILE` clears a stale entry without touching the working file: run it only when he asks. `core.checkStat` is set to `minimal` in `.git/config` here and in the three submodules, so that git does not rewrite a copied index merely because the files' inode numbers differ on the other host. That makes the conflict rare, not impossible, and a fresh clone lacks the setting.
- **Pulling.** John's git configuration sets `pull.rebase` and `rebase.autoStash`, so a pull stashes whatever is uncommitted in the checkout, his changes as well as yours, and puts it back afterwards. It puts back the working files, not the index as it was: a change that John had staged to a tracked file comes back unstaged. Commit your own work first. Then `git fetch`, and compare what comes in (`git diff --name-only HEAD...origin/master`) with what `git status` still shows as changed: if a file is in both, or if anything is staged that is not yours, stop and ask. A stash that does not go back cleanly stays in `git stash list`, with conflict markers in the files, and the pull still exits with 0, so read what it prints. If it reports a conflict, stop and ask: leave the markers, the index and the stash as they are, do not follow git's advice to drop the stash or to reset, and tell John which files hold markers. A pull that fails, or that prints `Created autostash` and no `Applied autostash`, has left its stash inside `.git`, where `git stash list` does not show it: stop and ask, and tell John what it printed. If the rebase stops on a conflict with a commit of yours, the stashed changes are held inside `.git` until it ends, and `git rebase --abort` puts them back. Never drop a stash that a pull left, not even your own pull's: it holds John's changes as well as yours.
- **Old versions.** Read an old version of a file with `git show REV:PATH`, or in a worktree. A commit older than the guards has none of them, so do not check one out here.
- **Committing.** Commit your own files by path: `git add` what is new, then `git commit -m "..." -- PATH...`, which takes the working copies of those paths and nothing else that is staged. `git add -A` and `git commit -a` take whatever else is changed or untracked in the checkout. To commit only some hunks of a file, as with `init.org`, stage them without an interactive command, for instance with `git apply --cached` and a patch that holds only your hunks, and run a plain `git commit`. Before that, `git diff --cached --name-only` must show nothing else staged; if it does, stop and ask.
- **No plans or specs.** John has removed the plans and specs that were committed here. Keep such a document, and your working record of how you carried out a change, outside the checkout: in your reply to John, or where he says. What a later reader needs goes into the commit message or into a comment in the code. This is about new documents in this repository: leave the ones that are here alone, and a submodule follows its own guidance.
- **Unsaved buffers.** John's init keeps the auto-save file of a local file beside it, as `#NAME#`, and makes no lock files. A `#NAME#` beside a file means that his Emacs holds unsaved edits to it, or held them when it last crashed: stop and ask before you edit that file or let a `git pull`, `checkout` or `stash` rewrite it. The absence of one proves little, because Emacs writes it only after a pause or a few hundred keystrokes.
- **Worktrees.** Put a `git worktree` outside the checkout, for example under `~/src`, or under `.claude/worktrees/`, which `.gitignore` covers. Anywhere else at the top of the checkout it is litter that `git add -A` would commit. A worktree lacks the ignored files (`init.el`, `settings.el`, `nix-packages.el`, the `.elc` files) and the contents of the submodules, so name those by their paths in the real checkout.

### Ending a Session

Work is not finished until it is committed and pushed, and you push it yourself: do not leave the push to John. Where this file says to stop and ask, that comes first: ask, and finish when John has answered.

1. Run the checks that fit what you changed: the tests under Running Emacs, `make test-xdg` where rule 9 calls for it, and `make check-litter`. There is no build to run (rule 1). What `make check-litter` lists from before your session blocks nothing once you have told John.
2. Commit your own files or hunks as Committing describes. A change inside a submodule is committed and pushed there first (see What Is in `lisp/`).
3. Push:

   ```bash
   git fetch
   git status                                   # what is still changed here
   git diff --name-only HEAD...origin/master    # what comes in
   git pull --rebase                            # read Pulling first
   cmp init.org ~/org/init.org                  # after a pull; see Time stamps
   git push
   git status                                   # the branch must be up to date with origin
   ```

   If the push fails, find out why and try again.
4. Remove the stashes, branches and worktrees that you made, and leave all others. A stash that your pull left is not one of them (see Pulling): name it in your hand-off.
5. Say what you did, what is left open and what the next session needs to know. There is no issue tracker here, so what is left to do goes into that hand-off.
