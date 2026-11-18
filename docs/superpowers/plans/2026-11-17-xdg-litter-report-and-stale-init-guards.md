# XDG Litter Report and Stale-Init Guards Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make `make check-litter` see runtime files that `.gitignore` does not name, and make sure that an `init.org` or `init.el` from before the move of state cannot start Emacs quietly on a host that has been moved.

**Architecture:** Four changes to files that exist already. The litter report asks git for untracked entries as well as ignored ones, and lists the untracked ones at the top of the checkout. `.gitignore` gains a rule for what agent tools leave in the checkout and for each remaining default name that Emacs writes on its own account. `lisp/user-paths.el` puts a variable watcher on its three roots, so that an old `init.el` fails at its first definition. The Makefile refuses to copy or to tangle an `init.org` that does not call the library's guard, builds again an `init.el` that does not, and fails when the `init.el` it has built does not. Each change has tests that run in scratch directories.

**Tech Stack:** bash (also the system bash 3.2), git, GNU Make (also the system's 3.81), Emacs Lisp (GNU Emacs 31.1.50) with ERT, `shellcheck`.

**Spec:** Follow-ups 17, 20 and 21 of `docs/superpowers/plans/2026-11-17-emacs-xdg-reorganization.md`, quoted in Appendix A. They state the problems. The section "Design" states the decisions this plan takes, and why. Appendix B says how the design was tested before this plan was written.

## Global Constraints

- The canonical `init.org` is `~/org/init.org`. This plan does not change it, and does not change the copy in the checkout.
- No guard may fire on the configuration as it is today. `~/org/init.org` calls `(user-paths-check-migrated)`, and nothing in the init or in a package it loads assigns one of the three roots; Task 6 checks both again before anything is pushed.
- A rule in `.gitignore` for a runtime path is a safety net: `~/src/scripts/changes` runs `git add -A` and pushes. A rule is for what Emacs writes on its own account or as a record of use. No rule may hide settings that a person saves on request, or code.
- What the litter report passes over as known must be ignored by this checkout's own `.gitignore`. The report must give the same answer whatever the caller's git configuration and global ignore file say.
- Tests never touch real state. Each runs in a scratch directory, gives git, make and Emacs a scratch home, and clears the variables through which a git hook would point git at the caller's repository.
- A hand-made trial against a throw-away home must start from an empty environment (`env -i`), or set `XDG_CONFIG_HOME`, `XDG_DATA_HOME`, `XDG_STATE_HOME` and `XDG_CACHE_HOME` as well as `HOME`. John's shell exports all four, and they take precedence over `HOME`.
- Never run plain `make`, `make init.el` or `make -B` in the worktree or in the live checkout: it copies `~/org/init.org` and loads the whole init against live state. `make test-xdg`, `make audit-xdg` and `make check-litter` are safe.
- Every shell script passes `shellcheck` and runs under `/bin/bash` 3.2. The Makefile works with `/usr/bin/make`, which is GNU Make 3.81.
- Tasks 1 to 5 change nothing outside the worktree, apart from git's own record of the worktree and its branch.
- Commit subjects follow the repository's style, `area: Sentence`. Add whatever attribution trailer your own instructions require.

## Review Focus

Each line names a condition the follow-ups imply but do not state, the behaviour a reasonable person expects, and the test that pins it.

1. **A machine without John's global ignore file.** On Clio a global ignore file hides `.claude/settings.local.json` and `.DS_Store`; in an agent's empty environment, or on a new host, nothing does. The report must be clean in both cases, and `git add -A` must take neither. Pinned by `git add -A would take nothing from a migrated checkout` and `a global ignore file changes nothing` in `xdg/check-litter-test.sh`, which seals itself from the caller's git configuration (Task 1).
2. **An agent tool writes into the checkout.** A brainstorm server leaves a token under `.superpowers/`, and a worktree can appear under `.claude/worktrees/`. Neither may be committed, and a file that is not ignored must be reported even beside ones that are. Pinned by the same two checks and by `an untracked file under .claude is reported, and only that` (Task 1).
3. **git cannot say what is in the checkout,** or is asked about a directory that is not the top of one. Neither may turn into `No litter`. Pinned by the four checks that end in `is an error` (Task 1).
4. **Unsaved work in the checkout.** John's init keeps the auto-save file of a local file beside it, and a file visited in a new directory has nothing there but its auto-save file until it is saved. `make check-litter` must not fail because a buffer is unsaved, and `git add -A` must not commit the auto-save file. Pinned by the eight checks `... is ignored` and `... is not litter` for `#notes#`, `.#notes`, `docs/#plan.md#` and `docs/.#plan.md`, and by `a new directory with only an auto-save file is not litter` and the check after it (Task 2).
5. **The stale file is not where the first check looks.** A stale copy can land in the checkout while `~/org/init.org` is current; a restored `~/org/init.org` can be older than the file it replaces; a stale `init.el` can arrive newer than `init.org`; a stale `init.elc` shadows whatever is built. None may be built or loaded quietly, and none may end in a refusal that the printed advice does not cure. Pinned by the sections of `xdg/make-init-test.sh` from `the file it replaced comes back` to `a compiled init would shadow the one that is built` (Task 4).
6. **The tests are run from a git hook.** git then exports `GIT_DIR`, and a test that builds a scratch repository with `git -C` would work on the real one. Pinned by running both shell tests with `GIT_DIR` set (Task 1 Steps 2 and 7).

Five more, lower on the list. A directory can hold a generated file beside a hand-written one, as `user-lisp/` and `auctex/` do; the generated file must be ignored and the directory still listed (`generated autoloads are ignored beside hand-written Lisp`, `parsed TeX files are ignored beside a hand-written style`, Task 2). The library can be loaded a second time, and tests bind the roots with `let`; neither may be refused (`user-paths-test-roots-cannot-be-redefined`, Task 3, beside `user-paths-test-loading-twice-changes-nothing`, which the library had already). A root that has no value yet must be allowed to get one (`user-paths-test-a-root-without-a-value-can-be-given-one`, Task 3). A file that cannot be read must be an error of its own, not a file that "predates the move" (`make fails on a ~/org/init.org it cannot read`, Task 4). And an `init.org` in which the call stands where it is not tangled must fail aloud, not build again in silence at every start (`an init.org that only mentions the call is built, and that fails`, Task 4).

## Design

The follow-ups name the problems and offer alternatives. These are the choices, with the reason for each.

- **The report lists every untracked entry at the top of the checkout, and none below.** The top is where Emacs's defaults write, and where `git add -A` does the damage. John keeps unfinished files under tracked directories (`prompts/`, `lisp/`, `docs/`), and a report that failed for each of them would be ignored. Follow-up 17 offered "a list of what may be untracked" as the alternative. There is no such list: whatever may sit at the top unversioned is ignored by a rule, and the report's list of known names is for ignored entries only.
- **What the report passes over must be ignored by this checkout's own rules.** A first version let the list of known names serve untracked entries too, so that `.claude/` would not be reported on a machine without John's global ignore file. Two reviewers showed what that hides: a file an agent tool adds under `.claude/` or `.superpowers/` is committed by `changes` while the report calls the checkout clean. So `.gitignore` now names `.claude/settings.local.json`, `.claude/worktrees/`, `.superpowers/` and `.DS_Store` itself, and anything else untracked at the top is reported.
- **A rule for what Emacs writes on its own account or as a record of use; none for settings and code.** A rule keeps a file out of `changes`, which pushes. That is right for a cookie jar, a cache, a score file, a diary or a time log, and wrong for `abbrev_defs`, `calc.el`, a file under `user-lisp/` or an AUCTeX style, which someone may want versioned with the configuration. Those stay visible to git, and the report lists them while they are untracked. The report lists every ignored file as well, so nothing with a rule can sit here unnoticed.
- **Auto-save and lock files are ignored by git and passed over by the report; backup files are ignored and reported.** The first two belong to an editing session, or hold work to recover after a crash; a directory that holds nothing else is a file that was visited there and not saved yet, and is passed over too. John's init keeps backups under the state root, so a backup file in the checkout comes from an Emacs without it, and is reported wherever it is, under `lisp/` as well. Auto-save files have been committed here by `changes` more than once, the last time in May 2025.
- **The library refuses to give its roots another value.** Follow-up 21 offered a marker file left by the mover, or a check in `early-init.el` for the guard call. A marker has to be kept in step on every host. A check of the text of `init.el` reads a file of 290 KB at every start. A variable watcher costs nothing, needs no file, and fails at exactly the form that makes an old init dangerous: its own definition of `user-data-directory`, which every version of `~/org/init.org` in that repository's history has near its top. The error names the file being loaded, and blames an init from before the move only when that file is an init file.
- **The Makefile requires the guard call; it does not search for the old definition.** The build is where an old `init.org` first does harm: `make init.el` loads the tangled file in a batch Emacs, which never reads `early-init.el`, so the watcher is not there yet. Requiring the call also catches an init that has lost its guard by accident. The call counts wherever it stands on a line that is not a comment, so that wrapping it in another form does not make `runemacs` refuse a good file.
- **The check runs before the copy from `~/org`, and again before tangling.** With only the second check, a stale `~/org/init.org` would first replace the checkout's copy and then be refused; a restored file with an older time stamp would never be copied again, and the refusal would stay. With only the first, a stale copy that arrives in the checkout itself would be built.
- **An `init.el` that does not call the guard is built again, and a rebuild removes `init.elc`.** make compares time stamps, and the hourly mirror between the hosts copies ignored files, so a stale `init.el` can arrive newer than `init.org`. Emacs loads `init.elc` in preference to `init.el`, so a stale one would shadow whatever is built, and the library's advice to run `make -B init.el` would not help.
- **The `init.el` that was built is checked too.** The check of `init.org` reads text. It cannot tell a call in a source block from one in prose, under a `COMMENT` heading or in a block that is not tangled. Such a file would pass, its `init.el` would lack the call, and the rule above would then build it again at every start without a word. So the build fails, with a message, when the `init.el` it has just made does not call the guard.
- **The library has no `user-paths-unload-function`.** It is loaded for the life of the session and installs advice as well; it was never meant to be unloaded.

## What was found while this was designed

An executor needs these facts; none of them is in the follow-ups.

- **Every assignment reaches a watcher as the operation `set`.** On Emacs 31.1.50, `setq`, `set`, `set-default`, `setq-default`, `defconst`, `setopt`, `customize-set-variable` and `set-default-toplevel-value` all arrive as `set`, from interpreted, byte-compiled and natively compiled code alike; `let`, `let*`, `cl-letf` and `cl-progv` arrive as `let` and `unlet`; a `defvar` of a variable that has a value does not arrive at all. A `defconst` of a variable that has been made unbound arrives as `set` while the variable has no value, which is why the watcher asks `boundp` first. `makunbound` and `defvaralias` get past it; nothing uses either on a root.
- **Nothing in the configuration assigns a root.** The sealed audit (`make audit-xdg`) loads the whole init with every `use-package` feature, about 1,670 features in all. With the watcher in place it reports `580 forms, 0 failed` and `0 offenders, 0 failed forms`, as it did before. A search of `~/org/init.org`, the checkout, the Custom file, the 2,888 Lisp files of the installed packages and Emacs's own Lisp found no assignment, and no other variable of these names.
- **The old init writes nothing before it defines its data directory.** Up to that form it sets the garbage collector, loads `nix-packages.el` and `use-package`, and runs exec-path-from-shell. In a terminal Emacs started on the real pre-move `init.el` with the new `early-init.el`, the session stopped at the definition with the library's message in `*Warnings*`, `after-init-hook` still ran, and nothing was created in the configuration directory.
- **`runemacs` stops when `make` fails.** It runs `make -C ~/.config/emacs EMACS=... init.el` under `set -eu` and then opens the application. A refused build therefore means that Emacs is not opened. From a terminal the message is on the screen. From the Keyboard Maestro macro that runs `runemacs`, standard error is dropped (`IncludeStdErr` is false, and standard output goes to `/tmp/runemacs.log`), so any failed build shows only as Emacs not opening. That was so before this plan, for an error anywhere in `init.org`.
- **The copy of `init.org` keeps the time stamp of `~/org/init.org`.** The Makefile copies with `cp -p`, and copies only when the file in `~/org` is newer. Both `/bin/cp` and GNU `cp` keep the time to the nanosecond on APFS, so nothing is copied again until `~/org/init.org` changes.
- **git prints a directory whose whole content is ignored as one entry.** With `--ignored=traditional`, `user-lisp/` holding only its autoloads file is listed as `!! user-lisp/`. With a hand-written file beside it, git prints `?? user-lisp/` and `!! user-lisp/.user-lisp-autoloads.el`, and `git add -A` takes only the hand-written file.
- **`.claude/` was ignored on Clio only through the global ignore file.** `~/.config/git/ignore` names `settings.local.json`, the one file in that directory. Without that file git lists `.claude/` as untracked.
- **The global ignore file does not ignore auto-save files.** Its first line is `#*#`, which git reads as a comment. The line is generated from John's Nix configuration, and this plan does not change it; the checkout gets a rule of its own, written `\#*#`.
- **John's init keeps local auto-saves beside the file, and makes no lock files.** `auto-save-file-name-transforms` redirects remote files only, and `create-lockfiles` is nil. An Emacs without the init makes both kinds.
- **A git hook exports `GIT_DIR`.** With it set, `git -C DIR` works on the repository of the hook, not on DIR. The litter test builds a scratch repository with `git -C`, so it clears git's repository variables first, and so does the script. `xdg/migrate-test.sh` does the same in two lines of its own and had no such guard: run with `GIT_DIR` set, it initialised and staged files in the repository that variable named. No hook of this repository runs the tests today.
- **`origin/master` has moved.** Another session, on Hera, pushed `b20c11b1a` at 20:45 on 17 November. It changes `init.org` and two files under `lisp/`, none of which this plan touches. Clio's checkout is one commit behind and has a modified `init.org`; Task 6 says how it is brought up to date without losing that.

## File Structure

| File | Change | Responsibility |
|---|---|---|
| `xdg/check-litter.sh` | modified in Tasks 1 and 2 | Reports runtime state that is back in the checkout, now including untracked entries at the top |
| `xdg/check-litter-test.sh` | modified in Tasks 1 and 2 | Tests for the report, 124 checks |
| `xdg/migrate-test.sh` | modified in Task 1 | Clears git's repository variables before it builds its scratch repository |
| `.gitignore` | modified in Tasks 1 and 2 | 4 rules for what agent tools and the Finder leave, and 53 for further defaults, for AUCTeX's parsed files, and for backup, auto-save and lock files |
| `lisp/user-paths.el` | modified in Task 3 | Refuses to give a root another value |
| `lisp/user-paths-test.el` | modified in Task 3 | Three more tests, 20 in all |
| `Makefile` | modified in Task 4 | Refuses to copy or tangle an `init.org` without the guard call, builds again an `init.el` without it, fails when the built `init.el` lacks it, removes `init.elc` on a rebuild; `test-xdg` runs the new test |
| `xdg/make-init-test.sh` | new in Task 4 | Runs the real Makefile in a scratch home with a stand-in for Emacs, 57 checks |
| `README.md` | modified in Task 5 | One sentence on the two guards |
| `docs/superpowers/plans/2026-11-17-emacs-xdg-reorganization.md` | modified in Task 5 | Follow-ups 17, 20 and 21, the note for John, and Task 10's text of the `test-xdg` target and its counts |

## Before you start

- Work on branch `xdg-guards` in a git worktree outside the checkout, cut from `origin/master`. Create it with exactly these commands, and do not let superpowers:using-git-worktrees choose the place: its default is a directory inside the checkout.

  ```bash
  git -C ~/.config/emacs fetch origin
  git -C ~/.config/emacs worktree add ~/src/emacs-xdg-guards -b xdg-guards origin/master
  ```

  In this plan `WT` is `~/src/emacs-xdg-guards`, and the commands of Tasks 1 to 5 run from there. Where an expected output shows `<WT>`, the command prints that directory's full path. Another session has uncommitted work in the main checkout; stay out of it.
- `emacs` on `PATH` is `/Applications/Emacs.app/Contents/MacOS/bin/emacs`.
- The tests may be run as they stand. `xdg/check-litter-test.sh` gives git a scratch home and an empty configuration; `xdg/make-init-test.sh` starts `make` from an empty environment; `lisp/user-paths-test.el` points the XDG variables into a scratch directory before it loads the library.
- In an expected output, `(...)` stands for a time stamp and a duration.
- A committed `lisp/user-paths.el` takes effect the next time Emacs starts on a host. Nothing in this plan needs Emacs to be closed.
- Task 6 needs the network (a push, and ssh to Hera) and changes the main checkout on both hosts. Tasks 1 to 5 do not.

---

### Task 1: The litter report lists untracked entries

**Files:**
- Modify: `xdg/check-litter-test.sh`
- Modify: `.gitignore`
- Modify: `xdg/check-litter.sh`
- Modify: `xdg/migrate-test.sh`

**Interfaces:**
- Consumes: `git status --porcelain -z --untracked-files=normal --ignored=traditional`, which prints one record per path, each ending in a NUL: `?? PATH` for an untracked path, `!! PATH` for an ignored one. A directory whose whole content is untracked, or whose whole content is ignored, is one record with a trailing slash.
- Produces: `xdg/check-litter.sh [CHECKOUT]`. Exit 0 and `No litter in CHECKOUT` when nothing is listed; exit 1 and one line per finding otherwise; exit 2 when CHECKOUT is not the top of a git checkout or git cannot be asked. An ignored path is printed as `CHECKOUT/PATH`, an untracked one as ``CHECKOUT/PATH (untracked: `git add -A' would commit it)``. The test gains the helpers `exactly DESCRIPTION LINE...` (the report must fail and print exactly these lines) and `error DESCRIPTION COMMAND...` (the command must exit with status 2 and must not print `No litter`). Task 2 uses `exactly`, adds one line to the script's list of known names, and adds rules to `.gitignore`.

- [x] **Step 1: Write the failing tests**

In `xdg/check-litter-test.sh`, replace

```bash
repo=$home/.config/emacs

# clean DESCRIPTION: the check must pass.
clean() {
```

with

```bash
repo=$home/.config/emacs

# Git must read neither the caller's configuration nor the caller's global
# ignore file: what they hide differs from one machine to the next.  And a
# git hook exports GIT_DIR and its relatives, which would send the git
# commands below to the caller's repository.
# shellcheck disable=SC2046  # one word for each variable name
unset $(git rev-parse --local-env-vars) GIT_TEMPLATE_DIR
export GIT_CONFIG_GLOBAL=/dev/null GIT_CONFIG_NOSYSTEM=1
export XDG_CONFIG_HOME=$home/.config

# clean DESCRIPTION: the check must pass.
clean() {
```

and replace

```bash
}

put() {
    mkdir -p "$(dirname "$1")"
```

with

```bash
}

# exactly DESCRIPTION LINE...: the check must fail and print these lines
# and no others.  A path printed with no remark is one that git ignores,
# so `git add -A' cannot commit it.
exactly() {
    local description=$1 output expected
    shift
    expected=$(printf '%s\n' "$@")
    if output=$(HOME="$home" "$here/check-litter.sh" "$repo" 2>&1); then
        failed=$((failed + 1))
        printf 'FAIL  %s (the check passed)\n' "$description"
    elif [[ $output == "$expected" ]]; then
        passed=$((passed + 1))
        printf 'ok    %s\n' "$description"
    else
        failed=$((failed + 1))
        printf 'FAIL  %s\n%s\n' "$description" "$output"
    fi
}

# error DESCRIPTION COMMAND...: COMMAND must exit with status 2 and must
# not call the checkout clean.
error() {
    local description=$1 output status
    shift
    output=$("$@" 2>&1)
    status=$?
    if [[ $status -eq 2 && $output != *'No litter'* ]]; then
        passed=$((passed + 1))
        printf 'ok    %s\n' "$description"
    else
        failed=$((failed + 1))
        printf 'FAIL  %s (status %s)\n%s\n' "$description" "$status" "$output"
    fi
}

put() {
    mkdir -p "$(dirname "$1")"
```

and replace

```bash
put "$repo/init.org"
put "$repo/lisp/a.el"
git -C "$repo" add .gitignore init.org lisp
put "$repo/init.el"
put "$repo/settings.el"
```

with

```bash
put "$repo/init.org"
put "$repo/lisp/a.el"
put "$repo/docs/plan.md"
git -C "$repo" add .gitignore init.org lisp docs
put "$repo/init.el"
put "$repo/settings.el"
```

and replace

```bash
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
```

with

```bash
put "$repo/eln-cache/31/x.eln"
put "$repo/.claude/settings.local.json"
put "$repo/.claude/worktrees/agent/README.md"
put "$repo/.superpowers/brainstorm/.last-token"
put "$repo/.DS_Store"
put "$repo/docs/.DS_Store"
ln -s /nix/store/none "$repo/nix-packages"
ln -s /nix/store/none.el "$repo/nix-packages.el"
clean 'a migrated checkout is clean'

# All of that is ignored by the checkout's own rules, so `git add -A' would
# take none of it, and no global ignore file is needed for the report.
if [[ -z $(git -C "$repo" add -A --dry-run) ]]; then
    passed=$((passed + 1))
    printf 'ok    git add -A would take nothing from a migrated checkout\n'
else
    failed=$((failed + 1))
    printf 'FAIL  git add -A would take nothing from a migrated checkout\n'
    git -C "$repo" add -A --dry-run
fi
mkdir -p "$home/.config/git"
printf '%s\n' settings.local.json .DS_Store '*.pem' >"$home/.config/git/ignore"
clean 'a global ignore file changes nothing'
rm -rf "${home:?}/.config/git"

# Untracked and not ignored: `git add -A' would commit it.  At the top of
# the checkout that is where Emacs's defaults write; below a tracked
# directory it is work in progress.
put "$repo/notes.txt"
exactly 'an untracked file at the top is reported' \
    "$repo/notes.txt (untracked: \`git add -A' would commit it)"
rm "$repo/notes.txt"

put "$repo/surprise/state.el"
exactly 'an untracked directory at the top is reported' \
    "$repo/surprise (untracked: \`git add -A' would commit it)"
rm -rf "${repo:?}/surprise"

put "$repo/lisp/b.el"
put "$repo/lisp/sub/c.el"
put "$repo/docs/draft.md"
clean 'untracked files below a tracked directory are work in progress'
rm -rf "$repo/lisp/b.el" "${repo:?}/lisp/sub" "$repo/docs/draft.md"

# What an agent tool adds beside its ignored files is untracked like
# anything else, and the ignored files beside it are still passed over.
put "$repo/.claude/commands/review.md"
exactly 'an untracked file under .claude is reported, and only that' \
    "$repo/.claude (untracked: \`git add -A' would commit it)"
rm -rf "${repo:?}/.claude/commands"

# The report must not depend on how git is configured to show untracked
# files.
git -C "$repo" config status.showUntrackedFiles no
put "$repo/tramp"
exactly 'ignored litter is reported when git hides untracked files' "$repo/tramp"
rm "$repo/tramp"
put "$repo/notes.txt"
exactly 'an untracked file is reported when git hides untracked files' \
    "$repo/notes.txt (untracked: \`git add -A' would commit it)"
rm "$repo/notes.txt"
git -C "$repo" config status.showUntrackedFiles all
clean 'a migrated checkout is clean when git lists every untracked file'
git -C "$repo" config --unset status.showUntrackedFiles

# Each of these names has a rule in .gitignore.  The line must be the path
# alone: with a remark, the rule would be missing.
for path in data/history var/pcache/fonts url/cache/a transient/history.el \
    auto-save-list/.saves-1-host~ multisession/files/emoji/x persist/queues \
```

and replace

```bash
    package-quickstart.el server/server; do
    put "$repo/$path"
    litter "${path%%/*} is reported" "$repo/${path%%/*}"
    rm -rf "${repo:?}/${path%%/*}"
done
```

with

```bash
    package-quickstart.el server/server; do
    put "$repo/$path"
    exactly "${path%%/*} is ignored, and reported" "$repo/${path%%/*}"
    rm -rf "${repo:?}/${path%%/*}"
done
```

and replace

```bash
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
```

with

```bash
clean 'the checkout is clean again afterwards'

error 'a directory that is not a checkout is an error' \
    env HOME="$home" "$here/check-litter.sh" "$scratch"

# Paths in git's answer are relative to the top of the checkout.  For a
# directory below it the report would print paths that do not exist, or
# call a copy of the checkout clean because git ignores it.
error 'a directory below the top of a checkout is an error' \
    env HOME="$home" "$here/check-litter.sh" "$repo/lisp"

# If git cannot say what is in the checkout, the report must not call it
# clean.
cp "$repo/.git/index" "$scratch/index"
printf 'not an index\n' >"$repo/.git/index"
error 'a failing git status is an error, not a clean report' \
    env HOME="$home" "$here/check-litter.sh" "$repo"
cp "$scratch/index" "$repo/.git/index"
error 'a temporary directory that is missing is an error' \
    env HOME="$home" TMPDIR="$scratch/missing" "$here/check-litter.sh" "$repo"
clean 'the checkout is clean once git works again'

printf '\n%d passed, %d failed\n' "$passed" "$failed"
```

The first block gives git a scratch home and no configuration, for every command in the test and for the script it runs. The loop over the old names changes from `litter` to `exactly`: now that untracked entries are reported too, a line that merely contains the name would be printed with or without the rule, and the check would no longer show that the rule is there.

- [x] **Step 2: Run the tests to verify that they fail**

Run: `xdg/check-litter-test.sh 2>&1 | grep -E '^FAIL|passed, '`

Expected:

```text
FAIL  git add -A would take nothing from a migrated checkout
FAIL  a global ignore file changes nothing
FAIL  an untracked file at the top is reported (the check passed)
FAIL  an untracked directory at the top is reported (the check passed)
FAIL  an untracked file under .claude is reported, and only that (the check passed)
FAIL  ignored litter is reported when git hides untracked files (the check passed)
FAIL  an untracked file is reported when git hides untracked files (the check passed)
FAIL  a migrated checkout is clean when git lists every untracked file
FAIL  a directory below the top of a checkout is an error (status 0)
FAIL  a failing git status is an error, not a clean report (status 0)
FAIL  a temporary directory that is missing is an error (status 0)
39 passed, 11 failed
```

Each failure is one of the defects. `.gitignore` has no rule for what agent tools and the Finder leave (the first), and with a second file in `.claude/` the script reports the one that is ignored (the second). The script lists no untracked entry (the next three, and the seventh). It leaves `status.showUntrackedFiles` to the configuration: with `no`, git lists no ignored entry either, and with `all` it lists the files of an ignored directory one by one, which the script's list of known names does not match (the sixth and the eighth). It accepts a directory below the top of the checkout and calls it clean, and it prints `No litter` when git fails (the ninth and the tenth). The last fails only for its status: the script has no temporary file yet.

Run: `GIT_DIR=/nonexistent/.git xdg/migrate-test.sh 2>/dev/null | grep -E '^FAIL|passed, '`

Expected:

```text
FAIL  only the unknown file is reported as left behind
233 passed, 1 failed
```

That is how a git hook would run the mover's test: with `GIT_DIR` set, its `git -C` commands leave the scratch repository alone and go where the variable points. Nothing can be created at the path used here, and git's complaints about it are what `2>/dev/null` hides. The run takes a minute or two.

- [x] **Step 3: Ignore what agent tools and the Finder leave**

Append to `.gitignore`:

```gitignore

# What agent tools and the Finder leave here.  These rules keep it out of
# `git add -A' on every machine, and they are why `make check-litter'
# passes over it: a global ignore file differs from one machine to the
# next, and the report must not.
/.claude/settings.local.json
/.claude/worktrees/
/.superpowers/
.DS_Store
```

- [x] **Step 4: Change the script**

In `xdg/check-litter.sh`, replace

```bash
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
```

with

```bash
#   - every ignored path in the checkout that is not known configuration
#     or a build product;
#   - every untracked path at the top of the checkout: `git add -A' would
#     commit it, and the top is where Emacs's defaults write.  Untracked
#     files below a tracked directory are work in progress and are left
#     alone;
#   - every empty directory at the top of the checkout.
#
# What counts as known configuration must be ignored by this checkout's
# own .gitignore.  A global ignore file differs from one machine to the
# next, and the report must not.
#
# An Emacs started with -Q or -q reads no init file and writes to the
# built-in defaults, so an auto-save-list/, transient/ or url/ directory,
# or a file such as tramp, bookmarks or network-security.eld, can appear
# here after such a run.  Move it to the place lisp/user-paths.el gives
# that file, or delete it if it holds nothing worth keeping.  eln-cache/
# appears for the same reason, cannot be prevented, and is not reported.
#
# The exit status is 0 when nothing is listed, 1 when something is, and 2
# when CHECKOUT is not the top of a git checkout, git cannot be asked, or
# no temporary file can be made.

set -euo pipefail
```

and replace

```bash
status=0

if ! git -C "$checkout" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
    printf 'check-litter: %s is not a git checkout\n' "$checkout" >&2
    exit 2
fi
```

with

```bash
status=0

# A git hook exports GIT_DIR and its relatives.  They would send every git
# command below to the repository of the hook, whatever CHECKOUT is.
# shellcheck disable=SC2046  # one word for each variable name
unset $(git rev-parse --local-env-vars 2>/dev/null)

# Paths in git's answer are relative to the top of the checkout, so that is
# what CHECKOUT must be.  If git refuses, its own reason is printed first.
top=$(git -C "$checkout" rev-parse --show-toplevel) || top=
if [[ -z $top || ! $top -ef $checkout ]]; then
    printf 'check-litter: %s is not the top of a git checkout\n' "$checkout" >&2
    exit 2
fi
```

and replace

```bash
done

while IFS= read -r -d '' entry; do
    [[ $entry == '!! '* ]] || continue
    path=${entry#'!! '}
    case $path in
    init.el | settings.el | nix-packages | nix-packages.el) continue ;;
    certs/ | eln-cache/ | .claude/ | .superpowers/) continue ;;
    prompts/.prompt-deploy-manifest.json) continue ;;
    lisp/* | *.elc | .DS_Store | */.DS_Store) continue ;;
```

with

```bash
done

# Ask git once, with the two settings that decide what it lists, so that
# the report does not depend on status.showUntrackedFiles.  If git cannot
# answer, say so: an empty list would read as a clean checkout.
listing=$(mktemp "${TMPDIR:-/tmp}/check-litter.XXXXXX") || {
    printf 'check-litter: cannot create a temporary file\n' >&2
    exit 2
}
trap 'rm -f "$listing"' EXIT
if ! git --no-optional-locks -C "$checkout" status --porcelain -z \
    --untracked-files=normal --ignored=traditional >"$listing"; then
    printf 'check-litter: git status failed in %s\n' "$checkout" >&2
    exit 2
fi

while IFS= read -r -d '' entry; do
    case $entry in
    '?? '*)
        # Untracked.  Below a tracked directory it is work in progress.
        path=${entry#'?? '}
        path=${path%/}
        if [[ $path != */* ]]; then
            report "$checkout/$path (untracked: \`git add -A' would commit it)"
        fi
        continue
        ;;
    '!! '*) path=${entry#'!! '} ;;
    *) continue ;;
    esac
    # Ignored.  Known configuration and build products are passed over.
    case $path in
    init.el | settings.el | nix-packages | nix-packages.el) continue ;;
    certs/ | eln-cache/ | .claude/* | .superpowers/*) continue ;;
    prompts/.prompt-deploy-manifest.json) continue ;;
    lisp/* | *.elc | .DS_Store | */.DS_Store) continue ;;
```

and replace

```bash
    esac
    report "$checkout/${path%/}"
done < <(git --no-optional-locks -C "$checkout" status --porcelain --ignored -z)

while IFS= read -r directory; do
```

with

```bash
    esac
    report "$checkout/${path%/}"
done <"$listing"

while IFS= read -r directory; do
```

- [x] **Step 5: Keep the mover's test out of the caller's repository**

In `xdg/migrate-test.sh`, replace

```bash
}
trap cleanup EXIT

passed=0
```

with

```bash
}
trap cleanup EXIT

# A git hook exports GIT_DIR and its relatives.  They would send the git
# commands below to the repository of the hook.
# shellcheck disable=SC2046  # one word for each variable name
unset $(git rev-parse --local-env-vars) GIT_TEMPLATE_DIR

passed=0
```

- [x] **Step 6: Run the tests to verify that they pass**

Run: `xdg/check-litter-test.sh | tail -1 && PATH="/usr/bin:/bin:$PATH" /bin/bash xdg/check-litter-test.sh | tail -1 && shellcheck xdg/check-litter.sh xdg/check-litter-test.sh xdg/migrate-test.sh; echo "exit=$?"`

Expected:

```text
50 passed, 0 failed
50 passed, 0 failed
exit=0
```

The second run uses the system's bash 3.2, git and BSD tools.

- [x] **Step 7: Run both tests as a git hook would**

Run: `GIT_DIR=/nonexistent/.git xdg/check-litter-test.sh 2>/dev/null | tail -1; GIT_DIR=/nonexistent/.git xdg/migrate-test.sh 2>/dev/null | tail -1`

Expected:

```text
50 passed, 0 failed
234 passed, 0 failed
```

- [x] **Step 8: Run the report on the worktree and on the live checkout**

Run: `xdg/check-litter.sh; echo "exit=$?"; xdg/check-litter.sh ~/.config/emacs; echo "exit=$?"`

Expected:

```text
No litter in <WT>
exit=0
No litter in /Users/johnw/.config/emacs
exit=0
```

Both runs only read. The second uses the worktree's script and the live checkout's own `.gitignore`, which does not have the new rules yet. If either prints a path instead, the path is real: leave the script as it is and report the line.

- [x] **Step 9: Commit**

```bash
git add xdg/check-litter-test.sh .gitignore xdg/check-litter.sh xdg/migrate-test.sh
git commit -m "xdg: Report untracked files at the top of the checkout"
```

---

### Task 2: Ignore rules for the remaining default names

**Files:**
- Modify: `xdg/check-litter-test.sh`
- Modify: `.gitignore`
- Modify: `xdg/check-litter.sh`

**Interfaces:**
- Consumes: the script and the test of Task 1, and the test's helpers `clean DESCRIPTION`, `exactly DESCRIPTION LINE...` and `put FILE`.
- Produces: nothing that a later task uses.

- [x] **Step 1: Write the failing tests**

In `xdg/check-litter-test.sh`, replace

```bash
done

put "$repo/eshell/history"
litter 'eshell history is reported' "$repo/eshell/history"
```

with

```bash
done

# More defaults of Emacs and of the installed packages.  Each line is a
# file to create, and the path the report must then print.
while IFS='|' read -r path listed; do
    put "$repo/$path"
    exactly "$listed is ignored, and reported" "$repo/$listed"
    rm -rf "${repo:?}/${path%%/*}"
done <<'NAMES'
completions|completions
idlwave/idlusercat.el|idlwave
shadow_todo|shadow_todo
type-break|type-break
filesets-cache.el|filesets-cache.el
thumbs/a.png|thumbs
tramp-host.encfs6.xml|tramp-host.encfs6.xml
newsticker/feeds/x|newsticker
image-dired/a.jpg|image-dired
rcirc-log/channel|rcirc-log
user-lisp/.user-lisp-autoloads.el|user-lisp
srecode-map.el|srecode-map.el
semanticdb/x|semanticdb
ede-projects.el|ede-projects.el
kkcrc|kkcrc
games/snake-scores|games
tutorial/x|tutorial
ecompleterc|ecompleterc
org-persist/index.eld|org-persist
eww-bookmarks|eww-bookmarks
bdfcache.el|bdfcache.el
diary|diary
notes|notes
quickurls|quickurls
timelog|timelog
todo/todo.todo|todo
.emacs.desktop|.emacs.desktop
.emacs.desktop.lock|.emacs.desktop.lock
wombag/token|wombag
.mc-lists.el|.mc-lists.el
projectile-bookmarks.eld|projectile-bookmarks.eld
projectile-sessions/x|projectile-sessions
org-table-highlight-metadata.el|org-table-highlight-metadata.el
lena-snapshots/x|lena-snapshots
wikipedia.db|wikipedia.db
auctex/auto/x.el|auctex
web-cookies|web-cookies
nov-places|nov-places
org-roam.db|org-roam.db
aria2c.session|aria2c.session
aria2-controller.eieio|aria2-controller.eieio
.persistent-scratch|.persistent-scratch
bm-repository|bm-repository
vimish-fold/x|vimish-fold
workspace/x|workspace
lsp-cache/x|lsp-cache
intelephense/x|intelephense
index.sqlite|index.sqlite
.lsp-eslint-choices|.lsp-eslint-choices
NAMES

# Beside a file that a person wrote, the generated one is still ignored,
# and the directory is listed for the sake of the other.
put "$repo/user-lisp/mine.el"
put "$repo/user-lisp/.user-lisp-autoloads.el"
exactly 'generated autoloads are ignored beside hand-written Lisp' \
    "$repo/user-lisp (untracked: \`git add -A' would commit it)" \
    "$repo/user-lisp/.user-lisp-autoloads.el"
rm -rf "${repo:?}/user-lisp"
put "$repo/auctex/style/mine.el"
put "$repo/auctex/auto/x.el"
exactly 'parsed TeX files are ignored beside a hand-written style' \
    "$repo/auctex (untracked: \`git add -A' would commit it)" \
    "$repo/auctex/auto"
rm -rf "${repo:?}/auctex"

# Settings that a person saves on request, and code, have no rule: they
# stay visible to git and to this report.
for path in abbrev_defs calc.el eudc-options shadows strokes viper \
    user-lisp/mine.el auctex/style/mine.el; do
    put "$repo/$path"
    exactly "${path%%/*} is not ignored" \
        "$repo/${path%%/*} (untracked: \`git add -A' would commit it)"
    rm -rf "${repo:?}/${path%%/*}"
done

# Backup files come from an Emacs without this init, which keeps its own
# elsewhere.  They are ignored and reported, wherever they are.
put "$repo/notes.txt~"
exactly 'a backup file at the top is ignored, and reported' "$repo/notes.txt~"
rm "$repo/notes.txt~"
put "$repo/docs/plan.md~"
exactly 'a backup file below a tracked directory is ignored, and reported' \
    "$repo/docs/plan.md~"
rm "$repo/docs/plan.md~"
put "$repo/lisp/a.el~"
exactly 'a backup file under lisp is ignored, and reported' "$repo/lisp/a.el~"
rm "$repo/lisp/a.el~"

# Auto-save and lock files belong to an editing session.  Git must ignore
# them, so that `git add -A' cannot commit one, and they are not litter.
for path in '#notes#' '.#notes' 'docs/#plan.md#' 'docs/.#plan.md'; do
    case $path in
    *'.#'*) ln -s 'someone@host.999:1700000000' "$repo/$path" ;;
    *) put "$repo/$path" ;;
    esac
    if git -C "$repo" check-ignore -q -- "$path"; then
        passed=$((passed + 1))
        printf 'ok    %s is ignored\n' "$path"
    else
        failed=$((failed + 1))
        printf 'FAIL  %s is ignored\n' "$path"
    fi
    clean "$path is not litter"
    rm "$repo/$path"
done

# A file visited in a new directory, and not saved yet, has only its
# auto-save file there.  With anything else beside it the directory counts.
put "$repo/docs/new/#draft.md#"
clean 'a new directory with only an auto-save file is not litter'
rm -rf "${repo:?}/docs/new"
put "$repo/drafts/#draft.md#"
clean 'nor is one at the top of the checkout'
put "$repo/drafts/cache.db"
exactly 'with another file beside the auto-save file it is reported' \
    "$repo/drafts (untracked: \`git add -A' would commit it)"
rm -rf "${repo:?}/drafts"
put "$repo/var/#x#"
put "$repo/var/y"
exactly 'a state directory is reported though it holds an auto-save file' "$repo/var"
rm -rf "${repo:?}/var"

put "$repo/eshell/history"
litter 'eshell history is reported' "$repo/eshell/history"
```

The table has one line for each new rule that names a file or a directory: the path to create, and the path the report must then print with no remark. `user-lisp` and `auctex` are printed as directories because git prints a directory whose whole content is ignored as one entry.

- [x] **Step 2: Run the tests to verify that they fail**

Run: `xdg/check-litter-test.sh 2>&1 | grep -c '^FAIL'; xdg/check-litter-test.sh 2>&1 | tail -1`

Expected:

```text
61
63 passed, 61 failed
```

The forty-nine names of the table are not ignored yet. Neither are the two generated files beside hand-written ones, the three backup files, nor the four auto-save and lock files; the two of those four at the top of the checkout are reported as untracked, and so is the new directory at the top that holds only an auto-save file.

- [x] **Step 3: Add the rules**

Append to `.gitignore`:

```gitignore

# More defaults, of Emacs itself and of the packages this configuration
# loads: state, caches, and what Emacs records as it is used (bookmarks,
# scores, logs, a diary, notes).  None of it belongs in a commit, and
# `make check-litter' lists whatever turns up.  Settings that a person
# saves on request (abbrev_defs, calc.el, eudc-options, shadows, strokes,
# viper) and code (user-lisp/, auctex/style/, themes) have no rule on
# purpose: they stay visible, and the report lists them while they are
# untracked.
/.emacs.desktop
/.emacs.desktop.lock
/.lsp-eslint-choices
/.mc-lists.el
/.persistent-scratch
/aria2-controller.eieio
/aria2c.session
/bdfcache.el
/bm-repository
/completions
/diary
/ecompleterc
/ede-projects.el
/eww-bookmarks
/filesets-cache.el
/games/
/idlwave/
/image-dired/
/index.sqlite
/intelephense/
/kkcrc
/lena-snapshots/
/lsp-cache/
/newsticker/
/notes
/nov-places
/org-persist/
/org-roam.db
/org-table-highlight-metadata.el
/projectile-bookmarks.eld
/projectile-sessions/
/quickurls
/rcirc-log/
/semanticdb/
/shadow_todo
/srecode-map.el
/thumbs/
/timelog
/todo/
/tramp-*.encfs6.xml
/tutorial/
/type-break
/user-lisp/.user-lisp-autoloads.el
/vimish-fold/
/web-cookies
/wikipedia.db
/wombag/
/workspace/
# What AUCTeX parses is a cache; its style directory holds styles that a
# person writes.
/auctex/*
!/auctex/style/
# Backup files come from an Emacs without this init, which keeps its own
# under the state root; `make check-litter' lists them.  Auto-save and lock
# files belong to an editing session, and it leaves them alone.
*~
\#*#
.#*
```

The names come from a sweep of Emacs's own Lisp and of the packages this configuration loads, for every default that is built from `user-emacs-directory`; a reviewer then found the writer of each in the sources. Each was sorted by what its file holds. Not all of them are state or caches in the strict sense. `diary`, `notes`, `quickurls`, `timelog` and `todo/` hold what a person enters through a command. `eww-bookmarks`, `lena-snapshots/`, `org-table-highlight-metadata.el` and `wikipedia.db` are data, which `lisp/user-paths.el` keeps under the data root. `tramp-*.encfs6.xml` holds key configuration that Tramp writes. They get a rule all the same, because none of it belongs in a commit that `changes` pushes.

- [x] **Step 4: Report backup files everywhere, and leave auto-save and lock files out of the report**

In `xdg/check-litter.sh`, replace

```bash
#   - ~/.emacs.d, ~/.emacs and ~/.emacs.el, any of which makes Emacs
#     ignore this checkout altogether;
#   - every ignored path in the checkout that is not known configuration
#     or a build product;
#   - every untracked path at the top of the checkout: `git add -A' would
#     commit it, and the top is where Emacs's defaults write.  Untracked
```

with

```bash
#   - ~/.emacs.d, ~/.emacs and ~/.emacs.el, any of which makes Emacs
#     ignore this checkout altogether;
#   - every ignored path in the checkout that is not known configuration,
#     a build product, or the auto-save or lock file of a file that is
#     being edited, alone in its directory or not;
#   - every untracked path at the top of the checkout: `git add -A' would
#     commit it, and the top is where Emacs's defaults write.  Untracked
```

and replace

```bash
    # Ignored.  Known configuration and build products are passed over.
    case $path in
    init.el | settings.el | nix-packages | nix-packages.el) continue ;;
    certs/ | eln-cache/ | .claude/* | .superpowers/*) continue ;;
    prompts/.prompt-deploy-manifest.json) continue ;;
    lisp/* | *.elc | .DS_Store | */.DS_Store) continue ;;
    eshell/)
        # alias, login and profile are configuration; history is not.
```

with

```bash
    # Ignored.  Known configuration and build products are passed over.
    case $path in
    # A backup file comes from an Emacs without this init, wherever it is.
    *'~') ;;
    init.el | settings.el | nix-packages | nix-packages.el) continue ;;
    certs/ | eln-cache/ | .claude/* | .superpowers/*) continue ;;
    prompts/.prompt-deploy-manifest.json) continue ;;
    lisp/* | *.elc | .DS_Store | */.DS_Store) continue ;;
    # Auto-save and lock files belong to an editing session, or hold work
    # to recover after a crash.  .gitignore names them so that `git add -A'
    # never commits one; they are not state.
    '#'*'#' | */'#'*'#' | '.#'* | */'.#'*) continue ;;
    eshell/)
        # alias, login and profile are configuration; history is not.
```

and replace

```bash
        done < <(ls -A "$checkout/eshell")
        continue
        ;;
    esac
```

with

```bash
        done < <(ls -A "$checkout/eshell")
        continue
        ;;
    */)
        # A directory that holds nothing but auto-save and lock files: a
        # file was visited in a new directory and has not been saved yet.
        if [[ -z $(find "$checkout/$path" ! -type d ! -name '#*#' ! -name '.#*' -print -quit) ]]; then
            continue
        fi
        ;;
    esac
```

The first new line of the list has no `continue`: a backup file falls through to the report before `lisp/*` can pass it over.

- [x] **Step 5: Run the tests to verify that they pass**

Run: `xdg/check-litter-test.sh | tail -1 && PATH="/usr/bin:/bin:$PATH" /bin/bash xdg/check-litter-test.sh | tail -1 && shellcheck xdg/check-litter.sh xdg/check-litter-test.sh; echo "exit=$?"`

Expected:

```text
124 passed, 0 failed
124 passed, 0 failed
exit=0
```

- [x] **Step 6: Check that no rule hides a tracked file**

Run: `git ls-files -ci --exclude-from=.gitignore; echo "exit=$?"`

Expected: `exit=0` and no other line. The command lists every tracked file that a rule of `.gitignore` matches.

- [x] **Step 7: Run the report on the worktree and on the live checkout**

Run: `xdg/check-litter.sh; echo "exit=$?"; xdg/check-litter.sh ~/.config/emacs; echo "exit=$?"`

Expected:

```text
No litter in <WT>
exit=0
No litter in /Users/johnw/.config/emacs
exit=0
```

If either prints a path, leave the script as it is and report the line.

- [x] **Step 8: Commit**

```bash
git add xdg/check-litter-test.sh .gitignore xdg/check-litter.sh
git commit -m "xdg: Ignore the remaining default state files"
```

---

### Task 3: The roots cannot be given another value

**Files:**
- Modify: `lisp/user-paths-test.el`
- Modify: `lisp/user-paths.el`

**Interfaces:**
- Consumes: the constants `user-data-directory`, `user-state-directory` and `user-cache-directory` of `lisp/user-paths.el`, and the test file's `user-paths-test--child ENVIRONMENT FORM`, `user-paths-test--bare` and `user-paths-test-root`.
- Produces: `(user-paths--keep-root SYMBOL NEWVAL OPERATION WHERE)`, a variable watcher that the library installs on its three roots. Nothing else calls it. Its error message contains the variable's name, `lisp/user-paths.el` and the file being loaded if there is one; when that file is called `init.el` or `init.elc`, it also says to run `make -B init.el`.

- [x] **Step 1: Write the failing tests**

In `lisp/user-paths-test.el`, replace

```elisp
      (delete-directory legacy))))

(ert-deftest user-paths-test-early-init-loads-the-library ()
  ;; early-init.el sits beside lisp/ and finds the library from
```

with

```elisp
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
```

The third test writes an `init.el` that begins as `init.org` did until the move, and loads it in a fresh Emacs that has loaded the library.

- [x] **Step 2: Run the tests to verify that they fail**

Run: `emacs --batch -Q -l lisp/user-paths-test.el -f ert-run-tests-batch-and-exit 2>&1 | grep -E '^Ran |^   FAILED  user'`

Expected:

```text
Ran 20 tests, 17 results as expected, 3 unexpected (...)
   FAILED  user-paths-test-a-root-without-a-value-can-be-given-one
   FAILED  user-paths-test-a-stale-init-stops-at-its-first-definition
   FAILED  user-paths-test-roots-cannot-be-redefined
```

- [x] **Step 3: Guard the roots**

In `lisp/user-paths.el`, replace

```elisp
;; beside its package in init.org, written as (user-data "..."),
;; (user-state "...") or (user-cache "...").
;;
;; An Emacs started with -Q or -q reads neither early-init.el nor init.el
```

with

```elisp
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
```

and replace

```elisp
  "Expand PATH below `user-cache-directory'."
  (expand-file-name path user-cache-directory))

(defconst user-paths-table
```

with

```elisp
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
```

- [x] **Step 4: Run the tests to verify that they pass**

Run: `emacs --batch -Q -l lisp/user-paths-test.el -f ert-run-tests-batch-and-exit 2>&1 | grep -E '^Ran |FAILED'`

Expected:

```text
Ran 20 tests, 20 results as expected, 0 unexpected (...)
```

- [x] **Step 5: Check that the library compiles without a warning**

Run: `d=$(mktemp -d) && cp lisp/user-paths.el "$d/" && emacs --batch -Q -f batch-byte-compile "$d/user-paths.el" 2>&1 | grep -c .; ls "$d"; rm -rf "$d"`

Expected:

```text
0
user-paths.el
user-paths.elc
```

The `0` is the number of lines the compiler printed. The compiled file stays in the scratch directory: `early-init.el` loads the source by name, and no `user-paths.elc` may ever sit beside it.

- [x] **Step 6: Commit**

```bash
git add lisp/user-paths-test.el lisp/user-paths.el
git commit -m "user-paths: Refuse to give a root another value"
```

---

### Task 4: make refuses a stale init.org

**Files:**
- Create: `xdg/make-init-test.sh`
- Modify: `Makefile`

**Interfaces:**
- Consumes: the Makefile's rules `init.org: ~/org/init.org` and `init.el: init.org`, and the call `(user-paths-check-migrated)` in `init.org`.
- Produces: the make variable `GUARD`, the phony target `stale-init`, and a `test-xdg` target that runs five test files.

- [x] **Step 1: Write the failing test**

Create `xdg/make-init-test.sh`:

```bash
#!/usr/bin/env bash
# make-init-test.sh --- the Makefile must not build init.el from a stale init.org
#
# Usage: xdg/make-init-test.sh
#
# An init.org from before lisp/user-paths.el keeps its state inside the
# configuration directory.  Built on a host whose state has moved, it
# starts Emacs on empty histories and says nothing.  Such a file can come
# back from the other host or from git, so `make init.el' refuses it, in
# ~/org and in the checkout, and leaves the last init.el in place.
#
# The test runs the real Makefile in a throw-away home directory, with a
# stand-in for Emacs that records that it was started and copies the source
# blocks of init.org to init.el.

set -uo pipefail

here=$(cd "$(dirname "$0")" && pwd -P)
scratch=$(mktemp -d "${TMPDIR:-/tmp}/make-init-test.XXXXXX")
if [[ -z $scratch || ! -d $scratch ]]; then
    printf 'make-init-test: cannot create a scratch directory\n' >&2
    exit 2
fi
scratch=$(cd "$scratch" && pwd -P)

# Remove the scratch directory on exit, and nothing that is not one.
cleanup() {
    case $scratch in
    */make-init-test.??????) rm -rf "$scratch" ;;
    esac
}
trap cleanup EXIT

passed=0
failed=0
home=$scratch/home
repo=$home/.config/emacs
canonical=$home/org/init.org

# check DESCRIPTION COMMAND...: passes when COMMAND succeeds.
check() {
    local description=$1
    shift
    if "$@"; then
        passed=$((passed + 1))
        printf 'ok    %s\n' "$description"
    else
        failed=$((failed + 1))
        printf 'FAIL  %s\n' "$description"
    fi
}

mkdir -p "$repo/lisp" "$home/org" "$scratch/bin"
cp "$here/../Makefile" "$repo/Makefile"

# The stand-in leaves a line for each start, and "tangles": what stands
# between #+begin_src and #+end_src goes to init.el, and nothing else does.
cat >"$scratch/bin/emacs" <<'EOF'
#!/bin/sh
echo started >>"$EMACS_STARTS"
sed -n '/^#+begin_src/,/^#+end_src/{/^#+/!p;}' init.org >init.el
EOF
chmod +x "$scratch/bin/emacs"

# build [ARGS...]: run make init.el in the scratch home, with nothing of
# the caller's environment but PATH.
build() {
    env -i PATH="$scratch/bin:$PATH" HOME="$home" EMACS_STARTS="$scratch/starts" \
        make -C "$repo" "$@" init.el >"$scratch/output" 2>&1
}
# fails [ARGS...]: make must fail.
fails() {
    ! build "$@"
}
# printed TEXT, not_printed TEXT: what the last run of make said.
printed() {
    grep -qF -- "$1" "$scratch/output"
}
not_printed() {
    ! printed "$1"
}
# refused [ARGS...]: make must fail before it builds anything, and with the
# refusal, not with some other error.
refused() {
    fails "$@" && printed 'does not call (user-paths-check-migrated)' &&
        not_printed 'was built'
}
starts() {
    if [[ -f $scratch/starts ]]; then wc -l <"$scratch/starts" | tr -d ' '; else echo 0; fi
}

# make compares modification times, and a build takes less than a second.
# Give each version of init.org a day of its own, and move init.el to the
# afternoon of the day it was built from, so that the next version is newer.
day() {
    touch -t "202601${1}0000" "$canonical"
}
built_on() {
    touch -t "202601${1}1200" "$repo/init.el"
}

# current MARK, stale MARK: an init.org of each kind.  MARK is a line of its
# source block, so that init.el shows which init.org it was built from.
current() {
    printf '%s\n' '* Init' '#+begin_src emacs-lisp' "(require 'user-paths)" \
        '(user-paths-check-migrated)' "$1" '#+end_src'
}
stale() {
    printf '%s\n' '* Init' '#+begin_src emacs-lisp' \
        '(defconst user-data-directory (emacs-path "data"))' "$1" '#+end_src'
}

# --------------------------------------------------- a current init.org
current 'one' >"$canonical"
day 01
check 'a current init.org is built' build
built_on 01
check 'the build started Emacs once' test "$(starts)" = 1
check 'init.el holds the build' grep -q '^one$' "$repo/init.el"

# ------------------------------- a stale one arrives in ~/org, and is newer
stale 'two' >"$canonical"
day 02
check 'a stale ~/org/init.org is refused' refused
# shellcheck disable=SC2088  # the message spells the file with a tilde
check 'the refusal names that file' printed '~/org/init.org does not call'
check 'the refusal says what to do' printed 'Restore ~/org/init.org'
check 'it was not copied into the checkout' grep -q '^one$' "$repo/init.org"
check 'Emacs was not started for it' test "$(starts)" = 1
check 'init.el is still the last good build' grep -q '^one$' "$repo/init.el"
check 'a second try is refused as well' refused
check 'a forced build is refused as well' refused -B
check 'Emacs was still not started' test "$(starts)" = 1
check 'init.el is still the last good build after that' grep -q '^one$' "$repo/init.el"

# ---------- the file it replaced comes back, with the time stamp it had
current 'one' >"$canonical"
day 01
check 'with ~/org/init.org restored there is nothing to build' build
check 'Emacs was not started for that' test "$(starts)" = 1
check 'init.el is the same build as before' grep -q '^one$' "$repo/init.el"

# ------------------------------------------------ a newer current one
current 'three' >"$canonical"
day 03
check 'a newer current init.org is built' build
built_on 03
check 'the build started Emacs again' test "$(starts)" = 2
check 'init.el holds the new build' grep -q '^three$' "$repo/init.el"

# ------- a stale copy lands in the checkout; the one in ~/org is current
rm -f "$repo/init.org"
stale 'four' >"$repo/init.org"
touch -t 202601040000 "$repo/init.org"
check 'a stale init.org in the checkout is refused' refused
check 'the refusal names that file' grep -q '^init.org does not call' "$scratch/output"
check 'the refusal says how to get the current one' printed 'touch ~/org/init.org'
check 'Emacs was not started for it' test "$(starts)" = 2
check 'init.el is still the last good build' grep -q '^three$' "$repo/init.el"
check 'a forced build is refused as well' refused -B
day 05
check 'once ~/org/init.org is touched, the current one is built' build
built_on 05
check 'the build started Emacs a third time' test "$(starts)" = 3
check 'the checkout has the current init.org again' grep -q '^three$' "$repo/init.org"
check 'init.el is built from it' grep -q '^three$' "$repo/init.el"

# ------------------------ the call counts wherever it stands on a line
printf '%s\n' '* Init' '#+begin_src emacs-lisp' \
    '  (unless noninteractive (user-paths-check-migrated))' 'five' '#+end_src' >"$canonical"
day 06
check 'a call inside another form is the call' build
built_on 06
check 'the build started Emacs a fourth time' test "$(starts)" = 4
check 'init.el holds that build' grep -q '^five$' "$repo/init.el"

# ------------------------------- but not on a line that is a comment
printf '%s\n' '* Init' '#+begin_src emacs-lisp' ';; (user-paths-check-migrated)' \
    '#+end_src' >"$canonical"
day 07
check 'a call that is commented out is not the call' refused
check 'Emacs was not started for it' test "$(starts)" = 4
check 'init.el is unchanged by that' grep -q '^five$' "$repo/init.el"

# ---------------- a file that cannot be read is an error, not a stale file
current 'six' >"$canonical"
day 08
chmod 000 "$canonical"
check 'make fails on a ~/org/init.org it cannot read' fails
check 'and does not call that file stale' not_printed 'does not call'
chmod 644 "$canonical"
check 'Emacs was not started for it' test "$(starts)" = 4
check 'init.el is unchanged by that, too' grep -q '^five$' "$repo/init.el"
check 'once it can be read, it is built' build
built_on 08
check 'init.el holds the build' grep -q '^six$' "$repo/init.el"

# -------- a stale init.el arrives from another host, newer than init.org
rm -f "$repo/init.el"
stale 'seven' >"$repo/init.el"
built_on 09
check 'a stale init.el that make would call up to date is built again' build
built_on 09
check 'init.el holds the current init' grep -q '^six$' "$repo/init.el"
check 'the build started Emacs for it' test "$(starts)" = 6

# ------- and beside a stale init.org it is left alone, with the refusal
rm -f "$repo/init.org" "$repo/init.el"
stale 'nine' >"$repo/init.org"
stale 'nine' >"$repo/init.el"
touch -t 202601100000 "$repo/init.org"
built_on 10
check 'a stale init.el beside a stale init.org is refused' refused
check 'Emacs was not started for them' test "$(starts)" = 6
check 'init.el is still there' grep -q '^nine$' "$repo/init.el"

# -------------------- a compiled init would shadow the one that is built
current 'eight' >"$canonical"
day 11
printf 'stale\n' >"$repo/init.elc"
check 'a newer current init.org is built over them' build
built_on 11
check 'init.el holds the build' grep -q '^eight$' "$repo/init.el"
check 'the build removed the compiled init' test ! -e "$repo/init.elc"

# ------ the call is in init.org, but not where it is tangled into init.el
printf '%s\n' '* Init' 'The first block calls (user-paths-check-migrated).' \
    '#+begin_src emacs-lisp' 'ten' '#+end_src' >"$canonical"
day 12
check 'an init.org that only mentions the call is built, and that fails' fails
check 'the failure says what init.el lacks' printed 'init.el was built and does not call'
check 'the build started Emacs for it' test "$(starts)" = 8
check 'a second try fails in the same way, and is not silent' fails
check 'it says the same' printed 'init.el was built and does not call'
current 'eleven' >"$canonical"
day 13
check 'with the call back in its block, the build passes' build
check 'init.el holds that build' grep -q '^eleven$' "$repo/init.el"

printf '\n%d passed, %d failed\n' "$passed" "$failed"
[[ $failed -eq 0 ]]
```

Run: `chmod +x xdg/make-init-test.sh`

The test copies the real Makefile into a scratch home and starts `make` there from an empty environment. `emacs` on its `PATH` is a stand-in that records that it was started and "tangles": it copies what stands in the source blocks of `init.org` to `init.el`, so that the content of `init.el` shows which `init.org` it was built from, and a call outside a source block does not reach it. make compares modification times and a build takes less than a second, so the test gives each version of `init.org` a day of its own.

- [x] **Step 2: Run the test to verify that it fails**

Run: `xdg/make-init-test.sh | grep -c '^FAIL'; xdg/make-init-test.sh | tail -1`

Expected:

```text
40
17 passed, 40 failed
```

Without the checks, every stale file is copied and built, a stale `init.el` is left alone, `init.elc` stays, and an `init.el` without the call is built without a word.

- [x] **Step 3: Add the checks and the test to the Makefile**

The recipe lines begin with a tab.

In `Makefile`, replace

```make
all: init.el

init.org: ~/org/init.org
	@if test ~/org/init.org -nt $@; then	        \
	    rm -f $@;					\
	    cp -p ~/org/init.org $@;		        \
	    chmod 444 $@;				\
	fi

# Generate lisp and compile it
init.el: init.org
	@rm -f $@
	@$(BATCH_LOAD)						\
		--eval "(require 'org)"				\
```

with

```make
all: init.el

# An init.org that does not call the guard of lisp/user-paths.el dates from
# before state moved out of this directory.  Emacs would start from it on
# empty histories, and keep its state here again.  Such a file is neither
# copied here nor tangled, and init.el stays as it was.  It can come back
# from the ~/org repository or from another host.  The check reads the text:
# the call counts wherever it stands on a line that is not a Lisp comment.
# Whether it is tangled shows in init.el, which is checked once it is built.
GUARD = ^[^;]*(user-paths-check-migrated

init.org: ~/org/init.org
	@if test ~/org/init.org -nt $@; then				\
	    grep -q '$(GUARD)' ~/org/init.org; found=$$?;		\
	    if test $$found -eq 1; then					\
		echo '~/org/init.org does not call'			\
		     '(user-paths-check-migrated).' >&2;		\
		echo 'An init.org without that call predates the move'	\
		     'of state out of this directory, so it is not'	\
		     'copied here and init.el is left as it was.'	\
		     'Restore ~/org/init.org; its versions are'		\
		     'listed by "git -C ~/org log -- init.org".' >&2;	\
		exit 1;							\
	    fi;								\
	    test $$found -eq 0 || exit $$found;				\
	    rm -f $@;							\
	    cp -p ~/org/init.org $@;					\
	    chmod 444 $@;						\
	fi

# An init.el from before the move can arrive from another host as well,
# newer than init.org, and make would call it up to date.  One that does
# not call the guard is built again.
ifneq ($(wildcard init.el),)
ifneq ($(shell grep -q '$(GUARD)' init.el; echo $$?),0)
.PHONY: stale-init
init.el: stale-init
endif
endif

# Generate lisp and compile it.  The copy of init.org here can be stale
# while ~/org/init.org is not (an old init.org checked out from git, or a
# copy from another host), so it is checked again before it is tangled.
# A compiled init.elc would be loaded in place of the init.el built here,
# so it goes as well; `make speed' builds it again.
init.el: init.org
	@grep -q '$(GUARD)' init.org; found=$$?;			\
	if test $$found -eq 1; then					\
	    echo 'init.org does not call'				\
		 '(user-paths-check-migrated).' >&2;			\
	    echo 'An init.org without that call predates the move of'	\
		 'state out of this directory, so it is not built and'	\
		 'init.el is left as it was.  Run'			\
		 '"touch ~/org/init.org" to have the current one'	\
		 'copied here.' >&2;					\
	    exit 1;							\
	fi;								\
	test $$found -eq 0
	@rm -f $@ $@c
	@$(BATCH_LOAD)						\
		--eval "(require 'org)"				\
```

and replace

```make
		--eval "(setq org-confirm-babel-evaluate nil)"	\
		--eval "(org-babel-load-file \"init.org\")"
	@chmod 444 $@

```

with

```make
		--eval "(setq org-confirm-babel-evaluate nil)"	\
		--eval "(org-babel-load-file \"init.org\")"
	@grep -q '$(GUARD)' $@ || {					\
	    echo 'init.el was built and does not call'			\
		 '(user-paths-check-migrated): in init.org the call'	\
		 'is not in a source block that is tangled.' >&2;	\
	    exit 1;							\
	}
	@chmod 444 $@

```

and replace

```make
	@xdg/check-litter.sh

# Unit tests for the path library and the migration tools.
test-xdg:
	@$(EMACS_BATCH) -Q -l lisp/user-paths-test.el -f ert-run-tests-batch-and-exit
```

with

```make
	@xdg/check-litter.sh

# Unit tests for the path library, the migration tools and this Makefile.
test-xdg:
	@$(EMACS_BATCH) -Q -l lisp/user-paths-test.el -f ert-run-tests-batch-and-exit
```

and replace

```make
	@xdg/migrate-test.sh
	@xdg/check-litter-test.sh

# Load the whole init in a sealed copy and report paths that still point here.
```

with

```make
	@xdg/migrate-test.sh
	@xdg/check-litter-test.sh
	@xdg/make-init-test.sh

# Load the whole init in a sealed copy and report paths that still point here.
```

- [x] **Step 4: Run the test to verify that it passes**

Run: `xdg/make-init-test.sh | tail -1 && PATH="/usr/bin:/bin:$PATH" /bin/bash xdg/make-init-test.sh | tail -1 && shellcheck xdg/make-init-test.sh; echo "exit=$?"`

Expected:

```text
57 passed, 0 failed
57 passed, 0 failed
exit=0
```

The second run uses the system's GNU Make 3.81.

- [x] **Step 5: Run every test**

Run: `make test-xdg 2>&1 | grep -E 'Ran |passed, '`

Expected:

```text
Ran 20 tests, 20 results as expected, 0 unexpected (...)
Ran 7 tests, 7 results as expected, 0 unexpected (...)
234 passed, 0 failed
124 passed, 0 failed
57 passed, 0 failed
```

`make test-xdg` is safe in the worktree: it runs the five test files and nothing else. It takes a minute or two.

- [x] **Step 6: Check that the real files pass**

Run: `grep -c '^[^;]*(user-paths-check-migrated' ~/org/init.org ~/.config/emacs/init.org ~/.config/emacs/init.el | sort`

Expected:

```text
/Users/johnw/.config/emacs/init.el:1
/Users/johnw/.config/emacs/init.org:1
/Users/johnw/org/init.org:1
```

This only reads the three files. If a count is 0, stop: with this Makefile `runemacs` would refuse to start Emacs, or would build `init.el` again at every start.

- [x] **Step 7: Commit**

```bash
git add xdg/make-init-test.sh Makefile
git commit -m "make: Refuse to build init.el from a stale init.org"
```

---

### Task 5: Record the work

**Files:**
- Modify: `README.md`
- Modify: `docs/superpowers/plans/2026-11-17-emacs-xdg-reorganization.md`

**Interfaces:**
- Consumes: Tasks 1 to 4.
- Produces: a reorganization plan whose Task 10 quotes the `test-xdg` target as it now is.

- [x] **Step 1: Say in the README what stops an old init**

In `README.md`, replace

```markdown
under `$XDG_CACHE_HOME/emacs`. `lisp/user-paths.el` defines the three roots
and `early-init.el` loads it first. Run `make check-litter` to see whether
anything has crept back.

I keep my Emacs file in literate Org mode, so that it's easier to organize and
```

with

```markdown
under `$XDG_CACHE_HOME/emacs`. `lisp/user-paths.el` defines the three roots
and `early-init.el` loads it first. Run `make check-litter` to see whether
anything has crept back. `make init.el` refuses an `init.org` from before
this layout, and an `init.el` from before it stops with an error at its own
definition of the data directory, before it has written anything.

I keep my Emacs file in literate Org mode, so that it's easier to organize and
```

- [x] **Step 2: Close the follow-ups in the reorganization plan, and bring its Task 10 up to date**

Task 10 of that plan is still to be done. It replaces the `test-xdg` target by exact text and gives the counts to expect, and both have changed. The patch below makes eight changes: three in Task 10's introduction and interfaces, two in the text of its Step 2, one in the counts of its Step 3, one in the note for John, and one hunk that closes Follow-ups 17, 20 and 21. Save it to a file outside the worktree and apply it from the worktree with `git apply FILE`.

```diff
--- a/docs/superpowers/plans/2026-11-17-emacs-xdg-reorganization.md
+++ b/docs/superpowers/plans/2026-11-17-emacs-xdg-reorganization.md
@@ -4265,5 +4265,5 @@
 ### Task 10: Remove the one-time tools
 
-Do this two weeks after Task 9, once John has looked through the attic and the collisions on both hosts. Run it on Clio; Hera receives the result by `git pull`. The mover, its tests, the guard and the litter report stay: they are what puts a host right if state ever comes back.
+Do this two weeks after Task 9, once John has looked through the attic and the collisions on both hosts. Run it on Clio; Hera receives the result by `git pull`. The mover, its tests, the guard, the litter report and the Makefile's test stay: they are what puts a host right if state ever comes back.
 
 **Files:**
@@ -4274,5 +4274,5 @@
 **Interfaces:**
 - Consumes: both hosts migrated, `make check-litter` clean on both.
-- Produces: a checkout with only the permanent files of the File Structure table.
+- Produces: a checkout with only the permanent files of the File Structure table, and `xdg/make-init-test.sh`, which `docs/superpowers/plans/2026-11-17-xdg-litter-report-and-stale-init-guards.md` added.
 
 - [ ] **Step 1: Remove the editor and the audit**
@@ -4299,5 +4299,5 @@
 
 ```make
-# Unit tests for the path library and the migration tools.
+# Unit tests for the path library, the migration tools and this Makefile.
 test-xdg:
 	@$(EMACS_BATCH) -Q -l lisp/user-paths-test.el -f ert-run-tests-batch-and-exit
@@ -4305,4 +4305,5 @@
 	@xdg/migrate-test.sh
 	@xdg/check-litter-test.sh
+	@xdg/make-init-test.sh
 
 # Load the whole init in a sealed copy and report paths that still point here.
@@ -4314,9 +4315,11 @@
 
 ```make
-# Unit tests for the path library, the mover and the litter report.
+# Unit tests for the path library, the mover, the litter report and this
+# Makefile.
 test-xdg:
 	@$(EMACS_BATCH) -Q -l lisp/user-paths-test.el -f ert-run-tests-batch-and-exit
 	@xdg/migrate-test.sh
 	@xdg/check-litter-test.sh
+	@xdg/make-init-test.sh
 ```
 
@@ -4328,7 +4331,8 @@
 
 ```text
-Ran 17 tests, 17 results as expected, 0 unexpected (...)
+Ran 20 tests, 20 results as expected, 0 unexpected (...)
 234 passed, 0 failed
-38 passed, 0 failed
+124 passed, 0 failed
+57 passed, 0 failed
 ```
 
@@ -4402,5 +4406,5 @@
 **Open, for John.**
 
-- Commit `init.org` in the `~/org` repository; `changes` does it. Until then its `HEAD` holds the old init, and a stash or a reset there would bring it back. The old init has no guard and would start on empty state (Follow-up 21).
+- Commit `init.org` in the `~/org` repository; `changes` does it. Until then its `HEAD` holds the old init, and a stash or a reset there would bring it back. The old init has no guard and would start on empty state (Follow-up 21). *Done at 20:24 the same evening. The old init is still in that repository's history; since Follow-up 21 was closed, `make init.el` refuses it.*
 - Task 7 Step 16 by hand on each host. On Hera also run `emacsclient -s /tmp/johnw-emacs/server --eval '(list init-file-had-error (get-buffer "*Warnings*"))'` after the first start; it should print `(nil nil)`.
 - Task 9 Steps 2 to 4. The hourly item of the task `Home` is suspended. The weekly "validate" item is not, and is next due on Monday 23 November at 05:00. The two hosts' `backups/` directories differed before the move, which suggests that the task already excludes `~/.local/share/emacs` and `~/.local/state`: look at the rules before deciding. At the first run both sides will have changed in `~/.local/share/gnus` and in `.config/emacs/.git`; going by its own log, ChronoSync has until now reported such files as conflicts and overwritten neither. Clio's copies are the ones in use.
@@ -4430,9 +4434,9 @@
 15. **Directory shortcuts.** `lisp/dired-ext.el` has a shortcut for `~/.config/emacs`. The three new roots have none; adding them is a matter of taste and of free keys.
 16. **Gnus keeps its own home.** `gnus-home-directory` is `~/.local/share/gnus/`: 783 MB, written every day. It is outside the checkout, and this plan does not touch it. Bringing it under the three roots would mean sorting some two dozen Gnus variables into mail and drafts (data), read marks and the registry (state) and article caches (cache), on a mail store in daily use. That is a plan of its own.
-17. **The litter report lists ignored paths only.** `xdg/check-litter.sh` skips every entry of `git status` that is not ignored, so a runtime file that `.gitignore` does not name is neither reported nor kept out of `changes`. About twenty built-in default names are in that position (`abbrev_defs`, `calc.el`, `games/`, `eww-bookmarks`, `image-dired/`, `diary` and others). Either report untracked entries as well, with a list of what may be untracked, or add the names to `.gitignore`. Two smaller points in the same script: it depends on git's `status.showUntrackedFiles`, and it prints `No litter` if `git status` itself fails.
+17. **The litter report lists ignored paths only.** `xdg/check-litter.sh` skips every entry of `git status` that is not ignored, so a runtime file that `.gitignore` does not name is neither reported nor kept out of `changes`. About twenty built-in default names are in that position (`abbrev_defs`, `calc.el`, `games/`, `eww-bookmarks`, `image-dired/`, `diary` and others). Either report untracked entries as well, with a list of what may be untracked, or add the names to `.gitignore`. Two smaller points in the same script: it depends on git's `status.showUntrackedFiles`, and it prints `No litter` if `git status` itself fails. **Closed on 17 November 2026** by `docs/superpowers/plans/2026-11-17-xdg-litter-report-and-stale-init-guards.md`: the report lists untracked entries at the top of the checkout as well, `.gitignore` names the remaining defaults that are state, caches or records of use, and both smaller points are fixed. Settings that a person saves on request (`abbrev_defs`, `calc.el` and the like) have no rule on purpose; the report lists them while they are untracked.
 18. **Paths that are still built from the configuration directory.** `image-dired-dir` (thumbnails, a cache), `diary-file` (data), `wombag-dir` (it uses `XDG_CACHE_HOME`, and falls back to the configuration directory in an Emacs that has no such variable), and org-remark (Follow-up 14). Each is one row of `user-paths-table`. The fallback `%backup%~` in `files.el` cannot be redirected.
 19. **An interrupted move can get past the guard.** The mover removes `data/` before it has moved `eshell/`, `persist/`, `tree-sitter/` and the other sources that come later in its manifest, and the guard looks only at `data/`. If `--apply` stops in between, the next start is quiet and partly empty. Nothing is lost, and `--apply --prefer=source` puts it right. Moving the `data/` entries to the end of the manifest closes it. In the same script a data root that is a symbolic link is taken for a clash, and the tests have no case for an apply that stops half-way.
-20. **`early-init.el` redirects before the guard can refuse.** Between the arrival of the branch and the first build, an Emacs started from the Dock runs the old `init.el` with the new early paths. Loading the library from `early-init.el` only when `data/` is absent closes it. Also, the library requires `xdg` before it redirects the native-compilation cache, so `xdg.el` is compiled again at every interactive start.
-21. **There is no guard in the other direction.** An old `init.org` on a host that has been moved starts without complaint on empty state and re-creates `data/`. It can come back from the `~/org` repository (a stash, a reset, a checkout) or from the other host. The mover could leave a marker for the library to check, or `early-init.el` could refuse an `init.el` that never calls `user-paths-check-migrated`.
+20. **`early-init.el` redirects before the guard can refuse.** Between the arrival of the branch and the first build, an Emacs started from the Dock runs the old `init.el` with the new early paths. Loading the library from `early-init.el` only when `data/` is absent closes it. Also, the library requires `xdg` before it redirects the native-compilation cache, so `xdg.el` is compiled again at every interactive start. **The first point was closed on 17 November 2026** by `docs/superpowers/plans/2026-11-17-xdg-litter-report-and-stale-init-guards.md`, in another way: the library refuses to give a root another value, so the old `init.el` stops at its own definition of `user-data-directory`. The second point stands.
+21. **There is no guard in the other direction.** An old `init.org` on a host that has been moved starts without complaint on empty state and re-creates `data/`. It can come back from the `~/org` repository (a stash, a reset, a checkout) or from the other host. The mover could leave a marker for the library to check, or `early-init.el` could refuse an `init.el` that never calls `user-paths-check-migrated`. **Closed on 17 November 2026** by `docs/superpowers/plans/2026-11-17-xdg-litter-report-and-stale-init-guards.md`, with neither: `make init.el` refuses an `init.org` that does not call the guard and builds again an `init.el` that does not, and the library refuses to give a root another value, which stops an old `init.el` at its first definition. That plan's Follow-ups say what this leaves open.
 22. **The one-time tools, if they are kept beyond Task 10.** The audit's reader takes a form cut short by a missing paren for the end of the file. Errors in hooks are logged and not counted. A new empty directory is not reported. `run.sh` stops with rsync's error 23 in a checkout where a tracked file is deleted from the working tree. `mcp-server-lib-install-directory` belongs on the list of allowed variables. `audit.el` runs the whole audit when it is loaded in a batch Emacs. The editor counts an edit as done when the new text is present even if the old text is too, and it overwrites the file in place.
 23. **Emacs starts that bypass `runemacs`.** On Clio two Keyboard Maestro macros (Cmd-Shift-M, and Home in Firefox) and org-protocol links start Emacs.app directly. On Hera `mailto:` links and the default mail client do, and org-protocol goes through an AppleScript applet whose script names Emacs. Such a start skips the build, so it runs whatever `init.el` was tangled last. Reading that applet with `osadecompile` starts Emacs too.
```

- [x] **Step 3: Check the edits**

Run: `git diff --stat | tail -1; grep -c 'xdg-litter-report-and-stale-init-guards' docs/superpowers/plans/2026-11-17-emacs-xdg-reorganization.md`

Expected:

```text
 2 files changed, 17 insertions(+), 11 deletions(-)
4
```

- [x] **Step 4: Commit**

```bash
git add README.md docs/superpowers/plans/2026-11-17-emacs-xdg-reorganization.md
git commit -m "xdg: Record the litter report and the stale-init guards"
```

---

### Task 6: Land it on Clio and Hera

This task is not for a subagent. It pushes to `origin`, changes the main checkout on Clio, where John's Emacs is running and another session has uncommitted work, and reaches Hera over ssh.

**Files:**
- No file of the repository changes. `master` on `origin`, on Clio and on Hera moves forward.

**Interfaces:**
- Consumes: the five commits of Tasks 1 to 5 on `xdg-guards`, each reviewed.
- Produces: both hosts on the same commit, with `make test-xdg` and `make check-litter` passing on each.

- [x] **Step 1: Check the whole branch in the worktree**

Run: `make test-xdg 2>&1 | grep -E 'Ran |passed, '`

Expected: the five lines of Task 4 Step 5.

Run: `make audit-xdg 2>&1 | grep -E '^audit: |^PASS|^FAIL'`

Expected:

```text
audit: 0 offenders, 0 failed forms
PASS
```

The audit loads the whole init, with the new library, in a sealed copy; it takes half a minute. A form that assigned a root would be a failed form. The count of forms and features on the line before these drifts with the packages.

Run: `grep -c '^[^;]*(user-paths-check-migrated' ~/org/init.org ~/.config/emacs/init.org ~/.config/emacs/init.el | sort; ssh hera "grep -c '^[^;]*(user-paths-check-migrated' ~/org/init.org ~/.config/emacs/init.org ~/.config/emacs/init.el | sort; ls ~/.config/emacs/init.elc"; ls ~/.config/emacs/init.elc`

Expected: six lines that end in `:1`, and twice `No such file or directory`. A count of 0 means that the new Makefile would refuse that host's file or build it again; an `init.elc` would be removed by the next build. Stop and look before going on.

- [x] **Step 2: Push the branch to origin as master**

```bash
git -C ~/src/emacs-xdg-guards fetch origin
git -C ~/src/emacs-xdg-guards log --oneline HEAD..origin/master
```

Expected: the second command prints nothing. If it prints commits, `master` has moved again: run `git rebase origin/master` in the worktree, then `make test-xdg`, then repeat this step.

```bash
git -C ~/src/emacs-xdg-guards push origin xdg-guards:master
```

This is a fast-forward on the remote. It touches no working tree.

- [x] **Step 3: Bring Clio's checkout up to date**

Clio's `master` is behind `origin/master` by the commit of the other session and by this plan's commits. That other commit changes `init.org`, and the copy of `init.org` in the checkout is modified, so git will not fast-forward over it. The copy is not a file anyone edits: it is what `make` last copied from `~/org/init.org`. Check that it holds nothing that `~/org/init.org` lacks, set it aside, fast-forward, and copy `~/org/init.org` into its place as the Makefile does.

```bash
cd ~/.config/emacs && git fetch origin
d=$(mktemp -d /tmp/landing.XXXXXX)
git diff --name-only HEAD origin/master | sort >"$d/incoming"
git status --porcelain | cut -c4- | sort >"$d/dirty"
comm -12 "$d/incoming" "$d/dirty"
```

Expected: `init.org` and nothing else. Any other name is a file that both the incoming commits and an uncommitted change touch: stop, and leave the checkout as it is.

```bash
git show HEAD:init.org >"$d/base" && git show origin/master:init.org >"$d/theirs"
git merge-file -p init.org "$d/base" "$d/theirs" >"$d/merged"; echo "exit=$?"
cmp "$d/merged" ~/org/init.org && echo same
```

Expected: `exit=0` and `same`. The copy's own changes together with the incoming ones are then exactly what `~/org/init.org` holds, so nothing is lost by replacing the copy. If either differs, stop.

```bash
cp -p init.org "$d/init.org.before"
git checkout -- init.org
git merge --ff-only origin/master
rm -f init.org && cp -p ~/org/init.org init.org && chmod 444 init.org
git status --short
```

Expected: the fast-forward succeeds, and `git status --short` prints the entries it printed before this step. The copy now has the time stamp of `~/org/init.org`, as after a `make`; the next `runemacs` builds `init.el` from it, which it would have done in any case, because `~/org/init.org` is newer than `init.el`.

- [x] **Step 4: Bring Hera's checkout up to date**

```bash
ssh hera 'cd ~/.config/emacs && git fetch origin && git diff --name-only HEAD origin/master | sort >/tmp/guards-incoming && git status --porcelain | cut -c4- | sort >/tmp/guards-dirty && comm -12 /tmp/guards-incoming /tmp/guards-dirty; rm -f /tmp/guards-incoming /tmp/guards-dirty'
```

Expected: nothing. Hera already has the other session's commit, so only this plan's files come in, and none of them is modified there.

```bash
ssh hera 'cd ~/.config/emacs && git merge --ff-only origin/master && git log --oneline -1'
```

- [x] **Step 5: Check both hosts**

Run on each (on Hera through `ssh hera`): `make -C ~/.config/emacs test-xdg 2>&1 | grep -E 'Ran |passed, '; make -C ~/.config/emacs check-litter; git -C ~/.config/emacs status -sb | head -1`

Expected on each: the five lines of Task 4 Step 5, `No litter in /Users/johnw/.config/emacs`, and `## master...origin/master` with nothing after it.

`make test-xdg` is safe in the live checkout: every test works in a scratch directory.

- [x] **Step 6: Keep the record, then remove the worktree**

Copy the ledger and the reviews of this plan from the worktree's `.superpowers/` directory to `~/.local/state/emacs/migration/guards/` on Clio, beside the records of the move, so that Task 10 of the reorganization plan removes them together. Then:

```bash
git -C ~/.config/emacs worktree remove ~/src/emacs-xdg-guards
git -C ~/.config/emacs branch -d xdg-guards
```

- [ ] **Step 7: The next start of Emacs on each host (John)**

`runemacs` builds `init.el` once more, because `init.org` is newer, and opens Emacs. In the new session:

```bash
emacsclient -s /tmp/johnw-emacs/server --eval '(list init-file-had-error (get-variable-watchers (quote user-data-directory)))'
```

Expected: `(nil (user-paths--keep-root))`.

If `runemacs` prints that `init.org` does not call `(user-paths-check-migrated)`, the message says which file and what to do. If Emacs opens with a warning that a root "is set by lisp/user-paths.el and cannot become" something, the file it names is from before the move: run `make -B init.el` in `~/.config/emacs`.

---

## Execution record

Tasks 1 to 5 were carried out on 17 November 2026 in the worktree, each by an implementer of its own, and each commit was reviewed. Task 6 followed the same night. The steps above that are ticked were done. `master` on `origin`, on Clio and on Hera holds the commits listed here and the ones that add this record.

| | |
|---|---|
| Commits of the five tasks | `7a7e7bb53`, `8af292a5f`, `dc3028c5e`, `31834c59e`, `bd8be20c5` |
| Commits made after the reviews | `bb83d59c7`, `ebf7a6274`, `1666bcd4b`, `6fd8d4bc6`, `0edf54807`, `24e430bde`, `5a69fba1f` |
| `make test-xdg` | 20 and 7 ERT tests, and 234, 124 and 57 checks, all passing: in the worktree at `5a69fba1f`, and in the checkout of each host after its fast-forward |
| `make audit-xdg` at `5a69fba1f` | `580 forms, 0 failed`; `0 offenders, 0 failed forms`; `PASS` |
| `make check-litter` | `No litter` on Clio and on Hera |
| The real files | `~/org/init.org`, and `init.org` and `init.el` of the checkout, call the guard on both hosts; neither host has an `init.elc` |
| Hera's checkout | fast-forwarded at 23:05 on 17 November; no Emacs was running there |
| Clio's checkout | fast-forwarded at 00:00 on 18 November, after John had quit Emacs |

The ledger, the implementers' reports and all the reviews are in `~/.local/state/emacs/migration/guards/` on Clio.

**Where the execution departed from the text.**

- The text of this plan was changed after the reviews, as Appendix B says, so that it shows the files as they are. The commits of the five tasks hold the files as the plan first had them; the seven later commits bring them to what is printed here.
- Task 5 Step 2: the implementer copied the reference file instead of applying the patch. The result was compared byte for byte with what the patch gives.
- Task 6 Step 1 was run twice, the second time at `5a69fba1f`.
- Task 6 Step 3 waited an hour. At 22:52 John's running Emacs on Clio held an unsaved buffer of `lisp/org-ql-semantic.el`, a file that the other session's commit `b20c11b1a` changes. The fast-forward would have changed it on disk under the buffer, and saving the buffer afterwards would have undone that commit. John was asked, and quit Emacs; the step was then done as written. Its two checks gave `init.org` and `same`.

**Open, for John.**

- `lisp/#org-ql-semantic.el#` is still in Clio's checkout. It is the auto-save file of that buffer, and it holds the file as it was before the other session's commit, with whitespace changed on three lines. Do not recover from it; delete it. git ignores it now, and the report passes over it.
- Task 6 Step 7 on each host, at the next start of Emacs there. `runemacs` will build `init.el` once on each, because `init.org` is newer than `init.el` on both.
- Follow-ups 3, 4 and 5 are decisions for John: the Keyboard Maestro macro, the global ignore file, and whether settings saved on request should be ignored as well.

---

## Follow-ups

What this plan leaves open, most serious first. None of it is needed for the two guards to do their work on the paths John uses.

1. **A checkout of a commit older than this plan guards nothing.** It has the old Makefile and the old library, or none. Started there, an old init runs quietly and makes `data/` again. Nothing inside a checkout can guard against its own old versions. The smallest fix lies outside: `runemacs` could refuse to open Emacs unless `init.el` calls `user-paths-check-migrated`.
2. **A batch load of a stale `init.el` is not guarded.** `emacs --batch -l init.el` reads no `early-init.el`, so the watcher is not installed, and a stale `init.el` does not load the library itself. `make` now builds such an `init.el` again, so a gate that runs `make` first is covered; one that loads `init.el` directly is not.
3. **From the Keyboard Maestro macro, a failed build is silent.** The macro `Run Emacs` drops standard error, so a refusal, like any other error in the build, shows only as Emacs not opening. Including errors in that action, or a notification from `runemacs` when `make` fails, would show the reason. `~/src/scripts/start` stops at the same point, before `brew` and `start-apps`.
4. **The global ignore file's first line is a comment.** `#*#` in `~/.config/git/ignore` ignores nothing; in the Nix configuration it should read `\#*#`.
5. **Settings that a person saves on request have no rule.** If `abbrev_defs`, `calc.el`, `eudc-options`, `shadows`, `strokes` or `viper` appears at the top of the checkout, `changes` commits it. The report lists it as untracked, but only when someone runs it. Whether these should be ignored as well is John's decision; each is one line of `.gitignore` and one line of the test.
6. **A refused build can leave a stale `init.org` in the checkout.** When the stale file arrived in the checkout itself, it stays there as a modified tracked file until `~/org/init.org` is touched, and `changes` would commit it. The report does not mention it.
7. **A pull that changes `init.org` hides `~/org/init.org` from make.** git gives the checkout's copy the time of the pull, which is newer than `~/org/init.org`, so `make` does not copy that file again until it changes, and builds `init.el` from the committed copy. When the two differ, as they do while `~/org/init.org` holds changes that are not committed here, the build is without them. This is older than this plan; Task 6 Step 3 works around it once.
8. **A stale `~/org/init.org` with an old time stamp is not noticed** until that file is next saved. Nothing is built from it in the meantime.
9. **`wombag-dir` falls back to the configuration directory** in an Emacs that has no `XDG_CACHE_HOME`, which is Follow-up 18 of the reorganization plan. The new rule for `wombag/` keeps it out of a commit, and the report shows it.
10. **Small points.** A stale `init.elc` beside an `init.el` that make calls up to date stays until the next build; Emacs loads it, the library stops it, and the advice in its message removes it. There is no `init.elc` on either host. Two corners of the report: a backup file that sits alone in a new directory below `lisp/` is passed over, because git lists that directory as one ignored entry and everything ignored below `lisp/` is taken for a build product; and a new directory that holds a `.DS_Store` beside an auto-save file is reported, as is one that holds a `.DS_Store` alone. In `/bin/sh`, `test -nt` compares whole seconds, so a change to `~/org/init.org` in the same second as the last copy is not seen. A build whose batch load fails leaves an `init.el` that make takes for built. The last two are older than this plan.

---

## Appendix A: The follow-ups this plan closes

From `docs/superpowers/plans/2026-11-17-emacs-xdg-reorganization.md`, as they stood before Task 5.

> 17. **The litter report lists ignored paths only.** `xdg/check-litter.sh` skips every entry of `git status` that is not ignored, so a runtime file that `.gitignore` does not name is neither reported nor kept out of `changes`. About twenty built-in default names are in that position (`abbrev_defs`, `calc.el`, `games/`, `eww-bookmarks`, `image-dired/`, `diary` and others). Either report untracked entries as well, with a list of what may be untracked, or add the names to `.gitignore`. Two smaller points in the same script: it depends on git's `status.showUntrackedFiles`, and it prints `No litter` if `git status` itself fails.
>
> 20. **`early-init.el` redirects before the guard can refuse.** Between the arrival of the branch and the first build, an Emacs started from the Dock runs the old `init.el` with the new early paths. Loading the library from `early-init.el` only when `data/` is absent closes it. Also, the library requires `xdg` before it redirects the native-compilation cache, so `xdg.el` is compiled again at every interactive start.
>
> 21. **There is no guard in the other direction.** An old `init.org` on a host that has been moved starts without complaint on empty state and re-creates `data/`. It can come back from the `~/org` repository (a stash, a reset, a checkout) or from the other host. The mover could leave a marker for the library to check, or `early-init.el` could refuse an `init.el` that never calls `user-paths-check-migrated`.

## Appendix B: How the design was tested before this plan was written

Every change in this plan was first built in a scratch copy of the checkout, with its tests. Five reviewers, each with one part and no knowledge of the others' work, were then asked to break it by experiment, in scratch homes and under a sandbox that denies writes below the home directory. None found a defect that would stop Emacs or fire on the current configuration. What they found changed the design in these places:

- **The report.** Its list of known names had been extended to untracked entries, which hid agent files that `changes` would commit; the rules moved into `.gitignore` instead. Thirty existing checks had stopped proving that their rule exists; they now compare the exact line. A directory that is not the top of a checkout got a false `No litter`, and a failing `mktemp` exited with the status for litter.
- **The rules.** The writer of every name was found in the sources, with file and line. Backup files were ignored only by the global ignore file. The comment that called every name "state or a cache" was wrong for five of them. Deleting any one of the rules made the test fail.
- **The library.** A stale `init.elc` defeated the message's advice; the build now removes it, and the message names the file being loaded. The semantics were confirmed for byte-compiled and natively compiled code, for threads and for buffer-local values. Six mutations of the watcher were each caught by a test.
- **The Makefile.** In all 24 orderings of the three time stamps, with a stale or a current file in each place and with both versions of make, no stale file was built and no current one refused. The check was too strict about how the call is written, and reported a file it could not read as one that predates the move. A stale `init.el` newer than `init.org` passed as up to date. Eleven mutations of the Makefile were each caught by the test.

What could not be checked: a GUI start of Emacs, which the rules of the review forbade and a terminal Emacs stood in for; Hera, which the reviewers did not reach and Task 6 checks; and what Keyboard Maestro shows when its shell action fails.

The plan was then executed, and each task's commit and the whole branch were reviewed again by six reviewers who had not seen the design work. All approved, with minor findings. Those changed the text of this plan in these places, and the branch carries them as commits of their own after the five tasks: a backup file under `lisp/` is reported like any other; a new directory that holds only an auto-save file is passed over; the library's message blames an old init only when an init file is being loaded; the build fails when the `init.el` it made does not call the guard, which closes a silent rebuild at every start that this plan's own rule for a stale `init.el` had opened; `xdg/migrate-test.sh` clears git's repository variables as the litter test does; and several comments and messages say more exactly what is true. A seventh reviewer then read those commits, and an eighth ran the final Makefile and library against copies of the real files of this host: both approved. The first asked for the test that pins the library's message for a file that is not an init file, which was added, and found the two corners of the report that Follow-up 10 records.
