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
    printf 'x\n' >"$1"
}

# A checkout after migration: tracked files, plus the untracked
# configuration and build products that are allowed to be there.
mkdir -p "$repo"
git -C "$repo" init -q
cp "$here/../.gitignore" "$repo/.gitignore"
put "$repo/init.org"
put "$repo/lisp/a.el"
put "$repo/docs/plan.md"
git -C "$repo" add .gitignore init.org lisp docs
put "$repo/init.el"
put "$repo/settings.el"
put "$repo/lisp/a.elc"
put "$repo/certs/ca.pem"
put "$repo/eshell/alias"
put "$repo/eshell/login"
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
    request/curl-cookie-jar tree-sitter/libtree-sitter-c.dylib projects \
    projects.eld projectile-frecency.eld elpy/rpc-venv/pyvenv.cfg \
    emojis/set/1.png gptel-agent/sessions.db '%backup%~' .lsp-session-v1 \
    tramp network-security.eld .org-id-locations history recentf bookmarks \
    places ido.last ielm-history.eld org-clock-save.el elpa/archives/x \
    package-quickstart.el server/server; do
    put "$repo/$path"
    exactly "${path%%/*} is ignored, and reported" "$repo/${path%%/*}"
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
[[ $failed -eq 0 ]]
