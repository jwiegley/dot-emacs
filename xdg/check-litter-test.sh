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
abbrev_defs|abbrev_defs
calc.el|calc.el
eudc-options|eudc-options
shadows|shadows
strokes|strokes
viper|viper
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

# Code has no rule: it stays visible to git and to this report.
for path in user-lisp/mine.el auctex/style/mine.el; do
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

# Alone it changes nothing, and the report says what it would do.
put "$home/.emacs.el"
exactly 'a .emacs.el in the home directory is reported for what it does' \
    "$home/.emacs.el exists: Emacs loads it as the init file once ~/.emacs.d or ~/.emacs exists"
rm "$home/.emacs.el"

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
