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
