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
# when CHECKOUT is not the top of a git checkout or git cannot be asked.

set -euo pipefail

checkout=${1:-$(cd "$(dirname "$0")/.." && pwd -P)}
status=0

# A git hook exports GIT_DIR and its relatives.  They would send every git
# command below to the repository of the hook, whatever CHECKOUT is.
# shellcheck disable=SC2046  # one word for each variable name
unset $(git rev-parse --local-env-vars 2>/dev/null)

# Paths in git's answer are relative to the top of the checkout, so that is
# what CHECKOUT must be.
top=$(git -C "$checkout" rev-parse --show-toplevel 2>/dev/null) || top=
if [[ -z $top || ! $top -ef $checkout ]]; then
    printf 'check-litter: %s is not the top of a git checkout\n' "$checkout" >&2
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
done <"$listing"

while IFS= read -r directory; do
    report "$directory (empty directory)"
done < <(find "$checkout" -mindepth 1 -maxdepth 1 -type d -empty | LC_ALL=C sort)

if [[ $status -eq 0 ]]; then
    printf 'No litter in %s\n' "$checkout"
fi
exit "$status"
