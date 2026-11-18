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
