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
