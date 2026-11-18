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
