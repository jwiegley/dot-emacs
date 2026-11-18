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
