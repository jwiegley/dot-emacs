#!/usr/bin/env bash
# migrate.sh --- move Emacs runtime state out of the configuration checkout
#
# Usage:
#   xdg/migrate.sh                  preview: print every action, change nothing
#   xdg/migrate.sh --apply          perform the moves
#   xdg/migrate.sh --rollback DIR   undo the moves recorded in DIR/moves.tsv
#
# When a destination already holds a different file, --apply refuses until
# you say which copy wins: add --prefer=source for the copy in the
# configuration directory, or --prefer=destination for the copy that is
# already there.  The other copy is kept in the run directory either way.
# A preview takes the same option and shows the result.
#
# Each file goes to the root that fits what it is, as lisp/user-paths.el
# has it: data to $XDG_DATA_HOME/emacs, state to $XDG_STATE_HOME/emacs and
# caches to $XDG_CACHE_HOME/emacs.  Leftovers of packages that are gone go
# to an attic inside the run directory for a person to review.  Nothing is
# deleted, except a source file that is byte-identical to its destination
# and directories that the moves have emptied.
#
# Every rename is recorded in <state>/migration/<stamp>/moves.tsv, and a tar
# archive of every source inside the configuration directory that is not a
# cache is written there first; the old data/ directory goes into it whole.
# The backups directory, which is outside the checkout already, is only
# renamed.  The script is safe to run again: sources that are already gone
# are skipped.
#
# Quit every Emacs first.  A running session rewrites its history files at
# their old paths, on timers as well as on exit.

set -euo pipefail
umask 077

die() {
    printf 'migrate: %s\n' "$*" >&2
    exit 1
}

# An unset, empty or relative XDG value counts as unset, as it does in
# lisp/user-paths.el.  Repeated and trailing slashes are dropped, so that
# two spellings of one directory compare equal.
xdg_home() {
    local value=${!1:-}
    case $value in
    /*) ;;
    *) value=$2 ;;
    esac
    while [[ $value == *//* ]]; do
        value=${value//\/\//\/}
    done
    printf '%s\n' "${value%/}"
}

[[ -n ${HOME:-} ]] || die 'HOME is not set'

CONFIG_DIR=$(xdg_home XDG_CONFIG_HOME "$HOME/.config")/emacs
DATA_DIR=$(xdg_home XDG_DATA_HOME "$HOME/.local/share")/emacs
STATE_DIR=$(xdg_home XDG_STATE_HOME "$HOME/.local/state")/emacs
CACHE_DIR=$(xdg_home XDG_CACHE_HOME "$HOME/.cache")/emacs
STAMP=${EMACS_XDG_STAMP:-$(date +%Y%m%d-%H%M%S)}
RUN_DIR=$STATE_DIR/migration/$STAMP

# KIND|SOURCE|DESTINATION.  SOURCE is relative to the configuration
# directory, or with the prefix `@data/' to the data root, for a file that
# already lives outside the checkout and only changes roots.  DESTINATION
# is relative to the root that KIND names: `data', `state', `cache', or
# `attic' (leftovers kept for review).  `prune' removes SOURCE if the
# moves above it left it empty.  Order matters: an entry that takes part
# of a directory must precede the entry that takes the rest.  The old init
# kept all three kinds under data/, so the entries for its state and its
# caches come first and `data|data|.' takes what is left, which includes
# any file this list does not know.  No entry may move anything into a
# directory that a later entry takes as its source: a preview sees only
# what is on disk there.  That is why data/backups has an entry of its own
# ahead of `data|data|.', which would otherwise put it into <data>/backups.
manifest() {
    cat <<'EOF'
cache|url/cache|url
prune|url|-
cache|data/url/cache|url
cache|data/projectile.cache|projectile.cache
cache|data/org-roam.db|org-roam.db
cache|data/org-roam.db-journal|org-roam.db-journal
cache|data/org-roam.db-wal|org-roam.db-wal
cache|data/org-roam.db-shm|org-roam.db-shm
cache|data/xeft.db|xeft.db
data|data/.cache/lsp|lsp
prune|data/.cache|-
attic|data/mc-lists.elc|data/mc-lists.elc
attic|data/workgroups|data/workgroups
state|data/.lsp-session-v1|lsp-session-v1
state|data/auto-save-list|auto-save-list
state|data/backups|backups
state|data/bm-repository|bm-repository
state|data/bmk-bmenu-state.el|bmk-bmenu-state.el
state|data/history|history
state|data/network-security.data|network-security.data
state|data/nov-places|nov-places
state|data/org-clock-save.el|org-clock-save.el
state|data/org-id-locations|org-id-locations
state|data/persistent-scratch|persistent-scratch
state|data/places|places
state|data/prescient-save.el|prescient-save.el
state|data/projectile-bookmarks.eld|projectile-bookmarks.eld
state|data/recentf|recentf
state|data/slime-history.eld|slime-history.eld
state|data/tramp|tramp
state|data/transient/history.el|transient/history.el
state|data/url|url
data|data|.
state|@data/backups|backups
attic|data-MacPort|data-MacPort
state|eshell/history|eshell/history
state|eshell/lastdir|eshell/lastdir
state|projects|projects
state|projectile-frecency.eld|projectile-frecency.eld
state|multisession|multisession
data|persist|persist
data|hash-store|hash-store
state|request|request
data|tree-sitter|tree-sitter
cache|eln-cache|eln-cache
data|emojis|emojis
cache|var/pcache|pcache
attic|var/osm|var/osm
prune|var|-
attic|transient|transient
attic|auto-save-list|auto-save-list
attic|elpy|elpy
attic|gptel-agent|gptel-agent
attic|.lsp-session-v1|.lsp-session-v1
attic|.org-generic-id-locations|.org-generic-id-locations
attic|anvil-worker.log|anvil-worker.log
attic|%backup%~|%backup%~
prune|agent|-
EOF
}

# Files that hold tokens or cookies; they end up owner-only.
private_files() {
    cat <<EOF
$DATA_DIR/oauth2-auto.plist
$DATA_DIR/persist/org-gcal--sync-tokens
$STATE_DIR/request/curl-cookie-jar
$STATE_DIR/url/cookies
EOF
}

# Print directory $1 with the symbolic links in its existing part resolved,
# so that two spellings of one place compare equal.
physical() {
    local path=$1 rest='' base
    while [[ ! -d $path ]]; do
        rest=/${path##*/}$rest
        path=${path%/*}
        if [[ -z $path ]]; then
            path=/
        fi
    done
    base=$(cd -P -- "$path" && pwd -P) || die "cannot resolve $path"
    if [[ $base == / ]]; then
        base=''
    fi
    if [[ -z $base$rest ]]; then
        printf '/\n'
    else
        printf '%s%s\n' "$base" "$rest"
    fi
}

source_of() {
    case $1 in
    @data/*) printf '%s\n' "$DATA_DIR/${1#@data/}" ;;
    *) printf '%s\n' "$CONFIG_DIR/$1" ;;
    esac
}

destination_of() {
    local root
    case $1 in
    data) root=$DATA_DIR ;;
    state) root=$STATE_DIR ;;
    cache) root=$CACHE_DIR ;;
    attic) root=$RUN_DIR/attic ;;
    *) die "unknown manifest kind: $1" ;;
    esac
    if [[ $2 == . ]]; then
        printf '%s\n' "$root"
    else
        printf '%s\n' "$root/$2"
    fi
}

APPLY=0
PREFER=
CONFLICTS=0

# A preview must print exactly the commands that --apply runs, so it keeps
# a list of the renames and removals it has printed and answers every
# question about the file system as if they had happened.  A removal has
# an empty VIRT_TO.
VIRT_FROM=()
VIRT_TO=()
RESOLVED=

# A preview without --prefer leaves each clashing source where it is.  HELD
# lists them, so that no later entry takes one of them, or a directory that
# holds one, to another root.
HELD=()

is_held() {
    local index=${#HELD[@]}
    while ((index > 0)); do
        index=$((index - 1))
        if [[ ${HELD[index]} == "$1" ]]; then
            return 0
        fi
    done
    return 1
}

holds_held() {
    local index=${#HELD[@]}
    while ((index > 0)); do
        index=$((index - 1))
        if [[ ${HELD[index]} == "$1"/* ]]; then
            return 0
        fi
    done
    return 1
}

# Succeed if --apply creates directory $1 before it moves anything.
made_first() {
    case $1 in
    "$DATA_DIR" | "$STATE_DIR" | "$CACHE_DIR" | "$STATE_DIR/migration" | "$RUN_DIR" | "$RUN_DIR/attic")
        return 0
        ;;
    esac
    return 1
}

# Set RESOLVED to the path that holds, on disk today, what a preview has
# put at $1.  Fail if the preview has moved or removed $1.
resolve() {
    local path=$1 index from to
    RESOLVED=$path
    [[ $APPLY == 0 ]] || return 0
    index=${#VIRT_FROM[@]}
    while ((index > 0)); do
        index=$((index - 1))
        from=${VIRT_FROM[index]}
        to=${VIRT_TO[index]}
        if [[ -n $to && ($path == "$to" || $path == "$to"/*) ]]; then
            path=$from${path#"$to"}
        elif [[ $path == "$from" || $path == "$from"/* ]]; then
            return 1
        fi
    done
    RESOLVED=$path
}

present() {
    resolve "$1" || return 1
    if [[ -e $RESOLVED || -L $RESOLVED ]]; then
        return 0
    fi
    [[ $APPLY == 0 ]] && made_first "$1"
}

is_directory() {
    resolve "$1" || return 1
    if [[ -d $RESOLVED && ! -L $RESOLVED ]]; then
        return 0
    fi
    [[ $APPLY == 0 && ! -e $RESOLVED && ! -L $RESOLVED ]] && made_first "$1"
}

is_file() {
    resolve "$1" || return 1
    [[ -f $RESOLVED && ! -L $RESOLVED ]]
}

same_bytes() {
    local first
    resolve "$1" || return 1
    first=$RESOLVED
    resolve "$2" || return 1
    cmp -s -- "$first" "$RESOLVED"
}

# Succeed if $1 and $2 are one file or directory under two names.
same_place() {
    local first
    resolve "$1" || return 1
    first=$RESOLVED
    resolve "$2" || return 1
    [[ $first -ef $RESOLVED ]]
}

# Print the children of directory $1 under the names they have there.
children_of() {
    local child
    resolve "$1" || return 0
    [[ -d $RESOLVED ]] || return 0
    find "$RESOLVED" -mindepth 1 -maxdepth 1 -print | LC_ALL=C sort |
        while IFS= read -r child; do
            printf '%s\n' "$1/${child##*/}"
        done
}

has_children() {
    local child
    while IFS= read -r child; do
        if present "$child"; then
            return 0
        fi
    done < <(children_of "$1")
    return 1
}

record() {
    if [[ $APPLY == 1 ]]; then
        printf '%s\n' "$1" >>"$RUN_DIR/moves.tsv"
    fi
}

rename_to() {
    local src=$1 dest=$2
    printf '  mv     %s -> %s\n' "$src" "$dest"
    if [[ $APPLY == 1 ]]; then
        mkdir -p "$(dirname "$dest")"
        # Log first.  If the run stops between the two commands, the
        # rollback sees a move that never happened and skips it.
        record "$(printf 'MV\t%s\t%s' "$src" "$dest")"
        mv -- "$src" "$dest"
    else
        VIRT_FROM+=("$src")
        VIRT_TO+=("$dest")
    fi
}

remove_directory() {
    printf '  rmdir  %s\n' "$1"
    if [[ $APPLY == 1 ]]; then
        record "$(printf 'RMDIR\t%s' "$1")"
        rmdir -- "$1"
    else
        VIRT_FROM+=("$1")
        VIRT_TO+=("")
    fi
}

move_entry() {
    local src=$1 dest=$2 child saved
    present "$src" || return 0
    # One place under two names: there is nothing to move, and a file must
    # never be taken for a duplicate of itself.
    if same_place "$src" "$dest"; then
        return 0
    fi
    if is_held "$src"; then
        return 0
    fi
    if ! present "$dest" && ! holds_held "$src"; then
        rename_to "$src" "$dest"
        return 0
    fi
    # Both are directories, or the source holds a file that has to stay:
    # go child by child, then drop the source if that emptied it.
    if is_directory "$src" && { ! present "$dest" || is_directory "$dest"; }; then
        while IFS= read -r child; do
            move_entry "$child" "$dest/${child##*/}"
        done < <(children_of "$src")
        if has_children "$src"; then
            printf '  stays  %s (not empty)\n' "$src"
        else
            remove_directory "$src"
        fi
        return 0
    fi
    # The same bytes on both sides: the source is redundant.
    if is_file "$src" && is_file "$dest" && same_bytes "$src" "$dest"; then
        printf '  same   %s == %s\n' "$src" "$dest"
        if [[ $APPLY == 1 ]]; then
            record "$(printf 'DUP\t%s\t%s' "$src" "$dest")"
            rm -f -- "$src"
        else
            VIRT_FROM+=("$src")
            VIRT_TO+=("")
        fi
        return 0
    fi
    # A real conflict: both sides hold something, and it differs.  Which
    # copy is right depends on how the destination came to exist, so a
    # person decides.  The copy that loses is kept beside the log.
    CONFLICTS=$((CONFLICTS + 1))
    case $PREFER in
    source)
        if inside "$RUN_DIR" "$dest"; then
            die "cannot set $dest aside: it holds the migration records"
        fi
        saved=$RUN_DIR/collisions$dest
        if present "$saved"; then
            die "two sources clash at $dest; settle that one by hand"
        fi
        printf '  keep   %s (it was at the destination)\n' "$saved"
        rename_to "$dest" "$saved"
        rename_to "$src" "$dest"
        ;;
    destination)
        saved=$RUN_DIR/collisions$src
        printf '  keep   %s (the destination stays as it is)\n' "$saved"
        rename_to "$src" "$saved"
        ;;
    *)
        printf '  clash  %s <> %s\n' "$src" "$dest"
        HELD+=("$src")
        ;;
    esac
}

prune_entry() {
    local dir=$1
    is_directory "$dir" || return 0
    if has_children "$dir"; then
        printf '  stays  %s (not empty)\n' "$dir"
    else
        remove_directory "$dir"
    fi
}

# The tests name a file of process names in EMACS_XDG_TEST_PS_FILE.
emacs_processes() {
    if [[ -n ${EMACS_XDG_TEST_PS_FILE:-} ]]; then
        cat -- "$EMACS_XDG_TEST_PS_FILE"
    else
        ps -u "$(id -u)" -o comm=
    fi | awk '{ count = split($0, part, "/"); name = part[count]
                if (name ~ /^(Emacs|emacs|emacs-[0-9][0-9.]*|\.emacs-wrapped)$/)
                    print $0 }'
}

inside() {
    [[ $1 == "$2" || $1 == "$2"/* ]]
}

preflight() {
    local legacy running kind src odd index other
    local -a roots=("$CONFIG_DIR" "$DATA_DIR" "$STATE_DIR" "$CACHE_DIR")
    local -a real=()
    [[ -d $CONFIG_DIR ]] || die "no configuration directory at $CONFIG_DIR"
    [[ -f $CONFIG_DIR/init.org ]] ||
        die "$CONFIG_DIR does not look like the Emacs checkout (no init.org)"
    for legacy in "$HOME/.emacs.d" "$HOME/.emacs" "$HOME/.emacs.el"; do
        if [[ -e $legacy || -L $legacy ]]; then
            die "$legacy exists and would outrank $CONFIG_DIR at startup; move it away first"
        fi
    done
    for src in "${roots[@]}" "$STATE_DIR/migration" "$RUN_DIR"; do
        if [[ (-e $src || -L $src) && ! -d $src ]]; then
            die "$src is not a directory"
        fi
    done
    # Compare the roots as places, not as strings: one of them may be
    # reached through a symbolic link.
    for src in "${roots[@]}"; do
        real+=("$(physical "$src")")
    done
    for index in 1 2 3; do
        if inside "${real[index]}" "${real[0]}" || inside "${real[0]}" "${real[index]}"; then
            die "the data, state and cache roots must lie outside the configuration directory; ${roots[index]} does not"
        fi
        for other in 1 2 3; do
            if [[ $other -gt $index ]] &&
                { inside "${real[index]}" "${real[other]}" || inside "${real[other]}" "${real[index]}"; }; then
                die "the data, state and cache roots must be three separate directories; ${roots[index]} and ${roots[other]} are not"
            fi
        done
    done
    while IFS='|' read -r kind src _; do
        src=$(source_of "$src")
        if [[ -L $src ]]; then
            die "$src is a symbolic link; resolve it by hand first"
        fi
        # The log holds one tab-separated record per line.
        if [[ -d $src ]]; then
            odd=$(find "$src" \( -name $'*\t*' -o -name $'*\n*' \) -print | head -n 1)
            if [[ -n $odd ]]; then
                die "a name under $src contains a tab or a newline; rename it first"
            fi
        fi
    done < <(manifest)
    running=$(emacs_processes) || die 'cannot list running processes'
    if [[ -n $running ]]; then
        printf 'migrate: Emacs is running:\n%s\n' "$running" >&2
        if [[ $APPLY == 1 ]]; then
            die 'quit every Emacs, then run this again'
        fi
        printf 'migrate: this preview can go stale; --apply will refuse until Emacs has quit\n' >&2
    fi
}

backup_sources() {
    local kind src dest other covered
    local -a candidates=() sources=()
    # Only what is in the checkout is archived.  A source under `@data/'
    # never matches here: it is outside the checkout already, and the move
    # only renames it.
    while IFS='|' read -r kind src dest; do
        if [[ $kind == data || $kind == state || $kind == attic ]] &&
            [[ -e $CONFIG_DIR/$src || -L $CONFIG_DIR/$src ]]; then
            candidates+=("$src")
        fi
    done < <(manifest)
    # A source inside a directory that is archived whole would go in twice.
    for src in ${candidates[@]+"${candidates[@]}"}; do
        covered=0
        for other in "${candidates[@]}"; do
            if [[ $src == "$other"/* ]]; then
                covered=1
            fi
        done
        if [[ $covered == 0 ]]; then
            sources+=("$src")
        fi
    done
    if [[ ${#sources[@]} -gt 0 ]]; then
        printf 'Archiving %d sources to %s\n' "${#sources[@]}" "$RUN_DIR/pre-migration.tar"
        tar -cpf "$RUN_DIR/pre-migration.tar" -C "$CONFIG_DIR" -- "${sources[@]}"
    fi
}

leftovers() {
    local entry name
    while IFS= read -r entry; do
        present "$entry" || continue
        name=${entry##*/}
        case $name in
        .git | .gitignore | .gitmodules | .gitea | .github | .claude | .superpowers) continue ;;
        init.el | settings.el | nix-packages | nix-packages.el | certs | eshell) continue ;;
        esac
        if [[ -n $(git -C "$CONFIG_DIR" ls-files -- ":(literal)$name" 2>/dev/null | head -n 1) ]]; then
            continue
        fi
        printf '  %s\n' "$entry"
    done < <(children_of "$CONFIG_DIR")
}

walk_manifest() {
    local kind src dest
    while IFS='|' read -r kind src dest; do
        if [[ $kind == prune ]]; then
            prune_entry "$(source_of "$src")"
        else
            move_entry "$(source_of "$src")" "$(destination_of "$kind" "$dest")"
        fi
    done < <(manifest)
}

migrate() {
    local file
    preflight
    printf 'Configuration: %s\nData:          %s\nState:         %s\nCache:         %s\n' \
        "$CONFIG_DIR" "$DATA_DIR" "$STATE_DIR" "$CACHE_DIR"
    if [[ $APPLY == 1 ]]; then
        # Rehearse first: a conflict must stop the run before anything moves.
        APPLY=0
        walk_manifest >/dev/null
        APPLY=1
        VIRT_FROM=()
        VIRT_TO=()
        HELD=()
        if [[ $CONFLICTS -gt 0 && -z $PREFER ]]; then
            die "$CONFLICTS destinations already hold a different file; preview to see them, then add --prefer=source or --prefer=destination"
        fi
        CONFLICTS=0
        mkdir -p "$DATA_DIR" "$STATE_DIR" "$CACHE_DIR" "$RUN_DIR/attic"
        chmod 700 "$DATA_DIR" "$STATE_DIR" "$CACHE_DIR" "$RUN_DIR"
        : >>"$RUN_DIR/moves.tsv"
        backup_sources
        printf 'Moving; the log is %s\n' "$RUN_DIR/moves.tsv"
    else
        printf 'Preview only: nothing is changed.  Run with --apply to move.\n'
    fi
    walk_manifest
    if [[ $APPLY == 1 ]]; then
        while IFS= read -r file; do
            if [[ -f $file && ! -L $file ]]; then
                chmod 600 "$file"
            fi
        done < <(private_files)
        rmdir "$RUN_DIR/attic" 2>/dev/null || true
    fi
    if [[ $CONFLICTS -gt 0 && -z $PREFER ]]; then
        printf '%d destinations already hold a different file (the clash lines).\n' "$CONFLICTS"
        printf -- '--apply will need --prefer=source or --prefer=destination.\n'
    fi
    printf 'Left in %s, neither tracked nor expected:\n' "$CONFIG_DIR"
    leftovers
    printf 'Done.\n'
}

rollback() {
    local run=$1 log line op first second lost=0
    log=$run/moves.tsv
    [[ -f $log ]] || die "no moves.tsv in $run"
    APPLY=1
    preflight
    # Undo in reverse order.  awk reverses the file: tac is not on macOS.
    # A record whose move is already undone, or never happened, is skipped,
    # so a rollback that stopped can be run again.
    while IFS= read -r line; do
        IFS=$'\t' read -r op first second <<<"$line"
        case $op in
        MV)
            if [[ ! -e $second && ! -L $second ]]; then
                if [[ -e $first || -L $first ]]; then
                    continue
                fi
                printf '  lost   %s (neither it nor %s exists)\n' "$first" "$second"
                lost=$((lost + 1))
                continue
            fi
            if [[ -e $first || -L $first ]]; then
                die "cannot undo: $first exists; move it away and run the rollback again"
            fi
            mkdir -p "$(dirname "$first")"
            mv -- "$second" "$first"
            printf '  mv     %s -> %s\n' "$second" "$first"
            ;;
        RMDIR)
            mkdir -p "$first"
            printf '  mkdir  %s\n' "$first"
            ;;
        DUP)
            if [[ -e $first || -L $first ]]; then
                if [[ -f $first && ! -L $first ]] && cmp -s -- "$first" "$second"; then
                    continue
                fi
                die "cannot undo: $first exists; move it away and run the rollback again"
            fi
            if [[ ! -e $second && ! -L $second ]]; then
                printf '  lost   %s (neither it nor %s exists)\n' "$first" "$second"
                lost=$((lost + 1))
                continue
            fi
            mkdir -p "$(dirname "$first")"
            cp -p -- "$second" "$first"
            printf '  copy   %s -> %s\n' "$second" "$first"
            ;;
        *) die "unreadable line in $log: $line" ;;
        esac
    done < <(awk '{ line[NR] = $0 } END { for (i = NR; i > 0; i--) print line[i] }' "$log")
    if [[ $lost -gt 0 ]]; then
        printf 'Rolled back, except for the %d marked "lost": neither the moved file\n' "$lost"
        printf 'nor its original exists.  The archive in %s may hold them.\n' "$run"
        printf 'The log stays in place, so this can be run again.\n'
        exit 1
    fi
    mv -- "$log" "$log.rolled-back"
    printf 'Rolled back: every file is where it was.  File modes that the move\n'
    printf 'tightened stay tight.  The archive and the log remain in %s\n' "$run"
}

usage() {
    die 'usage: migrate.sh [--apply] [--prefer=source|--prefer=destination] | --rollback DIR'
}

if [[ ${1:-} == --rollback ]]; then
    [[ $# -eq 2 && -n $2 ]] || usage
    rollback "$2"
    exit 0
fi
for argument in "$@"; do
    case $argument in
    --apply) APPLY=1 ;;
    --prefer=source | --prefer=destination) PREFER=${argument#--prefer=} ;;
    *) usage ;;
    esac
done
migrate
