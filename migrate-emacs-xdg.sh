#!/usr/bin/env bash
# One-time migration of this Emacs setup to XDG config, data, and cache roots.
#
# Final layout:
#
#   ~/.config/emacs       configuration checkout plus generated init.el
#   ~/.config/emacs/lisp  personal Emacs Lisp
#   ~/.local/share/emacs  durable, user-specific state
#   ~/.cache/emacs        disposable, rebuildable state
#
# Home Manager currently exposes this repository as ~/.emacs.d. Emacs gives
# that legacy location precedence over ~/.config/emacs, so changing Lisp paths
# alone is insufficient: the Home Manager link and every launcher that names it
# must change together. No --init-directory flag is needed once ~/.emacs.d is
# gone and ~/.config/emacs/init.el exists.
#
# Safety model:
#
# - Existing Git work is never reset, stashed, staged, committed, or pushed.
# - Pre-migration status plus staged and unstaged diffs are copied under
#   ~/.local/share/emacs/migration-backup/.
# - Existing data is moved, not discarded. Destination collisions are retained
#   beneath the same backup directory.
# - Embedded patches accept either pristine or already-applied state, allowing a
#   retry after a failed build or activation.
# - Unknown files in the pre-existing ~/.config/emacs directory stop migration
#   rather than being guessed at.
# - Nix activation occurs only after an explicit YES confirmation and successful
#   source checks, tests, and a non-activating system build.
#
# Quit personal Emacs GUI and daemon instances first. They can rewrite history,
# SQLite WAL files, and caches while those files are moving.
#
# First run:
#
#   bash ~/src/dot-emacs/migrate-emacs-xdg.sh
#
# After Home Manager installs the new link, this equivalent path also works:
#
#   bash ~/.config/emacs/migrate-emacs-xdg.sh

# Abort on failed commands, unset variables, and failed pipeline members. Use a
# private umask because migrated state includes OAuth credentials and histories.
set -euo pipefail
IFS=$'\n\t'
umask 077

die() {
    printf 'migrate-emacs-xdg: %s\n' "$*" >&2
    exit 1
}

need() {
    command -v "$1" >/dev/null 2>&1 || die "required command not found: $1"
}

# Fail before touching files if migration primitives are unavailable. `patch'
# applies audited source edits; `rsync' merges existing state while preserving
# metadata and collision backups.
for command in bash cmp find git make nix-instantiate patch python3 realpath rsync; do
    need "$command"
done

[[ $(uname -s) == Darwin ]] || die 'this script expects the current nix-darwin setup'
[[ -n ${HOME:-} ]] || die 'HOME is not set'

# Source checkouts may be overridden for testing, but defaults match Home Manager
# links on this system. Resolve symlinks now so later identity checks compare
# physical repository paths rather than alternate spellings.
EMACS_REPO_INPUT=${EMACS_REPO:-$HOME/src/dot-emacs}
NIX_REPO_INPUT=${NIX_REPO:-$HOME/src/nix}
SCRIPTS_REPO_INPUT=${SCRIPTS_REPO:-$HOME/src/scripts}

[[ -d $EMACS_REPO_INPUT/.git ]] || die "Emacs repository not found: $EMACS_REPO_INPUT"
[[ -d $NIX_REPO_INPUT/.git ]] || die "Nix repository not found: $NIX_REPO_INPUT"
[[ -d $SCRIPTS_REPO_INPUT/.git ]] || die "scripts repository not found: $SCRIPTS_REPO_INPUT"

EMACS_REPO=$(cd "$EMACS_REPO_INPUT" && pwd -P)
NIX_REPO=$(cd "$NIX_REPO_INPUT" && pwd -P)
SCRIPTS_REPO=$(cd "$SCRIPTS_REPO_INPUT" && pwd -P)

# Respect explicit XDG roots. Their standard fallbacks produce the requested
# ~/.config, ~/.local/share, and ~/.cache layout.
CONFIG_HOME=${XDG_CONFIG_HOME:-$HOME/.config}
DATA_HOME=${XDG_DATA_HOME:-$HOME/.local/share}
CACHE_HOME=${XDG_CACHE_HOME:-$HOME/.cache}
CONFIG_DIR=$CONFIG_HOME/emacs
DATA_DIR=$DATA_HOME/emacs
CACHE_DIR=$CACHE_HOME/emacs

# ~/doc/org/init.org is the old canonical literate source. HOST selects the
# nix-darwin output used for the non-activating build and final switch.
OLD_INIT=$HOME/doc/org/init.org
HOST=${HOSTNAME:-$(hostname -s)}

# These sentinel files verify repository identity before path-specific patches
# are even written to temporary storage.
[[ -f $EMACS_REPO/init.org ]] || die 'init.org missing from Emacs repository'
[[ -f $NIX_REPO/config/xdg-symlinks.nix ]] || die 'unexpected Nix repository layout'
[[ -f $SCRIPTS_REPO/syncup ]] || die 'unexpected scripts repository layout'

# ~/.emacs and ~/.emacs.el outrank both ~/.emacs.d and XDG config. Refuse them
# explicitly; otherwise migration could appear successful while Emacs loads a
# completely different init file.
for legacy_init in "$HOME/.emacs" "$HOME/.emacs.el"; do
    [[ ! -e $legacy_init && ! -L $legacy_init ]] ||
        die "$legacy_init outranks XDG init discovery; move it before running this script"
done

# Before activation, ~/.emacs.d should be the Home Manager link to this same
# checkout. An unrelated legacy directory could contain unexamined config or
# state, so never remove or replace it automatically.
if [[ -e $HOME/.emacs.d || -L $HOME/.emacs.d ]]; then
    [[ $(realpath "$HOME/.emacs.d") == "$EMACS_REPO" ]] ||
        die "$HOME/.emacs.d does not resolve to $EMACS_REPO"
fi

# On a resumed run Home Manager may already have created the XDG link. Accept it
# only when it reaches this exact checkout; any other target is a conflict.
if [[ -L $CONFIG_DIR ]]; then
    [[ $(realpath "$CONFIG_DIR") == "$EMACS_REPO" ]] ||
        die "$CONFIG_DIR is a symlink but does not resolve to $EMACS_REPO"
fi

# The repository copy becomes canonical. Require byte-for-byte agreement with
# the old Org-tree copy before archiving that copy, preventing silent loss of
# edits made in only one location.
if [[ -e $OLD_INIT ]]; then
    cmp -s "$OLD_INIT" "$EMACS_REPO/init.org" ||
        die "$OLD_INIT differs from $EMACS_REPO/init.org; reconcile them first"
fi

# ~/.config/emacs already exists as a small ordinary directory on this host.
# Certificates are configuration and move into the repository; the Anvil log is
# cache. Home Manager cannot replace this directory with its managed symlink
# until it is empty. Refuse unknown entries instead of hiding or deleting them.
if [[ -d $CONFIG_DIR && ! -L $CONFIG_DIR ]]; then
    while IFS= read -r entry; do
        case ${entry##*/} in
        certs | anvil-worker.log | .DS_Store) ;;
        *) die "unexpected existing config entry: $entry" ;;
        esac
    done < <(find "$CONFIG_DIR" -mindepth 1 -maxdepth 1 -print)
elif [[ -L $CONFIG_DIR ]]; then
    : # Resume after Home Manager has installed the desired link.
elif [[ -e $CONFIG_DIR ]]; then
    die "$CONFIG_DIR exists but is not a directory"
fi

# Interactive confirmation is also activation authorization: the final switch
# invokes sudo and changes the live Home Manager generation. Automation must opt
# in explicitly with EMACS_XDG_MIGRATION_CONFIRM=YES.
if [[ ${EMACS_XDG_MIGRATION_CONFIRM:-} != YES ]]; then
    [[ -t 0 ]] || die 'set EMACS_XDG_MIGRATION_CONFIRM=YES for non-interactive execution'
    printf '%s\n' \
        'Quit personal Emacs GUI and daemon instances before continuing.' \
        "This will patch $EMACS_REPO, $NIX_REPO, and $SCRIPTS_REPO," \
        'move Emacs state, build nix-darwin, and activate it with sudo.'
    read -r -p 'Type YES to continue: ' reply
    [[ $reply == YES ]] || die 'cancelled'
fi

# Use one timestamped recovery root for source snapshots and every destination
# collision. Temporary patch files disappear on exit; recovery material does not.
STAMP=$(date +%Y%m%d-%H%M%S)
BACKUP_DIR=$DATA_DIR/migration-backup/$STAMP
COLLISION_DIR=$BACKUP_DIR/collisions
PATCH_TMP=$(mktemp -d "${TMPDIR:-/tmp}/emacs-xdg-patches.XXXXXX")
trap 'rm -rf "$PATCH_TMP"' EXIT
mkdir -p "$BACKUP_DIR" "$COLLISION_DIR" "$CACHE_DIR"

# Capture both index-relative and worktree-relative patches because these
# repositories may already contain unrelated staged work. `--binary' keeps the
# snapshot usable even if a future local edit is not plain text.
record_repo() {
    local name=$1 repo=$2
    {
        printf 'repository: %s\n\n' "$repo"
        git -C "$repo" status --short --branch || true
    } >"$BACKUP_DIR/$name-status.txt"
    git -C "$repo" diff --binary >"$BACKUP_DIR/$name-unstaged.patch" || true
    git -C "$repo" diff --cached --binary >"$BACKUP_DIR/$name-staged.patch" || true
}

record_repo dot-emacs "$EMACS_REPO"
record_repo nix "$NIX_REPO"
record_repo scripts "$SCRIPTS_REPO"

# Patches are pinned to files inspected when this script was generated. They use
# zero-context unified diffs so this Bash file contains no whitespace-only diff
# markers; removed lines still provide exact guards against patching wrong code.
#
# The Emacs patch establishes data/cache helpers, redirects every observed writer,
# creates early-init.el for native-comp/package paths, makes repository init.org
# canonical, and updates current documentation. Runtime files are unignored so
# future regressions become visible in `git status'.
cat >"$PATCH_TMP/emacs.patch" <<'PATCH'
--- a/init.org
+++ b/init.org
@@ -92 +92 @@
-** Define the "data environment" for this instance of Emacs
+** Define XDG data and cache directories for this instance of Emacs
@@ -97,6 +97,3 @@
-
-  (let ((emacs-data-suffix
-         (and (string= "emacsERC" emacs-environment) "alt")))
-
-    (defconst alternate-emacs (string= emacs-data-suffix "alt"))
-
+  (defconst alternate-emacs (string= "emacsERC" emacs-environment))
+
+  (let ((instance (if alternate-emacs "emacs/alt" "emacs")))
@@ -104,6 +101,41 @@
-      (emacs-path (if emacs-data-suffix
-                      (format "data-%s" emacs-data-suffix)
-                    "data"))))
-
-  (defun user-data (dir)
-    (expand-file-name dir user-data-directory)))
+      (file-name-as-directory
+       (expand-file-name instance
+                         (or (getenv "XDG_DATA_HOME") "~/.local/share"))))
+    (defconst user-cache-directory
+      (file-name-as-directory
+       (expand-file-name instance
+                         (or (getenv "XDG_CACHE_HOME") "~/.cache")))))
+
+  (defun user-data (path)
+    (expand-file-name path user-data-directory))
+
+  (defun user-cache (path)
+    (expand-file-name path user-cache-directory))
+
+  (dolist (directory (list user-data-directory user-cache-directory))
+    (make-directory directory t))
+
+  ;; Bind defaults before their libraries load, so packages do not write state
+  ;; below `user-emacs-directory'.
+  (with-no-warnings
+    (setq package-user-dir (user-data "elpa")
+          package-quickstart-file (user-cache "package-quickstart.el")
+          project-list-file (user-data "projects")
+          multisession-directory (user-data "multisession/")
+          persist--directory-location (user-data "persist/")
+          request-storage-directory (user-data "request/")
+          hash-store-directory (user-data "hash-store/")
+          org-persist-directory (user-data "org-persist/")
+          projectile-frecency-file (user-data "projectile-frecency.eld")
+          gptel-anthropic-oauth-cache-dir (user-data "oauth/anthropic/")
+          gptel-claude-oauth-cache-dir (user-data "oauth/claude/")
+          pcache-directory (user-cache "pcache/")
+          emojify-emojis-dir (user-cache "emojis/")
+          elisp-autofmt-cache-directory (user-cache "elisp-autofmt/")
+          org-generic-id-locations-file
+          (user-cache "org-generic-id-locations")))
+
+  (with-no-warnings
+    (add-to-list 'treesit-extra-load-path (user-cache "tree-sitter/"))
+    (setq treesit--install-language-grammar-out-dir-history
+          (list (user-cache "tree-sitter/")))))
@@ -462 +494 @@
-  (auto-save-list-file-prefix (user-data "auto-save-list/.saves-"))
+  (auto-save-list-file-prefix (user-cache "auto-save-list/.saves-"))
@@ -475 +507 @@
-  (backup-directory-alist '(("." . "~/.local/share/emacs/backups")))
+  (backup-directory-alist `(("." . ,(user-data "backups"))))
@@ -581 +613 @@
-               "~/.config/emacs/certs/vulcan-ca-bundle.pem"))
+               (emacs-path "certs/vulcan-ca-bundle.pem")))
@@ -1136 +1168 @@
-  (bookmark-default-file "~/doc/bookmarks"))
+  (bookmark-default-file (user-data "bookmarks")))
@@ -2376 +2408 @@
-  (erc-log-channels-directory "~/.local/share/ERC")
+  (erc-log-channels-directory (user-data "erc/"))
@@ -2599,0 +2632,2 @@
+  (eshell-history-file-name (user-data "eshell/history"))
+  (eshell-last-dir-ring-file-name (user-data "eshell/lastdir"))
@@ -3360,0 +3395,2 @@
+  :custom
+  (gptel-claude-oauth-cache-dir (user-data "oauth/claude/"))
@@ -3371,0 +3408,2 @@
+  :custom
+  (gptel-anthropic-oauth-cache-dir (user-data "oauth/anthropic/"))
@@ -4675 +4713 @@
-  (forge-database-file "~/.config/forge/database.sqlite")
+  (forge-database-file (user-data "forge/database.sqlite"))
@@ -5922 +5960 @@
-  (projectile-cache-file (user-data "projectile.cache"))
+  (projectile-cache-file (user-cache "projectile.cache"))
@@ -5931,0 +5970 @@
+  (projectile-frecency-file (user-data "projectile-frecency.eld"))
@@ -6604 +6643 @@
-  (tramp-auto-save-directory "~/.local/share/emacs/backups")
+  (tramp-auto-save-directory (user-data "backups"))
@@ -6661 +6700 @@
-  (setq tramp-persistency-file-name (user-data "tramp")))
+  (setq tramp-persistency-file-name (user-cache "tramp")))
@@ -6836 +6875 @@
-  (url-cache-directory (user-data "url/cache")))
+  (url-cache-directory (user-cache "url/cache")))
@@ -9200,2 +9239,2 @@
-  (lsp-server-install-dir (user-data ".cache/lsp"))
-  (lsp-session-file (user-data ".lsp-session-v1"))
+  (lsp-server-install-dir (user-cache "lsp/"))
+  (lsp-session-file (user-cache "lsp/session"))
@@ -9593,0 +9633 @@
+  (elpy-rpc-virtualenv-path (user-cache "elpy/rpc-venv"))
@@ -10023 +10063 @@
-  (setq gnus-home-directory "~/.local/share/gnus/"
+  (setq gnus-home-directory (user-data "gnus/")
@@ -10876 +10916 @@
-  (gnus-sieve-file "~/.local/share/gnus/active")
+  (gnus-sieve-file (user-data "gnus/active"))
@@ -11261 +11301 @@
-               (expand-file-name "~/.emacs.d/lisp/org-mode/doc"))
+               (emacs-path "lisp/org-mode/doc"))
@@ -13484 +13524 @@
-  (xeft-database (user-data "xeft.db"))
+  (xeft-database (user-cache "xeft.db"))
--- a/Makefile
+++ b/Makefile
@@ -5,2 +4,0 @@
-
-TARGET = $(patsubst %.el,%.elc,init.el)
@@ -27,8 +25 @@
-init.org: ~/org/init.org
-	@if test ~/org/init.org -nt $@; then	        \
-	    rm -f $@;					\
-	    cp -p ~/org/init.org $@;		        \
-	    chmod 444 $@;				\
-	fi
-
-# Generate lisp and compile it
+# Generate Lisp from the repository's canonical Org source.
@@ -46,6 +37,2 @@
-%.elc: %.el
-	@echo Compiling file $<
-	@$(BATCH_LOAD) -f batch-byte-compile $<
-
-speed: init.elc
-	time $(BATCH_LOAD) -Q -L . -l init		\
+speed: init.el
+	time $(BATCH_LOAD) -Q -L . -l init.el		\
@@ -65 +52 @@
-	rm -f init.el *.elc *~ settings.el
+	rm -f init.el *~
--- a/.gitignore
+++ b/.gitignore
@@ -2,6 +1,0 @@
-/.org-generic-id-locations
-/data*/
-/eln-cache/
-/elpy/
-/emojis/
-/eshell/
@@ -9,8 +2,0 @@
-/persist/
-/projects
-/request/
-/settings.el
-/transient/
-/var/
-/.lsp-session-v1
-/.cache/
@@ -18,2 +3,0 @@
-/gptel-agent/
-/elisp-autofmt-cache/
@@ -29 +12,0 @@
-projectile-frecency.eld
--- a/lisp/personal.el
+++ b/lisp/personal.el
@@ -572 +572 @@
-            (parse-packages "~/org/init.org" #'init-org-packages)
+            (parse-packages (emacs-path "init.org") #'init-org-packages)
--- a/lisp/coq-lookup.el
+++ b/lisp/coq-lookup.el
@@ -89 +89 @@
-    (expand-file-name "coq-lookup" base))
+    (expand-file-name "emacs/coq-lookup" base))
--- a/lisp/llm-setup/CLAUDE.md
+++ b/lisp/llm-setup/CLAUDE.md
@@ -66 +66 @@
-The deployed path (`~/.emacs.d/lisp/llm-setup`) is the same physical directory
+The deployed path (`~/.config/emacs/lisp/llm-setup`) is the same physical directory
--- a/SUBMODULE-AUTHORSHIP.md
+++ b/SUBMODULE-AUTHORSHIP.md
@@ -9 +9 @@
-submodule (see `~/.emacs.d/.gitmodules`).
+submodule (see `~/.config/emacs/.gitmodules`).
@@ -117 +117 @@
-To turn one back into a submodule of `~/.emacs.d` and drop its Nix definition:
+To turn one back into a submodule of `~/.config/emacs` and drop its Nix definition:
@@ -120 +120 @@
-cd ~/.emacs.d
+cd ~/.config/emacs
@@ -124 +124 @@
-# then re-add its (use-package … :load-path "lisp/alert") in ~/org/init.org,
+# then re-add its (use-package … :load-path "lisp/alert") in ~/.config/emacs/init.org,
--- a/test-emacs
+++ b/test-emacs
@@ -1 +1 @@
-./src/emacs -batch -L ~/.emacs.d/lisp -l ~/.emacs.d/lisp/condition-variables.el
+./src/emacs -batch -L ~/.config/emacs/lisp -l ~/.config/emacs/lisp/condition-variables.el
--- /dev/null
+++ b/early-init.el
@@ -0,0 +1,20 @@
+;;; early-init.el --- Early XDG paths -*- lexical-binding: t; -*-
+
+(let* ((instance (if (string= "emacsERC" (getenv "NIX_MYENV_NAME"))
+                     "emacs/alt"
+                   "emacs"))
+       (data-directory
+        (expand-file-name instance
+                          (or (getenv "XDG_DATA_HOME") "~/.local/share")))
+       (cache-directory
+        (expand-file-name instance
+                          (or (getenv "XDG_CACHE_HOME") "~/.cache"))))
+  (make-directory data-directory t)
+  (make-directory cache-directory t)
+  (setq package-user-dir (expand-file-name "elpa" data-directory)
+        package-quickstart-file
+        (expand-file-name "package-quickstart.el" cache-directory))
+  (startup-redirect-eln-cache
+   (expand-file-name "eln-cache/" cache-directory)))
+
+;;; early-init.el ends here
PATCH

# Home Manager must own ~/.config/emacs and must stop creating ~/.emacs.d, since
# legacy init discovery would otherwise win. Tests and runemacs change in the
# same patch so declarative policy, validation, and invocation stay synchronized.
cat >"$PATCH_TMP/nix.patch" <<'PATCH'
--- a/config/xdg-symlinks.nix
+++ b/config/xdg-symlinks.nix
@@ -62 +62 @@
-      ".emacs.d".source = mkLink "${home}/src/dot-emacs";
+      ".config/emacs".source = mkLink "${home}/src/dot-emacs";
--- a/test/home/host-behavior.nix
+++ b/test/home/host-behavior.nix
@@ -751 +751,2 @@
-  && builtins.hasAttr ".emacs.d" config.home.file
+  && builtins.hasAttr ".config/emacs" config.home.file
+  && !(builtins.hasAttr ".emacs.d" config.home.file)
@@ -757,0 +759 @@
+  && !(builtins.hasAttr ".config/emacs" config.home.file)
--- a/test/bin/gates-slow-test.py
+++ b/test/bin/gates-slow-test.py
@@ -2491 +2491 @@
-                    ".emacs.d",
+                    ".config/emacs",
--- a/Makefile
+++ b/Makefile
@@ -295 +295 @@
-	for repo in .config/pushme .emacs.d src/nix src/scripts doc org; do \
+	for repo in .config/pushme .config/emacs src/nix src/scripts doc org; do \
--- a/bin/runemacs
+++ b/bin/runemacs
@@ -2 +2 @@
-exec load-env-emacs${1:-$EMACSVER} bash -c "unset TZ ; make -C ~/.emacs.d open"
+exec load-env-emacs${1:-$EMACSVER} bash -c "unset TZ ; make -C ~/.config/emacs open"
PATCH

# User scripts also name the old location. Update package-review, synchronization,
# and prompt lookup paths; syncup now tangles init.el rather than producing a
# source-tree init.elc that belongs in cache.
cat >"$PATCH_TMP/scripts.patch" <<'PATCH'
--- a/changes-all
+++ b/changes-all
@@ -3 +3 @@
-cd ~/.emacs.d/lisp && changes
+cd ~/.config/emacs/lisp && changes
--- a/syncup
+++ b/syncup
@@ -23,2 +23,2 @@
-cd ~/.emacs.d
-load-env-emacs$EMACSVER make init.elc && rm -f init.elc
+cd ~/.config/emacs
+load-env-emacs$EMACSVER make init.el
--- a/gemini_to_org.py
+++ b/gemini_to_org.py
@@ -45,3 +45,3 @@
-SHORTEN_PROMPT_FILE = os.path.expanduser('~/.emacs.d/prompts/shorten.txt')
-INFER_TASKS_PROMPT_FILE = os.path.expanduser('~/.emacs.d/prompts/infer-tasks.md')
-TITLE_PROMPT_FILE = os.path.expanduser('~/.emacs.d/prompts/title.txt')
+SHORTEN_PROMPT_FILE = os.path.expanduser('~/.config/emacs/prompts/shorten.txt')
+INFER_TASKS_PROMPT_FILE = os.path.expanduser('~/.config/emacs/prompts/infer-tasks.md')
+TITLE_PROMPT_FILE = os.path.expanduser('~/.config/emacs/prompts/title.txt')
--- a/README.md
+++ b/README.md
@@ -513 +513 @@
-- Emacs integration (`.emacs.d` synchronization)
+- Emacs integration (`~/.config/emacs` synchronization)
PATCH

# Determine all three patch states before applying any. A clean forward dry-run
# means source is pristine. A clean reverse dry-run means an earlier attempt
# already applied it. Anything else is mixed or unexpected and stops safely.
patch_state() {
    local repo=$1 patch_file=$2
    if (cd "$repo" &&
        patch --dry-run --silent --batch --forward -p1 <"$patch_file"); then
        printf 'apply\n'
    elif (cd "$repo" &&
          patch --dry-run --silent --batch --reverse -p1 <"$patch_file"); then
        printf 'applied\n'
    else
        die "patch is neither cleanly applicable nor already applied: $patch_file"
    fi
}

emacs_patch_state=$(patch_state "$EMACS_REPO" "$PATCH_TMP/emacs.patch")
nix_patch_state=$(patch_state "$NIX_REPO" "$PATCH_TMP/nix.patch")
scripts_patch_state=$(patch_state "$SCRIPTS_REPO" "$PATCH_TMP/scripts.patch")

# Apply only pristine patch sets. This makes retries after later migration/build
# failures harmless without weakening checks for partially edited files.
if [[ $emacs_patch_state == apply ]]; then
    chmod u+w "$EMACS_REPO/init.org"
    (
        cd "$EMACS_REPO"
        patch --batch --forward -p1 <"$PATCH_TMP/emacs.patch"
    )
fi
if [[ $nix_patch_state == apply ]]; then
    (
        cd "$NIX_REPO"
        patch --batch --forward -p1 <"$PATCH_TMP/nix.patch"
    )
fi
if [[ $scripts_patch_state == apply ]]; then
    (
        cd "$SCRIPTS_REPO"
        patch --batch --forward -p1 <"$PATCH_TMP/scripts.patch"
    )
fi
chmod 644 "$EMACS_REPO/early-init.el" "$EMACS_REPO/init.org"

# Move one file or merge one directory without losing either side. Missing sources
# are success so reruns can continue. Each collision receives a distinct backup
# subtree; identical files collapse to one copy.
move_count=0
move_path() {
    local src=$1 dest=$2 call_backup
    # A previous run may already have moved this source. Guard against empty/root
# arguments before any rm or mv operation.
    [[ -e $src || -L $src ]] || return 0
    [[ -n $src && -n $dest && $src != / && $dest != / ]] || die 'unsafe move path'

    # Numbered backup roots prevent two independent merges with the same relative
# filename from overwriting each other's recovery copies.
    ((move_count += 1))
    call_backup=$COLLISION_DIR/$move_count
    mkdir -p "$call_backup" "$(dirname "$dest")"
    printf 'move: %s -> %s\n' "$src" "$dest"

    # Directories may already exist (notably ~/.local/share/emacs/backups). rsync
# merges metadata-preservingly and backs up overwritten destination files. Source
# deletion happens only after rsync reports success.
    if [[ -d $src && ! -L $src ]]; then
        if [[ (-e $dest || -L $dest) && (! -d $dest || -L $dest) ]]; then
            mv "$dest" "$call_backup/"
        fi
        mkdir -p "$dest"
        rsync -a --remove-source-files --backup --backup-dir="$call_backup" \
            "$src/" "$dest/"
        rm -rf "$src"
    else
        # For single files, discard only a byte-identical duplicate. Otherwise
# preserve the old destination first, then install the migrated source.
        if [[ -e $dest || -L $dest ]]; then
            if [[ -f $src && -f $dest ]] && cmp -s "$src" "$dest"; then
                rm -f "$src"
                return 0
            fi
            mv "$dest" "$call_backup/"
        fi
        mv "$src" "$dest"
    fi
}

# Preserve configuration already present at ~/.config/emacs, then remove only the
# now-empty directory. Home Manager needs the path absent so it can atomically
# install its out-of-store symlink to this checkout. On resumed runs, an existing
# correct symlink bypasses this block.
if [[ -d $CONFIG_DIR && ! -L $CONFIG_DIR ]]; then
    move_path "$CONFIG_DIR/certs" "$EMACS_REPO/certs"
    move_path "$CONFIG_DIR/anvil-worker.log" "$CACHE_DIR/anvil-worker.log"
    move_path "$CONFIG_DIR/.DS_Store" "$CACHE_DIR/orphans/config-.DS_Store"
    rmdir "$CONFIG_DIR"
fi

# Old `data/' mixed durable state with rebuildable indexes. Pull known caches out
# first; then merge everything remaining (history, cookies, Org databases, etc.)
# into ~/.local/share/emacs.
move_path "$EMACS_REPO/data/auto-save-list" "$CACHE_DIR/auto-save-list"
move_path "$EMACS_REPO/data/projectile.cache" "$CACHE_DIR/projectile.cache"
move_path "$EMACS_REPO/data/tramp" "$CACHE_DIR/tramp"
move_path "$EMACS_REPO/data/url/cache" "$CACHE_DIR/url/cache"
move_path "$EMACS_REPO/data/.cache/lsp" "$CACHE_DIR/lsp"
move_path "$EMACS_REPO/data/xeft.db" "$CACHE_DIR/xeft.db"
move_path "$EMACS_REPO/data" "$DATA_DIR"

# emacsERC previously used an alternate data suffix. Merge both historical names
# into XDG `alt/' roots while retaining the same instance isolation.
for old_alt in "$EMACS_REPO/data-alt" "$EMACS_REPO/data-MacPort"; do
    move_path "$old_alt/auto-save-list" "$CACHE_DIR/alt/auto-save-list"
    move_path "$old_alt/projectile.cache" "$CACHE_DIR/alt/projectile.cache"
    move_path "$old_alt/tramp" "$CACHE_DIR/alt/tramp"
    move_path "$old_alt/url/cache" "$CACHE_DIR/alt/url/cache"
    move_path "$old_alt/.cache/lsp" "$CACHE_DIR/alt/lsp"
    move_path "$old_alt/xeft.db" "$CACHE_DIR/alt/xeft.db"
    move_path "$old_alt" "$DATA_DIR/alt"
done

# Durable state survives cache deletion: histories, known projects, sessions,
# cookies, content-addressed data, and user choices. OAuth token files also belong
# here despite their old directory being named `.cache'; losing them requires
# reauthentication. Eshell alias/login files remain in config, while mutable
# history/last-directory files move to data.
# Persistent state.
move_path "$EMACS_REPO/multisession" "$DATA_DIR/multisession"
move_path "$EMACS_REPO/persist" "$DATA_DIR/persist"
move_path "$EMACS_REPO/projects" "$DATA_DIR/projects"
move_path "$EMACS_REPO/request" "$DATA_DIR/request"
move_path "$EMACS_REPO/transient" "$DATA_DIR/transient"
move_path "$EMACS_REPO/gptel-agent" "$DATA_DIR/gptel-agent"
move_path "$EMACS_REPO/hash-store" "$DATA_DIR/hash-store"
move_path "$EMACS_REPO/projectile-frecency.eld" "$DATA_DIR/projectile-frecency.eld"
move_path "$EMACS_REPO/eshell/history" "$DATA_DIR/eshell/history"
move_path "$EMACS_REPO/eshell/lastdir" "$DATA_DIR/eshell/lastdir"
move_path "$EMACS_REPO/.cache/anthropic-oauth" "$DATA_DIR/oauth/anthropic"
move_path "$EMACS_REPO/.cache/claude-oauth" "$DATA_DIR/oauth/claude"

# These artifacts can be recreated from configuration or primary data: native and
# byte-code support files, downloaded emoji/tree-sitter assets, indexes, language
# servers, and formatter caches. Keeping them under ~/.cache/emacs makes cache
# eviction safe and keeps Git configuration clean.
# Rebuildable cache.
move_path "$EMACS_REPO/auto-save-list" "$CACHE_DIR/auto-save-list"
move_path "$EMACS_REPO/eln-cache" "$CACHE_DIR/eln-cache"
move_path "$EMACS_REPO/elisp-autofmt-cache" "$CACHE_DIR/elisp-autofmt"
move_path "$EMACS_REPO/elpy" "$CACHE_DIR/elpy"
move_path "$EMACS_REPO/emojis" "$CACHE_DIR/emojis"
move_path "$EMACS_REPO/tree-sitter" "$CACHE_DIR/tree-sitter"
move_path "$EMACS_REPO/var/pcache" "$CACHE_DIR/pcache"
move_path "$EMACS_REPO/var/osm" "$CACHE_DIR/osm"
move_path "$EMACS_REPO/var" "$CACHE_DIR/legacy-var"
move_path "$EMACS_REPO/.lsp-session-v1" "$CACHE_DIR/lsp/session"
move_path "$EMACS_REPO/.org-generic-id-locations" "$CACHE_DIR/org-generic-id-locations"
move_path "$EMACS_REPO/.cache" "$CACHE_DIR"
move_path "$EMACS_REPO/%backup%~" "$CACHE_DIR/orphans/%backup%~"
# Anvil indexes and logs are rebuildable; its authoritative state database is not.
# Wildcard loops below also catch SQLite journal/WAL companions without naming
# volatile suffixes individually.
move_path "$EMACS_REPO/.anvil-semantic" "$CACHE_DIR/anvil/semantic"
move_path "$EMACS_REPO/anvil-worker-init.el" "$CACHE_DIR/anvil/worker-init.el"
move_path "$EMACS_REPO/anvil-worker.log" "$CACHE_DIR/anvil/worker.log"
for database in \
    "$EMACS_REPO"/anvil-memory-index.db* \
    "$EMACS_REPO"/anvil-org-index.db*; do
    [[ -e $database ]] && move_path "$database" "$CACHE_DIR/anvil/${database##*/}"
done
for database in "$EMACS_REPO"/anvil-state.db*; do
    [[ -e $database ]] && move_path "$database" "$DATA_DIR/anvil/${database##*/}"
done

# A few Emacs packages already stored state outside ~/.emacs.d, but not beneath
# the unified Emacs namespace. Bring bookmarks, ERC/Gnus state, Forge's database,
# and coq-lookup's generated index into the same data/cache roots.
# State formerly kept outside this repository.
move_path "$HOME/doc/bookmarks" "$DATA_DIR/bookmarks"
move_path "$DATA_HOME/ERC" "$DATA_DIR/erc"
move_path "$DATA_HOME/gnus" "$DATA_DIR/gnus"
move_path "$CONFIG_HOME/forge/database.sqlite" "$DATA_DIR/forge/database.sqlite"
rmdir "$CONFIG_HOME/forge" 2>/dev/null || true
move_path "$CACHE_HOME/coq-lookup" "$CACHE_DIR/coq-lookup"

# init.org in dot-emacs is now canonical. Archive the old tracked Org-tree copy
# rather than merely leaving two writable sources that will drift. The earlier
# cmp guard proves this archived copy matched the pre-patch repository source.
move_path "$OLD_INIT" "$BACKUP_DIR/init.org.from-doc-org"

# Restrict top-level state roots and credential directories. Preserve ordinary
# file modes elsewhere, but force OAuth token payloads to owner-read/write only.
mkdir -p "$DATA_DIR" "$CACHE_DIR"
chmod 700 "$DATA_DIR" "$CACHE_DIR"
for oauth_dir in "$DATA_DIR/oauth/anthropic" "$DATA_DIR/oauth/claude"; do
    if [[ -d $oauth_dir ]]; then
        chmod 700 "$oauth_dir"
        find "$oauth_dir" -type f -exec chmod 600 {} +
    fi
done

# Byte-code beside source is disposable and can shadow newer .el files. Delete it
# rather than relocating stale artifacts; normal native compilation will rebuild
# code under ~/.cache/emacs/eln-cache via early-init.el. init.el is also regenerated
# from canonical init.org below.
find "$EMACS_REPO" -path "$EMACS_REPO/.git" -prune -o \
    -type f -name '*.elc' -delete
rm -f "$EMACS_REPO/init.el"

# Cheap source checks run before expensive Nix work: shell parsers cover launchers,
# Python AST parsing avoids generating __pycache__, and Nix parsing checks changed
# modules without evaluating or activating the system.
# Source-level checks.
bash -n "$SCRIPTS_REPO/changes-all" "$SCRIPTS_REPO/syncup"
sh -n "$NIX_REPO/bin/runemacs"
python3 - "$SCRIPTS_REPO/gemini_to_org.py" <<'PY'
import ast
import pathlib
import sys

ast.parse(pathlib.Path(sys.argv[1]).read_text())
PY
nix-instantiate --parse "$NIX_REPO/config/xdg-symlinks.nix" >/dev/null
nix-instantiate --parse "$NIX_REPO/test/home/host-behavior.nix" >/dev/null

# Tangle and load init.org inside the same Nix-managed Emacs environment used by
# runemacs. Fall back to PATH Emacs only when that environment loader is absent.
EMACS_LOADER=load-env-emacs${EMACSVER:-30MacPort}
if command -v "$EMACS_LOADER" >/dev/null 2>&1; then
    "$EMACS_LOADER" make -C "$EMACS_REPO" init.el
elif command -v emacs >/dev/null 2>&1; then
    make -C "$EMACS_REPO" init.el
else
    die "neither $EMACS_LOADER nor emacs is available"
fi

# Nix order is deliberate: repository contracts first, then a non-activating
# system build, then `switch'. The switch may refresh local-input locks and uses
# sudo only for final profile activation. Initial YES confirmation authorizes it.
# Verify Nix behavior, build first, then perform explicitly confirmed activation.
(
    cd "$NIX_REPO"
    make test
    ./build system
    make HOSTNAME="$HOST" switch
)

# Filesystem checks catch the most dangerous half-migration: legacy ~/.emacs.d
# remaining would silently outrank XDG config even if every Lisp variable were
# correct. Also prove Home Manager's new link reaches this checkout.
[[ -L $CONFIG_DIR ]] || die "$CONFIG_DIR is not a Home Manager symlink after activation"
[[ $(realpath "$CONFIG_DIR") == "$EMACS_REPO" ]] ||
    die "$CONFIG_DIR does not resolve to $EMACS_REPO"
[[ ! -e $HOME/.emacs.d && ! -L $HOME/.emacs.d ]] ||
    die "$HOME/.emacs.d still exists and will outrank XDG configuration"
[[ -f $CONFIG_DIR/init.el && -f $CONFIG_DIR/early-init.el ]] ||
    die 'generated init.el or early-init.el missing from XDG configuration'

# Keep verification on the configured Emacs toolchain rather than accidentally
# testing a different executable from PATH.
run_emacs_env() {
    if command -v "$EMACS_LOADER" >/dev/null 2>&1; then
        "$EMACS_LOADER" "$@"
    else
        "$@"
    fi
}

# First launch without --init-directory to test real-world discovery: Emacs must
# choose ~/.config/emacs naturally. Batch mode does not load user init, so a second
# launch explicitly loads early-init.el and init.el to validate Lisp-level data,
# cache, and native-comp destinations without opening a GUI.
EXPECTED_CONFIG=$CONFIG_DIR run_emacs_env emacs --batch --eval \
    '(unless (file-equal-p user-emacs-directory (getenv "EXPECTED_CONFIG"))
       (error "Emacs discovered %S, expected %S"
              user-emacs-directory (getenv "EXPECTED_CONFIG")))'

EXPECTED_CONFIG=$CONFIG_DIR \
EXPECTED_DATA=$DATA_DIR \
EXPECTED_CACHE=$CACHE_DIR \
run_emacs_env emacs --batch \
    --init-directory="$CONFIG_DIR" \
    --load="$CONFIG_DIR/early-init.el" \
    --load="$CONFIG_DIR/init.el" \
    --eval \
    '(unless (and (file-equal-p user-emacs-directory (getenv "EXPECTED_CONFIG"))
                  (file-equal-p user-data-directory (getenv "EXPECTED_DATA"))
                  (file-equal-p user-cache-directory (getenv "EXPECTED_CACHE"))
                  (file-in-directory-p (car native-comp-eln-load-path)
                                       (getenv "EXPECTED_CACHE")))
       (error "XDG path verification failed"))'

# Report locations plus every affected repository. Staging and commit boundaries
# remain a human decision because unrelated work existed before migration.
printf '\nMigration complete. Backup: %s\n' "$BACKUP_DIR"
printf '%s\n' \
    "config: $CONFIG_DIR" \
    "data:   $DATA_DIR" \
    "cache:  $CACHE_DIR" \
    '' \
    'Review Git status below. Script deliberately does not stage, commit, or push.'
for repo in "$EMACS_REPO" "$NIX_REPO" "$SCRIPTS_REPO" "$HOME/doc/org"; do
    printf '\n### %s\n' "$repo"
    git -C "$repo" status --short --branch || true
done
