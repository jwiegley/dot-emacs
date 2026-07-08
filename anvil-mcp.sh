#!/bin/sh
# anvil-mcp.sh --- Claude Code stdio entry point for the Anvil MCP server.
#
# anvil-stdio.sh invokes a bare `emacsclient', but in this environment
# Emacs lives in a nix store env with no stable bin/ symlink on PATH.
# Resolve emacsclient beside the *running* Emacs.app process so the
# client always matches the daemon serving /tmp/johnw-emacs/server;
# fall back to whatever PATH already provides.
#
# Register with:
#   claude mcp add anvil --scope user -- \
#     ~/.emacs.d/anvil-mcp.sh --socket=/tmp/johnw-emacs/server --server-id=anvil

emacs_bin=$(ps -axo command= \
    | sed -n 's|^\(/nix/store/[^ ]*\)/Applications/Emacs.app/Contents/MacOS/Emacs.*|\1/bin|p' \
    | head -1)
if [ -n "$emacs_bin" ]; then
    PATH="$emacs_bin:$PATH"
    export PATH
fi

exec "$(dirname "$0")/anvil-stdio.sh" "$@"
