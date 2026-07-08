#!/nix/store/azk9ni0ks4gbvy7msvaz7j7h32zllpja-bash-5.3p9/bin/bash
# anvil-stdio.sh - Connect to Anvil MCP server via stdio transport
#
# Copyright (C) 2025 Laurynas Biveinis
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <https://www.gnu.org/licenses/>.

set -eu -o pipefail

# Default values
INIT_FUNCTION=""
STOP_FUNCTION=""
SOCKET=""
SERVER_ID=""
EMACS_MCP_DEBUG_LOG=${EMACS_MCP_DEBUG_LOG:-""}

# GNU base64 tolerates stray non-alphabet bytes with --ignore-garbage;
# BSD/macOS base64 has no such flag.  Probe once at startup and pass
# the flag only where supported.
if printf 'Zg==' | base64 -d --ignore-garbage >/dev/null 2>&1; then
	_anvil_b64_flags="--ignore-garbage"
else
	_anvil_b64_flags=""
fi

# Debug logging setup
if [ -n "$EMACS_MCP_DEBUG_LOG" ]; then
	# Verify log file is writable
	if ! touch "$EMACS_MCP_DEBUG_LOG" 2>/dev/null; then
		echo "Error: Cannot write to debug log file: $EMACS_MCP_DEBUG_LOG" >&2
		exit 1
	fi

	# Helper function for debug logging
	mcp_debug_log() {
		local direction="$1"
		local message="$2"
		local timestamp
		timestamp=$(date "+%Y-%m-%d %H:%M:%S")
		echo "[$timestamp] [$$] MCP-${direction}: ${message}" >>"$EMACS_MCP_DEBUG_LOG"
	}

	mcp_debug_log "INFO" "Debug logging enabled"

	# Log version/path so future failure reports can tell which copy of
	# anvil-stdio.sh was actually executed (opencode/zed MCP configs
	# sometimes point to a checkout other than the user's working copy).
	_anvil_script_path="$0"
	_anvil_script_dir="$(cd "$(dirname "$0")" 2>/dev/null && pwd || echo '?')"
	_anvil_git_sha="$(git -C "$_anvil_script_dir" rev-parse --short HEAD 2>/dev/null || echo 'no-git')"
	_anvil_mtime="$(stat -c %Y "$_anvil_script_path" 2>/dev/null || stat -f %m "$_anvil_script_path" 2>/dev/null || echo 'unknown')"
	mcp_debug_log "INFO" "anvil-stdio.sh path=$_anvil_script_path git=$_anvil_git_sha mtime=$_anvil_mtime"
	mcp_debug_log "INFO" "tooling bash=$(command -v bash || echo '?') sed=$(command -v sed || echo '?') tr=$(command -v tr || echo '?') base64=$(command -v base64 || echo '?') emacsclient=$(command -v emacsclient || echo '?')"
else
	# No-op function when debug logging is disabled
	mcp_debug_log() {
		:
	}
fi

# --- Retry wrapper for emacsclient ------------------------------------
# Absorbs the ~few-second window where `emacs --daemon' is being
# restarted: emacsclient then fails with "can't find socket" /
# "Connection refused" until the new daemon's server file is ready.
# Retrying silently keeps the MCP pipe alive so upstream Claude Code
# (or whoever is driving this bridge) doesn't see a hard failure for
# a routine daemon bounce.
#
# Configure with env vars (defaults chosen to cover a typical restart):
#   ANVIL_EMACSCLIENT_RETRY_MAX        attempts (default 60)
#   ANVIL_EMACSCLIENT_RETRY_DELAY_MS   delay per attempt in ms (default 100)
# 60 * 100ms = 6 seconds of tolerance.
ANVIL_EMACSCLIENT_RETRY_MAX=${ANVIL_EMACSCLIENT_RETRY_MAX:-60}
ANVIL_EMACSCLIENT_RETRY_DELAY_MS=${ANVIL_EMACSCLIENT_RETRY_DELAY_MS:-100}

# anvil_emacsclient_retry STDERR_FILE -- EMACSCLIENT_ARGS...
#
# Run `emacsclient EMACSCLIENT_ARGS...', retrying on transient socket-
# missing / connection-refused errors.  STDERR_FILE receives stderr of
# the final attempt.  Non-socket failures (e.g. elisp errors) surface
# immediately so genuine faults aren't masked.
# Prints emacsclient's stdout on success; exits with emacsclient's rc.
anvil_emacsclient_retry() {
	local stderr_file="$1"
	shift
	if [ "${1-}" = "--" ]; then shift; fi

	local attempt=0 out="" rc=0
	while :; do
		set +e
		# VAL-PATCH-TIMEOUT-V2: hard wall-clock cap on emacsclient.
		# Default 330s (daemon's `with-timeout' is 300s — we sit
		# slightly above so the daemon can return a richer error
		# first when possible).  Set ANVIL_EMACSCLIENT_TIMEOUT=0
		# to disable.  Prefer GNU timeout(1); fall back to perl
		# alarm() since perl is universally pre-installed.
		_anvil_tmo="${ANVIL_EMACSCLIENT_TIMEOUT:-330}"
		if [ "$_anvil_tmo" = "0" ]; then
			out=$(emacsclient "$@" 2>"$stderr_file")
		elif command -v timeout >/dev/null 2>&1; then
			out=$(timeout "$_anvil_tmo" emacsclient "$@" 2>"$stderr_file")
		elif command -v perl >/dev/null 2>&1; then
			out=$(perl -e 'alarm shift @ARGV; exec @ARGV' \
				"$_anvil_tmo" emacsclient "$@" 2>"$stderr_file")
		else
			out=$(emacsclient "$@" 2>"$stderr_file")
		fi
		rc=$?
		set -e
		if [ "$rc" -eq 0 ]; then
			printf '%s' "$out"
			return 0
		fi
		if [ -s "$stderr_file" ] \
			&& grep -qE "can't find socket|Connection refused|server.*not.*running|No such file or directory" "$stderr_file"; then
			attempt=$((attempt + 1))
			if [ "$attempt" -ge "$ANVIL_EMACSCLIENT_RETRY_MAX" ]; then
				mcp_debug_log "RETRY-EXHAUSTED" "attempts=$attempt max=$ANVIL_EMACSCLIENT_RETRY_MAX rc=$rc"
				printf '%s' "$out"
				return "$rc"
			fi
			if [ "$attempt" -eq 1 ] || [ $((attempt % 10)) -eq 0 ]; then
				mcp_debug_log "RETRY" "attempt=$attempt rc=$rc stderr=$(tr '\n' ' ' <"$stderr_file" | cut -c1-120)"
			fi
			if [ "$ANVIL_EMACSCLIENT_RETRY_DELAY_MS" -gt 0 ]; then
				local delay_sec
				delay_sec=$(awk -v ms="$ANVIL_EMACSCLIENT_RETRY_DELAY_MS" 'BEGIN{printf "%.3f", ms/1000}')
				sleep "$delay_sec"
			fi
			continue
		fi
		# Non-retriable failure — surface immediately.
		printf '%s' "$out"
		return "$rc"
	done
}

# Parse command line arguments
while [ $# -gt 0 ]; do
	case "$1" in
	--init-function=*)
		INIT_FUNCTION="${1#--init-function=}"
		shift
		;;
	--stop-function=*)
		STOP_FUNCTION="${1#--stop-function=}"
		shift
		;;
	--socket=*)
		SOCKET="${1#--socket=}"
		shift
		;;
	--server-id=*)
		SERVER_ID="${1#--server-id=}"
		shift
		;;
	*)
		echo "Unknown option: $1" >&2
		echo "Usage: $0 [--init-function=name] [--stop-function=name] [--socket=path] [--server-id=id]" >&2
		exit 1
		;;
	esac
done

# Set socket arguments if provided
if [ -n "$SOCKET" ]; then
	readonly SOCKET_OPTIONS=("-s" "$SOCKET")
	mcp_debug_log "INFO" "Using socket: $SOCKET"
else
	readonly SOCKET_OPTIONS=()
fi

# Log init function info if provided
if [ -n "$INIT_FUNCTION" ]; then
	mcp_debug_log "INFO" "Using init function: $INIT_FUNCTION"

	# Derive server-id from init function if not explicitly provided
	# This is a hack for backwards compatibility and will be removed later
	if [ -z "$SERVER_ID" ]; then
		# Extract server-id by removing -mcp-enable suffix
		SERVER_ID="${INIT_FUNCTION%-mcp-enable}"
		mcp_debug_log "INFO" "Derived server-id from init function: $SERVER_ID"
	fi
else
	mcp_debug_log "INFO" "No init function specified"
fi

# Log server-id
if [ -n "$SERVER_ID" ]; then
	mcp_debug_log "INFO" "Using server-id: $SERVER_ID"
else
	# Default to "default" if not specified
	SERVER_ID="default"
	mcp_debug_log "INFO" "Using default server-id: $SERVER_ID"
fi

# Initialize MCP if init function is provided
if [ -n "$INIT_FUNCTION" ]; then
	mcp_debug_log "INIT-CALL" "emacsclient ${SOCKET_OPTIONS[@]+"${SOCKET_OPTIONS[@]}"} -e ($INIT_FUNCTION) (with retry)"

	# Execute the command and capture output and return code
	init_stderr_file="/tmp/mcp-init-stderr.$$-$(date +%s%N)"
	mcp_debug_log "INIT-STDERR-FILE" "$init_stderr_file"
	set +e
	INIT_OUTPUT=$(anvil_emacsclient_retry "$init_stderr_file" -- \
		${SOCKET_OPTIONS[@]+"${SOCKET_OPTIONS[@]}"} \
		-e "($INIT_FUNCTION)")
	INIT_RC=$?
	set -e

	# Log results
	mcp_debug_log "INIT-RC" "$INIT_RC"
	mcp_debug_log "INIT-OUTPUT" "$INIT_OUTPUT"
	if [ -s "$init_stderr_file" ]; then
		mcp_debug_log "INIT-STDERR" "$(cat "$init_stderr_file")"
	fi
	rm -f "$init_stderr_file"
else
	mcp_debug_log "INFO" "Skipping init function call (none provided)"
fi

# --- T71: MCP Content-Length framing read helpers --------------------
# The standard MCP stdio transport frames messages as:
#
#     Content-Length: <N>\r\n
#     \r\n
#     <N bytes JSON body>
#
# Older callers may still emit line-delimited JSON.  We sniff the first
# byte of each request: if it is `{', treat as legacy line mode; if it
# is `C' (start of "Content-Length:"), treat as framed.  Mode is
# decided per-request to keep the legacy fallback transparent for
# dev/test invocations.
#
# Output: when input was framed, emit a framed response; otherwise emit
# legacy single-line JSON.

# anvil_mcp_read_framed_message
#
# Reads one MCP framed message from STDIN.  Headers are read line by
# line until an empty line; then exactly N bytes of body are read.
# Prints the JSON body on STDOUT (no trailing newline).  Returns 1 on
# EOF or malformed framing, 2 if no Content-Length header found.
anvil_mcp_read_framed_message() {
	local first_line="$1"
	local header_line content_length=""

	# Process the already-consumed first line.
	# Strip trailing CR (DOS line endings).
	first_line="${first_line%$'\r'}"
	if [[ "$first_line" =~ ^[Cc]ontent-[Ll]ength:[[:space:]]*([0-9]+)[[:space:]]*$ ]]; then
		content_length="${BASH_REMATCH[1]}"
	fi

	# Read remaining header lines until blank line.
	while IFS= read -r header_line; do
		header_line="${header_line%$'\r'}"
		if [ -z "$header_line" ]; then
			break
		fi
		if [[ "$header_line" =~ ^[Cc]ontent-[Ll]ength:[[:space:]]*([0-9]+)[[:space:]]*$ ]]; then
			content_length="${BASH_REMATCH[1]}"
		fi
	done

	if [ -z "$content_length" ]; then
		return 2
	fi

	# Read exactly content_length bytes of body.
	# `head -c N` is portable across GNU/BSD coreutils for byte count.
	local body
	body=$(head -c "$content_length")
	if [ -z "$body" ]; then
		return 1
	fi
	printf '%s' "$body"
	return 0
}

# anvil_mcp_emit_framed_response BODY
#
# Emits BODY framed with Content-Length.  N is computed in bytes
# (not characters) because the MCP spec mandates byte length.
anvil_mcp_emit_framed_response() {
	local body="$1"
	local n
	# `wc -c' counts bytes (LANG=C ensures no locale weirdness).
	n=$(LC_ALL=C printf '%s' "$body" | wc -c)
	# Strip leading whitespace from wc output (BSD pads).
	n="${n##* }"
	printf 'Content-Length: %s\r\n\r\n%s' "$n" "$body"
}

# Process input and print response
while IFS= read -r line; do
	# T71: detect framing.  An MCP framed request begins with
	# `Content-Length:' (case-insensitive); legacy line-delimited
	# requests begin with `{'.
	# Strip CR for cross-platform safety.
	_anvil_first_line="${line%$'\r'}"
	_anvil_framed=0
	if [[ "$_anvil_first_line" =~ ^[Cc]ontent-[Ll]ength: ]]; then
		_anvil_framed=1
		mcp_debug_log "FRAMING" "Content-Length detected"
		# Re-read full framed message; reuse the already-consumed line.
		line=$(anvil_mcp_read_framed_message "$_anvil_first_line") || {
			mcp_debug_log "FRAMING-ERROR" "rc=$? first=$_anvil_first_line"
			continue
		}
	fi

	# Log the incoming request
	mcp_debug_log "REQUEST" "$line"

	# Base64 encode the raw JSON to avoid emacsclient transport issues
	# with a specific combination of length, UTF-8 characters, and quoting
	# that occurs in Test 5 with the Lithuanian letter 'ą'
	base64_input=$(echo -n "$line" | base64)
	mcp_debug_log "BASE64-INPUT" "$base64_input"

	# Process JSON-RPC request and return the result with proper UTF-8 encoding
	# Encode the response to base64 to avoid any character encoding issues
	# Handle nil responses from notifications by converting to empty string
	elisp_expr="(base64-encode-string (encode-coding-string (or (anvil-server-process-jsonrpc (base64-decode-string \"$base64_input\") \"$SERVER_ID\") \"\") 'utf-8 t) t)"

	# Get response from emacsclient (with retry across daemon restarts).
	# Capture stderr for debugging and rc for logging only; existing code
	# downstream treats an empty `base64_response' as a soft failure.
	stderr_file="/tmp/mcp-stderr.$$-$(date +%s%N)"
	set +e
	base64_response=$(anvil_emacsclient_retry "$stderr_file" -- \
		${SOCKET_OPTIONS[@]+"${SOCKET_OPTIONS[@]}"} \
		-e "$elisp_expr")
	_anvil_client_rc=$?
	set -e
	mcp_debug_log "EMACSCLIENT-RC" "$_anvil_client_rc"

	# Check for stderr output
	if [ -s "$stderr_file" ]; then
		mcp_debug_log "EMACSCLIENT-STDERR" "$(cat "$stderr_file")"
	fi
	rm -f "$stderr_file"

	mcp_debug_log "BASE64-RESPONSE" "$base64_response"

	# Handle the base64 response - first strip quotes if present
	if [[ "$base64_response" == \"* && "$base64_response" == *\" ]]; then
		# Remove the surrounding quotes
		base64_response="${base64_response:1:${#base64_response}-2}"
		# Unescape any quotes inside
		base64_response="${base64_response//\\\"/\"}"
	fi

	# Repair Windows MSYS frame-boundary corruption.
	# emacsclient.c uses a read buffer of BUFSIZ+1 bytes; on MSYS / mingw
	# stdio.h, BUFSIZ is 512.  The Emacs server's `server-reply-print'
	# splits its output into frames of up to `server-msg-size' (1024 by
	# default), so on Windows every frame larger than ~512 bytes overruns
	# the client's read buffer.  When that happens, the tail of the frame
	# loses its `-print-nonl ' prefix and emacsclient prints it as
	#   *ERROR*: Unknown message: <tail>
	# interleaved with the legitimate base64 payload.  Strip those
	# injection markers with `sed s///g' (POSIX BRE, so `\*' is
	# unambiguously a literal asterisk on every sed implementation --
	# unlike `awk' where `\*' in ERE is treated differently by gawk /
	# mawk / busybox / git-bash-bundled awk and may cause the strip to
	# silently fail).  Then remove ALL CR/LF bytes; frame boundaries
	# leave CRLF behind, and `tr' is trivially portable.  `--ignore-
	# garbage' on the base64 decoder is NOT sufficient on its own: the
	# marker text "ERROR Unknown message" is 15 base64-alphabet bytes
	# that the decoder happily consumes as payload, throwing off the
	# multiple-of-4 requirement and yielding `invalid input' under
	# `set -e -o pipefail'.  Stripping the marker textually, before
	# decoding, is what makes Windows work at all.
	# (No-op on Linux/macOS where one frame fits in one read.)
	base64_response=$(printf '%s' "$base64_response" \
		| sed 's/\*ERROR\*: Unknown message: //g' \
		| tr -d '\r\n')

	# Diagnostic: confirm strip actually happened.  If markers survived,
	# base64 -d will almost certainly fail below, and we want the log to
	# say so out loud rather than just ending at BASE64-RESPONSE.
	_anvil_marker_survivors=$(printf '%s' "$base64_response" | grep -c '\*ERROR\*' || true)
	mcp_debug_log "INFO" "after-strip len=${#base64_response} markers=$_anvil_marker_survivors"

	# Decode the base64 content (lenient against stray non-base64 bytes).
	# Capture rc/stderr explicitly so that a decode failure is logged
	# instead of silently killing the script under `set -e -o pipefail'.
	_anvil_decode_err="/tmp/mcp-decode-err.$$-$(date +%s%N)"
	set +e
	formatted_response=$(printf '%s' "$base64_response" | base64 -d $_anvil_b64_flags 2>"$_anvil_decode_err")
	_anvil_decode_rc=$?
	set -e
	if [ "$_anvil_decode_rc" != 0 ]; then
		mcp_debug_log "DECODE-ERROR" "rc=$_anvil_decode_rc stderr=$(cat "$_anvil_decode_err" 2>/dev/null | tr '\n' ' ') input_head=${base64_response:0:160}"
	fi
	rm -f "$_anvil_decode_err"

	mcp_debug_log "RESPONSE" "$formatted_response"

	# Only output non-empty responses
	if [ -n "$formatted_response" ]; then
		if [ "$_anvil_framed" = "1" ]; then
			# T71: framed output for MCP-compliant clients.
			anvil_mcp_emit_framed_response "$formatted_response"
		else
			# Legacy line-delimited output (dev / test mode).
			echo "$formatted_response"
		fi
	else
		# VAL-PATCH-ALWAYS-REPLY: empty daemon output for a
		# request-with-id would otherwise hang the MCP client
		# forever.  Synthesise a JSON-RPC error so the client
		# can match the id and move on.  Notifications (no id)
		# stay silent as the protocol expects.
		_anvil_id_field=$(printf '%s' "$line" \
			| sed -nE 's/.*"id"[[:space:]]*:[[:space:]]*([0-9]+|"[^"]*"|null).*/\1/p' \
			| head -1)
		if [ -n "$_anvil_id_field" ] && [ "$_anvil_id_field" != "null" ]; then
			_anvil_synth=$(printf '{"jsonrpc":"2.0","id":%s,"error":{"code":-32603,"message":"Bridge synthetic error: daemon returned empty response (emacsclient rc=%s)"}}' "$_anvil_id_field" "${_anvil_client_rc:-?}")
			mcp_debug_log "SYNTH-ERROR" "id=$_anvil_id_field rc=${_anvil_client_rc:-?}"
			if [ "$_anvil_framed" = "1" ]; then
				anvil_mcp_emit_framed_response "$_anvil_synth"
			else
				echo "$_anvil_synth"
			fi
		fi
	fi
done

# Stop MCP if stop function is provided
if [ -n "$STOP_FUNCTION" ]; then
	mcp_debug_log "INFO" "Stopping MCP with function: $STOP_FUNCTION"
	mcp_debug_log "STOP-CALL" "emacsclient ${SOCKET_OPTIONS[@]+"${SOCKET_OPTIONS[@]}"} -e ($STOP_FUNCTION) (with retry)"

	# Execute the command and capture output and return code
	stop_stderr_file="/tmp/mcp-stop-stderr.$$-$(date +%s%N)"
	set +e
	STOP_OUTPUT=$(anvil_emacsclient_retry "$stop_stderr_file" -- \
		${SOCKET_OPTIONS[@]+"${SOCKET_OPTIONS[@]}"} \
		-e "($STOP_FUNCTION)")
	STOP_RC=$?
	set -e

	# Log results
	mcp_debug_log "STOP-RC" "$STOP_RC"
	mcp_debug_log "STOP-OUTPUT" "$STOP_OUTPUT"
	if [ -s "$stop_stderr_file" ]; then
		mcp_debug_log "STOP-STDERR" "$(cat "$stop_stderr_file")"
	fi
	rm -f "$stop_stderr_file"
else
	mcp_debug_log "INFO" "Skipping stop function call (none provided)"
fi
