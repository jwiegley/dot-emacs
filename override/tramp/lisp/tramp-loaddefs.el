;;; tramp-loaddefs.el --- automatically extracted autoloads
;;
;;; Code:


;;;### (autoloads nil "tramp" "tramp.el" (21868 7516 0 0))
;;; Generated autoloads from tramp.el

(defvar tramp-methods nil "\
Alist of methods for remote files.
This is a list of entries of the form (NAME PARAM1 PARAM2 ...).
Each NAME stands for a remote access method.  Each PARAM is a
pair of the form (KEY VALUE).  The following KEYs are defined:
  * `tramp-remote-shell'
    This specifies the shell to use on the remote host.  This
    MUST be a Bourne-like shell.  It is normally not necessary to
    set this to any value other than \"/bin/sh\": Tramp wants to
    use a shell which groks tilde expansion, but it can search
    for it.  Also note that \"/bin/sh\" exists on all Unixen,
    this might not be true for the value that you decide to use.
    You Have Been Warned.
  * `tramp-remote-shell-args'
    For implementation of `shell-command', this specifies the
    arguments to let `tramp-remote-shell' run a single command.
  * `tramp-login-program'
    This specifies the name of the program to use for logging in to the
    remote host.  This may be the name of rsh or a workalike program,
    or the name of telnet or a workalike, or the name of su or a workalike.
  * `tramp-login-args'
    This specifies the list of arguments to pass to the above
    mentioned program.  Please note that this is a list of list of arguments,
    that is, normally you don't want to put \"-a -b\" or \"-f foo\"
    here.  Instead, you want a list (\"-a\" \"-b\"), or (\"-f\" \"foo\").
    There are some patterns: \"%h\" in this list is replaced by the host
    name, \"%u\" is replaced by the user name, \"%p\" is replaced by the
    port number, and \"%%\" can be used to obtain a literal percent character.
    If a list containing \"%h\", \"%u\" or \"%p\" is unchanged during
    expansion (i.e. no host or no user specified), this list is not used as
    argument.  By this, arguments like (\"-l\" \"%u\") are optional.
    \"%t\" is replaced by the temporary file name produced with
    `tramp-make-tramp-temp-file'.  \"%k\" indicates the keep-date
    parameter of a program, if exists.  \"%c\" adds additional
    `tramp-ssh-controlmaster-options' options for the first hop.
  * `tramp-login-env'
     A list of environment variables and their values, which will
     be set when calling `tramp-login-program'.
  * `tramp-async-args'
    When an asynchronous process is started, we know already that
    the connection works.  Therefore, we can pass additional
    parameters to suppress diagnostic messages, in order not to
    tamper the process output.
  * `tramp-copy-program'
    This specifies the name of the program to use for remotely copying
    the file; this might be the absolute filename of scp or the name of
    a workalike program.  It is always applied on the local host.
  * `tramp-copy-args'
    This specifies the list of parameters to pass to the above mentioned
    program, the hints for `tramp-login-args' also apply here.
  * `tramp-copy-env'
     A list of environment variables and their values, which will
     be set when calling `tramp-copy-program'.
  * `tramp-remote-copy-program'
    The listener program to be applied on remote side, if needed.
  * `tramp-remote-copy-args'
    The list of parameters to pass to the listener program, the hints
    for `tramp-login-args' also apply here.  Additionally, \"%r\" could
    be used here and in `tramp-copy-args'.  It denotes a randomly
    chosen port for the remote listener.
  * `tramp-copy-keep-date'
    This specifies whether the copying program when the preserves the
    timestamp of the original file.
  * `tramp-copy-keep-tmpfile'
    This specifies whether a temporary local file shall be kept
    for optimization reasons (useful for \"rsync\" methods).
  * `tramp-copy-recursive'
    Whether the operation copies directories recursively.
  * `tramp-default-port'
    The default port of a method is needed in case of gateway connections.
    Additionally, it is used as indication which method is prepared for
    passing gateways.
  * `tramp-gw-args'
    As the attribute name says, additional arguments are specified here
    when a method is applied via a gateway.
  * `tramp-tmpdir'
    A directory on the remote host for temporary files.  If not
    specified, \"/tmp\" is taken as default.
  * `tramp-connection-timeout'
    This is the maximum time to be spent for establishing a connection.
    In general, the global default value shall be used, but for
    some methods, like \"su\" or \"sudo\", a shorter timeout
    might be desirable.

What does all this mean?  Well, you should specify `tramp-login-program'
for all methods; this program is used to log in to the remote site.  Then,
there are two ways to actually transfer the files between the local and the
remote side.  One way is using an additional scp-like program.  If you want
to do this, set `tramp-copy-program' in the method.

Another possibility for file transfer is inline transfer, i.e. the
file is passed through the same buffer used by `tramp-login-program'.  In
this case, the file contents need to be protected since the
`tramp-login-program' might use escape codes or the connection might not
be eight-bit clean.  Therefore, file contents are encoded for transit.
See the variables `tramp-local-coding-commands' and
`tramp-remote-coding-commands' for details.

So, to summarize: if the method is an out-of-band method, then you
must specify `tramp-copy-program' and `tramp-copy-args'.  If it is an
inline method, then these two parameters should be nil.  Methods which
are fit for gateways must have `tramp-default-port' at least.

Notes:

When using `su' or `sudo' the phrase \"open connection to a remote
host\" sounds strange, but it is used nevertheless, for consistency.
No connection is opened to a remote host, but `su' or `sudo' is
started on the local host.  You should specify a remote host
`localhost' or the name of the local host.  Another host name is
useful only in combination with `tramp-default-proxies-alist'.")

(defvar tramp-default-method-alist nil "\
Default method to use for specific host/user pairs.
This is an alist of items (HOST USER METHOD).  The first matching item
specifies the method to use for a file name which does not specify a
method.  HOST and USER are regular expressions or nil, which is
interpreted as a regular expression which always matches.  If no entry
matches, the variable `tramp-default-method' takes effect.

If the file name does not specify the user, lookup is done using the
empty string for the user name.

See `tramp-methods' for a list of possibilities for METHOD.")

(custom-autoload 'tramp-default-method-alist "tramp" t)

(defvar tramp-default-user-alist nil "\
Default user to use for specific method/host pairs.
This is an alist of items (METHOD HOST USER).  The first matching item
specifies the user to use for a file name which does not specify a
user.  METHOD and USER are regular expressions or nil, which is
interpreted as a regular expression which always matches.  If no entry
matches, the variable `tramp-default-user' takes effect.

If the file name does not specify the method, lookup is done using the
empty string for the method name.")

(custom-autoload 'tramp-default-user-alist "tramp" t)

(defvar tramp-default-host-alist nil "\
Default host to use for specific method/user pairs.
This is an alist of items (METHOD USER HOST).  The first matching item
specifies the host to use for a file name which does not specify a
host.  METHOD and HOST are regular expressions or nil, which is
interpreted as a regular expression which always matches.  If no entry
matches, the variable `tramp-default-host' takes effect.

If the file name does not specify the method, lookup is done using the
empty string for the method name.")

(custom-autoload 'tramp-default-host-alist "tramp" t)

(defconst tramp-local-host-regexp (concat "\\`" (regexp-opt (list "localhost" "localhost6" (system-name) "127.0.0.1" "::1") t) "\\'") "\
Host names which are regarded as local host.")

(defconst tramp-prefix-domain-format "%" "\
String matching delimiter between user and domain names.")

(defconst tramp-prefix-domain-regexp (regexp-quote tramp-prefix-domain-format) "\
Regexp matching delimiter between user and domain names.
Derived from `tramp-prefix-domain-format'.")

(defvar tramp-foreign-file-name-handler-alist nil "\
Alist of elements (FUNCTION . HANDLER) for foreign methods handled specially.
If (FUNCTION FILENAME) returns non-nil, then all I/O on that file is done by
calling HANDLER.")

(autoload 'tramp-tramp-file-p "tramp" "\
Return t if NAME is a string with Tramp file name syntax.

\(fn NAME)" nil nil)

(autoload 'tramp-set-completion-function "tramp" "\
Sets the list of completion functions for METHOD.
FUNCTION-LIST is a list of entries of the form (FUNCTION FILE).
The FUNCTION is intended to parse FILE according its syntax.
It might be a predefined FUNCTION, or a user defined FUNCTION.
For the list of predefined FUNCTIONs see `tramp-completion-function-alist'.

Example:

    (tramp-set-completion-function
     \"ssh\"
     '((tramp-parse-sconfig \"/etc/ssh_config\")
       (tramp-parse-sconfig \"~/.ssh/config\")))

\(fn METHOD FUNCTION-LIST)" nil nil)

(autoload 'tramp-completion-mode-p "tramp" "\
Check, whether method / user name / host name completion is active.

\(fn)" nil nil)

(autoload 'tramp-parse-rhosts "tramp" "\
Return a list of (user host) tuples allowed to access.
Either user or host may be nil.

\(fn FILENAME)" nil nil)

(autoload 'tramp-parse-shosts "tramp" "\
Return a list of (user host) tuples allowed to access.
User is always nil.

\(fn FILENAME)" nil nil)

(autoload 'tramp-parse-sconfig "tramp" "\
Return a list of (user host) tuples allowed to access.
User is always nil.

\(fn FILENAME)" nil nil)

(autoload 'tramp-parse-shostkeys "tramp" "\
Return a list of (user host) tuples allowed to access.
User is always nil.

\(fn DIRNAME)" nil nil)

(autoload 'tramp-parse-sknownhosts "tramp" "\
Return a list of (user host) tuples allowed to access.
User is always nil.

\(fn DIRNAME)" nil nil)

(autoload 'tramp-parse-hosts "tramp" "\
Return a list of (user host) tuples allowed to access.
User is always nil.

\(fn FILENAME)" nil nil)

(autoload 'tramp-parse-passwd "tramp" "\
Return a list of (user host) tuples allowed to access.
Host is always \"localhost\".

\(fn FILENAME)" nil nil)

(autoload 'tramp-parse-netrc "tramp" "\
Return a list of (user host) tuples allowed to access.
User may be nil.

\(fn FILENAME)" nil nil)

(autoload 'tramp-parse-putty "tramp" "\
Return a list of (user host) tuples allowed to access.
User is always nil.

\(fn REGISTRY-OR-DIRNAME)" nil nil)

(autoload 'tramp-mode-string-to-int "tramp" "\
Converts a ten-letter `drwxrwxrwx'-style mode string into mode bits.

\(fn MODE-STRING)" nil nil)

(autoload 'tramp-file-mode-from-int "tramp" "\
Turn an integer representing a file mode into an ls(1)-like string.

\(fn MODE)" nil nil)

(autoload 'tramp-get-local-uid "tramp" "\


\(fn ID-FORMAT)" nil nil)

(autoload 'tramp-get-local-gid "tramp" "\


\(fn ID-FORMAT)" nil nil)

(autoload 'tramp-check-cached-permissions "tramp" "\
Check `file-attributes' caches for VEC.
Return t if according to the cache access type ACCESS is known to
be granted.

\(fn VEC ACCESS)" nil nil)

(autoload 'tramp-local-host-p "tramp" "\
Return t if this points to the local host, nil otherwise.

\(fn VEC)" nil nil)

(autoload 'tramp-make-tramp-temp-file "tramp" "\
Create a temporary file on the remote host identified by VEC.
Return the local name of the temporary file.

\(fn VEC)" nil nil)

(autoload 'tramp-read-passwd "tramp" "\
Read a password from user (compat function).
Consults the auth-source package.
Invokes `password-read' if available, `read-passwd' else.

\(fn PROC &optional PROMPT)" nil nil)

(autoload 'tramp-clear-passwd "tramp" "\
Clear password cache for connection related to VEC.

\(fn VEC)" nil nil)

(autoload 'tramp-time-diff "tramp" "\
Return the difference between the two times, in seconds.
T1 and T2 are time values (as returned by `current-time' for example).

\(fn T1 T2)" nil nil)

(autoload 'tramp-shell-quote-argument "tramp" "\
Similar to `shell-quote-argument', but groks newlines.
Only works for Bourne-like shells.

\(fn S)" nil nil)

;;;***

;;;### (autoloads nil "tramp-adb" "tramp-adb.el" (21894 64139 0 0))
;;; Generated autoloads from tramp-adb.el

(defvar tramp-adb-program "adb" "\
Name of the Android Debug Bridge program.")

(custom-autoload 'tramp-adb-program "tramp-adb" t)

(defvar tramp-adb-connect-if-not-connected nil "\
Try to run `adb connect' if provided device is not connected currently.
It is used for TCP/IP devices.")

(custom-autoload 'tramp-adb-connect-if-not-connected "tramp-adb" t)

(defconst tramp-adb-method "adb" "\
*When this method name is used, forward all calls to Android Debug Bridge.")

(defvar tramp-adb-prompt "^\\(?:[[:digit:]]*|?\\)?\\(?:[[:alnum:]]*@[[:alnum:]]*[^#\\$]*\\)?[#\\$][[:space:]]" "\
Regexp used as prompt in almquist shell.")

(custom-autoload 'tramp-adb-prompt "tramp-adb" t)

(add-to-list 'tramp-methods `(,tramp-adb-method (tramp-tmpdir "/data/local/tmp") (tramp-default-port 5555)))

(add-to-list 'tramp-default-host-alist `(,tramp-adb-method nil ""))

(eval-after-load 'tramp '(tramp-set-completion-function tramp-adb-method '((tramp-adb-parse-device-names ""))))

(add-to-list 'tramp-foreign-file-name-handler-alist (cons 'tramp-adb-file-name-p 'tramp-adb-file-name-handler))

(defsubst tramp-adb-file-name-p (filename) "\
Check if it's a filename for ADB." (let ((v (tramp-dissect-file-name filename))) (string= (tramp-file-name-method v) tramp-adb-method)))

(autoload 'tramp-adb-file-name-handler "tramp-adb" "\
Invoke the ADB handler for OPERATION.
First arg specifies the OPERATION, second arg is a list of arguments to
pass to the OPERATION.

\(fn OPERATION &rest ARGS)" nil nil)

(autoload 'tramp-adb-parse-device-names "tramp-adb" "\
Return a list of (nil host) tuples allowed to access.

\(fn IGNORE)" nil nil)

;;;***

;;;### (autoloads nil "tramp-cache" "tramp-cache.el" (21796 63328
;;;;;;  0 0))
;;; Generated autoloads from tramp-cache.el

(defvar tramp-cache-data (make-hash-table :test 'equal) "\
Hash table for remote files properties.")

(defvar tramp-connection-properties nil "\
List of static connection properties.
Every entry has the form (REGEXP PROPERTY VALUE).  The regexp
matches remote file names.  It can be nil.  PROPERTY is a string,
and VALUE the corresponding value.  They are used, if there is no
matching entry for PROPERTY in `tramp-cache-data'.")

(custom-autoload 'tramp-connection-properties "tramp-cache" t)

(autoload 'tramp-get-file-property "tramp-cache" "\
Get the PROPERTY of FILE from the cache context of KEY.
Returns DEFAULT if not set.

\(fn KEY FILE PROPERTY DEFAULT)" nil nil)

(autoload 'tramp-set-file-property "tramp-cache" "\
Set the PROPERTY of FILE to VALUE, in the cache context of KEY.
Returns VALUE.

\(fn KEY FILE PROPERTY VALUE)" nil nil)

(autoload 'tramp-flush-file-property "tramp-cache" "\
Remove all properties of FILE in the cache context of KEY.

\(fn KEY FILE)" nil nil)

(autoload 'tramp-flush-directory-property "tramp-cache" "\
Remove all properties of DIRECTORY in the cache context of KEY.
Remove also properties of all files in subdirectories.

\(fn KEY DIRECTORY)" nil nil)

(autoload 'tramp-get-connection-property "tramp-cache" "\
Get the named PROPERTY for the connection.
KEY identifies the connection, it is either a process or a vector.
If the value is not set for the connection, returns DEFAULT.

\(fn KEY PROPERTY DEFAULT)" nil nil)

(autoload 'tramp-set-connection-property "tramp-cache" "\
Set the named PROPERTY of a connection to VALUE.
KEY identifies the connection, it is either a process or a vector.
PROPERTY is set persistent when KEY is a vector.

\(fn KEY PROPERTY VALUE)" nil nil)

(autoload 'tramp-connection-property-p "tramp-cache" "\
Check whether named PROPERTY of a connection is defined.
KEY identifies the connection, it is either a process or a vector.

\(fn KEY PROPERTY)" nil nil)

(autoload 'tramp-flush-connection-property "tramp-cache" "\
Remove all properties identified by KEY.
KEY identifies the connection, it is either a process or a vector.

\(fn KEY)" nil nil)

(autoload 'tramp-cache-print "tramp-cache" "\
Print hash table TABLE.

\(fn TABLE)" nil nil)

(autoload 'tramp-list-connections "tramp-cache" "\
Return a list of all known connection vectors according to `tramp-cache'.

\(fn)" nil nil)

(autoload 'tramp-parse-connection-properties "tramp-cache" "\
Return a list of (user host) tuples allowed to access for METHOD.
This function is added always in `tramp-get-completion-function'
for all methods.  Resulting data are derived from connection history.

\(fn METHOD)" nil nil)

;;;***

;;;### (autoloads nil "tramp-cmds" "tramp-cmds.el" (21852 17488 0
;;;;;;  0))
;;; Generated autoloads from tramp-cmds.el

(autoload 'tramp-cleanup-connection "tramp-cmds" "\
Flush all connection related objects.
This includes password cache, file cache, connection cache,
buffers.  KEEP-DEBUG non-nil preserves the debug buffer.
KEEP-PASSWORD non-nil preserves the password cache.
When called interactively, a Tramp connection has to be selected.

\(fn VEC &optional KEEP-DEBUG KEEP-PASSWORD)" t nil)

(autoload 'tramp-cleanup-this-connection "tramp-cmds" "\
Flush all connection related objects of the current buffer's connection.

\(fn)" t nil)

(autoload 'tramp-cleanup-all-connections "tramp-cmds" "\
Flush all Tramp internal objects.
This includes password cache, file cache, connection cache, buffers.

\(fn)" t nil)

(autoload 'tramp-cleanup-all-buffers "tramp-cmds" "\
Kill all remote buffers.

\(fn)" t nil)

(autoload 'tramp-version "tramp-cmds" "\
Print version number of tramp.el in minibuffer or current buffer.

\(fn ARG)" t nil)

(autoload 'tramp-bug "tramp-cmds" "\
Submit a bug report to the Tramp developers.

\(fn)" t nil)

;;;***

;;;### (autoloads nil "tramp-efs" "tramp-efs.el" (21670 25948 0 0))
;;; Generated autoloads from tramp-efs.el

(defconst tramp-efs-method "ftp" "\
Name of the method invoking EFS.")

(when (featurep 'xemacs) (add-to-list 'tramp-methods (cons tramp-efs-method nil)) (add-to-list 'tramp-default-method-alist (list "\\`ftp\\." nil tramp-efs-method)) (add-to-list 'tramp-default-method-alist (list nil "\\`\\(anonymous\\|ftp\\)\\'" tramp-efs-method)))

(eval-after-load 'tramp '(tramp-set-completion-function tramp-efs-method '((tramp-parse-netrc "~/.netrc"))))

(autoload 'tramp-efs-file-name-handler "tramp-efs" "\
Invoke the EFS handler for OPERATION.
First arg specifies the OPERATION, second args is a list of arguments to
pass to the OPERATION.

\(fn OPERATION &rest ARGS)" nil nil)

(defsubst tramp-efs-file-name-p (filename) "\
Check if it's a filename that should be forwarded to EFS." (when (string-match (nth 0 tramp-file-name-structure) filename) (string= (tramp-file-name-method (tramp-dissect-file-name filename)) tramp-efs-method)))

(when (featurep 'xemacs) (add-to-list 'tramp-foreign-file-name-handler-alist (cons 'tramp-efs-file-name-p 'tramp-efs-file-name-handler)))

;;;***

;;;### (autoloads nil "tramp-ftp" "tramp-ftp.el" (21670 25419 0 0))
;;; Generated autoloads from tramp-ftp.el

(defconst tramp-ftp-method "ftp" "\
When this method name is used, forward all calls to Ange-FTP.")

(unless (featurep 'xemacs) (add-to-list 'tramp-methods (cons tramp-ftp-method nil)) (add-to-list 'tramp-default-method-alist (list "\\`ftp\\." nil tramp-ftp-method)) (add-to-list 'tramp-default-method-alist (list nil "\\`\\(anonymous\\|ftp\\)\\'" tramp-ftp-method)))

(eval-after-load 'tramp '(tramp-set-completion-function tramp-ftp-method '((tramp-parse-netrc "~/.netrc"))))

(autoload 'tramp-ftp-file-name-handler "tramp-ftp" "\
Invoke the Ange-FTP handler for OPERATION.
First arg specifies the OPERATION, second arg is a list of arguments to
pass to the OPERATION.

\(fn OPERATION &rest ARGS)" nil nil)

(defsubst tramp-ftp-file-name-p (filename) "\
Check if it's a filename that should be forwarded to Ange-FTP." (string= (tramp-file-name-method (tramp-dissect-file-name filename)) tramp-ftp-method))

(unless (featurep 'xemacs) (add-to-list 'tramp-foreign-file-name-handler-alist (cons 'tramp-ftp-file-name-p 'tramp-ftp-file-name-handler)))

;;;***

;;;### (autoloads nil "tramp-gvfs" "tramp-gvfs.el" (21854 59166 0
;;;;;;  0))
;;; Generated autoloads from tramp-gvfs.el

(defvar tramp-gvfs-methods '("dav" "davs" "obex" "sftp" "synce") "\
List of methods for remote files, accessed with GVFS.")

(custom-autoload 'tramp-gvfs-methods "tramp-gvfs" t)

(add-to-list 'tramp-default-user-alist '("\\`synce\\'" nil nil))

(defvar tramp-gvfs-zeroconf-domain "local" "\
Zeroconf domain to be used for discovering services, like host names.")

(custom-autoload 'tramp-gvfs-zeroconf-domain "tramp-gvfs" t)

(when (featurep 'dbusbind) (dolist (elt tramp-gvfs-methods) (unless (assoc elt tramp-methods) (add-to-list 'tramp-methods (cons elt nil)))))

(defvar tramp-bluez-discover-devices-timeout 60 "\
Defines seconds since last bluetooth device discovery before rescanning.
A value of 0 would require an immediate discovery during hostname
completion, nil means to use always cached values for discovered
devices.")

(custom-autoload 'tramp-bluez-discover-devices-timeout "tramp-gvfs" t)

(defsubst tramp-gvfs-file-name-p (filename) "\
Check if it's a filename handled by the GVFS daemon." (and (tramp-tramp-file-p filename) (let ((method (tramp-file-name-method (tramp-dissect-file-name filename)))) (and (stringp method) (member method tramp-gvfs-methods)))))

(autoload 'tramp-gvfs-file-name-handler "tramp-gvfs" "\
Invoke the GVFS related OPERATION.
First arg specifies the OPERATION, second arg is a list of arguments to
pass to the OPERATION.

\(fn OPERATION &rest ARGS)" nil nil)

(when (featurep 'dbusbind) (add-to-list 'tramp-foreign-file-name-handler-alist (cons 'tramp-gvfs-file-name-p 'tramp-gvfs-file-name-handler)))

;;;***

;;;### (autoloads nil "tramp-gw" "tramp-gw.el" (21670 25416 0 0))
;;; Generated autoloads from tramp-gw.el

(defconst tramp-gw-tunnel-method "tunnel" "\
Method to connect HTTP gateways.")

(defconst tramp-gw-socks-method "socks" "\
Method to connect SOCKS servers.")

(add-to-list 'tramp-default-user-alist (list (concat "\\`" (regexp-opt (list tramp-gw-tunnel-method tramp-gw-socks-method)) "\\'") nil (user-login-name)))

(autoload 'tramp-gw-open-connection "tramp-gw" "\
Open a remote connection to VEC (see `tramp-file-name' structure).
Take GW-VEC as SOCKS or HTTP gateway, i.e. its method must be a
gateway method.  TARGET-VEC identifies where to connect to via
the gateway, it can be different from VEC when there are more
hops to be applied.

It returns a string like \"localhost#port\", which must be used
instead of the host name declared in TARGET-VEC.

\(fn VEC GW-VEC TARGET-VEC)" nil nil)

;;;***

;;;### (autoloads nil "tramp-sh" "tramp-sh.el" (21868 4572 0 0))
;;; Generated autoloads from tramp-sh.el

(defvar tramp-inline-compress-start-size 4096 "\
The minimum size of compressing where inline transfer.
When inline transfer, compress transferred data of file
whose size is this value or above (up to `tramp-copy-size-limit').
If it is nil, no compression at all will be applied.")

(custom-autoload 'tramp-inline-compress-start-size "tramp-sh" t)

(defvar tramp-copy-size-limit 10240 "\
The maximum file size where inline copying is preferred over an out-of-the-band copy.
If it is nil, out-of-the-band copy will be used without a check.")

(custom-autoload 'tramp-copy-size-limit "tramp-sh" t)

(defvar tramp-terminal-type "dumb" "\
Value of TERM environment variable for logging in to remote host.
Because Tramp wants to parse the output of the remote shell, it is easily
confused by ANSI color escape sequences and suchlike.  Often, shell init
files conditionalize this setup based on the TERM environment variable.")

(custom-autoload 'tramp-terminal-type "tramp-sh" t)

(defvar tramp-histfile-override ".tramp_history" "\
When invoking a shell, override the HISTFILE with this value.
When setting to a string, it redirects the shell history to that
file.  Be careful when setting to \"/dev/null\"; this might
result in undesired results when using \"bash\" as shell.

The value t, the default value, unsets any setting of HISTFILE,
and sets both HISTFILESIZE and HISTSIZE to 0.  If you set this
variable to nil, however, the *override* is disabled, so the
history will go to the default storage location,
e.g. \"$HOME/.sh_history\".")

(custom-autoload 'tramp-histfile-override "tramp-sh" t)

(defconst tramp-color-escape-sequence-regexp "[[;0-9]+m" "\
Escape sequences produced by the \"ls\" command.")

(defconst tramp-initial-end-of-output "#$ " "\
Prompt when establishing a connection.")

(defvar tramp-use-ssh-controlmaster-options t "\
Whether to use `tramp-ssh-controlmaster-options'.")

(custom-autoload 'tramp-use-ssh-controlmaster-options "tramp-sh" t)

(add-to-list 'tramp-methods '("rcp" (tramp-login-program "rsh") (tramp-login-args (("%h") ("-l" "%u"))) (tramp-remote-shell "/bin/sh") (tramp-remote-shell-args ("-c")) (tramp-copy-program "rcp") (tramp-copy-args (("-p" "%k") ("-r"))) (tramp-copy-keep-date t) (tramp-copy-recursive t)))

(add-to-list 'tramp-methods '("remcp" (tramp-login-program "remsh") (tramp-login-args (("%h") ("-l" "%u"))) (tramp-remote-shell "/bin/sh") (tramp-remote-shell-args ("-c")) (tramp-copy-program "rcp") (tramp-copy-args (("-p" "%k"))) (tramp-copy-keep-date t)))

(add-to-list 'tramp-methods '("scp" (tramp-login-program "ssh") (tramp-login-args (("-l" "%u") ("-p" "%p") ("%c") ("-e" "none") ("%h"))) (tramp-async-args (("-q"))) (tramp-remote-shell "/bin/sh") (tramp-remote-shell-args ("-c")) (tramp-copy-program "scp") (tramp-copy-args (("-P" "%p") ("-p" "%k") ("-q") ("-r") ("%c"))) (tramp-copy-keep-date t) (tramp-copy-recursive t) (tramp-gw-args (("-o" "GlobalKnownHostsFile=/dev/null") ("-o" "UserKnownHostsFile=/dev/null") ("-o" "StrictHostKeyChecking=no"))) (tramp-default-port 22)))

(add-to-list 'tramp-methods '("scpx" (tramp-login-program "ssh") (tramp-login-args (("-l" "%u") ("-p" "%p") ("%c") ("-e" "none") ("-t" "-t") ("%h") ("/bin/sh"))) (tramp-async-args (("-q"))) (tramp-remote-shell "/bin/sh") (tramp-remote-shell-args ("-c")) (tramp-copy-program "scp") (tramp-copy-args (("-P" "%p") ("-p" "%k") ("-q") ("-r") ("%c"))) (tramp-copy-keep-date t) (tramp-copy-recursive t) (tramp-gw-args (("-o" "GlobalKnownHostsFile=/dev/null") ("-o" "UserKnownHostsFile=/dev/null") ("-o" "StrictHostKeyChecking=no"))) (tramp-default-port 22)))

(add-to-list 'tramp-methods '("rsync" (tramp-login-program "ssh") (tramp-login-args (("-l" "%u") ("-p" "%p") ("%c") ("-e" "none") ("%h"))) (tramp-async-args (("-q"))) (tramp-remote-shell "/bin/sh") (tramp-remote-shell-args ("-c")) (tramp-copy-program "rsync") (tramp-copy-args (("-t" "%k") ("-r"))) (tramp-copy-env (("RSYNC_RSH") ("ssh" "%c"))) (tramp-copy-keep-date t) (tramp-copy-keep-tmpfile t) (tramp-copy-recursive t)))

(add-to-list 'tramp-methods '("rsh" (tramp-login-program "rsh") (tramp-login-args (("%h") ("-l" "%u"))) (tramp-remote-shell "/bin/sh") (tramp-remote-shell-args ("-c"))))

(add-to-list 'tramp-methods '("remsh" (tramp-login-program "remsh") (tramp-login-args (("%h") ("-l" "%u"))) (tramp-remote-shell "/bin/sh") (tramp-remote-shell-args ("-c"))))

(add-to-list 'tramp-methods '("ssh" (tramp-login-program "ssh") (tramp-login-args (("-l" "%u") ("-p" "%p") ("%c") ("-e" "none") ("%h"))) (tramp-async-args (("-q"))) (tramp-remote-shell "/bin/sh") (tramp-remote-shell-args ("-c")) (tramp-gw-args (("-o" "GlobalKnownHostsFile=/dev/null") ("-o" "UserKnownHostsFile=/dev/null") ("-o" "StrictHostKeyChecking=no"))) (tramp-default-port 22)))

(add-to-list 'tramp-methods '("sshx" (tramp-login-program "ssh") (tramp-login-args (("-l" "%u") ("-p" "%p") ("%c") ("-e" "none") ("-t" "-t") ("%h") ("/bin/sh"))) (tramp-async-args (("-q"))) (tramp-remote-shell "/bin/sh") (tramp-remote-shell-args ("-c")) (tramp-gw-args (("-o" "GlobalKnownHostsFile=/dev/null") ("-o" "UserKnownHostsFile=/dev/null") ("-o" "StrictHostKeyChecking=no"))) (tramp-default-port 22)))

(add-to-list 'tramp-methods '("telnet" (tramp-login-program "telnet") (tramp-login-args (("%h") ("%p") ("2>/dev/null"))) (tramp-remote-shell "/bin/sh") (tramp-remote-shell-args ("-c")) (tramp-default-port 23)))

(add-to-list 'tramp-methods '("nc" (tramp-login-program "telnet") (tramp-login-args (("%h") ("%p") ("2>/dev/null"))) (tramp-remote-shell "/bin/sh") (tramp-remote-shell-args ("-c")) (tramp-copy-program "nc") (tramp-copy-args (("-w" "1") ("-v") ("%h") ("%r"))) (tramp-remote-copy-program "nc") (tramp-remote-copy-args (("-l") ("-p" "%r"))) (tramp-default-port 23)))

(add-to-list 'tramp-methods '("su" (tramp-login-program "su") (tramp-login-args (("-") ("%u"))) (tramp-remote-shell "/bin/sh") (tramp-remote-shell-args ("-c")) (tramp-connection-timeout 10)))

(add-to-list 'tramp-methods '("sudo" (tramp-login-program "sudo") (tramp-login-args (("-u" "%u") ("-s") ("-H") ("-p" "Password:"))) (tramp-login-env (("SHELL") ("/bin/sh"))) (tramp-remote-shell "/bin/sh") (tramp-remote-shell-args ("-c")) (tramp-connection-timeout 10)))

(add-to-list 'tramp-methods '("ksu" (tramp-login-program "ksu") (tramp-login-args (("%u") ("-q"))) (tramp-remote-shell "/bin/sh") (tramp-remote-shell-args ("-c")) (tramp-connection-timeout 10)))

(add-to-list 'tramp-methods '("krlogin" (tramp-login-program "krlogin") (tramp-login-args (("%h") ("-l" "%u") ("-x"))) (tramp-remote-shell "/bin/sh") (tramp-remote-shell-args ("-c"))))

(add-to-list 'tramp-methods `("plink" (tramp-login-program "plink") (tramp-login-args (("-l" "%u") ("-P" "%p") ("-ssh") ("-t") ("%h") ("\"") (,(format "env 'TERM=%s' 'PROMPT_COMMAND=' 'PS1=%s'" tramp-terminal-type tramp-initial-end-of-output)) ("/bin/sh") ("\""))) (tramp-remote-shell "/bin/sh") (tramp-remote-shell-args ("-c")) (tramp-default-port 22)))

(add-to-list 'tramp-methods `("plinkx" (tramp-login-program "plink") (tramp-login-args (("-load") ("%h") ("-t") ("\"") (,(format "env 'TERM=%s' 'PROMPT_COMMAND=' 'PS1=%s'" tramp-terminal-type tramp-initial-end-of-output)) ("/bin/sh") ("\""))) (tramp-remote-shell "/bin/sh") (tramp-remote-shell-args ("-c"))))

(add-to-list 'tramp-methods `("pscp" (tramp-login-program "plink") (tramp-login-args (("-l" "%u") ("-P" "%p") ("-ssh") ("-t") ("%h") ("\"") (,(format "env 'TERM=%s' 'PROMPT_COMMAND=' 'PS1=%s'" tramp-terminal-type tramp-initial-end-of-output)) ("/bin/sh") ("\""))) (tramp-remote-shell "/bin/sh") (tramp-remote-shell-args ("-c")) (tramp-copy-program "pscp") (tramp-copy-args (("-l" "%u") ("-P" "%p") ("-scp") ("-p" "%k") ("-q") ("-r"))) (tramp-copy-keep-date t) (tramp-copy-recursive t) (tramp-default-port 22)))

(add-to-list 'tramp-methods `("psftp" (tramp-login-program "plink") (tramp-login-args (("-l" "%u") ("-P" "%p") ("-ssh") ("-t") ("%h") ("\"") (,(format "env 'TERM=%s' 'PROMPT_COMMAND=' 'PS1=%s'" tramp-terminal-type tramp-initial-end-of-output)) ("/bin/sh") ("\""))) (tramp-remote-shell "/bin/sh") (tramp-remote-shell-args ("-c")) (tramp-copy-program "pscp") (tramp-copy-args (("-l" "%u") ("-P" "%p") ("-sftp") ("-p" "%k") ("-q") ("-r"))) (tramp-copy-keep-date t) (tramp-copy-recursive t)))

(add-to-list 'tramp-methods '("fcp" (tramp-login-program "fsh") (tramp-login-args (("%h") ("-l" "%u") ("sh" "-i"))) (tramp-remote-shell "/bin/sh") (tramp-remote-shell-args ("-i") ("-c")) (tramp-copy-program "fcp") (tramp-copy-args (("-p" "%k"))) (tramp-copy-keep-date t)))

(add-to-list 'tramp-default-method-alist `(,tramp-local-host-regexp "\\`root\\'" "su"))

(add-to-list 'tramp-default-user-alist `(,(concat "\\`" (regexp-opt '("su" "sudo" "ksu")) "\\'") nil "root"))

(add-to-list 'tramp-default-user-alist `(,(concat "\\`" (regexp-opt '("rcp" "remcp" "rsh" "telnet" "nc" "krlogin" "fcp")) "\\'") nil ,(user-login-name)))

(defconst tramp-completion-function-alist-rsh '((tramp-parse-rhosts "/etc/hosts.equiv") (tramp-parse-rhosts "~/.rhosts")) "\
Default list of (FUNCTION FILE) pairs to be examined for rsh methods.")

(defconst tramp-completion-function-alist-ssh '((tramp-parse-rhosts "/etc/hosts.equiv") (tramp-parse-rhosts "/etc/shosts.equiv") (tramp-parse-shosts "/etc/ssh_known_hosts") (tramp-parse-sconfig "/etc/ssh_config") (tramp-parse-shostkeys "/etc/ssh2/hostkeys") (tramp-parse-sknownhosts "/etc/ssh2/knownhosts") (tramp-parse-rhosts "~/.rhosts") (tramp-parse-rhosts "~/.shosts") (tramp-parse-shosts "~/.ssh/known_hosts") (tramp-parse-sconfig "~/.ssh/config") (tramp-parse-shostkeys "~/.ssh2/hostkeys") (tramp-parse-sknownhosts "~/.ssh2/knownhosts")) "\
Default list of (FUNCTION FILE) pairs to be examined for ssh methods.")

(defconst tramp-completion-function-alist-telnet '((tramp-parse-hosts "/etc/hosts")) "\
Default list of (FUNCTION FILE) pairs to be examined for telnet methods.")

(defconst tramp-completion-function-alist-su '((tramp-parse-passwd "/etc/passwd")) "\
Default list of (FUNCTION FILE) pairs to be examined for su methods.")

(defconst tramp-completion-function-alist-putty `((tramp-parse-putty ,(if (memq system-type '(windows-nt)) "HKEY_CURRENT_USER\\Software\\SimonTatham\\PuTTY\\Sessions" "~/.putty/sessions"))) "\
Default list of (FUNCTION REGISTRY) pairs to be examined for putty sessions.")

(eval-after-load 'tramp '(progn (tramp-set-completion-function "rcp" tramp-completion-function-alist-rsh) (tramp-set-completion-function "remcp" tramp-completion-function-alist-rsh) (tramp-set-completion-function "scp" tramp-completion-function-alist-ssh) (tramp-set-completion-function "scpx" tramp-completion-function-alist-ssh) (tramp-set-completion-function "rsync" tramp-completion-function-alist-ssh) (tramp-set-completion-function "rsh" tramp-completion-function-alist-rsh) (tramp-set-completion-function "remsh" tramp-completion-function-alist-rsh) (tramp-set-completion-function "ssh" tramp-completion-function-alist-ssh) (tramp-set-completion-function "sshx" tramp-completion-function-alist-ssh) (tramp-set-completion-function "telnet" tramp-completion-function-alist-telnet) (tramp-set-completion-function "nc" tramp-completion-function-alist-telnet) (tramp-set-completion-function "su" tramp-completion-function-alist-su) (tramp-set-completion-function "sudo" tramp-completion-function-alist-su) (tramp-set-completion-function "ksu" tramp-completion-function-alist-su) (tramp-set-completion-function "krlogin" tramp-completion-function-alist-rsh) (tramp-set-completion-function "plink" tramp-completion-function-alist-ssh) (tramp-set-completion-function "plinkx" tramp-completion-function-alist-putty) (tramp-set-completion-function "pscp" tramp-completion-function-alist-ssh) (tramp-set-completion-function "psftp" tramp-completion-function-alist-ssh) (tramp-set-completion-function "fcp" tramp-completion-function-alist-ssh)))

(defvar tramp-remote-path '(tramp-default-remote-path "/bin" "/usr/bin" "/sbin" "/usr/sbin" "/usr/local/bin" "/usr/local/sbin" "/local/bin" "/local/freeware/bin" "/local/gnu/bin" "/usr/freeware/bin" "/usr/pkg/bin" "/usr/contrib/bin" "/opt/bin" "/opt/sbin" "/opt/local/bin") "\
List of directories to search for executables on remote host.
For every remote host, this variable will be set buffer local,
keeping the list of existing directories on that host.

You can use `~' in this list, but when searching for a shell which groks
tilde expansion, all directory names starting with `~' will be ignored.

`Default Directories' represent the list of directories given by
the command \"getconf PATH\".  It is recommended to use this
entry on top of this list, because these are the default
directories for POSIX compatible commands.  On remote hosts which
do not offer the getconf command (like cygwin), the value
\"/bin:/usr/bin\" is used instead of.

`Private Directories' are the settings of the $PATH environment,
as given in your `~/.profile'.")

(custom-autoload 'tramp-remote-path "tramp-sh" t)

(defvar tramp-remote-process-environment `("TMOUT=0" "LC_CTYPE=''" ,(format "TERM=%s" tramp-terminal-type) ,(format "INSIDE_EMACS='%s,tramp:%s'" emacs-version tramp-version) "CDPATH=" "HISTORY=" "MAIL=" "MAILCHECK=" "MAILPATH=" "PAGER=cat" "autocorrect=" "correct=") "\
List of environment variables to be set on the remote host.

Each element should be a string of the form ENVVARNAME=VALUE.  An
entry ENVVARNAME= disables the corresponding environment variable,
which might have been set in the init files like ~/.profile.

Special handling is applied to the PATH environment, which should
not be set here. Instead, it should be set via `tramp-remote-path'.")

(custom-autoload 'tramp-remote-process-environment "tramp-sh" t)

(defvar tramp-sh-extra-args '(("/bash\\'" . "-norc -noprofile")) "\
Alist specifying extra arguments to pass to the remote shell.
Entries are (REGEXP . ARGS) where REGEXP is a regular expression
matching the shell file name and ARGS is a string specifying the
arguments.

This variable is only used when Tramp needs to start up another shell
for tilde expansion.  The extra arguments should typically prevent the
shell from reading its init file.")

(custom-autoload 'tramp-sh-extra-args "tramp-sh" t)

(add-to-list 'tramp-foreign-file-name-handler-alist '(identity . tramp-sh-file-name-handler) 'append)

(autoload 'tramp-sh-file-name-handler "tramp-sh" "\
Invoke remote-shell Tramp file name handler.
Fall back to normal file name handler if no Tramp handler exists.

\(fn OPERATION &rest ARGS)" nil nil)

;;;***

;;;### (autoloads nil "tramp-smb" "tramp-smb.el" (21854 59226 0 0))
;;; Generated autoloads from tramp-smb.el

(defconst tramp-smb-method "smb" "\
Method to connect SAMBA and M$ SMB servers.")

(unless (memq system-type '(cygwin windows-nt)) (add-to-list 'tramp-methods `(,tramp-smb-method (tramp-remote-shell "") (tramp-tmpdir "/C$/Temp"))))

(add-to-list 'tramp-default-method-alist `(nil ,tramp-prefix-domain-regexp ,tramp-smb-method))

(add-to-list 'tramp-default-user-alist `(,(concat "\\`" tramp-smb-method "\\'") nil nil))

(eval-after-load 'tramp '(tramp-set-completion-function tramp-smb-method '((tramp-parse-netrc "~/.netrc"))))

(defvar tramp-smb-program "smbclient" "\
Name of SMB client to run.")

(custom-autoload 'tramp-smb-program "tramp-smb" t)

(defvar tramp-smb-acl-program "smbcacls" "\
Name of SMB acls to run.")

(custom-autoload 'tramp-smb-acl-program "tramp-smb" t)

(defvar tramp-smb-conf "/dev/null" "\
Path of the smb.conf file.
If it is nil, no smb.conf will be added to the `tramp-smb-program'
call, letting the SMB client use the default one.")

(custom-autoload 'tramp-smb-conf "tramp-smb" t)

(defvar tramp-smb-winexe-program "winexe" "\
Name of winexe client to run.
If it isn't found in the local $PATH, the absolute path of winexe
shall be given.  This is needed for remote processes.")

(custom-autoload 'tramp-smb-winexe-program "tramp-smb" t)

(defvar tramp-smb-winexe-shell-command "powershell.exe" "\
Shell to be used for processes on remote machines.
This must be Powershell V2 compatible.")

(custom-autoload 'tramp-smb-winexe-shell-command "tramp-smb" t)

(defvar tramp-smb-winexe-shell-command-switch "-file -" "\
Command switch used together with `tramp-smb-winexe-shell-command'.
This can be used to disable echo etc.")

(custom-autoload 'tramp-smb-winexe-shell-command-switch "tramp-smb" t)

(defsubst tramp-smb-file-name-p (filename) "\
Check if it's a filename for SMB servers." (string= (tramp-file-name-method (tramp-dissect-file-name filename)) tramp-smb-method))

(autoload 'tramp-smb-file-name-handler "tramp-smb" "\
Invoke the SMB related OPERATION.
First arg specifies the OPERATION, second arg is a list of arguments to
pass to the OPERATION.

\(fn OPERATION &rest ARGS)" nil nil)

(unless (memq system-type '(cygwin windows-nt)) (add-to-list 'tramp-foreign-file-name-handler-alist (cons 'tramp-smb-file-name-p 'tramp-smb-file-name-handler)))

;;;***

;;;### (autoloads nil "tramp-uu" "tramp-uu.el" (21670 25411 0 0))
;;; Generated autoloads from tramp-uu.el

(autoload 'tramp-uuencode-region "tramp-uu" "\
UU-encode the region between BEG and END.

\(fn BEG END)" nil nil)

;;;***

;;;### (autoloads nil "trampver" "trampver.el" (21984 394 0 0))
;;; Generated autoloads from trampver.el

(defconst tramp-version "2.2.12" "\
This version of Tramp.")

(defconst tramp-bug-report-address "tramp-devel@gnu.org" "\
Email address to send bug reports to.")

;;;***

;;;### (autoloads nil nil ("tramp-compat.el") (21984 394 695807 0))

;;;***

(provide 'tramp-loaddefs)
;; Local Variables:
;; version-control: never
;; no-byte-compile: t
;; no-update-autoloads: t
;; coding: utf-8
;; End:
;;; tramp-loaddefs.el ends here
