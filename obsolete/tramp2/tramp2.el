;;; tramp2.el --- Network file access via login shell

;; Copyright (C) 2001 Free Software Foundation, Inc.

;;; Commentary:

;; Based on the TRAMP code by Kai Groﬂjohann, et al.

;;; Code:

(require 'cl)				
(require 'timer)
(require 'shell)

(require 'tramp2-compat)

;; Byte compiler pacifiers.
(eval-when-compile
  (defvar tramp2-state	nil)
  (defvar tramp2-perl	nil)
  (defvar tramp2-ls	nil)
  (defvar tramp2-dd	nil)
  (defvar tramp2-read	nil)
  (defvar tramp2-write	nil)
)


(defconst tramp2-version "$Id: tramp2.el,v 1.1 2001/12/06 12:18:48 kaig Exp $"
  "The CVS version number of this tramp2 release.")


;; Error thrown when a file is invalid.
(define-error 'tramp2-file-error
  "Error thrown when a tramp2 specific error occurs.
Inheritance ensures that anything expecting generic file errors will be happy."
  'file-error)


(defvar tramp2-load-hooks nil
  "*Hooks run when the tramp2 file interface is loaded.")

(defvar tramp2-temp-dir nil
  "If not nil, a directory in which to store tramp2 temporary files.
By default, the value of TMPDIR or TMP is used, or \"/tmp\".")

(defvar tramp2-temp-name-prefix nil
  "If not nil, a unique prefix string to identify tramp2 files.")


(defconst tramp2-path-tag "/!/"
  "Regular expression matching a TRAMP2 path tag.
If you redefine this, be aware that you *need* the second `/' in
the value before any `:' is present.

Since `:' is an integral part of the tramp2 connect syntax, this
requires that the path tag contain a `/'.

Other possible values here are: \"/tramp/\" or \"/!t/\".")


;; Internal.
(defconst tramp2-path-connect (concat ;; match a protocol statement
			              ;; 1     2      2        3            3   1
				      "\\(\\[\\([^]]+\\)\\]\\|\\([a-zA-Z]+\\)|\\)?"
				      ;; match a user statement
				      ;; 4  5                5   4
				      "\\(\\([-_a-zA-Z0-9]+\\)@\\)?"
				      ;; match a host
				      ;; 6               6
				      "\\([-a-zA-Z0-9]+\\)?"
				      ":")
  "Regular expression matching a single complete connect expression.
This does not (and can't cleanly) represent all the rules for a /valid/
connect expression, but it simplifies the first-stage approximation well.")

(defvar tramp2-shell-prompt-pattern (list
				     (cons 'default shell-prompt-pattern))
  "A set of regular expressions to match the prompt of a remote host.
Values in this are looked up with `tramp2-find-value'.")


(defvar tramp2-remote-shell-alist (list
				   '(default ("/bin/sh -i"
					      "/bin/bash -i"
					      "/bin/ksh -i"
					      "/bin/zsh -i")))
  "Define the remote shell to run on a particular host.
Values in this are looked up with `tramp2-find-value' and the
result is treated as an active expression (`tramp2-expression').

The shell run by executing the command-line given should be an
interactive Bourne shell capable of expanding a '~' into the
home directory of a user.

If the value is a list of strings, these strings are tested in
order to detect which of them supports tilde expansion. The
default set should work with the auto-detection support on
most systems.")


(defvar tramp2-directory-abbrev-alist nil
  "An alist of directory abbreviation lists to use on remote systems.
Values in this are looked up with `tramp2-find-value'.

This is the equivalent of `directory-abbrev-alist' for tramp2 remote
machines.")


;; REVISIT: Internal...
(defvar tramp2-handler-alist nil
  "Associative list of tramp2 file operation handlers.
To define a file operation handler, see the `def-tramp-handler' macro.

This list is automatically generated. You shouldn't change this
by hand.")


;; REVISIT: What should this be in the release?
(defvar tramp2-default-protocol 'ssh
  "The default protocol to use.")

;; REVISIT: Populate this with a larger number of connections.
(defvar tramp2-protocol-alist '((ssh . ((command . tramp2-ssh-make-command))))
  "An associative set of protocol tags, each mapping to an alist
defining the characteristics of the connection.

Each protocol has a symbol as a tag. The defined characteristics are:

* `command', the command line to execute. A tramp2 active expression.
  See `tramp2-expression' for more details.

* `encoding', the encoding to use for the connection.
  If this is unspecified, an inline transfer encoding is automatically
  detected on the remote machine. See `tramp2-encoding-alist' for
  more details.")

   
(defvar tramp2-ssh-executable (list
			       '(default "ssh"))
  "Arguments to provide to an ssh connection.
Values in this are looked up with `tramp2-find-value' and the
result treated with `tramp2-expression'.")


(defvar tramp2-ssh-arguments (list
			      '(default "-t -e none"))
  "Arguments to provide to an ssh connection.
Values in this are looked up with `tramp2-find-value' and the
result treated with `tramp2-expression'.")



(defvar tramp2-encoding-alist '((base64 . ((test  . tramp2-base64-test)
					   (write . tramp2-base64-write)
					   (read  . tramp2-base64-read)))
				
				(uuencode . ((test  . tramp2-uuencode-test)
					     (write . tramp2-uuencode-write)
					     (read  . tramp2-uuencode-read))))
  "An associative list of encoding types and their properties.
Each encoding has a name and a number of properties. Each property
is a symbol representing a function to call to achieve a specified
result.

* `test', a function to test if the encoding is suitable for use
  with a given connection.

  It is called with two arguments, the final connection and the
  path that triggered the connection. It should return `t' if the
  encoding is suitable and `nil' otherwise.

  If this property is not present, the encoding will be used if
  specified in a protocol without verification, and will not be
  detected automatically on a remote machine.

* `write', a function to send data to the remote machine.
  It is a function name that is called with five arguments,
  SOURCE, START, END, FILE and APPEND.

  SOURCE is the buffer that holds the data to be sent. This data
  *must not* be changed by this routine.

  START and END are positions in the SOURCE buffer. The data from
  START to END should be written to the remote file.

  FILE is the full tramp2 path of the file to write.

  If APPEND is non-nil, the data should be appended to the file,
  if it already exists. The file should be overwritten otherwise.

  This routine *must not* change the current buffer.


* `read', a function to read data from a file on the remote machine.
  It will be called in the connection buffer for a connection, with
  three arguments, START, END and FILE.

  START and END are byte positions in the remote file to be read.
  START and END may be nil, in which case the whole file should be read.

  FILE is the remote file to read from.

  This routine should return a buffer object that contains the decoded
  data from the remote machine. This must contain *only* the bytes from
  START to END in the remote file.")
  


(defvar tramp2-base64-coder
  (list
   `(default ((encoder ("mimencode"
			"recode ../64"
			,(concat "perl -e 'use MIME::Base64 qw(encode_base64);"
				  "$/ = undef; print encode_base64(<STDIN>);'")))
	      (decoder ("mimencode -u"
			"recode /64.."
			,(concat "perl -e 'use MIME::Base64 qw(decode_base64);"
				  "$/ = undef; print decode_base64(<STDIN>);'"))))))
  "An associative list of base64 coding programs for remote machines.
Values in this are looked up with `tramp2-find-value'.

The value is a list of properties with the following predefined:

* `encoder', the remote command to encode to base64.
* `decoder', the remote command to decode from base64.

Each of these may be a string, in which case they are used as a
command directly, or a list of strings in which case each command
is tried in turn until one is found that succeeds.

The encoder and decoder command need not be the same executable
or even the same item in the list.")



;; REVISIT: Semi-public, fill this in.
(defvar tramp2-connect-actors
  (list
   '("pass\\(phrase\\|word\\)[^:]*:" 	. tramp2-send-password)
   '(tramp2-shell-prompt 		. (throw 'ready t)))
  "A list of actions to take while connecting to a remote machine.
See `tramp2-run-actors' for details on the content of this list.

This set of actions is run while establishing each hop in the connection
sequence. Matching for password prompts and similar questions should
go here.")


(defvar tramp2-shell-startup-actors
  (list
   '(tramp2-shell-prompt                . (throw 'ready t)))
  "A list of actions to take while executing a remote login shell.
See `tramp2-run-actors' for details on the content of this list.

This set of actions is run while executing a suitable login shell
on the remote machine.")



;; REVISIT: Semi-public.
(defvar tramp2-setup-functions '(tramp2-setup-coding-system
                                 tramp2-setup-interactive-shell
				 tramp2-setup-remote-environment
				 tramp2-setup-detect-tools
				 tramp2-setup-file-transfer
				 tramp2-setup-file-newer-than)
  "The list of functions to run, in order, to setup the remote shell.
This is run in the tramp2 connection buffer and should run commands
to ensure that the remote shell is ready to accept commands.

The function is run in the connection buffer. Setup functions must
accept two arguments, the connect object for the final hop of the
connection and the full path that triggered the request.

See `tramp2-send-command' for details on sending a command to the
remote system.

Note that you almost certainly *DON'T* want to make any function
other than `tramp2-setup-interactive-shell' the first function in
this list.

If you do, you should be aware that `tramp2-send-command' (amongst
other things) will not work.")


(defconst tramp2-shell-default-environment '(("HISTFILE"  nil)
					     ("TRAMP"     "yes")
					     ("PATH"      tramp2-shell-path)
					     ("TERM"      "dumb")
					     ("MAIL"      nil)
					     ("MAILCHECK" nil)
					     ("MAILPATH"  nil)
					     ("CDPATH"    nil)
					     ("LC_TIME"   "C")
					     ("PS1"       "1> ")
					     ("PS2"       "2> ")
					     ("PS3"       "3> "))
  "Default remote environment values set into the remote shell.
The values here can be overridden by values in `tramp2-shell-environment'.

You should not need to change the values in here directly. Values
in this list are processed in the same way as values in the
`tramp2-shell-environment' list.")


(defvar tramp2-shell-environment nil
  "Remote environment values to set for the remote shell.
Values in this are looked up with `tramp2-find-value'.

The value is a list of values to set into the remote environment.
Each entry in the list is a string value, naming the environment
value, and an active expression (`tramp2-expression') to set it to.

If the value to set the variable to is `nil' the variable is unset
instead. To set an empty value, use \"\" as the value.

Values in this list override the TRAMP2 provided system default
values in `tramp2-shell-default-environment'.")


(defvar tramp2-remote-shell-path   '("/bin"
				     "/usr/bin"
				     "/usr/sbin"
				     "/usr/local/bin"
				     "/usr/ccs/bin"
				     "/local/bin"
				     "/local/freeware/bin"
				     "/local/gnu/bin"
				     "/usr/freeware/bin"
				     "/usr/pkg/bin")
  "*The directories to search for directories on the remote machine.")


(defvar tramp2-remote-tools '((tramp2-perl ("perl5" "perl")      tramp2-remote-perl-v5)
			      (tramp2-ls   "ls"			 tramp2-remote-ls-verify)
			      (tramp2-ln   "ln")
			      (tramp2-dd   "dd"))
  "A list of tools to detect on the remote machine.
Each entry is a list with two or three entries. These are:

* symbol, the name of the variable to set.

  This symbol is made a buffer local variable for the connection
  and set to the full path of the tool, or `nil' if the tool was
  not found.

* tool, a string or a list of strings.

  This is the name of the tool to look for. If it is a string, it
  is searched for directly. If it is a list, each string in it is
  searched for in order.

* verify, an optional function to call to verify the tool.

  If the third element is present, it is called as a function with
  two arguments, the current path and the full path of the detected
  tool.

  If this routine returns nil, the tool is ignored and the search
  continues.")


  

(defvar tramp2-remote-file-newer-than
  (list
   "test $1 -nt $2"
   "test -n \"`find $1 -prune -newer $2 -print`\""
   (concat "perl -e \"if ((stat(\\\"$1\\\"))[9] > "
	   "(stat(\\\"$2\\\"))[9]) { exit 0 } else { exit 1 }\""))
  
  "A list of shell commands that determine if one file is newer than the other.
The commands are invoked with $1 being the first file and $2 the second. They
should return 0 if $1 is newer than $2, or any other value otherwise.")

;; INTERNAL: This should be moved elsewhere...
(defconst tramp2-remote-file-newer-than-function
  (concat "tramp2_file_newer_than () { "
	  "test -e \"$1\" || { echo nil; return 0; }; "
	  "test -e \"$2\" || { echo t; return 0; }; "
	  "if { %s; }; then echo t; else echo nil; fi; "
	  "return 0; }")
  "A shell function that tests if a file is newer than another file and
produces lisp `read'-able output.")


;; REVISIT: This should be, like, 30 in the release. Short for debugging. :)
(defconst tramp2-timeout 1000
  "*Number of seconds to wait for a timeout.")

;; REVISIT: This should be on the order of 0.3 seconds, a very short spin-time
;; to allow data to come in before we look at it. This is done while waiting
;; for the global timeout to expire...
(defconst tramp2-timeout-short 0.3
  "Number of seconds to wait for a short timeout.
This value is used internally as the delay before checking more
input from remote processes and so forth.")

;; Internal only...
(defconst tramp2-raw-coding-system 'raw-text-dos
  "The coding system to use when sending to a process.
This shouldn't need to be changed except in exceptional circumstances.")



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Debug/progress message support.

;; REVISIT: This should be, like, zero or something.
(defvar tramp2-verbose t
  "How verbose tramp2 should be about it's progress.
If this is a symbol, all messages are displayed. If it's a number, the
higher the value, the more verbose tramp2 will be.

Setting this to ten or higher is the same as setting it to `t'.")


(defun tramp2-message (level &rest args)
  "Display a message if LEVEL > `tramp2-verbose'."
  (when (or (symbolp tramp2-verbose)
	    (> tramp2-verbose level))
    (apply 'message args)))


(defvar tramp2-unhandled-operations (list)
  "A list of all the file operations that we don't handle in tramp2 yet.")

;; REVISIT: Should be `nil' for a release.
(defvar tramp2-debug-preserve-evidence t
  "If this is t, evidence is preserved to help diagnose failure conditions.
This inhibits the normal destruction of connection buffers when an error
is signaled.")

;; REVISIT: Should be `nil' for a release.
(defconst tramp2-debug-be-paranoid t
  "If this is t, tramp2 will do a number of paranoid things in an effort
to avoid triggering bugs in the code and breaking things. This includes
interactively confiming a number of decisions that it makes internally
and other, similar things.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The hooks into the XEmacs file handlers.
;; This is the initial entry-point to the handlers. Almost all access to
;; tramp functionality will go through this routine.

;; This fiddling ensures that we make the front of the list, that
;; we never end up duplicated and that we can dynamically change
;; our value in the list. Exciting, no?

;;;###autoload
(let ((val (cons tramp2-path-tag #'tramp2-file-name-handler))
      (now (assoc tramp2-path-tag file-name-handler-alist)))
  (unless (equal val now)
    (delq now file-name-handler-alist)
    (setq file-name-handler-alist (append (list val) file-name-handler-alist))))


;;;###autoload
(defun tramp2-file-name-handler (operation &rest args)
  "tramp2 file name handler.
This is invoked when a file operation is performed on a tramp2 file.
It locates the handler for the function, parses the file path into a
tramp2 path object and then calls the handler function with the
appropriate arguments."
  (let ((handler (tramp2-find-handler-for operation)))
    (if handler
	(apply handler args)
      ;; DEBUG support only, remove later?
      (add-to-list 'tramp2-unhandled-operations operation)
      (tramp2-call-without-handler operation args))))


;; Based on the original tramp function. 
(defun tramp2-call-without-handler (operation args)
  "Invoke normal file name handler for OPERATION.
This inhibits EFS and Ange-FTP, too, because they conflict with tramp."
  (let ((inhibit-file-name-handlers (list 'tramp2-file-name-handler
;					  'efs-file-handler-function
;					  'ange-ftp-hook-function
					  (and (eq inhibit-file-name-operation operation)
					       inhibit-file-name-handlers)))
        (inhibit-file-name-operation operation))
    (apply operation args)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Routines to manage the database of supported handlers.
(defun tramp2-find-handler-for (name)
  "Find the tramp2 operation handler for NAME in the database."
  (cdr-safe (assoc name tramp2-handler-alist)))


(defmacro def-tramp-handler (name args doc &rest body)
  "Define a new filename handler for tramp2.
NAME is the operation name and ARGS is the list of arguments that it
accepts. DOC will be used as the docstring.

This will define a suitable handler function for the file operation,
ensure that it is inserted in the file handler list and ensure that
any filename arguments are parsed correctly into tramp2 paths before
the handler is called.

The handler will be called \"tramp2-do-NAME\". 

The symbol name `file' is magic in the ARGS. The first occurrance of
this name is treated as the filename parameter to the handler. This
will be automatically converted from the string representation to
a tramp2 path object."
  (let ((fn-symbol  (intern (concat "tramp2-do-" (symbol-name name))))
	(file-magic (member 'file args))
	(fn	    nil))

    ;; Build the function declaration, including the magic
    ;; parsing of `file' if we need it and the registration of the function.
    (list 'progn
	  `(let ((current (assoc ',name tramp2-handler-alist)))
	     (if current
		 (setcdr current ',fn-symbol)
	       (add-to-list 'tramp2-handler-alist (cons ',name ',fn-symbol))))
	  (append (list 'defun fn-symbol args doc)
		  (if file-magic
		      `((let ,@(append
				'(((file (cond ((tramp2-path-p file) file)
					       ((stringp file) (tramp2-path-parse file))
					       (t (tramp2-error
						   (list "Invalid path" file)))))))
				body)))
		    body)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Miscelaneous support and compatibility routines.
(defun tramp2-find-value (user host data &optional default)
  "Find the appropriate data value in a tramp2 alist.
The list is searched for a number of keys, specifically:
  * (user . host)
  * host
  * 'default

If none of these are matched, the optional DEFAULT is returned."
  (or (car-safe (cdr-safe (or (assoc (cons user host) data)
			      (assoc host             data)
			      (assoc 'default         data))))
      default))

(defun tramp2-temp-dir ()
  "Return a temporary directory for use with tramp2."
  (file-name-as-directory (or tramp2-temp-dir
			      (getenv "TMPDIR")
			      (getenv "TMP")
			      (getenv "TEMP")
			      "/tmp")))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Support for the default protocols
(defun tramp2-ssh-make-command (user host)
  "Return a command string suitable for running ssh to a remote machine."
  (format "%s %s %s %s"
	  (tramp2-find-value user host tramp2-ssh-executable "ssh")
	  (tramp2-find-value user host tramp2-ssh-arguments "")
	  (if user (format "-l %s" user) "")
	  (or host "localhost")))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Shell setup support.
(defun tramp2-send-password (user host)
  "Send a password to the remote system to allow a login to proceed.
The password will be interactively prompted for, and all efforts are
made to prevent it existing arbitrarily long in memory.

Using this functionality is insecure, though, and should be avoided
where possible."
  (let ((passwd (read-passwd (buffer-substring (tramp2-point-at-bol)
					       (tramp2-point-at-eol)))))
    ;; Send the password directly to avoid copying...
    (process-send-string nil passwd)
    (process-send-string nil "\n")
    ;; Kill the password.
    (fillarray passwd 0))
  ;; Don't actually run a command...
  nil)
  
(defun tramp2-shell-prompt (user host)
  "Return a regular expression to match a shell prompt on a remote machine.
This is drawn from the `tramp2-shell-prompt-pattern' alist, against the
cons of (user . host), then host alone, then `default'."
  (tramp2-find-value user host tramp2-shell-prompt-pattern shell-prompt-pattern))

(defun tramp2-setup-coding-system (connect path)
  "Make sure the coding system is sane.
Note that it can change suddenly when, for example, we send the
password to a local process and it then establishes the connection to
the remote system. So, we detect from the end of the last match to the
start of the next match..."
  (let ((cs (process-coding-system (get-buffer-process (current-buffer)))))
    (save-excursion
      (goto-char (point-min))
      (when (and (search-forward "\r" nil t)
                 (not (vectorp (coding-system-eol-type (car cs))))
                 (not (equal 1 (coding-system-eol-type (car cs)))))
        ;; Urk. Found a newline. This shouldn't happen *ever*
        (pop-to-buffer (current-buffer))
        (debug)))))

(defun tramp2-setup-interactive-shell (connect path)
  "Establish an interactive shell on the remote system.
This is prerequisite to any other activity. Don't move this from
being the first setup function on the remote machine.

This does it's best to get a bourne shell that expands '~' running
as an interactive login."
  (let* ((user (tramp2-connect-user connect))
	 (host (tramp2-connect-host connect))
	 (shell (tramp2-find-value user host tramp2-remote-shell-alist "/bin/sh -i"))
	 found)
    ;; Search for a shell supporting tilde expansion...
    (setq found (catch 'found-shell
		  ;; Do we have a list of shells?
		  (if (listp shell)
		      (let ((shells shell)
			    shell)
			(while shells
			  (setq shell (car shells)
				shells (cdr shells))
			  (when (tramp2-setup-interactive-shell-test connect user shell)
			    (throw 'found-shell shell))))
		    (when (tramp2-setup-interactive-shell-test connect user shell)
		      (throw 'found-shell shell)))))
    ;; Did we actually find one?
    (if found
	(progn
	  ;; Replace the running shell with one that supports tilde expansion.
	  (tramp2-send-command-internal (format "exec %s" found))
	  ;; Turn off the display of our command, for efficiency.
	  (unless tramp2-debug-preserve-evidence
	    (tramp2-send-command-internal "stty -echo"))
	  ;; Resync with the remote shell...
	  (unless (tramp2-run-actors connect
				     (get-buffer-process (current-buffer))
				     tramp2-shell-startup-actors)
	    (if (eq 'run (process-status nil))
		(tramp2-error '("Remote host timed out")))
	    (tramp2-error '("Remote host closed connection"))))
      ;; Failed to find a suitable shell...
      (tramp2-error
		    '("Unable to find shell supporting tilde '~' expansion"
		      shell connect)))))

      
(defun tramp2-setup-interactive-shell-test (connect user shell)
  "Run SHELL on the remote machine and test if it supports tilde
expansion. Return the success or failure of that test.

We assume that USER, the user we loged in with, has a home
directory on the machine. If that user does not exist we presume
that the remote machine is Unix-alike and use \"root\".

This routine DOES NOT leave the remote shell running even
if it does support tilde expansion. This is because we want the
shell to exit and take down the whole connection later on..."
  (save-match-data
    (let ((user (or user "root")))
      ;; Execute the particular shell on the remote machine. Note that
      ;; we don't destroy the connection if the shell fails to exist.
      (tramp2-send-command-internal shell)
      ;; Resync with the remote shell...
      (unless (tramp2-run-actors connect
				 (get-buffer-process (current-buffer))
				 tramp2-shell-startup-actors)
	(if (eq 'run (process-status nil))
	    (tramp2-error '("Remote host timed out")))
	(tramp2-error '("Remote host closed connection")))

      ;; The shell has made it to an interactive prompt. Now we want to
      ;; talk to it and determine if it actually does what we want...
      (unless (= 0 (tramp2-send-command (format "echo ~%s" user)))
	(tramp2-error (format "echo ~%s failed, very odd!" user) shell))
      ;; Return result of tilde expansion test...
      (let ((result (not (search-forward-regexp (format "^~%s" user) nil t))))
	;; Make the test shell exit...
	(tramp2-send-command-internal "exit")
	;; Return the result.
	result))))


(defun tramp2-setup-remote-environment (connect path)
  "Configure the remote environment for a tramp2 shell session."
  (let ((sys-env tramp2-shell-default-environment)
	(user-env (tramp2-find-value (tramp2-connect-user connect)
				     (tramp2-connect-host connect)
				     tramp2-shell-environment))
	env)
    ;; Walk through the system environment.
    (while sys-env
      (setq env (car sys-env)
	    sys-env (cdr sys-env))
      ;; Does this entry exist in the user-env?
      (unless (assoc (car env) user-env)
	;; Nope, set it.
	(tramp2-setup-remote-environment-set connect env)))
    ;; Walk through the user environment.
    (while user-env
      (setq env (car user-env)
	    user-env (cdr user-env))
      (tramp2-setup-remote-environment-set connect env))))


(defun tramp2-setup-remote-environment-set (connect env)
  "Set (or unset) the value specified in ENV for connection CONNECT."
  (let ((name (tramp2-shell-quote (car env)))
	(val  (tramp2-expression (cadr env) connect)))
    (unless (or (= 0 (tramp2-send-command (format (if val "export %s='%s'" "unset %s")
						  name val)))
		(not val))
      (tramp2-error (list "Failed to set value" name val)))))

(defun tramp2-shell-path (user host)
  "Return the remote search path to use for a connection."
  (mapconcat #'identity tramp2-remote-shell-path ":"))


(defun tramp2-setup-file-transfer (connect path)
  "Configure the remote file transfer encoding."
  (let* ((protocol (tramp2-connect-protocol connect))
	 (encoding (or (and (symbolp protocol)
			    (tramp2-protocol-get 'encoding protocol))
		       (tramp2-setup-file-transfer-autodetect connect path))))
    (unless encoding
      (tramp2-error (list "No valid encoding" path)))
    (tramp2-setup-file-transfer-install encoding)))


(defun tramp2-setup-file-transfer-autodetect (connect path)
  "Automatically detect a suitable transfer encodinging for the
given path and connection."
  (catch 'found
    (let ((encodings tramp2-encoding-alist)
	  encoding)
      (while encodings
	(setq encoding  (car encodings)
	      encodings (cdr encodings))
	(let ((name (car encoding))
	      (test (assoc 'test (cdr encoding))))
	  (when test
	    (when (funcall (cdr test) connect path)
	      (throw 'found name)))))
      nil)))


(defun tramp2-setup-file-transfer-install (encoding)
  "Install ENCODING as this buffers encoding type."
  (let ((data (cdr-safe (assoc encoding tramp2-encoding-alist))))
    (unless (and data
		 (assoc 'write data)
		 (assoc 'read  data))
      (tramp2-error (list "Poorly formed encoding" encoding)))
    (set (make-local-variable 'tramp2-write) (cdr (assoc 'write data)))
    (set (make-local-variable 'tramp2-read)  (cdr (assoc 'read  data)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Remote tool detection and configuration...
(defun tramp2-setup-detect-tools (connect path)
  "Detect the existence of required tools on the remote system
and ensure that they are recorded in the connection buffer.

The tools are specified in `tramp2-remote-tools'."
  (let ((tools tramp2-remote-tools))
    (while tools
      (tramp2-setup-detect-tool path (prog1 (car tools)
				       (setq tools (cdr tools)))))))

(defun tramp2-setup-detect-tool (path tool)
  "Detect the existence of a single required tool on the remote
system and ensure that it is recorded for the connection.

This routine requires that the tool test(1) be present on the
remote machine. Without that, we have no way of verifying that
the executable actually is.

Note that we *cannot* assume that the tool will not read STDIN
or that redirecting it from /dev/null will work. Don't modify
this routine to depend on either of those properties.

See `tramp2-setup-detect-tools' and `tramp2-remote-tools'."
  ;; If we got a list, search for them in order...
  ;; A single tool, look for it.
  (let ((variable   (nth 0 tool))
	(executable (nth 1 tool))
	(test       (nth 2 tool))
	exe)
    (setq exe
	  (catch 'found
	    ;; Now, for each executable on the list...
	    (if (listp executable)
		(while executable
		  (tramp2-setup-detect-one-tool path
						(prog1 (car executable)
						  (setq executable (cdr executable)))
						test))
	      (tramp2-setup-detect-one-tool path executable test))))
    (when exe
      (tramp2-message 7 (format "Found tool `%s'." exe))
      (set (make-local-variable variable) exe))))


(defconst tramp2-detect-tool-script (concat "("
					    "IFS=:; " "file='%s'; "
					    "for dir in $PATH; do "
					    "if test -x $dir/$file -a -f $dir/$file; "
					    "then echo $dir/$file; break; "
					    "fi; done; "
					    ")")
  "A shell script that can be formatted to detect the location of
all instances of an executable in the path on a remote machine.")

(defun tramp2-setup-detect-one-tool (path tool test)
  "Detect the executable TOOL on the remote system and set
VARIABLE to the full path to it.

If TEST is not null, it is called as a function with the path
to the tool, to test if it is a suitable version."
  (tramp2-message 7 (format "Looking for tool `%s'." tool))
  (when (= 0 (tramp2-send-command (format tramp2-detect-tool-script tool)))
    ;; Did we get any output?
    (goto-char (point-min))
    (save-match-data
      (while (not (looking-at "^$"))
	(setq tool (buffer-substring (tramp2-point-at-bol) (tramp2-point-at-eol)))
	(when (or (null test)
		  (funcall test path tool))
	  (throw 'found tool))
	(forward-line 1)))))


(defun tramp2-remote-ls-verify (path ls)
  "Determine if the remote LS command support the '-n' argument or not."
  (tramp2-message 7 (format "Checking `%s' for `-n' argument..." ls))
  (= 0 (tramp2-send-command (format "%s -an >/dev/null 2>&1" ls))))

(defun tramp2-remote-perl-v5 (path perl)
  "Ensure that the remote Perl is version 5 or above."
  (tramp2-message 7 (format "Checking `%s' is really Perl5 or better..." perl))
  (= 0 (tramp2-send-command (format "%s -e '$] >= 5'" perl))))


(defmacro tramp2-remote-tool (path tool)
  "Get the path of a tool on the remote machine, or nil if it was not found."
  `(tramp2-with-connection ,path
     ,tool))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Finding files newer than other files...
(defun tramp2-setup-file-newer-than (connect path)
  "Find a tool capable of determening which of a pair of files is
newer, then use that to implement `file-newer-than-file-p' as a
shell command on the remote machine.

The shell command is `tramp2_file_newer_than file1 file2' and
spits our a `read'-able version of the result, including existence
tests.

See `tramp2-remote-file-newer-than' for the shell commands that
are used to implement the newer than part of the test."
  ;; Test each of the commands on the remote system...
  (let ((commands tramp2-remote-file-newer-than))
    (catch 'done
      (while commands
	(when (and (= 0 (tramp2-send-command
			 (format tramp2-remote-file-newer-than-function 
				 (car commands))))
		   (= 0 (tramp2-send-command "tramp2_file_newer_than / /"))
		   (not (progn
			  (goto-char (point-min))
			  (read (current-buffer)))))
	  (throw 'done t))
	(setq commands (cdr commands)))
      ;; Make sure the definition is gone, gone, gone.
      (tramp2-send-command "unset tramp2_file_newer_than")
      (tramp2-error "No way to determine newer file found"))))

  


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Remote data reading and writing.
;; These routines are used at the low level to provide a unified wrapper
;; over the detected data transfer tools.
(defun tramp2-write (start end file &optional append)
  "Write the region from START to END in the current buffer
to FILE. If APPEND is non-nil, append to the remote file rather
than overwriting it."
  ;; Step into the tramp2 connection buffer...
  (let ((source (current-buffer)))
    (tramp2-with-connection file
      (unless (fboundp 'tramp2-write)
	(tramp2-error (list "No write routine for connection" file)))
      (funcall tramp2-write source start end file append))))


(defun tramp2-read (start end file)
  "Read the region from START to END (in bytes) from FILE.
This routine returns a buffer object that contains the content,
or nil if the file could not be read.

The content of the buffer should not be disturbed, as a precaution,
but any encoded read implementation should deal with this situation."
  ;; Step into the tramp2 connection buffer...
  (tramp2-with-connection file
    (unless (fboundp 'tramp2-read)
      (tramp2-error (list "No read routine for connection" file)))
    (funcall tramp2-read start end file)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Remote command execution support.
(put 'tramp2-with-connection 'lisp-indent-function 1)

(defmacro tramp2-with-connection (path &rest body)
  "Run BODY in the connection buffer for PATH.
BODY is evaluated like `progn'."
  ;; Make sure we have an established connection...
  `(let ((with-connection-buffer (or (get-buffer (tramp2-buffer-name ,path))
				     (tramp2-buffer-create ,path))))
     (unless (and with-connection-buffer (bufferp with-connection-buffer))
       (tramp2-error (list "Failed to find/create buffer" (tramp2-buffer-name ,path))))

     ;; Right, we got the buffer and all. Switch to it, do our thang...
     (with-current-buffer with-connection-buffer
       (unless (tramp2-buffer-p)
	 (tramp2-error (list "Invalid buffer for connect" (tramp2-buffer-name ,path))))

       ;; Establish the remote connection, if needed.
       (unless (eq tramp2-state 'connected)
	 (tramp2-establish-connection ,path))
       
       ;; Run the body of the thing...
       (progn . ,body))))

(defun tramp2-establish-connection (connection-path)
  "Establish the connection for the current buffer to a remote system.
This transitions the current buffer from an unconnected state to
a connected state, by executing the commands to connect through."
  (save-match-data
    (condition-case error
	;; Establish the connection...
	(let* ((setup tramp2-setup-functions)
	       (hops (tramp2-path-connect connection-path))
	       (hop  (prog1
			 (car hops)
		       (setq hops (cdr hops)))))
	  ;; Establish the first hop.
	  (unless (tramp2-run-hop 'tramp2-execute-local hop)
	    (tramp2-error
	     (list "Failed to make first connection"
		   (tramp2-buffer-name connection-path) hop)))
	  ;; Advance to the next state.
	  (tramp2-set-buffer-state 'in-progress)
	  (while hops
	    ;; Establish the next hop...
	    (unless (tramp2-run-hop 'tramp2-execute-nexthop (prog1
								(setq hop (car hops))
							      (setq hops (cdr hops))))
	      (tramp2-error
	       (list "Failed to make next connection"
		     (tramp2-buffer-name connection-path) hop))))
	       
	  ;; Advance to the setup state.
	  (tramp2-set-buffer-state 'setup)
	  ;; Run the setup hooks.
	  (while setup
	    (funcall (prog1 (car setup) (setq setup (cdr setup)))
		     hop connection-path))
	  ;; Advance the state to connected.
	  (tramp2-set-buffer-state 'connected))

      ;; If something broke during setup, kill off the connection buffer
      ;; and hope we get it right next time.
      (t (when (and (not tramp2-debug-preserve-evidence)
		    (buffer-live-p (current-buffer)))
	   (kill-buffer (current-buffer)))
	 ;; Keep that error moving up, though...
	 (signal (car error) (cdr error))))))
       
     
(defun tramp2-path-buffer (path)
  "Return the connection buffer for a tramp2 path."
  (tramp2-with-connection path
    (current-buffer)))



(defun tramp2-run-command (path command)
  "Execute COMMAND on the host specified by PATH.

This returns the return code of the command.
The current buffer is also changed to a buffer containing
the output of the command."
  (unless (and command
	       (stringp command)
	       (> (length command) 0))
    (tramp2-error (list "Invalid or empty command" command)))
  (tramp2-with-connection path
    (tramp2-send-command command)))    



(defun tramp2-run-hop (fn connect)
  "Execute the command for CONNECT via FN and run any connect actions
that match the output of it."
  (let ((command (tramp2-connect-command connect)))
    (save-match-data
      ;; Remove the old verbiage from the thing...
      (erase-buffer)
      ;; Get the remote command executed...
      (unless (= 0 (funcall fn command))
	(tramp2-error "Remote command failed" command))
      ;; Run the actors to respond to command output...
      (if (tramp2-run-actors connect
			     (get-buffer-process (current-buffer))
			     tramp2-connect-actors)
	  t
	(if (eq 'run (process-status nil))
	    (tramp2-error (list "Remote host timed out" command))
	  (tramp2-error (list "Remote host closed connection" command)))))))



(defun tramp2-run-actors (connect proc actors)
  "Run remote connection actors until the connection is complete.
PROC is the process object for the remote connection.

This function depends on `point' in the connection buffer being a
valid point to start looking for remote connection output from.

ACTORS is a list of actions to take while connecting to a remote
machine. This is a list of (MATCH . ACTION) pairs, executed in order.

MATCH is a tramp2 active expression. The string it returns is treated
as a regular expression to match against.

This match is applied from the start of the line following a line
containing a previously successful match.

For example, \"<eom>\" is the end of the last match and the buffer
contains:

\"password: <eom>
 <start>next line\"

The next match will start at \"<start>\".

ACTION is a tramp active expression that returns a string to send
to the remote system.

This function returns `t' if one of the actions signaled `ready'
or `nil' if the connection failed or timed out."
  (unless (and proc (processp proc))
    (tramp2-error "Invalid connection" proc))
  (unless (and (listp actors) (> (length actors) 0))
    (tramp2-error "Invalid action list" actors))

  (save-match-data
    (with-current-buffer (process-buffer proc)
      ;; Loop until someone exits via `throw' or remote exits.
      (with-timeout (tramp2-timeout nil)
	(catch 'ready
	  (while (eq 'run (process-status proc))
	    ;; Jump to the last search position.
	    (goto-char (point-min))

	    ;; Look for something to do.
	    (tramp2-message 5 "Looking for remote event...")
	    (let ((actions actors)
		  command act)
	      (while actions
		(setq act     (car actions)
		      actions (cdr actions))
		(when (search-forward-regexp (tramp2-expression (car act) connect) nil t)
		  (tramp2-message 5 "Looking for remote event... responding.")
		  ;; Send the action
		  (when (setq command (tramp2-expression (cdr act) connect))
		    (tramp2-send-command-internal command))
		  ;; Sync to the start of the next line.
		  (goto-char (match-end 0))
		  (tramp2-message 5 "Looking for start of next line...")
		  (let ((here (point)))
		    (while (and (<= (point) here)
				(forward-line 1))
		      (when (<= (point) here)
			(tramp2-accept-process-output proc tramp2-timeout-short))))
		  (delete-region (point-min) (point)))))
	    ;; Fetch more output
	    (tramp2-message 5 "Waiting for more input...")
	    (tramp2-accept-process-output proc tramp2-timeout-short)))))))



(defun tramp2-send-command-internal (command)
  "Send COMMAND to the current remote connection.
The command is automatically terminated with the appropriate
line-ending if it is not already.

You don't want to use this for most things. If does no error
checking on the remote command and does not return the
exit status of the remote command.

See `tramp2-send-command' for a vastly more useful routine
for remote command processing."
  (unless (tramp2-buffer-p)
    (tramp2-error (list "Invalid buffer for command" command)))
  (save-match-data
    (process-send-string nil (if (string-match "\n$" command)
				 (progn
				   (debug)
				   command)
			       (concat command "\n")))))


(defvar tramp2-bracket-string-count 0
  "Number of bracketing strings that have been generated.
This is a counter used to ensure that the generated string is
unique within this Emacs process.")

(defun tramp2-make-bracket-string ()
  "Generate a string that is relatively unique. The output shouldn't
occur in any output from any shell command anywhere on the planet,
nor should it be similar to the previously generated strings.

The string also has substitution points for indicating a start
or end string and a return code."
  (format "-=-=-=-=- tramp2 command %%s bracket %x %x %x: %%s : -=-=-=-=-"
	  (setq tramp2-bracket-string-count (1+ tramp2-bracket-string-count))
	  (mod (apply 'logxor (current-time)) (emacs-pid))
	  (apply 'logxor (current-time))))

	  
(defun tramp2-send-command (command)
  "Send COMMAND to the remote host and await it's completion.
When it exits, it's exit status is returned and the buffer
contains the output of the process.

Any other text contained within the buffer is removed by this call;
don't make it if you need the current content unless you preserve it
through some other mechanism.

If you *really* need to send a command without blocking - which you
don't need to do, let me assure you - see `tramp2-send-command-internal'."
  (save-match-data
    ;; Get hold of a string suitable for bracketing remote output.
    (let* ((raw-bracket (tramp2-make-bracket-string))
	   (start   (format "echo \"%s\"" (format raw-bracket "start" "$$")))
	   (exit     (format "echo \"%s\"" (format raw-bracket "end" "$?")))
	   (start-re (concat (format raw-bracket "start" "[0-9]+") "\n"))
	   (exit-re  (format raw-bracket "end" "\\([0-9]+\\)"))
	   (retval -1))
      ;; Erase the old buffer content.
      (erase-buffer)
      ;; Throw the command at the remote shell.
      (tramp2-send-command-internal (format "%s; { %s }; %s"
					    start
					    (if (string-match "\n$" command)
						command
					      (concat command "\n"))
					    exit))
      ;; Spin until the output shows up.
      (with-timeout (tramp2-timeout '(tramp2-error
						   (list "Remote host timed out" command)))
	(while (not (search-forward-regexp exit-re nil t))
	  (tramp2-accept-process-output (get-buffer-process (current-buffer))
				 tramp2-timeout-short)
	  (goto-char (point-min))))

      ;; We found the output...
      (goto-char (match-beginning 1))
      ;; Read in the value.
      (setq retval (read (current-buffer)))

      ;; Remove the trailer from the buffer...
      (delete-region (match-beginning 0) (point-max))
      ;; Find the leader
      (goto-char (point-min))
      (search-forward-regexp start-re nil t)
      ;; Remove it...
      (delete-region (point-min) (match-end 0))
      ;; And the extranious newline that sneaks in...
      ;; REVISIT: This is possibly wrong. Verify that this routing *is* the
      ;; cause of the extra newline that shows up.
      (when (looking-at "^$")
	(kill-line 1))

      ;; Return the result of the command being executed.
      retval)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Remote command drivers for the various connection stages.
(defun tramp2-execute-local (command)
  "Execute COMMAND in the context of a local Emacs."
  (let ((buffer (current-buffer))
	(process-connection-type t)	; need a tty for ssh. :/

	;; The default coding system for input...
	(coding-system-for-read tramp2-raw-coding-system)
	
	;; *must* run in a local directory. *must* We end up with infinite
	;; recursion otherwise, because the `unhandled-file-name-directory'
	;; routine fails to work as advertised. *sigh*
	(default-directory (tramp2-temp-dir))

        ;; Set the terminal type to be dumb, just in case. -kai
        (process-environment (copy-sequence process-environment))

	proc)
    ;; Set the terminal type to be dumb, just in case. -kai
    (setenv "TERM" "dumb")
    (unless (and (eq tramp2-state 'disconnected)
		 (null (get-buffer-process buffer)))
      (tramp2-error "Local command in non-disconected buffer" command))
    ;; Start the process, replacing the shell. We trust that we don't get
    ;; strange quoting or commands that make this fail to work.
    (setq proc (start-process-shell-command "tramp remote shell"
					    (current-buffer)
					    (concat "exec " command)))
    ;; Set a notification handler for connection failure...
    (set-process-sentinel proc #'tramp2-execute-local-sentinel)
    ;; Allow the process to silently die at the end of the Emacs session.
    (process-kill-without-query proc)
    ;; If the process exited before the sentinal was in place
    ;; - this does happen, you know - we need to handle that.
    (unless (eq (process-status proc) 'run)
      (tramp2-set-buffer-state 'disconnected))
    ;; Return process exit status - or 0 to show success.
    (process-exit-status proc)))
  
(defun tramp2-execute-local-sentinel (proc change)
  "Handle changes in process status for local connections."
  (tramp2-message 9 "Local process sentinal called: %s" change)
  (let ((status (process-status proc))
	(buffer (process-buffer proc)))
    ;; If it's not running...
    (unless (eq status 'run)
      ;; If it's not a clean exit (urgh!)
      ;; Hope that we don't need to do this for 'signal as well.
      (when (eq status 'stop)
	(kill-process proc))
      (when (buffer-live-p buffer)
	(with-current-buffer buffer
	  (tramp2-set-buffer-state 'disconnected)
	  (unless tramp2-debug-preserve-evidence
	    (erase-buffer)))))))



(defun tramp2-execute-nexthop (command)
  "Execute COMMAND to establish the next hop in a connection chain.
This *must* ensure that when the next-hop connection command exits,
the shell also exits and the connection is closed.

This is typically done by using 'exec' on the remote shell."
  (let ((proc (get-buffer-process (current-buffer))))
    (unless (and (tramp2-buffer-p)
		 (eq tramp2-state 'in-progress)
		 (not (null proc)))
      (tramp2-error (list "Next-hop command in bad buffer" command)))

    ;; Jumping to the next host is trivial, just exec the command...
    (tramp2-send-command-internal (format "exec %s" command))
    ;; Return the process status; if it's dead, something went wrong.
    (process-exit-status proc)))
    



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Connection buffer management.
(defun tramp2-buffer-name (path)
  "Return the buffer name that manages the tramp2 connection for PATH."
  (format "* tramp connection for: %s *"
	  (mapconcat 'tramp2-connect-to-string (tramp2-path-connect path) " / ")))


(defun tramp2-buffer-p (&optional buffer)
  "Determine if BUFFER is a tramp2 connection buffer.
The current buffer is used if none is specified."
  (local-variable-p 'tramp2-state (or buffer (current-buffer))))


;; Create a new connection buffer for a connection.
(defun tramp2-buffer-create (path)
  "Create a connection buffer for PATH in the `disconnected' state."
  (let ((buffer (get-buffer-create (tramp2-buffer-name path))))
    (condition-case nil
	(with-current-buffer buffer
	  ;; Don't record undo information...
	  (buffer-disable-undo)

	  ;; Set the default state.
	  (tramp2-set-buffer-state-internal 'disconnected)
	  (unless (tramp2-buffer-p)
	    (tramp2-error (list "Creating buffer failed" path))))
      (t (kill-buffer buffer)))
    buffer))


(defun tramp2-set-buffer-state (state)
  "Set the state of the connection for PATH to STATE.
STATE must be one of the known connection states:

* `disconnected'
  The buffer process does not exist and there is no connection to any
  process, local or remote.

* `in-progress'
  The buffer process is connected to an intermediate machine
  (or connection) between the local host and the final host.

* `setup'
  The buffer process is connected to the final shell but is not yet
  ready to run tramp2 commands remotely.

* `connected'
  The buffer is connected to the final shell and is ready to run
  remote commands.

This routine makes the changes to the buffer state atomically but does
not actually execute the commands required to achieve any transition.
It should be called *after* a state is transitioned to, not before.

Valid transitions are:
disconnected => in-progress | setup
in-progress  => setup
setup        => connected

connected    => disconnected

Note that it is an error to transition from the `in-progress' or `setup'
states to disconnected."
  (let ((buffer (current-buffer)))
    (unless (tramp2-buffer-p buffer)
      (tramp2-error "State change on unexisting connection"))

    (with-current-buffer buffer
      ;; Ensure that we are in a valid state.
      (unless (or (eq tramp2-state 'disconnected)
		  (eq tramp2-state 'in-progress)
		  (eq tramp2-state 'setup)
		  (eq tramp2-state 'connected))
	(tramp2-error (list "Connection state invalid" tramp2-state)))

      ;; Ensure that the transition is valid.
      (when (or (and (eq state 'in-progress) (not (eq tramp2-state 'disconnected)))
		(and (eq state 'setup)   (not (or (eq tramp2-state 'disconnected)
						  (eq tramp2-state 'in-progress))))
		(and (eq state 'connected)   (not (eq tramp2-state 'setup))))
	(tramp2-error (list "Bad state transition" tramp2-state state)))
      
      ;; Actually do the work of the transition.
      (tramp2-set-buffer-state-internal state))))


(defun tramp2-set-buffer-state-internal (state)
  "Set the tramp2 connection in BUFFER to STATE.
This does no validation of the state. See `tramp2-set-connection-state'."
    ;; Record the new state of the buffer.
    (set (make-local-variable 'tramp2-state) state))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Interpretation of the "active expression" stuff.
;; This is the worker that massages an active expression into the string
;; it should be.

(defun tramp2-expression (expression connect)
  "Convert EXPRESSION as an active expression using CONNECT.

An active expression is:
  * a symbol
    The symbol will be called as a function. The arguments `user' and
    `host' will be passed to the function. It should return a string
    to be used for the expression.

  * a function
    The function will be called with arguments `user' and `host'.
    It should return a string to be used for the expression.

  * a list
    The list will be evaluated. The variables `user' and `host' will
    be the current user and host. It should return a string to be used
    for the expression.

  * a string
    The string will used directly after substitutions occur.
    `%u' will be replaced by the user and `%h' by the host.
    These will be replaced with an empty string if there is no
    value."

  (save-match-data
    (cond ((and (symbolp expression) (fboundp expression))
	   (funcall expression
		    (tramp2-connect-user connect)
		    (tramp2-connect-host connect)))

	  ((functionp expression)
	   (funcall expression
		    (tramp2-connect-user connect)
		    (tramp2-connect-host connect)))

	  ((listp expression)
	   (let ((user (tramp2-connect-user connect))
		 (host (tramp2-connect-host connect))
		 (code expression))
	     (if (listp (car-safe expression))
		 (while code
		   (eval (prog1
			     (car code)
			   (setq code (cdr code)))))
	       (eval expression))))
	 
	  ((stringp expression)
	   (let ((text expression)
		 (user (tramp2-connect-user connect))
		 (host (tramp2-connect-host connect)))
	     (while (string-match "%u" text)
	       (setq text (replace-match user t t text)))
	     (while (string-match "%h" text)
	       (setq text (replace-match host t t text)))
	     text)))))
		  

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Protocol database managment.
(defun tramp2-protocol-get (protocol property)
  "Return the PROPERTY value of PROTOCOL, or `nil' if there is no
such property."
  (cdr-safe (assoc property (assoc protocol tramp2-protocol-alist))))

  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; path object management.
;; This defines a tramp2 path object and the constructor and accessor for
;; such a beast.
(defun tramp2-path-p (path)
  "Determine if the object presented is a well-formed TRAMP2 path object."
  (and (vectorp path)
       (eq 'tramp2-path-struct-tag (elt path 0))))

(defun tramp2-make-path (connect path)
  "Create a well-formed tramp2 path object."
  (unless (and (listp connect)
	       (listp (car connect)))
    (tramp2-error (list "Invalid connection" connect)))
  (vector 'tramp2-path-struct-tag
	  connect
	  path))

(defun tramp2-path-connect (path)
  "Return the connect set for a tramp2 path."
  (elt path 1))

(defun tramp2-path-remote-file (path)
  "Return the file path on the remote machine, from a tramp2 path."
  (elt path 2))

(defun tramp2-path-last-user (path)
  "Return the user name of the last connect statement in path."
  (unless (tramp2-path-p path)
    (tramp2-error "Not a tramp2 path" path))
  (tramp2-connect-user (car (reverse (tramp2-path-connect path)))))

(defun tramp2-path-last-host (path)
  "Return the host name of the last connect statement in path."
  (unless (tramp2-path-p path)
    (tramp2-error "Not a tramp2 path" path))
  (tramp2-connect-host (car (reverse (tramp2-path-connect path)))))
  

(defun tramp2-path-same-connection-p (the-file other-file)
  "Determine if the connections for THE-FILE and OTHER-FILE are
the same."
  (unless (tramp2-path-p the-file)
    (tramp2-error "Not a tramp path" the-file))
  (unless (tramp2-path-p other-file)
    (tramp2-error "Not a tramp path" other-file))
  ;; Now, get to it.
  (let ((c1 (tramp2-path-connect the-file))
	(c2 (tramp2-path-connect other-file)))
    (when (= (length c1) (length c2))
      (catch 'done
	(while c1
	  (unless (tramp2-connect-equal (prog1 (car c1) (setq c1 (cdr c1)))
					(prog1 (car c2) (setq c2 (cdr c2))))
	    (throw 'done nil)))
	t))))
	  
	
(defun tramp2-connect-p (connect)
  "Determine if an object is a well-formed tramp2 connect object."
  (and (listp connect)
       (eq 'tramp2-connect-struct-tag (nth 0 connect))))

(defun tramp2-make-connect (protocol user host)
  "Create a tramp2 connect object."
  (unless (or (null protocol)
	      (symbolp protocol)
	      (stringp protocol))
    (tramp2-error (list "Invalid protocol in connect" protocol)))
  (unless (or (null user)
	      (stringp user))
    (tramp2-error (list "Invalid user in connect" protocol)))
  (unless (or (null host)
	      (stringp host))
    (tramp2-error (list "Invalid host in connect" host)))
  (unless (or user host)
    (tramp2-error (list "Connect requires one of USER or HOST")))
  (list 'tramp2-connect-struct-tag protocol user host))

(defun tramp2-connect-protocol (connect)
  "Get the protocol identifier used for a connection."
  (nth 1 connect))

(defun tramp2-connect-user (connect)
  "Get the user identifier for a connect."
  (nth 2 connect))

(defun tramp2-connect-host (connect)
  "Get the host identifier for a connect."
  (nth 3 connect))

(defun tramp2-connect-to-string (connect)
  "Return a stringified version of a connect statement."
  (unless (tramp2-connect-p connect)
    (tramp2-error (list "Not a tramp2 connect list" connect)))
  (let ((protocol (tramp2-connect-protocol connect))
	(user     (tramp2-connect-user connect))
	(host     (tramp2-connect-host connect)))
    (concat (cond ((null protocol)    nil)
		  ((symbolp protocol) (concat (symbol-name protocol) "|"))
		  ((stringp protocol) (concat "[" protocol "]")))
	    (when user (concat user "@"))
	    host)))

(defun tramp2-connect-command (connect)
  "Return a fully expanded string specifying the command to run for
a given path."
  (let ((command (or (tramp2-connect-protocol connect)
		     tramp2-default-protocol)))
    (tramp2-expression (if (stringp command)
			   command
			 (tramp2-protocol-get command 'command))
		       connect)))


(defun tramp2-connect-equal (c1 c2)
  "Determine if the two connect expressions are equal."
  (equal c1 c2))

    

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Path string parser (and validator)
(defun tramp2-path-parse (the-path)
  "Parse a TRAMP2 path string into a structure defining the connections
and the remote file path required.

If THE-PATH is already a tramp2 path object, it is returned unmodified."
  (if (tramp2-path-p the-path)
      the-path
    (save-match-data
      (unless (and (stringp the-path)
		   (string-match (concat "^" tramp2-path-tag) the-path))
	(tramp2-error (list "Not a TRAMP2 path" the-path)))
      ;; Extract the connection expressions.
      (let ((case-fold-search 	t)
	    (path    		(substring the-path (match-end 0)))
	    (connect 		nil))
	(catch 'end
	  (while (string-match tramp2-path-connect path)
	    (unless (or (match-string 5 path) (match-string 6 path))
	      (throw 'end nil))
	    (setq connect (append connect
				  (list
				   (tramp2-make-connect (or (match-string 2 path)
							    (and (match-string 3 path)
								 (intern (match-string 3 path))))
							(match-string 5 path)
							(match-string 6 path))))
		  path    (substring path (match-end 0)))))
	(unless (string-match "^:.*$" path)
	  (tramp2-error (list "Not a TRAMP2 path" the-path)))
	(tramp2-make-path connect (substring path 1))))))

(defun tramp2-path-parse-safe (the-path)
  "Parse a string as a tramp2 path.
Unlike `tramp2-path-parse', this returns `nil' if the path is not
a tramp2 path and does not signal an error."
  (condition-case nil
      (tramp2-path-parse the-path)
    (tramp2-file-error nil)))


(defun tramp2-path-to-string (the-path)
  "Build a string version of a tramp path."
  (let ((path (tramp2-path-parse the-path)))
    (or (and (stringp the-path) the-path)
	(concat tramp2-path-tag
		(mapconcat 'tramp2-connect-to-string (tramp2-path-connect path) ":")
		"::" (tramp2-path-remote-file path)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Note that we exist, populate our file ops, run user hooks (if any)
(provide 'tramp2)

;; Load other components of the TRAMP2 code.
(require 'tramp2-hack)
(require 'tramp2-enc)
(require 'tramp2-ops)

;; Run any user hooks.
(run-hooks 'tramp2-load-hooks)


;; TODO:
;; * Port the MULE support from TRAMP for the connection process.
;;   See especially `tramp2-send-command' and `tramp2-execute-local'.
;;
;; * Port handlers from TRAMP to TRAMP2 (in tramp2-ops.el, please).
;;   See `def-tramp-handler' for details on writing a handler.
;;
;; * Is cl really required? FSF Emacs hate it with a passion, for some
;;   reason that I cannot fathom, and so prefer it not be required at
;;   runtime by any code... which we are doing.
;;
;; * Populate `tramp2-connect-actors'. This needs:
;;   - (more) password prompt handling
;;   - login name handling (?)
;;   - tset/terminal type prompting
;;
;; * Progress messages need to be refined.
;;   - Work out what level various events sit at and define constants.
;;   - Write progress messages for the code.
;;
;; * Better error handling.
;;   - Define a timeout error and a helper to throw one.
;;   - Throw human-readable error messages everywhere.
;;
;; * We should auto-load the encodings and so forth to avoid bloating
;;   the image.
;;
;; * Support for file-locking. This only requires the existence of
;;   symlink creation and testing predecates. We /should/ be able
;;   to do it. If not XEmacs (and Emacs if we have an enthusiast)
;;   should be patched to support it.
;;
;; * Get some python junky^W coder to write the Perl things in python
;;   as well. Maybe some other scripting languages, I don't know. The
;;   script-based stuff bits for performance, really, but it's better
;;   than lacking stat(2) on the remote machine. :)
;;
;; * `vc-find-file-hook' blows up nastily on tramp2 files. Why?
;;
;; * Support completion of host names from .authinfo, maybe /etc/hosts.
;;   - on a per-protocol basis, as a hook. Implement some generic support for
;;   it and stuff.



;;; tramp2.el ends here
