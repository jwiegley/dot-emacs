;;; tramp2-ops.el --- File operation handlers for TRAMP2

;; Copyright (C) 2001 Free Software Foundation, Inc.

;;; Commentary:

;; This defines the file operation handlers for TRAMP2

;; This is an example:

;; (def-tramp-handler sample-operation (file other-file)
;;   "This implements `sample-operation' for TRAMP2 files.

;; The argument FILE is magical - if this is a string, it is parsed to
;; a valid TRAMP2 path object. If it is already a path object, it is
;; left untouched.

;; This magic is based on the argument name. If you need to parse a
;; second file-name, you must do it by hand, as this example shows.

;; The handler is not run from the current buffer of the connection. If you
;; need to get access to the output from a command, wrap your code in 
;; `tramp2-with-connection'.

;; When calling file operations from within a handler, you should call
;; `tramp2-do-NAME' rather than NAME. This will call the internal handler and
;; saves the overhead of parsing the path in every function. Failing to do
;; this will result in an error at runtime, so do be careful.

;; Use `tramp2-run-command' to execute a command on a remote machine
;; suitable for a path."
;;   (condition-case error
;;       (let ((other-file (tramp2-path-parse other-file)))
;;	 ;; Do things with the file here
;; 	) 
;;     (tramp2-file-error (t)))) ; not a valid tramp2 path

;;; Code:
(eval-when-compile
  (require 'tramp2)
  (defvar tramp2-file-attributes-sent-perl	nil))

(require 'tramp2-cache)


;; Demonstration handler for remote operations...
(def-tramp-handler noop (file)
  "A simple remote command handler that changes nothing in the
remote system state."
  (tramp2-run-command file "true"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Vital hooks for supporting the Emacs file-handler model.
(def-tramp-handler unhandled-file-name-directory (filename)
  "Return a suitable local directory for tramp2 magic paths."
  (tramp2-temp-dir))
			   
      
(def-tramp-handler file-local-copy (file &optional buffer)
  "Make a local copy of FILE, returning the name.
If FILE is already local, return nil.

BUFFER is specified and optional in Emacs 20.7.3 and XEmacs 22.2.
It isn't /ever/ used by either of them, though, so it's an error
to pass it to this function. *sigh*"
  (when buffer
    (tramp2-error "`file-local-copy' with BUFFER! " file))

  ;; Right, return a local copy...
  (debug)

  ;; Well, OK, lie like a dog...
  nil)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Simple file-name mangling operations.
;; Note that these follow local system conventions regardless of the remote
;; host they are connected to. This might want to change to allow the mangling
;; function to be customised on a per-connection basis with `tramp2-find-value'.
;;
;; This would allow, for example, OS/2 or Win32 names to be mangled
;; appropriately for those few legacy systems that we are obliged to deal
;; with. :)
(def-tramp-handler file-name-nondirectory (file)
  "Return the name of the file without the directory part."
  (file-name-nondirectory (tramp2-path-remote-file file)))

(def-tramp-handler file-name-directory (file)
  "Return the directory part of file."
  ;; Return a stringified path with the same connect method but
  ;; we remove the non-directory part from the remote file.
  (tramp2-path-to-string
   (tramp2-make-path (tramp2-path-connect file)
		     (file-name-directory (tramp2-path-remote-file file)))))

(def-tramp-handler file-name-as-directory (file)
  "Return the path as a directory."
  (tramp2-path-to-string
   (tramp2-make-path (tramp2-path-connect file)
		     (file-name-as-directory (tramp2-path-remote-file file)))))

(def-tramp-handler directory-file-name (file)
  "Return the name of the file that holds directory data for a tramp2 filename."
  (tramp2-path-to-string
   (tramp2-make-path (tramp2-path-connect file)
		     (directory-file-name (tramp2-path-remote-file file)))))

;; REVISIT: Test this when KEEP-BACKUP-VERSION is not nil. I think it's incorrect.
(def-tramp-handler file-name-sans-versions (file &optional keep-backup-version)
  "Return the filename sans backup versions or strings."
  (tramp2-path-to-string
   (tramp2-make-path (tramp2-path-connect file)
		     (file-name-sans-versions (tramp2-path-remote-file file)
					      keep-backup-version))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Complex file-name mangling operations.
;; These operations require access to information on the remote system.
(def-tramp-handler file-truename (file &optional dir)
  "Return the canonical name of FILE, using the optional DIR
as the directory to search from when FILE is relative.

Since a TRAMP2 path can /never/ be relative to a directory, the
DIR part is a no-op.

From the function:
Return the canonical name of FILENAME.
Second arg DEFAULT is directory to start with if FILENAME is relative
 (does not start with slash); if DEFAULT is nil or missing,
 the current buffer's value of `default-directory' is used.
No component of the resulting pathname will be a symbolic link, as
 in the realpath() function."
  (when (tramp2-do-file-exists-p file)
    (tramp2-with-connection file
      ;; Now, walk through the link chain to the end...
      (let ((link (tramp2-path-remote-file file))
	    dest)
	(while (stringp (setq dest (car (tramp2-do-file-attributes file))))
	  (setq link (concat (file-name-directory link) dest))
	  (setq file (tramp2-make-path (tramp2-path-connect file) link))))
      ;; Return the truename of the file.
      (tramp2-path-to-string file))))


;; Note that PATH is not automatically parsed. This is because we might have
;; been called because DIR, not PATH, was the tramp2 file.
(def-tramp-handler expand-file-name (path &optional dir)
  "Expand FILE (potentially from DIR)."
  (let ((dir (tramp2-path-parse-safe dir)))
    (if (and (not (tramp2-path-parse-safe path))
	     dir
	     (not (file-name-absolute-p path)))
	;; Make the path relative...
	(tramp2-make-path-relative path dir)
      ;; Return the path unmodified...
      (if (tramp2-path-p path)
	  (tramp2-path-to-string path)
	path))))



(defun tramp2-make-path-relative (path directory)
  "Make PATH, a string or TRAMP2 path object, relative to DIRECTORY,
a tramp2 path object representing a directory.

This returns the string version of the relative path."
  (save-match-data
    (let ((dir (file-name-as-directory (tramp2-path-remote-file directory))))
      ;; Is the remote directory absolute?
      (unless (file-name-absolute-p dir)
	(setq dir (concat "~/" dir)))

      ;; Now, make the path relative...
      (setq path (concat dir path))
      
      ;; Expand any tilde sequence in the thing.
      (while (string-match "~[^/]*/?" path)
	(setq path (replace-match (tramp2-tilde-expand directory (match-string 0 path))
				  t t path)))

      ;; Now, remove /./ and /../ from the (full) path.
      (while (string-match "/\\./" path)
	(setq path (replace-match "/" t t path)))
      (while (string-match "/[^/]+/\\.\\./" path)
	(setq path (replace-match "/" t t path)))
      ;; EFS claim that this is correct. *shrug*
      (while (string-match "^\\(/+\\)\\.\\./" path)
	(setq path (replace-match "\\1" t nil path)))

      ;; Now, put together the result.
      (tramp2-path-to-string (tramp2-make-path (tramp2-path-connect directory) path)))))



(def-tramp-handler abbreviate-file-name (file &optional home-dir)
  "Abbreviate the path passed in, including substituting user home
directories, if needed."
  (save-match-data
    (let ((path (tramp2-path-remote-file file))
	  (abbrevs (tramp2-find-value (tramp2-path-last-user file)
				      (tramp2-path-last-host file)
				      tramp2-directory-abbrev-alist)))
      ;; The easy one, the directory hacks list...
      (while abbrevs
	(when (string-match (caar abbrevs) path)
	  (setq path (replace-match (cdar abbrevs) nil nil path)))
	(setq abbrevs (cdr abbrevs)))
      ;; Now, the home directory hack?
      (when home-dir
	(let ((home-dir (concat
			 (regexp-quote (substring (tramp2-tilde-expand file "~") 0 -1))
			 "\\(" (string directory-sep-char) "\\|\\'\\)")))
	  (when (string-match home-dir path)
	    (setq path (replace-match "~\\1" nil nil path)))))
      ;; Return the appropriate value...
      (tramp2-path-to-string (tramp2-make-path (tramp2-path-connect file)
					       path)))))


(defconst tramp2-environment-match (concat "\\("
					   ;; 2    2
					   "\\($$\\)" "\\|"
					   ;; 3            3  
					   "\\(${[^}]+}\\)" "\\|"
					   ;; 4             4
					   "\\($[a-z0-9_]+\\)"
					   "\\)")
  "A regular expression matching environment variable substitutions
in a path name.")

(def-tramp-handler substitute-in-file-name (path)
  "Replace environment variables in PATH with expanded versions.
This works with the enviroment on the local machine and on the
remote machine."
  (save-match-data
    (let ((file (tramp2-path-parse-safe path))
	  (connect (car (split-string path "::")))
	  (path   (cadr (split-string path "::"))))
      ;; Substitute in the connect part first...
      (while (string-match tramp2-environment-match connect)
	(let ((name (cond ((match-string 2 connect) "$")
			  ((match-string 3 connect)
			   (substring (match-string 3 connect) 2 -1))
			  ((match-string 4 connect)
			   (substring (match-string 3 connect) 1))
			  (t (tramp2-error
				    "Badly formed environment value" name)))))
	  (setq connect (replace-match (if (string-equal "$" name)
					   name
					 (tramp2-getenv file name))
				       nil t connect)))
	(setq file (tramp2-path-parse-safe (concat connect "::" path))))
      ;; Now, make sure the path is still ours...
      (if (null file)
	  ;; Call the original, it's not ours any longer...
	  (substitute-in-file-name (concat connect "::" path))
	;; Right, now we process the path part of it...
	(while (string-match tramp2-environment-match path)
	  (let ((name (cond ((match-string 2 path) "$")
			    ((match-string 3 path)
			     (substring (match-string 3 path) 2 -1))
			    ((match-string 4 path)
			     (substring (match-string 4 path) 1))
			    (t (tramp2-error
				      "Badly formed environment value" name)))))
	    (setq path (replace-match (if (string-equal "$" name)
					  name
					(tramp2-getenv file name))
				      nil t path))))
	;; Build up the full path expression...
	(concat connect "::" path)))))
      

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Simple tests for file properties.
(defmacro tramp2-handle-file-test (file test)
  "Use test(1) on the remote system to test the properties of a file."
  `(= 0 (tramp2-run-command ,file (format "test %s %s"
 					  ,test
					  (tramp2-shell-quote
					   (tramp2-path-remote-file ,file))))))

(def-tramp-handler file-regular-p (file)
  "Determine if a tramp2 file is a regular file."
  (tramp2-handle-file-test file "-f"))
  
(def-tramp-handler file-symlink-p (file)
  "Determine if a tramp2 file is a symlink."
  (when (tramp2-handle-file-test file "-L")
    (nth 0 (tramp2-do-file-attributes file))))

(def-tramp-handler file-writable-p (file)
  "Determine if a tramp2 file is writable."
  (tramp2-handle-file-test file "-w"))

(def-tramp-handler file-readable-p (file)
  "Determine if a tramp2 file is readable."
  (tramp2-handle-file-test file "-r"))

(def-tramp-handler file-exists-p (file)
  "Determine if a tramp2 file exists."
  (tramp2-handle-file-test file "-e"))

(def-tramp-handler file-directory-p (file)
  "Determine if a tramp2 file is a directory."
  (tramp2-handle-file-test file "-d"))


(def-tramp-handler file-remote-p (path)
  "Determine if a tramp2 file is on a remote machine. (hint: YES)"
  t)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Complex tests for file properties.
(def-tramp-handler file-attributes (file)
  "Return the file attributes of a remote file."
  ;; Select the particular implementation at runtime...
  (tramp2-with-connection file
    (if tramp2-perl
	(tramp2-do-file-attributes-with-perl file)
      (tramp2-do-file-attributes-with-ls file))))


;; Perl script to implement `file-attributes' in a Lisp `read'able output.
;; If you are hacking on this, note that you get *no* output unless this
;; spits out a complete line, including the '\n' at the end.
(defconst tramp2-perl-file-attributes
  (concat
   "$f = $ARGV[0];"
   "@s = lstat($f) or exit 1;"
   "if (($s[2] & 0170000) == 0120000) { $l = readlink($f); $l = \"\\\"$l\\\"\"; }"
   "elsif (($s[2] & 0170000) == 040000) { $l = \"t\"; }"
   "else { $l = \"nil\" };"
   "@s = stat($f) or exit 1;"
   "printf(\"(%s %u %u %u (%u %u) (%u %u) (%u %u) %u %u t (%u . %u) (%u %u))\\n\","
   "$l, $s[3], $s[4], $s[5], $s[8] >> 16 & 0xffff, $s[8] & 0xffff,"
   "$s[9] >> 16 & 0xffff, $s[9] & 0xffff, $s[10] >> 16 & 0xffff, $s[10] & 0xffff,"
   "$s[7], $s[2], $s[1] >> 16 & 0xffff, $s[1] & 0xffff, $s[0] >> 16 & 0xffff, $s[0] & 0xffff);"
   )
  "Perl script to produce output suitable for use with `file-attributes' 
  on the remote file system.") 


; These values conform to `file-attributes' from XEmacs 21.2.
; GNU Emacs and other tools not checked.
(defconst tramp2-file-mode-type-map '((0  . "-") ; Normal file (SVID-v2 and XPG2)
				      (1  . "p") ; fifo
				      (2  . "c") ; character device
				      (3  . "m") ; multiplexed character device (v7)
				      (4  . "d") ; directory
				      (5  . "?") ; Named special file (XENIX)
				      (6  . "b") ; block device
				      (7  . "?") ; multiplexed block device (v7)
				      (8  . "-") ; regular file
				      (9  . "n") ; network special file (HP-UX)
				      (10 . "l") ; symlink
				      (11 . "?") ; ACL shadow inode (Solaris, not userspace)
				      (12 . "s") ; socket
				      (13 . "D") ; door special (Solaris)
				      (14 . "w")) ; whiteout (BSD)
  "A list of file types returned from the `stat' system call.
This is used to map a mode number to a permission string.")

(defun tramp2-do-file-attributes-with-perl (file)
  "stat(2) FILE on the remote machine using Perl and return the result."
  ;; Do the Perl stat setup, falling back if we have to.
  ;; This is retried *every* stat, because I am mean. :/
  (unless (or (and (boundp 'tramp2-file-attributes-sent-perl)
		   tramp2-file-attributes-sent-perl)
	      (tramp2-do-file-attributes-setup-perl file))
    ;; Fall-back to the ls version, ugly as it is.
    (tramp2-message 5 (format "Falling back to `ls' for `file-attributes'."))
    (tramp2-do-file-attributes-with-ls file))
  
  ;; Run the stat on the remote machine.
  ;; If this fails, we know that the file does not exist.
  (when (= 0 (tramp2-run-command
	      file (format "tramp2_stat_file %s"
			   (tramp2-shell-quote (tramp2-path-remote-file file)))))
    (let ((result (read (current-buffer))))
      (setcar (nthcdr 8 result)
	      (tramp2-file-mode-from-int (nth 8 result)))
      result)))

(defun tramp2-do-file-attributes-setup-perl (file)
  "Send the Perl implementation of stat(2) to the remote host."
  (when (= 0 (tramp2-run-command 
	      file
	      (format "tramp2_stat_file () { %s -e '%s' \"$1\" 2>/dev/null; }"
		      tramp2-perl
		      tramp2-perl-file-attributes)))
    (set (make-local-variable 'tramp2-file-attributes-sent-perl) t)))

(defun tramp2-file-mode-from-int (mode)
  "Turn an integer representing a file mode into an ls(1)-like string."
  (let ((type	(cdr (assoc (logand (lsh mode -12) 15) tramp2-file-mode-type-map)))
	(user	(logand (lsh mode -6) 7))
	(group	(logand (lsh mode -3) 7))
	(other	(logand (lsh mode -0) 7))
	(suid	(> (logand (lsh mode -9) 4) 0))
	(sgid	(> (logand (lsh mode -9) 2) 0))
	(sticky	(> (logand (lsh mode -9) 1) 0)))
    (setq user  (tramp2-file-mode-permissions user  suid "s"))
    (setq group (tramp2-file-mode-permissions group sgid "s"))
    (setq other (tramp2-file-mode-permissions other sticky "t"))
    (concat type user group other)))

(defun tramp2-file-mode-permissions (perm suid suid-text)
  "Convert a permission bitset into a string.
This is used internally by `tramp-file-mode-from-int'."
  (let ((r (> (logand perm 4) 0))
	(w (> (logand perm 2) 0))
	(x (> (logand perm 1) 0)))
    (concat (or (and r "r") "-")
	    (or (and w "w") "-")
	    (or (and suid x suid-text)	; suid, execute
		(and suid (upcase suid-text)) ; suid, !execute
		(and x "x") "-"))))


;; REVISIT: Can more of the work here be done on the remote machine with,
;; say, sed(1) or something like that?
(defun tramp2-do-file-attributes-with-ls (file)
  "stat(2) FILE on the remote machine using ls, then parse and return the result."
  (debug))


(def-tramp-handler verify-visited-file-modtime (buffer)
  "Ensure that the file visited by BUFFER is up-to-date.
We need to handle this as a file-operation handler because
the default implementation uses stat(2) directly,
not `file-attributes'.

This follows the same process as the XEmacs C implementation -
it tollerates a whole second of variance between the last change
and what's recorded in the buffer."
  (with-current-buffer buffer
    (let ((file (tramp2-path-parse-safe buffer-file-name)))
      (unless file
	(tramp2-error "Buffer is not a tramp buffer" buffer-file-name))
      ;; Right, stat the thing.
      (let* ((mtime  (nth 5 (tramp2-do-file-attributes file)))
	     (btime  (visited-file-modtime)))
	(and (= (car mtime) (car btime))
	     (< (abs (- (cdr btime) (nth 1 mtime))) 1))))))


;; Note that /either/ file being ours causes this routine to be called.
(def-tramp-handler file-newer-than-file-p (file1 file2)
  "Test if one file is newer than the other.
This could be optimised with test(1) on the remote system, if the
two files share a remote system.

Return t if file FILE1 is newer than file FILE2.
If FILE1 does not exist, the answer is nil;
otherwise, if FILE2 does not exist, the answer is t."
  (let ((the-file (tramp2-path-parse-safe file1))
	(other-file (tramp2-path-parse-safe file2)))
    (if (and the-file other-file (tramp2-path-same-connection-p the-file other-file))
	;; Handle the simple case of both files on the same connection...
	(tramp2-handle-fast-file-newer-than-file-p the-file other-file)
      ;; Do this using `file-attributes'. This is unreliable on a
      ;; connection without a remote Perl, though.
      (let ((m1 (nth 5 (file-attributes file1)))
	    (m2 (nth 5 (file-attributes file2))))
	(cond ((not m1) nil)
	      ((not m2) t)
	      (t        (or (> (car m1) (car m2))
			    (> (cadr m1) (cadr m2)))))))))

(defun tramp2-handle-fast-file-newer-than-file-p (the-file other-file)
  "Test if one file is newer than the other.
This is an optimized version of the routine that depends on
both files being on the same remote host connection.

Note that we /don't/ use the optimized version when the
connection is different because we don't know that we can
accurately test the files.

Specifically, think of the case where we have root and user
at the same host. If we try to stat as root, we can see *any*
file. If we try it as user, we can't. Different behaviour and,
so, if we use the wrong id..."
  (tramp2-with-connection the-file
    (unless (= 0 (tramp2-run-command the-file
				     (format "tramp2_file_newer_than %s %s"
					     (tramp2-shell-quote
					      (tramp2-path-remote-file the-file))
					     (tramp2-shell-quote
					      (tramp2-path-remote-file other-file)))))
      (tramp2-error "Testing file newer than file"
	     (tramp2-path-remote-file the-file)
	     (tramp2-path-remote-file other-file)))
    ;; Read the result out of the buffer...
    (goto-char (point-min))
    (read (current-buffer))))

  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; File name completion and dired integration.
(defconst tramp2-find-file-completions
  (concat "( cd %s && "
	  "%s -a %s 2>/dev/null | "
	  "{ echo \\(; while read f; do "
	  "if test -d \"$f\" 2>/dev/null; then "
	  "echo \\\"$f/\\\"; else "
	  "echo \\\"$f\\\"; fi; done; "
	  "echo \\); }"
	  " )")
   
  "A shell script that lists completions of a file-name pattern.
This has the ls(1) command and the glob substituted into it.

It outputs a `read'-able list of completions in the current directory.

Substitions, in order, are:
* Remote directory
* ls command
* glob to match")


(def-tramp-handler file-name-all-completions (partial dir)
  "Find all possible completions for PARTIAL in DIR."
  (let ((dir (tramp2-path-parse dir)))
    (tramp2-with-connection dir
      (unless (= 0 (tramp2-run-command dir
				       (format tramp2-find-file-completions
					       (tramp2-shell-quote
						(tramp2-path-remote-file dir))
					       tramp2-ls
					       (if (and partial
							(> (length partial) 0))
						   (concat "-d " (tramp2-shell-quote partial) "*")
						 ""))))
	(tramp2-error (format "Unable to complete file names in %s"
					  (tramp2-path-remote-file dir))
	       (buffer-string)))
      ;; Now, parse out the results...
      (goto-char (point-min))
      (let ((full            (read (current-buffer)))
	    (without-ignored nil))
	;; Remove the trivial items from the list...
	(setq full (delete "./" (delete "../" full)))

	;; Now, set `without-ignored' to the value *after* excluding entries
	;; that have ignored extensions.
	(setq without-ignored (delete nil (mapcar #'tramp2-complete-ignore-files full)))

	;; Return the better list
	(if (> (length without-ignored) 0)
	    without-ignored
	  full)))))

(defsubst tramp2-complete-ignore-files (file)
  "If FILE is in `completion-ignored-extensions', return nil, else return FILE."
  (if (string-equal "/" (substring file -1))
      file
    (unless (member t (mapcar #'(lambda (ext) (tramp2-complete-ignored-file-p file ext))
			      completion-ignored-extensions))
      file)))
      

(defsubst tramp2-complete-ignored-file-p (file ext)
  "If FILE matches EXT at the end, return t, else nil."
  (let ((len (length ext)))
    (and (> (length file) len)
	 (string-equal ext (substring file (- len))))))


(def-tramp-handler file-name-completion (partial dir)
  "Find completions for PARTIAL in DIR."
  (try-completion partial
		  (mapcar (lambda (x) (cons x nil))
			  (file-name-all-completions partial dir))))
  



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; File reading and writing. The exciting stuff. :)
(def-tramp-handler write-region (start end file &optional append visit lockname silly-emacs)
  "Write a region of the current buffer to a tramp2 file.
This behaves like `write-region' for tramp2 files.

This routine operates correctly, without surprises, on both
XEmacs and Emacs, with regard the 7th (SILLY-EMACS) argument.

LOCKNAME (and file locking) are ignored by this routine.

Version specific information:

In Emacs, argument 7 SILLY-EMACS is CONFIRM.
In XEmacs, argument 7 SILLY-EMACS is CODING-SYSTEM.

Specifically, from documentation for `write-region':

Write current region into specified file.
By default the file's existing contents are replaced by the specified region.
When called from a program, takes three arguments:
START, END and FILENAME.  START and END are buffer positions.
Optional fourth argument APPEND if non-nil means
  append to existing file contents (if any).
Optional fifth argument VISIT if t means
  set last-save-file-modtime of buffer to this file's modtime
  and mark buffer not modified.
If VISIT is a string, it is a second file name;
  the output goes to FILENAME, but the buffer is marked as visiting VISIT.
  VISIT is also the file name to lock and unlock for clash detection.
If VISIT is neither t nor nil nor a string,
  that means do not print the \"Wrote file\" message.
The optional sixth arg LOCKNAME, if non-nil, specifies the name to 
  use for locking and unlocking, overriding FILENAME and VISIT. 
Kludgy feature: if START is a string, then that string is written 
to the file, instead of any buffer contents, and END is ignored. 

XEmacs specific documentation:

Optional seventh argument CODING-SYSTEM specifies the coding system 
  used to encode the text when it is written out, and defaults to 
  the value of `buffer-file-coding-system' in the current buffer. 
  Interactively, with a prefix arg, you will be prompted for the 
  coding system.

Emacs specific documentation:

The optional seventh arg CONFIRM, if non-nil, says ask for confirmation
  before overwriting an existing file."
  ;; Handle the basic argument lossage. Dammit.
  (when (or (featurep 'xemacs)
	    (and (not (null silly-emacs))
		 (file-exists-p file)
		 (yes-or-no-p (format "File %s on host %s exists, overwrite? "
				      (tramp2-path-remote-file file)
				      (tramp2-connect-host (last (tramp2-path-connect file)))))))
    (tramp2-write-region-internal start end file
				  append visit lockname
				  (and (featurep 'xemacs)
				       silly-emacs))))

(defun tramp2-write-region-internal (start end file append visit lockname coding-system)
  "Internal handler for `write-region' once the Emacs/XEmacs lossage
is dealt with.

Locking, and LOCKNAME specifically, are ignored."
  ;; Do we need to generate a special buffer?
  (if (stringp start)
      (with-temp-buffer
	(insert start)
	(tramp2-write (point-min) (point-max) file append))
    (tramp2-write (point-min) (point-max) file append)))
  

(def-tramp-handler insert-file-contents (file &optional visit start end replace)
  "Handle insertion of file content from the remote machine.

This actually copes with REPLACE, even though that requires C-level
support (at least on XEmacs). This is done through the wonders of
temporary files. Feel good yet?

Specifically, from documentation for `insert-file-contents':

Insert contents of file FILENAME after point.
Returns list of absolute file name and length of data inserted.
If second argument VISIT is non-nil, the buffer's visited filename
and last save file modtime are set, and it is marked unmodified.
If visiting and the file does not exist, visiting is completed
before the error is signaled.

The optional third and fourth arguments START and END
specify what portion of the file to insert.
If VISIT is non-nil, START and END must be nil.
If optional fifth argument REPLACE is non-nil,
it means replace the current buffer contents (in the accessible portion)
with the file contents.  This is better than simply deleting and inserting
the whole thing because (1) it preserves some marker positions
and (2) it puts less data in the undo list.

The coding system used for decoding the file is determined as follows:

1. `coding-system-for-read', if non-nil.
2. The result of `insert-file-contents-pre-hook', if non-nil.
3. The matching value for this filename from
   `file-coding-system-alist', if any.
4. `buffer-file-coding-system-for-read', if non-nil.
5. The coding system 'raw-text.

If a local value for `buffer-file-coding-system' in the current buffer
does not exist, it is set to the coding system which was actually used
for reading.

See also `insert-file-contents-access-hook',
`insert-file-contents-pre-hook', `insert-file-contents-error-hook',
and `insert-file-contents-post-hook'."

  ;; REVISIT: This is /so/ not finished...

  ;; Error-check the parameters...
  (when (and visit (or start end))
    (tramp2-error "If VISIT, START and END must be nil" start end visit))

  ;; Make sure this isn't a read-only buffer...
  (barf-if-buffer-read-only)

  ;; Fill in some basics...
  (let ((filename (tramp2-do-expand-file-name file))
	(attr     (tramp2-do-file-attributes file)))
    ;; Deal with the visit stuff...
    (when visit
      (setq buffer-file-name filename)
      (set-visited-file-modtime (or (nth 5 attr) '(0 0)))
      (set-buffer-modified-p nil))
    
    ;; If the file does not exist...
    (unless (tramp2-do-file-exists-p file)
      (error 'file-error (format "File `%s' not found on remote host" filename))
      (list filename 0))

    ;; Otherwise, we read the data and put it in it's place...
    (let ((data (tramp2-read start end file)))
      (unless (buffer-live-p data)
	(tramp2-error
		      (format "Failed to read from %s"
			      (tramp2-path-remote-file file))))
      
      ;; Are we doing the magic replace thing?
      (if replace
	  (let ((temp (tramp2-temp-file-name)))
	    (with-temp-file temp
	      (insert-buffer data))
	    ;; Don't let the C visit, we did that already.
	    (insert-file-contents temp nil start end replace)
	    (delete-file temp))
	;; Just insert the data...
	(insert-buffer data))

      ;; Return the absolute file name and the length of data inserted.
      (list filename (or (and start end (- end start))
			 (nth 7 attr))))))
  
    
	



(provide 'tramp2-ops)

;; TODO:
;; * `insert-file-contents' needs to be polished and checked for errors.
;;
;; * `file-newer-than-file-p' needs to use test(1) (or whatever) when the
;;   remote system does not support the Perl `file-attributes' implementation.
;;
;; * Support visiting of files (implement these ops):
;;
;; vc-registered create-file-buffer get-file-buffer abbreviate-file-name
;; substitute-in-file-name


;;; tramp2-ops.el ends here
