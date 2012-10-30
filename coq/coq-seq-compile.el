;; coq-seq-compile.el --- sequential compilation of required modules
;; Copyright (C) 1994-2012 LFCS Edinburgh.
;; Authors: Hendrik Tews
;; License:     GPL (GNU GENERAL PUBLIC LICENSE)
;; Maintainer: Hendrik Tews <hendrik@askra.de>
;;
;; $Id$
;;
;;; Commentary:
;;
;; This file implements compilation of required modules. The
;; compilation is done synchonously and sequentially. That is, Proof
;; General blocks before putting newly asserted items into
;; proof-action-list and compiles one module after the other.
;;


(eval-when-compile
  (require 'proof-compat))

(eval-when (compile)
  (require 'proof-shell)
  (defvar queueitems nil)       ; dynamic scope in p-s-extend-queue-hook
  (defvar coq-compile-before-require nil)       ; defpacustom
  (defvar coq-confirm-external-compilation nil); defpacustom
  (proof-ready-for-assistant 'coq))     ; compile for coq


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Multiple file handling -- sequential compilation of required modules
;;

;; constants

(defun get-coq-library-directory ()
  (let ((c (substring (shell-command-to-string "coqtop -where") 0 -1 )))
    (if (string-match c "not found")
        "/usr/local/lib/coq"
      c)))

(defconst coq-library-directory (get-coq-library-directory)
  "The coq library directory, as reported by \"coqtop -where\".")

(defcustom coq-dependency-analyzer
  (proof-locate-executable "coqdep" t nil)
  "Command to invoke coqdep."
  :type 'string
  :group 'coq)

(defcustom coq-compiler
  (proof-locate-executable "coqc" t nil)
  "Command to invoke the coq compiler."
  :type 'string
  :group 'coq)


;; user options and variables

(defgroup coq-auto-compile ()
  "Customization for automatic compilation of required files"
  :group 'coq
  :package-version '(ProofGeneral . "4.1"))

(defpacustom compile-before-require nil
  "If non-nil, check dependencies of required modules and compile if necessary.
If non-nil ProofGeneral intercepts \"Require\" commands and checks if the
required library module and its dependencies are up-to-date. If not, they
are compiled from the sources before the \"Require\" command is processed.

This option can be set/reset via menu
`Coq -> Settings -> Compile Before Require'."
  :type 'boolean
  :safe 'booleanp
  :group 'coq-auto-compile)

(defcustom coq-compile-command ""
  "External compilation command. If empty ProofGeneral compiles itself.
If unset (the empty string) ProofGeneral computes the dependencies of
required modules with coqdep and compiles as necessary. This internal
dependency checking does currently not handle ML modules.

If a non-empty string, the denoted command is called to do the
dependency checking and compilation. Before executing this
command the following keys are substituted as follows:
  %p  the (physical) directory containing the source of
      the required module
  %o  the Coq object file in the physical directory that will
      be loaded
  %s  the Coq source file in the physical directory whose
      object will be loaded
  %q  the qualified id of the \"Require\" command
  %r  the source file containing the \"Require\"

For instance, \"make -C %p %o\" expands to \"make -C bar foo.vo\"
when module \"foo\" from directory \"bar\" is required.

After the substitution the command can be changed in the
minibuffer if `coq-confirm-external-compilation' is t."
  :type 'string
  :safe (lambda (v)
          (and (stringp v)
               (or (not (boundp 'coq-confirm-external-compilation))
                   coq-confirm-external-compilation)))
  :group 'coq-auto-compile)

(defconst coq-compile-substitution-list
  '(("%p" physical-dir)
    ("%o" module-object)
    ("%s" module-source)
    ("%q" qualified-id)
    ("%r" requiring-file))
  "Substitutions for `coq-compile-command'.
Value must be a list of substitutions, where each substitution is
a 2-element list. The first element of a substitution is the
regexp to substitute, the second the replacement. The replacement
is evaluated before passing it to `replace-regexp-in-string', so
it might be a string, or one of the symbols 'physical-dir,
'module-object, 'module-source, 'qualified-id and
'requiring-file, which are bound to, respectively, the physical
directory containing the source file, the Coq object file in
'physical-dir that will be loaded, the Coq source file in
'physical-dir whose object will be loaded, the qualified module
identifier that occurs in the \"Require\" command, and the file
that contains the \"Require\".")

(defcustom coq-load-path nil
  "Non-standard coq library load path.
This list specifies the LoadPath extension for coqdep, coqc and
coqtop. Usually, the elements of this list are strings (for
\"-I\") or lists of two strings (for \"-R\" dir \"-as\" path).

The possible forms of elements of this list correspond to the 3
forms of include options ('-I' and '-R'). An element can be

  - A string, specifying a directory to be mapped to the empty
    logical path ('-I').
  - A list of the form '(rec dir path)' (where dir and path are
    strings) specifying a directory to be recursively mapped to the
    logical path 'path' ('-R dir -as path').
  - A list of the form '(norec dir path)', specifying a directory
    to be mapped to the logical path 'path' ('-I dir -as path').

For convenience the symbol 'rec' can be omitted and entries of
the form '(dir path)' are interpreted as '(rec dir path)'.

Under normal circumstances this list does not need to
contain the coq standard library or \".\" for the current
directory (see `coq-load-path-include-current')."
  :type '(repeat (choice (string :tag "simple directory without path (-I)")
                         (list :tag
                               "recursive directory with path (-R ... -as ...)"
                               (const rec)
                               (string :tag "directory")
                               (string :tag "log path"))
                         (list :tag
                               "simple directory with path (-I ... -as ...)"
                               (const nonrec)
                               (string :tag "directory")
                               (string :tag "log path"))))
  :safe 'coq-load-path-safep
  :group 'coq-auto-compile)

(defcustom coq-compile-auto-save 'ask-coq
  "Buffers to save before checking dependencies for compilation.
There are two orthogonal choices: Firstly one can save all or only the coq
buffers, where coq buffers means all buffers in coq mode except the current
buffer. Secondly, Emacs can ask about each such buffer or save all of them
unconditionally.

This makes four permitted values: 'ask-coq to confirm saving all
modified Coq buffers, 'ask-all to confirm saving all modified
buffers, 'save-coq to save all modified Coq buffers without
confirmation and 'save-all to save all modified buffers without
confirmation."
  :type
  '(radio
    (const :tag "ask for each coq-mode buffer, except the current buffer"
           ask-coq)
    (const :tag "ask for all buffers" ask-all)
    (const
     :tag
     "save all coq-mode buffers except the current buffer without confirmation"
     save-coq)
    (const :tag "save all buffers without confirmation" save-all))
  :safe (lambda (v) (member v '(ask-coq ask-all save-coq save-all)))
  :group 'coq-auto-compile)

(defcustom coq-lock-ancestors t
  "If non-nil, lock ancestor module files.
If external compilation is used (via `coq-compile-command') then
only the direct ancestors are locked. Otherwise all ancestors are
locked when the \"Require\" command is processed."
  :type 'boolean
  :safe 'booleanp
  :group 'coq-auto-compile)

(defpacustom confirm-external-compilation t
  "If set let user change and confirm the compilation command.
Otherwise start the external compilation without confirmation.

This option can be set/reset via menu
`Coq -> Settings -> Confirm External Compilation'."
  :type 'boolean
  :group 'coq-auto-compile)

(defcustom coq-load-path-include-current t
  "If `t' let coqdep search the current directory too.
Should be `t' for normal users. If `t' pass \"-I dir\" to coqdep when
processing files in directory \"dir\" in addition to any entries
in `coq-load-path'."
  :type 'boolean
  :safe 'booleanp
  :group 'coq-auto-compile)

(defcustom coq-compile-ignored-directories nil
  "Directories in which ProofGeneral should not compile modules.
List of regular expressions for directories in which ProofGeneral
should not compile modules. If a library file name matches one
of the regular expressions in this list then ProofGeneral does
neither compile this file nor check its dependencies for
compilation. It makes sense to include non-standard coq library
directories here if they are not changed and if they are so big
that dependency checking takes noticeable time."
  :type '(repeat regexp)
  :safe (lambda (v) (every 'stringp v))
  :group 'coq-auto-compile)

(defcustom coq-compile-ignore-library-directory t
  "If non-nil, ProofGeneral does not compile modules from the coq library.
Should be `t' for normal coq users. If `nil' library modules are
compiled if their sources are newer.

This option has currently no effect, because Proof General uses
coqdep to translate qualified identifiers into library file names
and coqdep does not output dependencies in the standard library."
  :type 'boolean
  :safe 'booleanp
  :group 'coq-auto-compile)

(defcustom coq-coqdep-error-regexp
  (concat "^\\*\\*\\* Warning: in file .*, library .* is required "
          "and has not been found")
  "Regexp to match errors in the output of coqdep.
coqdep indicates errors not always via a non-zero exit status,
but sometimes only via printing warnings. This regular expression
is used for recognizing error conditions in the output of
coqdep (when coqdep terminates with exit status 0). Its default
value matches the warning that some required library cannot be
found on the load path and ignores the warning for finding a
library at multiple places in the load path. If you want to turn
the latter condition into an error, then set this variable to
\"^\\*\\*\\* Warning\"."
  :type 'string
  :safe 'stringp
  :group 'coq-auto-compile)

(defconst coq-require-command-regexp
  "^Require[ \t\n]+\\(Import\\|Export\\)?[ \t\n]*"
  "Regular expression matching Require commands in Coq.
Should match \"Require\" with its import and export variants up to (but not
including) the first character of the first required module. The required
modules are matched separately with `coq-require-id-regexp'")

(defconst coq-require-id-regexp
  "[ \t\n]*\\([A-Za-z0-9_']+\\(\\.[A-Za-z0-9_']+\\)*\\)[ \t\n]*"
  "Regular expression matching one Coq module identifier.
Should match precisely one complete module identifier and surrounding
white space. The module identifier must be matched with group number 1.
Note that the trailing dot in \"Require A.\" is not part of the module
identifier and should therefore not be matched by this regexp.")

(defvar coq-compile-history nil
  "History of external Coq compilation commands.")

(defvar coq-compile-response-buffer "*coq-compile-response*"
  "Name of the buffer to display error messages from coqc and coqdep.")


(defvar coq-debug-auto-compilation nil
  "*Display more messages during compilation")


;; basic utilities

(defun time-less-or-equal (time-1 time-2)
  "Return `t' if time value time-1 is earlier or equal to time-2.
A time value is a list of two integers as returned by `file-attributes'.
The first integer contains the upper 16 bits and the second the lower
16 bits of the time."
  (or (time-less-p time-1 time-2)
      (equal time-1 time-2)))

(defun coq-max-dep-mod-time (dep-mod-times)
  "Return the maximum in DEP-MOD-TIMES.
Argument DEP-MOD-TIMES is a list where each element is either a
time value (see `time-less-or-equal') or 'just-compiled. The
function returns the maximum of the elements in DEP-MOD-TIMES,
where 'just-compiled is considered the greatest time value. If
DEP-MOD-TIMES is empty it returns nil."
  (let ((max nil))
    (while dep-mod-times
      (cond
       ((eq (car dep-mod-times) 'just-compiled)
        (setq max 'just-compiled
              dep-mod-times nil))
       ((eq max nil)
        (setq max (car dep-mod-times)))
       ((time-less-p max (car dep-mod-times))
        (setq max (car dep-mod-times))))
      (setq dep-mod-times (cdr-safe dep-mod-times)))
    max))


;; safety predicate for coq-load-path

(defun coq-load-path-safep (path)
  "Check if PATH is a safe value for `coq-load-path'."
  (and
   (listp path)
   (every
    (lambda (entry)
      (or (stringp entry)
          (and (listp entry)
               (eq (car entry) 'rec)
               (every 'stringp (cdr entry))
               (equal (length entry) 3))
          (and (listp entry)
               (eq (car entry) 'nonrec)
               (every 'stringp (cdr entry))
               (equal (length entry) 3))
          (and (listp entry)
               (every 'stringp entry)
               (equal (length entry) 2))))
    path)))

;; Compute command line for starting coqtop

(defun coq-prog-args ()
  ;; coqtop always adds the current directory to the LoadPath, so don't
  ;; include it in the -I options.
  (let ((coq-load-path-include-current nil))
    (append coq-prog-args (coq-include-options nil))))


;; ancestor (un-)locking

(defun coq-lock-ancestor (span ancestor-src)
  "Lock ancestor ANCESTOR-SRC and register it in SPAN.
Lock only if `coq-lock-ancestor' is non-nil. Further, do nothing,
if ANCESTOR-SRC is already a member of
`proof-included-files-list'. Otherwise ANCESTOR-SRC is locked and
registered in the 'coq-locked-ancestors property of the SPAN to
properly unlock ANCESTOR-SRC on retract."
  (if coq-lock-ancestors
      (let ((true-ancestor-src (file-truename ancestor-src)))
        (unless (member true-ancestor-src proof-included-files-list)
          (proof-register-possibly-new-processed-file true-ancestor-src)
          (span-set-property
           span 'coq-locked-ancestors
           (cons true-ancestor-src
                 (span-property span 'coq-locked-ancestors)))))))

(defun coq-unlock-ancestor (ancestor-src)
  "Unlock ANCESTOR-SRC."
  (let* ((true-ancestor (file-truename ancestor-src)))
    (setq proof-included-files-list
          (delete true-ancestor proof-included-files-list))
    (proof-restart-buffers (proof-files-to-buffers (list true-ancestor)))))

(defun coq-unlock-all-ancestors-of-span (span)
  "Unlock all ancestors that have been locked when SPAN was asserted."
  (mapc 'coq-unlock-ancestor (span-property span 'coq-locked-ancestors))
  (span-set-property span 'coq-locked-ancestors ()))

;; handle Require commands when queue is extended

(defun coq-compile-ignore-file (lib-obj-file)
  "Check whether ProofGeneral should handle compilation of LIB-OBJ-FILE.
Return `t' if ProofGeneral should skip LIB-OBJ-FILE and `nil' if
ProofGeneral should handle the file. For normal users it does, for instance,
not make sense to let ProofGeneral check if the coq standard library
is up-to-date."
  (or
   (and
    coq-compile-ignore-library-directory
    (eq (compare-strings coq-library-directory 0 nil
                         lib-obj-file 0 (length coq-library-directory))
        t)
    (if coq-debug-auto-compilation
        (message "Ignore lib file %s" lib-obj-file))
    t)
   (if (some
          (lambda (dir-regexp) (string-match dir-regexp lib-obj-file))
          coq-compile-ignored-directories)
       (progn
         (if coq-debug-auto-compilation
             (message "Ignore %s" lib-obj-file))
         t)
     nil)))

(defun coq-library-src-of-obj-file (lib-obj-file)
  "Return source file name for LIB-OBJ-FILE.
Chops off the last character of LIB-OBJ-FILE to convert \"x.vo\" to \"x.v\"."
  (substring lib-obj-file 0 (- (length lib-obj-file) 1)))

(defun coq-option-of-load-path-entry (entry)
  "Translate a single element from `coq-load-path' into options.
See `coq-load-path' for the possible forms of entry and to which
options they are translated."
  (cond
   ((stringp entry)
    (list "-I" (expand-file-name entry)))
   ((eq (car entry) 'nonrec)
    (list "-I" (expand-file-name (nth 1 entry)) "-as" (nth 2 entry)))
   (t
    (if (eq (car entry) 'rec)
        (setq entry (cdr entry)))
    (list "-R" (expand-file-name (car entry)) "-as" (nth 1 entry)))))

(defun coq-include-options (file)
  "Build the list of include options for coqc, coqdep and coqtop.
The options list includes all entries from `coq-load-path'
prefixed with suitable options and, if
`coq-load-path-include-current' is enabled, the directory base of
FILE. The resulting list is fresh for every call, callers can
append more arguments with `nconc'.

FILE should be an absolute file name. It can be nil if
`coq-load-path-include-current' is nil."
  (let ((result nil))
    (unless (coq-load-path-safep coq-load-path)
      (error "Invalid value in coq-load-path"))
    (when coq-load-path
      (setq result (coq-option-of-load-path-entry (car coq-load-path)))
      (dolist (entry (cdr coq-load-path))
        (nconc result (coq-option-of-load-path-entry entry))))
    (if coq-load-path-include-current
        (setq result
              (cons "-I" (cons (file-name-directory file) result))))
    result))

(defun coq-init-compile-response-buffer (command)
  "Initialize the buffer for the compilation output.
If `coq-compile-response-buffer' exists, empty it. Otherwise
create a buffer with name `coq-compile-response-buffer', put
it into `compilation-mode' and store it in
`coq-compile-response-buffer' for later use. Argument COMMAND is
the command whose output will appear in the buffer."
  (let ((buffer-object (get-buffer coq-compile-response-buffer)))
    (if buffer-object
        (let ((inhibit-read-only t))
          (with-current-buffer buffer-object
            (erase-buffer)))
      (setq buffer-object
            (get-buffer-create coq-compile-response-buffer))
      (with-current-buffer buffer-object
        (compilation-mode)))
    ;; I don't really care if somebody gets the right mode when
    ;; he saves and reloads this buffer. However, error messages in
    ;; the first line are not found for some reason ...
    (let ((inhibit-read-only t))
      (with-current-buffer buffer-object
        (insert "-*- mode: compilation; -*-\n\n" command "\n")))))

(defun coq-display-compile-response-buffer ()
  "Display the errors in `coq-compile-response-buffer'."
  (with-current-buffer coq-compile-response-buffer
    ;; fontification enables the error messages
    (let ((font-lock-verbose nil)) ; shut up font-lock messages
      (font-lock-fontify-buffer)))
  ;; Make it so the next C-x ` will use this buffer.
  (setq next-error-last-buffer (get-buffer coq-compile-response-buffer))
  (let ((window (display-buffer coq-compile-response-buffer)))
    (if proof-shrink-windows-tofit
        (save-excursion
          (save-selected-window
            (proof-resize-window-tofit window))))))

(defun coq-get-library-dependencies (lib-src-file &optional command-intro)
  "Compute dependencies of LIB-SRC-FILE.
Invoke \"coqdep\" on LIB-SRC-FILE and parse the output to
compute the compiled coq library object files on which
LIB-SRC-FILE depends. The return value is either a string or a
list. If it is a string then an error occurred and the string is
the core of the error message. If the return value is a list no
error occurred and the returned list is the (possibly empty) list
of file names LIB-SRC-FILE depends on.

If an error occurs this funtion displays
`coq-compile-response-buffer' with the complete command and its
output. The optional argument COMMAND-INTRO is only used in the
error case. It is prepended to the displayed command.

LIB-SRC-FILE should be an absolute file name. If it is, the
dependencies are absolute too and the simplified treatment of
`coq-load-path-include-current' in `coq-include-options' won't
break."
  (let ((coqdep-arguments
         (nconc (coq-include-options lib-src-file) (list lib-src-file)))
        coqdep-status coqdep-output)
    (if coq-debug-auto-compilation
        (message "call coqdep arg list: %s" coqdep-arguments))
    (with-temp-buffer
      (setq coqdep-status
            (apply 'call-process
                   coq-dependency-analyzer nil (current-buffer) nil
                   coqdep-arguments))
      (setq coqdep-output (buffer-string)))
    (if coq-debug-auto-compilation
        (message "coqdep status %s, output on %s: %s"
                 coqdep-status lib-src-file coqdep-output))
    (if (or
         (not (eq coqdep-status 0))
         (string-match coq-coqdep-error-regexp coqdep-output))
        (let* ((this-command (cons coq-dependency-analyzer coqdep-arguments))
               (full-command (if command-intro
                                 (cons command-intro this-command)
                               this-command)))
          ;; display the error
          (coq-init-compile-response-buffer
           (mapconcat 'identity full-command " "))
          (let ((inhibit-read-only t))
            (with-current-buffer coq-compile-response-buffer
              (insert coqdep-output)))
          (coq-display-compile-response-buffer)
          "unsatisfied dependencies")
      (if (string-match ": \\(.*\\)$" coqdep-output)
          (cdr-safe (split-string (match-string 1 coqdep-output)))
        ()))))

(defun coq-compile-library (src-file)
  "Recompile coq library SRC-FILE.
Display errors in buffer `coq-compile-response-buffer'."
  (message "Recompile %s" src-file)
  (let ((coqc-arguments
         (nconc (coq-include-options src-file) (list src-file)))
        coqc-status)
    (coq-init-compile-response-buffer
     (mapconcat 'identity (cons coq-compiler coqc-arguments) " "))
    (if coq-debug-auto-compilation
        (message "call coqc arg list: %s" coqc-arguments))
    (setq coqc-status
          (apply 'call-process
           coq-compiler nil coq-compile-response-buffer t coqc-arguments))
    (if coq-debug-auto-compilation
        (message "compilation %s exited with %s, output |%s|"
                 src-file coqc-status
                 (with-current-buffer coq-compile-response-buffer
                   (buffer-string))))
    (unless (eq coqc-status 0)
      (coq-display-compile-response-buffer)
      (let ((terminated-text (if (numberp coqc-status)
                                 "terminated with exit status"
                               "was terminated by signal")))
        (error "ERROR: Recompiling coq library %s %s %s"
               src-file terminated-text coqc-status)))))

(defun coq-compile-library-if-necessary (max-dep-obj-time src obj)
  "Recompile SRC to OBJ if necessary.
This function compiles SRC to the coq library object file OBJ
if one of the following conditions is true:
- a dependency has just been compiled
- OBJ does not exist
- SRC is newer than OBJ
- OBJ is older than the the youngest object file of the dependencies.

Argument MAX-DEP-OBJ-TIME provides the information about the
dependencies. It is either
- 'just-compiled if one of the dependencies of SRC has just
  been compiled
- the time value (see`time-less-or-equal') of the youngest (most
  recently created) object file among the dependencies
- nil if there are no dependencies, or if they are all ignored

If this function decides to compile SRC to OBJ it returns
'just-compiled. Otherwise it returns the modification time of
OBJ.

Note that file modification times inside Emacs have only a
precisision of 1 second. To avoid spurious recompilations we do
not recompile if the youngest object file of the dependencies and
OBJ have identical modification times."
  (let (src-time obj-time)
    (if (eq max-dep-obj-time 'just-compiled)
        (progn
          (coq-compile-library src)
          'just-compiled)
      (setq src-time (nth 5 (file-attributes src)))
      (setq obj-time (nth 5 (file-attributes obj)))
      (if (or
           (not obj-time)                     ; obj does not exist
           (time-less-or-equal obj-time src-time) ; src is newer
           (and
            max-dep-obj-time            ; there is a youngest dependency
                                        ; which is newer than obj
            (time-less-p obj-time max-dep-obj-time)))
          (progn
            (coq-compile-library src)
            'just-compiled)
        (if coq-debug-auto-compilation
            (message "Skip compilation of %s" src))
        obj-time))))

(defun coq-make-lib-up-to-date (coq-obj-hash span lib-obj-file)
  "Make library object file LIB-OBJ-FILE up-to-date.
Check if LIB-OBJ-FILE and all it dependencies are up-to-date
compiled coq library objects. Recompile the necessary objects, if
not. This function returns 'just-compiled if it compiled
LIB-OBJ-FILE. Otherwise it returns the modification time of
LIB-OBJ-FILE as time value (see `time-less-or-equal').

Either LIB-OBJ-FILE or its source file (or both) must exist when
entering this function.

Argument SPAN is the span of the \"Require\" command.
LIB-OBJ-FILE and its dependencies are locked and registered in
the span for for proper unlocking on retract.

Argument COQ-OBJ-HASH remembers the return values of this
function."
  (let ((result (gethash lib-obj-file coq-obj-hash)))
    (if result
        (progn
          (if coq-debug-auto-compilation
              (message "Checked %s already" lib-obj-file))
          result)
      ;; lib-obj-file has not been checked -- do it now
      (message "Check %s" lib-obj-file)
      (if (coq-compile-ignore-file lib-obj-file)
          ;; return minimal time for ignored files
          (setq result '(0 0))
        (let* ((lib-src-file
                (expand-file-name (coq-library-src-of-obj-file lib-obj-file)))
               dependencies deps-mod-time)
          (if (file-exists-p lib-src-file)
              ;; recurse into dependencies now
              (progn
                (setq dependencies (coq-get-library-dependencies lib-src-file))
                (if (stringp dependencies)
                    (error "File %s has %s" lib-src-file dependencies))
                (setq deps-mod-time
                      (mapcar
                       (lambda (dep)
                         (coq-make-lib-up-to-date coq-obj-hash span dep))
                       dependencies))
                (setq result
                      (coq-compile-library-if-necessary
                       (coq-max-dep-mod-time deps-mod-time)
                       lib-src-file lib-obj-file)))
            (message "coq-auto-compile: no source file for %s" lib-obj-file)
            (setq result
                  ;; 5 value: last modification time
                  (nth 5 (file-attributes lib-obj-file))))
          (coq-lock-ancestor span lib-src-file)))
      ;; at this point the result value has been determined
      ;; store it in the hash then
      (puthash lib-obj-file result coq-obj-hash)
      result)))

(defun coq-auto-compile-externally (span qualified-id absolute-module-obj-file)
  "Make MODULE up-to-date according to `coq-compile-command'.
Start a compilation to make ABSOLUTE-MODULE-OBJ-FILE up-to-date.
The compilation command is derived from `coq-compile-command' by
substituting certain keys, see `coq-compile-command' for details.
If `coq-confirm-external-compilation' is t then the user
must confirm the external command in the minibuffer, otherwise
the command is executed without confirmation.

Argument SPAN is the span of the \"Require\" command. The
ancestor ABSOLUTE-MODULE-OBJ-FILE is locked and registered in the
span for for proper unlocking on retract.

This function uses the low-level interface `compilation-start',
therefore the customizations for `compile' do not apply."
  (unless (coq-compile-ignore-file absolute-module-obj-file)
    (let* ((local-compile-command coq-compile-command)
           (physical-dir (file-name-directory absolute-module-obj-file))
           (module-object (file-name-nondirectory absolute-module-obj-file))
           (module-source (coq-library-src-of-obj-file module-object))
           (requiring-file buffer-file-name))
      (mapc
       (lambda (substitution)
         (setq local-compile-command
               (replace-regexp-in-string
                (car substitution) (eval (car (cdr substitution)))
                local-compile-command)))
       coq-compile-substitution-list)
      (if coq-confirm-external-compilation
          (setq local-compile-command
                (read-shell-command
                 "Coq compile command: " local-compile-command
                 (if (equal (car coq-compile-history) local-compile-command)
                     '(coq-compile-history . 1)
                   'coq-compile-history))))
      ;; buffers have already been saved before we entered this function
      ;; the next line is probably necessary to make recompile work
      (setq-default compilation-directory default-directory)
      (compilation-start local-compile-command)
      (coq-lock-ancestor
       span
       (coq-library-src-of-obj-file absolute-module-obj-file)))))

(defun coq-map-module-id-to-obj-file (module-id span)
  "Map MODULE-ID to the appropriate coq object file.
The mapping depends of course on `coq-load-path'. The current
implementation invokes coqdep with a one-line require command.
This is probably slower but much simpler than modelling coq file
loading inside ProofGeneral. Argument SPAN is only used for error
handling. It provides the location information of MODULE-ID for a
decent error message.

A peculiar consequence of the current implementation is that this
function returns () if MODULE-ID comes from the standard library."
  (let ((coq-load-path
         (if coq-load-path-include-current
             (cons default-directory coq-load-path)
           coq-load-path))
        (coq-load-path-include-current nil)
        (temp-require-file (make-temp-file "ProofGeneral-coq" nil ".v"))
        (coq-string (concat "Require " module-id "."))
        result)
    (unwind-protect
        (progn
          (with-temp-file temp-require-file
            (insert coq-string))
          (setq result
                (coq-get-library-dependencies
                 temp-require-file
                 (concat "echo \"" coq-string "\" > " temp-require-file))))
      (delete-file temp-require-file))
    (if (stringp result)
        ;; Error handling: coq-get-library-dependencies was not able to
        ;; translate module-id into a file name. We insert now a faked error
        ;; message into coq-compile-response-buffer to make next-error happy.
        (let ((error-message
               (format "Cannot find library %s in loadpath" module-id))
              (inhibit-read-only t))
          ;; Writing a message into coq-compile-response-buffer for next-error
          ;; does currently not work. We do have exact position information
          ;; about the span, but we don't know how much white space there is
          ;; between the start of the span and the start of the command string.
          ;; Check that coq-compile-response-buffer is a valid buffer!
          ;; (with-current-buffer coq-compile-response-buffer
          ;;   (insert
          ;;    (format "File \"%s\", line %d\n%s.\n"
          ;;            (buffer-file-name (span-buffer span))
          ;;            (with-current-buffer (span-buffer span)
          ;;              (line-number-at-pos (span-start span)))
          ;;            error-message)))
          ;; (coq-display-compile-response-buffer)
          (error error-message)))
    (assert (<= (length result) 1)
            "Internal error in coq-map-module-id-to-obj-file")
    (car-safe result)))

(defun coq-check-module (coq-object-local-hash-symbol span module-id)
  "Locate MODULE-ID and compile if necessary.
If `coq-compile-command' is not nil the whole task of checking which
modules need compilation and the compilation itself is done by an external
process. If `coq-compile-command' is nil ProofGeneral computes the
dependencies with \"coqdep\" and compiles modules as necessary. This internal
checking does currently not handle ML modules.

Argument SPAN is the span of the \"Require\" command. Locked
ancestors are registered in its 'coq-locked-ancestors property
for proper unlocking on retract.

Argument COQ-OBJECT-LOCAL-HASH-SYMBOL provides a place to store
the coq-obj-hash, which is used during internal
compilation (see `coq-make-lib-up-to-date'). This way one hash
will be used for all \"Require\" commands added at once to the
queue."
  (let ((module-obj-file (coq-map-module-id-to-obj-file module-id span)))
    ;; coq-map-module-id-to-obj-file currently returns () for
    ;; standard library modules!
    (when module-obj-file
      (if (> (length coq-compile-command) 0)
          (coq-auto-compile-externally span module-id module-obj-file)
        (unless (symbol-value coq-object-local-hash-symbol)
          (set coq-object-local-hash-symbol (make-hash-table :test 'equal)))
        (coq-make-lib-up-to-date (symbol-value coq-object-local-hash-symbol)
                                 span module-obj-file)))))

(defvar coq-process-require-current-buffer
  "Used in `coq-compile-save-some-buffers' and `coq-compile-save-buffer-filter'.
This only locally used variable communicates the current buffer
from `coq-compile-save-some-buffers' to
`coq-compile-save-buffer-filter'.")

(defun coq-compile-save-buffer-filter ()
  "Filter predicate for `coq-compile-save-some-buffers'.
See also `save-some-buffers'. Returns t for buffers with major mode
'coq-mode' different from coq-process-require-current-buffer and nil
for all other buffers. The buffer to test must be current."
  (and
   (eq major-mode 'coq-mode)
   (not (eq coq-process-require-current-buffer
            (current-buffer)))))
  
(defun coq-compile-save-some-buffers ()
  "Save buffers according to `coq-compile-auto-save'.
Uses the local variable coq-process-require-current-buffer to pass the
current buffer (which contains the Require command) to
`coq-compile-save-buffer-filter'."
  (let ((coq-process-require-current-buffer (current-buffer))
        unconditionally buffer-filter)
    (cond
     ((eq coq-compile-auto-save 'ask-coq)
      (setq unconditionally nil
            buffer-filter 'coq-compile-save-buffer-filter))
     ((eq coq-compile-auto-save 'ask-all)
      (setq unconditionally nil
            buffer-filter nil))
     ((eq coq-compile-auto-save 'save-coq)
      (setq unconditionally t
            buffer-filter 'coq-compile-save-buffer-filter))
     ((eq coq-compile-auto-save 'save-all)
      (setq unconditionally t
            buffer-filter nil)))
    (save-some-buffers unconditionally buffer-filter)))

(defun coq-preprocess-require-commands ()
  "Coq function for `proof-shell-extend-queue-hook'.
If `coq-compile-before-require' is non-nil, this function performs the
compilation (if necessary) of the dependencies."
  (if coq-compile-before-require
      (let (;; coq-object-hash-symbol serves as a pointer to the
            ;; coq-obj-hash (see coq-make-lib-up-to-date). The hash
            ;; will be initialized when needed and stored in the value
            ;; cell of coq-object-hash-symbol. The symbol is initialized
            ;; here to use one hash for all the requires that are added now.
            (coq-object-hash-symbol nil)
            string)
        (dolist (item queueitems)
          (let ((string (mapconcat 'identity (nth 1 item) " ")))
            (when (and string
                       (string-match coq-require-command-regexp string))
              (let ((span (car item))
                    (start (match-end 0)))
                (span-add-delete-action
                 span
                 `(lambda ()
                    (coq-unlock-all-ancestors-of-span ,span)))
                (coq-compile-save-some-buffers)
                ;; now process all required modules
                (while (string-match coq-require-id-regexp string start)
                  (setq start (match-end 0))
                  (coq-check-module 'coq-object-hash-symbol span
                                    (match-string 1 string))))))))))

(add-hook 'proof-shell-extend-queue-hook 'coq-preprocess-require-commands)

;; kill coqtop on script buffer change

(defun coq-switch-buffer-kill-proof-shell ()
  "Kill the proof shell without asking the user.
This function is for `proof-deactivate-scripting-hook'. It kills
the proof shell without asking the user for
confirmation (assuming she agreed already on switching the active
scripting buffer). This is needed to ensure the load path is
correct in the new scripting buffer."
  (unless proof-shell-exit-in-progress
    (proof-shell-exit t)))


(add-hook 'proof-deactivate-scripting-hook
          'coq-switch-buffer-kill-proof-shell
          t)



(provide 'coq-seq-compile)



;;   Local Variables: ***
;;   coding: utf-8 ***
;;   End: ***

;;; coq-seq-compile.el ends here
