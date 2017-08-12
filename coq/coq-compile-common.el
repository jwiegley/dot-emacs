;;; coq-compile-common.el --- common part of compilation feature

;; This file is part of Proof General.

;; Portions © Copyright 1994-2012  David Aspinall and University of Edinburgh
;; Portions © Copyright 2003, 2012, 2014  Free Software Foundation, Inc.
;; Portions © Copyright 2001-2017  Pierre Courtieu
;; Portions © Copyright 2010, 2016  Erik Martin-Dorel
;; Portions © Copyright 2011-2013, 2016-2017  Hendrik Tews
;; Portions © Copyright 2015-2017  Clément Pit-Claudel

;; Authors: Hendrik Tews
;; Maintainer: Hendrik Tews <hendrik@askra.de>

;; License:     GPL (GNU GENERAL PUBLIC LICENSE)

;;; Commentary:
;;
;; This file holds constants, options and some general functions for
;; the compilation feature.
;;

;;; Code:

(require 'proof-shell)
(require 'coq-system)
(require 'compile)

(eval-when-compile
  ;;(defvar coq-pre-v85 nil)
  (defvar coq-confirm-external-compilation); defpacustom
  (defvar coq-compile-parallel-in-background)) ; defpacustom

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Multiple file handling -- sequential compilation of required modules
;;

;;; enable / disable parallel / sequential compilation
;; I would rather put these functions into coq-seq-compile and
;; coq-par-compile, respectively. However, the :initialization
;; function of a defcustom seems to be evaluated when reading the
;; defcustom form. Therefore, these functions must be defined already,
;; when the defcustom coq-compile-parallel-in-background is read.

(defun coq-par-enable ()
  "Enable parallel compilation.
Must be used together with `coq-seq-disable'."
  (add-hook 'proof-shell-extend-queue-hook
	    'coq-par-preprocess-require-commands)
  (add-hook 'proof-shell-signal-interrupt-hook
	    'coq-par-user-interrupt)
  (add-hook 'proof-shell-handle-error-or-interrupt-hook
	    'coq-par-user-interrupt))

(defun coq-par-disable ()
  "Disable parallel compilation.
Must be used together with `coq-seq-enable'."
  (remove-hook 'proof-shell-extend-queue-hook
	       'coq-par-preprocess-require-commands)
  (remove-hook 'proof-shell-signal-interrupt-hook
	       'coq-par-user-interrupt)
  (remove-hook 'proof-shell-handle-error-or-interrupt-hook
	       'coq-par-user-interrupt))

(defun coq-seq-enable ()
  "Enable sequential synchronous compilation.
Must be used together with `coq-par-disable'."
  (add-hook 'proof-shell-extend-queue-hook
	    'coq-seq-preprocess-require-commands))

(defun coq-seq-disable ()
  "Disable sequential synchronous compilation.
Must be used together with `coq-par-enable'."
  (remove-hook 'proof-shell-extend-queue-hook
	       'coq-seq-preprocess-require-commands))



(defun coq-switch-compilation-method ()
  "Set function for coq-compile-parallel-in-background."
  (if coq-compile-parallel-in-background
      (progn
	(coq-par-enable)
	(coq-seq-disable))
    (coq-par-disable)
    (coq-seq-enable)))

(defun number-of-cpus ()
  (let (status ncpus)
    (condition-case nil
	(with-temp-buffer
	  (setq status
		(call-process "getconf" nil (current-buffer) t 
			      "_NPROCESSORS_ONLN"))
	  (setq ncpus (string-to-number (buffer-string))))
      (error
       (setq status -1)))
    (if (and (eq status 0) (> ncpus 0))
	ncpus
      nil)))

(defvar coq--max-background-vio2vo-percentage-shadow 40
  "Internal shadow value of `coq-max-background-vio2vo-percentage'.
This variable does always contain the same value as
`coq-max-background-vio2vo-percentage'. It is used only to break
the dependency cycle between `coq-set-max-vio2vo-jobs' and
`coq-max-background-vio2vo-percentage'.")

(defvar coq--internal-max-vio2vo-jobs 1
  "Internal number of vio2vo jobs.
This is the internal value, use
`coq-max-background-vio2vo-percentage' to configure.")

(defvar coq--internal-max-jobs 1
  "Value of `coq-max-background-compilation-jobs' translated to a number.")

(defun coq-set-max-vio2vo-jobs ()
  "Set `coq--internal-max-vio2vo-jobs'."
  (setq coq--internal-max-vio2vo-jobs
	(max 1
	     (round (* coq--internal-max-jobs
		       coq--max-background-vio2vo-percentage-shadow
		       0.01)))))

(defun coq-max-vio2vo-setter (symbol new-value)
  ":set function for `coq-max-background-vio2vo-percentage'.
SYMBOL should be 'coq-max-background-vio2vo-percentage"
  (set symbol new-value)
  (setq coq--max-background-vio2vo-percentage-shadow new-value)
  (coq-set-max-vio2vo-jobs))

(defun coq-max-jobs-setter (symbol new-value)
  ":set function for `coq-max-background-compilation-jobs'.
SYMBOL should be 'coq-max-background-compilation-jobs"
  (set symbol new-value)
  (cond
   ((eq new-value 'all-cpus)
    (setq new-value (number-of-cpus))
    (unless new-value
      (setq new-value 1)))
   ((and (integerp new-value) (> new-value 0)) t)
   (t (setq new-value 1)))
  (setq coq--internal-max-jobs new-value)
  (coq-set-max-vio2vo-jobs))

(defun coq-compile-quick-setter (symbol new-value)
  ":set function for `coq-compile-quick' for pre 8.5 compatibility.
Ignore any quick setting for Coq versions before 8.5."
  (cond
   ((or (eq new-value 'ensure-vo) (eq new-value 'no-quick))
    t)
   ((coq--pre-v85)
    (message "Ignore coq-compile-quick setting %s for Coq before 8.5"
	     new-value)
    (setq new-value 'no-quick)))
  (set symbol new-value))


;;; user options and variables

(defgroup coq-auto-compile ()
  "Customization for automatic compilation of required files"
  :group 'coq
  :package-version '(ProofGeneral . "4.1"))

(defcustom coq-compile-before-require nil
  "If non-nil, check dependencies of required modules and compile if necessary.
If non-nil ProofGeneral intercepts \"Require\" commands and checks if the
required library module and its dependencies are up-to-date. If not, they
are compiled from the sources before the \"Require\" command is processed.

This option can be set/reset via menu
`Coq -> Auto Compilation -> Compile Before Require'."
  :type 'boolean
  :safe 'booleanp
  :group 'coq-auto-compile)

(proof-deftoggle coq-compile-before-require)

(defcustom coq-compile-parallel-in-background nil
  "Choose the internal compilation method.
When Proof General compiles itself, you have the choice between
two implementations. If this setting is nil, then Proof General
uses the old implementation and compiles everything sequentially
with synchronous job. With this old method Proof General is
locked during compilation. If this setting is t, then the new
method is used and compilation jobs are dispatched in parallel in
the background. The maximal number of parallel compilation jobs
is set with `coq-max-background-compilation-jobs'.

This option can be set/reset via menu
`Coq -> Auto Compilation -> Compile Parallel In Background'."
  :type 'boolean
  :safe 'booleanp
  :group 'coq-auto-compile)

(proof-deftoggle coq-compile-parallel-in-background)

(defun coq-compile-parallel-in-background ()
  (coq-switch-compilation-method))

;; defpacustom fails to call :eval during inititialization, see trac #456
(coq-switch-compilation-method)

(defcustom coq-compile-quick 'no-quick
  "Control quick compilation, vio2vo and vio/vo files auto compilation.
This option controls whether ``-quick'' is used for parallel
background compilation and whether up-date .vo or .vio files are
used or deleted. Please use the customization system to change
this option to ensure that any ``-quick'' setting is ignored for
Coq before 8.5.

Note that ``-quick'' can be noticebly slower when your sources do
not declare section variables with ``Proof using''. Note that
even if you do declare section variables, ``-quick'' is typically
slower on small files.

Use the default `no-quick', if you have not yet switched to
``Proof using''. Use `quick-no-vio2vo', if you want quick
recompilation without producing .vo files. Value
`quick-and-vio2vo' updates missing prerequisites with ``-quick''
and starts vio2vo conversion on a subset of the availables
cores (see `coq-compile-vio2vo-percentage') when the quick
recompilation finished (but see below for a .vio .vo
incompatibility caveat). Note that all the previously described
modes might load .vio files and that you therefore might not
notice certain universe inconsistencies. Finally, use `ensure-vo'
for only importing .vo files with complete universe checks.

Detailed description of the 4 modes:

no-quick         Compile outdated prerequisites without ``-quick'',
                 producing .vo files, but don't compile prerequisites
                 for which an up-to-date .vio file exists. Delete
                 or overwrite outdated .vo files.

quick-no-vio2vo  Compile outdated prerequisites with ``-quick'',
                 producing .vio files, but don't compile prerequisites
                 for which an up-to-date .vo file exists. Delete
                 or overwrite outdated .vio files.

quick-and-vio2vo Same as `quick-no-vio2vo', but start vio2vo processes
                 after the last ``Require'' command has been processed
                 to convert the vio dependencies into vo files. With this
                 mode you might see asynchronous errors from vio2vo
                 compilation while you are processing stuff far below the
                 last require. vio2vo compilation is done on a subset of
                 the available cores, see `coq-compile-vio2vo-percentage'.
                 When `coq-compile-keep-going' is set, vio2vo compilation
                 is scheduled for those files for which coqc compilation
                 was successful.

                 Warning: This mode does only work when you process require
                 commands in batches. Slowly single-stepping through require's
                 might lead to inconsistency errors when loading some
                 libraries, see Coq issue #5223.

ensure-vo        Ensure that all library dependencies are present as .vo
                 files and delete outdated .vio files or .vio files that
                 are more recent than the corresponding .vo file. This
                 setting is the only one that ensures soundness.

This option can be set via menu
`Coq -> Auto Compilation -> Quick compilation'."
  :type
  '(radio
    (const :tag "don't use -quick but accept existing vio files" no-quick)
    (const :tag "use -quick, don't do vio2vo" quick-no-vio2vo)
    (const :tag "use -quick and do vio2vo" quick-and-vio2vo)
    (const :tag "ensure vo compilation, delete vio files" ensure-vo))
  :safe (lambda (v) (member v '(no-quick quick-no-vio2vo
					 quick-and-vio2vo ensure-vo)))
  :set 'coq-compile-quick-setter
  :group 'coq-auto-compile)

(defun coq-compile-prefer-quick ()
  "Return t if a .vio file would be prefered."
  (or
   (eq coq-compile-quick 'quick-no-vio2vo)
   (eq coq-compile-quick 'quick-and-vio2vo)))

(defcustom coq-compile-keep-going t
  "Continue compilation after the first error as far as possible.
Similar to ``make -k'', with this option enabled, the background
compilation continues after the first error as far as possible.
With this option disabled, background compilation is
immediately stopped after the first error.

This option can be set/reset via menu
`Coq -> Auto Compilation -> Keep going'.")

;; define coq-compile-keep-going-toggle
(proof-deftoggle coq-compile-keep-going)

(defcustom coq-max-background-compilation-jobs 'all-cpus
  "Maximal number of parallel jobs, if parallel compilation is enabled.
Use the number of available CPU cores if this is set to
'all-cpus. This variable is the user setting. The value that is
really used is `coq--internal-max-jobs'. Use `coq-max-jobs-setter'
or the customization system to change this variable. Otherwise
your change will have no effect, because `coq--internal-max-jobs'
is not adapted."
  :type '(choice (const :tag "use all CPU cores" all-cpus)
		 (integer :tag "fixed number" :value 1))
  :safe (lambda (v) (or (eq v 'all-cpus) (and (integerp v) (> v 0))))
  :set 'coq-max-jobs-setter
  :group 'coq-auto-compile)

(defcustom coq-max-background-vio2vo-percentage 40
  "Percentage of `coq-max-background-vio2vo-percentage' for vio2vo jobs.
This setting configures the maximal number of vio2vo background
jobs (if you set `coq-compile-quick' to 'quick-and-vio2vo) as
percentage of `coq-max-background-compilation-jobs'."
  :type 'number
  :safe 'numberp
  :set 'coq-max-vio2vo-setter
  :group 'coq-auto-compile)

(defcustom coq-compile-vio2vo-delay 2.5
  "Delay in seconds for the vio2vo compilation.
This delay helps to avoid running into a library inconsistency
with 'quick-and-vio2vo, see Coq issue #5223."
  :type 'number
  :safe 'numberp
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
confirmation.

This option can be set via menu
`Coq -> Auto Compilation -> Auto Save'."
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
locked when the \"Require\" command is processed.

This option can be set via menu
`Coq -> Auto Compilation -> Lock Ancestors'."

  :type 'boolean
  :safe 'booleanp
  :group 'coq-auto-compile)

;; define coq-lock-ancestors-toggle
(proof-deftoggle coq-lock-ancestors)

(defcustom coq-confirm-external-compilation t
  "If set let user change and confirm the compilation command.
Otherwise start the external compilation without confirmation.

This option can be set/reset via menu
`Coq -> Auto Compilation -> Confirm External Compilation'."
  :type 'boolean
  :group 'coq-auto-compile)


(defcustom coq-compile-ignored-directories nil
  "Directories in which ProofGeneral should not compile modules.
List of regular expressions for directories in which ProofGeneral
should not compile modules. If a library file name matches one
of the regular expressions in this list then ProofGeneral does
neither compile this file nor check its dependencies for
compilation. It makes sense to include non-standard coq library
directories here if they are not changed and if they are so big
that dependency checking takes noticeable time. The regular
expressions in here are always matched against the .vo file name,
regardless whether ``-quick'' would be used to compile the file
or not."
  :type '(repeat regexp)
  :safe (lambda (v) (every 'stringp v))
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


(defconst coq-require-id-regexp
  "[ \t\n]*\\([A-Za-z0-9_']+\\(\\.[A-Za-z0-9_']+\\)*\\)[ \t\n]*"
  "Regular expression matching one Coq module identifier.
Should match precisely one complete module identifier and surrounding
white space. The module identifier must be matched with group number 1.
Note that the trailing dot in \"Require A.\" is not part of the module
identifier and should therefore not be matched by this regexp.")

(defconst coq-require-command-regexp
  (concat "^\\(?:From[ \t\n]+\\(?1:[A-Za-z0-9_']+\\(?:\\.[A-Za-z0-9_']+\\)*\\)"
	  "[ \t\n]*\\)?"
	  "\\(?2:Require[ \t\n]+\\(?:Import\\|Export\\)?\\)[ \t\n]*")
  "Regular expression matching Require commands in Coq.
Should match \"Require\" with its import and export variants up to (but not
including) the first character of the first required module. The required
modules are matched separately with `coq-require-id-regexp'")

(defvar coq-compile-history nil
  "History of external Coq compilation commands.")

(defvar coq--compile-response-buffer "*coq-compile-response*"
  "Name of the buffer to display error messages from coqc and coqdep.")

(defvar coq--debug-auto-compilation nil
  "*Display more messages during compilation")


;;; basic utilities

(defun time-less-or-equal (time-1 time-2)
  "Return `t' if time value time-1 is earlier or equal to time-2.
A time value is a list of two, three or four integers of the
form (high low micro pico) as returned by `file-attributes' or
'current-time'. First element high contains the upper 16 bits and
the second low the lower 16 bits of the time."
  (not (time-less-p time-2 time-1)))

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


;;; ignore library files

(defun coq-compile-ignore-file (lib-obj-file)
  "Check whether ProofGeneral should handle compilation of LIB-OBJ-FILE.
Return `t' if ProofGeneral should skip LIB-OBJ-FILE and `nil' if
ProofGeneral should handle the file. For normal users it does,
for instance, not make sense to let ProofGeneral check if the coq
standard library is up-to-date. This function is always invoked
on the .vo file name, regardless whether the file would be
compiled with ``-quick'' or not."
  (if (some
       (lambda (dir-regexp) (string-match dir-regexp lib-obj-file))
       coq-compile-ignored-directories)
      (progn
	(when coq--debug-auto-compilation
	  (message "Ignore %s" lib-obj-file))
	t)
    nil))

;;; convert .vo files to .v files and module names

(defun coq-module-of-src-file (src-file)
  "Return the module name for SRC-FILE.
SRC-FILE must be a .v file."
  (let ((file (file-name-nondirectory src-file)))
  (substring file 0 (max 0 (- (length file) 2)))))

(defun coq-library-src-of-vo-file (lib-obj-file)
  "Return source file name for LIB-OBJ-FILE.
Chops off the last character of LIB-OBJ-FILE to convert \"x.vo\" to \"x.v\"."
  (substring lib-obj-file 0 (- (length lib-obj-file) 1)))

(defun coq-library-vio-of-vo-file (vo-obj-file)
  "Return .vio file name for VO-OBJ-FILE.
Changes the suffix from .vio to .vo. VO-OBJ-FILE must have a .vo suffix."
  (concat (coq-library-src-of-vo-file vo-obj-file) "io"))


;;; ancestor unlocking
;;; (locking is different for sequential and parallel compilation)

(defun coq-unlock-ancestor (ancestor-src)
  "Unlock ANCESTOR-SRC."
  (let* ((default-directory
	   (buffer-local-value 'default-directory
			       (or proof-script-buffer (current-buffer))))
	 (true-ancestor (file-truename ancestor-src)))
    (setq proof-included-files-list
          (delete true-ancestor proof-included-files-list))
    (proof-restart-buffers (proof-files-to-buffers (list true-ancestor)))))

(defun coq-unlock-all-ancestors-of-span (span)
  "Unlock all ancestors that have been locked when SPAN was asserted."
  (mapc 'coq-unlock-ancestor (span-property span 'coq-locked-ancestors))
  (span-set-property span 'coq-locked-ancestors ()))


;;; manage coq--compile-response-buffer

(defun coq-compile-display-error (command error-message display)
  "Display COMMAND and ERROR-MESSAGE in `coq--compile-response-buffer'.
If needed, reinitialize `coq--compile-response-buffer'. Then
display COMMAND and ERROR-MESSAGE."
  (unless (buffer-live-p (get-buffer coq--compile-response-buffer))
    (coq-init-compile-response-buffer))
  (let ((inhibit-read-only t)
	(deactivate-mark nil))
    (with-current-buffer coq--compile-response-buffer
      (save-excursion
	(goto-char (point-max))
	(insert command "\n" error-message "\n"))))
  (when display
    (coq-display-compile-response-buffer)))

(defun coq-init-compile-response-buffer (&optional command)
  "Initialize the buffer for the compilation output.
If `coq--compile-response-buffer' exists, empty it. Otherwise
create a buffer with name `coq--compile-response-buffer', put
it into `compilation-mode' and store it in
`coq--compile-response-buffer' for later use. Argument COMMAND is
the command whose output will appear in the buffer."
  (let ((buffer-object (get-buffer coq--compile-response-buffer)))
    (if buffer-object
        (let ((inhibit-read-only t))
          (with-current-buffer buffer-object
            (erase-buffer)))
      (setq buffer-object
            (get-buffer-create coq--compile-response-buffer))
      (with-current-buffer buffer-object
        (compilation-mode)
	;; read-only-mode makes compilation fail if some messages need
	;; to be displayed by compilation. there was a bug in emacs 23
	;; which make it work some time without this, but now it seems
	;; mandatory:
	(read-only-mode 0)))
    ;; I don't really care if somebody gets the right mode when
    ;; he saves and reloads this buffer. However, error messages in
    ;; the first line are not found for some reason ...
    (let ((inhibit-read-only t))
      (with-current-buffer buffer-object
        (insert "-*- mode: compilation; -*-\n\n")
	(when command
	  (insert command "\n"))))))

(defun coq-display-compile-response-buffer ()
  "Display the errors in `coq--compile-response-buffer'."
  (with-current-buffer coq--compile-response-buffer
    ;; fontification enables the error messages
    (let ((font-lock-verbose nil)) ; shut up font-lock messages
      (font-lock-fontify-buffer)))
  ;; Make it so the next C-x ` will use this buffer.
  (setq next-error-last-buffer (get-buffer coq--compile-response-buffer))
  (proof-display-and-keep-buffer coq--compile-response-buffer 1 t)
  ;; Partial fix for #54: ensure that the compilation response
  ;; buffer is not in a dedicated window.
  (mapc (lambda (w) (set-window-dedicated-p w nil))
      (get-buffer-window-list coq--compile-response-buffer nil t)))


;;; enable next-error to find vio2vo errors
;;
;; compilation-error-regexp-alist-alist is an alist mapping symbols to
;; what is expected for compilation-error-regexp-alist. This is
;; element of the form (REGEXP FILE [LINE COLUMN TYPE HYPERLINK
;; HIGHLIGHT...]). If REGEXP matches, the FILE'th subexpression gives
;; the file name, and the LINE'th subexpression gives the line number.
;; The COLUMN'th subexpression gives the column number on that line,
;; see the documentation of compilation-error-regexp-alist.
;;
;; Need to wrap adding the vio2vo error regex in eval-after-load,
;; because compile is loaded on demand and might not be present when
;; the user visits the first Coq file.

(eval-after-load 'compile
  '(progn
     (push
      '(coq-vio2vo
	"File \\(.*\\): proof of [^:]*\\(: chars \\([0-9]*\\)-\\([0-9]*\\)\\)?"
	1 nil 3)
      compilation-error-regexp-alist-alist)
     (push 'coq-vio2vo compilation-error-regexp-alist)))


;;; save some buffers

(defvar coq-compile-buffer-with-current-require
  "Local variable for two coq-seq-* functions.
This only locally used variable communicates the current buffer
from `coq-compile-save-some-buffers' to
`coq-compile-save-buffer-filter'.")

(defun coq-compile-save-buffer-filter ()
  "Filter predicate for `coq-compile-save-some-buffers'.
See also `save-some-buffers'. Returns t for buffers with major
mode 'coq-mode' different from
`coq-compile-buffer-with-current-require' and nil for all other
buffers. The buffer to test must be current."
  (and
   (eq major-mode 'coq-mode)
   (not (eq coq-compile-buffer-with-current-require
            (current-buffer)))))
  
(defun coq-compile-save-some-buffers ()
  "Save buffers according to `coq-compile-auto-save'.
Uses the local variable coq-compile-buffer-with-current-require to pass the
current buffer (which contains the Require command) to
`coq-compile-save-buffer-filter'."
  (let ((coq-compile-buffer-with-current-require (current-buffer))
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


;;; kill coqtop on script buffer change

(defun coq-switch-buffer-kill-proof-shell ()
  "Kill the proof shell without asking the user.
This function is for `proof-deactivate-scripting-hook'. It kills
the proof shell without asking the user for
confirmation (assuming she agreed already on switching the active
scripting buffer). This is needed to ensure the load path is
correct in the new scripting buffer."
  (unless proof-shell-exit-in-progress
    (proof-shell-exit t)))

;; This is now always done (in coq.el)
;(add-hook 'proof-deactivate-scripting-hook
;          'coq-switch-buffer-kill-proof-shell
;          t)


(provide 'coq-compile-common)

;;   Local Variables: ***
;;   coding: utf-8 ***
;;   End: ***

;;; coq-compile-common.el ends here
