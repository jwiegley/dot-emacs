;; coq-par-compile.el --- parallel compilation of required modules
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
;; compilation is done in parallel in the background (in contrast to
;; what you find in coq-seq-compile.el).
;;
;;
;;; TODO
;;
;; - fix -I current-dir argument for coqc invocations
;; - add option coq-par-keep-compilation-going
;; - check what happens if coq-par-coq-arguments gets a bad load path
;; - on error, try to put location info into the error message
;; 

(eval-when-compile
  (require 'proof-compat))

(eval-when (compile)
  (defvar queueitems nil)       ; dynamic scope in p-s-extend-queue-hook
  (defvar coq-compile-before-require nil)       ; defpacustom
  (defvar coq-compile-parallel-in-background nil) ; defpacustom
  (defvar coq-confirm-external-compilation nil)); defpacustom

(require 'coq-compile-common)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Multiple file handling -- parallel compilation of required modules
;;

;; This file implements parallel background compilation. It makes sure
;; that only a certain number (`coq-max-background-compilation-jobs')
;; of coqdep anc coqc processes are running in the background.
;;
;; In this file, compilation jobs are uninterned lisp symbols that
;; store all important information in their property list. New
;; compilation jobs are created when Require commands are parsed and
;; when the output of coqdep is processed. If there is space, new jobs
;; are directly launched. Otherwise, they are put into a queue
;; (`coq-par-compilation-queue') to be launched when some other
;; process terminates.
;;
;; Dependencies between files are reflected with suitable links. They
;; are established when the coqdep output is processed. A job with
;; dependencies waits for the dependencies to finish before it
;; continues with coqc.
;; 
;; It is pretty clear how to process these compilation jobs. The
;; problems are:
;;
;; 1- where to put the Require command and the items that follow it
;; 2- make sure ancestors are properly locked
;; 3- error reporting
;;
;; For 1- where to put the Require command and the items that follow it:
;;
;; The Require command and the items that follow cannot stay in
;; proof-action-list, as otherwise they would be sent to the prover
;; long before the compilation finishes. I therefore cut
;; proof-action-list into pieces and leave only the items before the
;; first Require on proof-action-list. The others are put into the
;; 'queueitems property of the top level compilation job. When this
;; job finishes, it puts the items back into proof-action-list and
;; lets Proof General process them as usual.
;;
;; When one Require command lists several modules or if there are
;; several Require commands, every required module gets its own
;; top-level compilation job and the queue items are stored with the
;; last module from each Require command. All these top-level
;; compilation jobs have so-called queue-depencency links between
;; them. These links ensure that a top-level module puts its items
;; back into proof-action-list only if all top-level jobs of those
;; modules that are required before it are finished.
;;
;; A problem occurs with "Require b a.", where b depends on a. To
;; avoid cycles in the dependency graph, here the top-level
;; compilation job for "a" will be a so-called clone of the real
;; compilation job. The Require item is stored with the clone. The
;; real job has dependency links to all its clones. Every clone waits
;; until its real job has finished.
;;
;; For 2- make sure ancestors are properly locked:
;;
;; The problem is "Require b. Require a.", where b depends on a. Here,
;; file a.v will be locked when the dependency b -> a is not known yet
;; to Proof General. Nevertheless, a.v must be associated with the
;; first Require command. Otherwise, a.v would be wrongly unlocked,
;; when only "Require a." is retracted.
;;
;; The problem is solved with the 'coq-locked-ancestors property of
;; spans that contain Require commands and with the
;; coq-par-ancestor-files hash. Ancestors in the 'coq-locked-ancestors
;; property are unlocked when this span is retracted. As locking is
;; done eagerly (as soon as coqdep runs first on the file), I only
;; have to make sure the right files appear in 'coq-locked-ancestors.
;;
;; Ancestor files accumulate in compilation jobs when the compilation
;; walks upwards the dependency tree. In the end, every top-level job
;; contains a list of all its direct and indirect ancestors. Because
;; of eager locking, all its ancestors are already locked, when a
;; top-level job is about to be retired. The coq-par-ancestor-files
;; hash therefore records whether some ancestor does already appear in
;; the 'coq-locked-ancestors property of some span before the current
;; one. If it doesn't, I store it in the current span.
;;
;; For 3- error reporting:
;;
;; For now, all compilation jobs are killed on the first error. All
;; items that are not yet asserted are retract. This is done with
;; signalling an error and calling `coq-par-emergency-cleanup' in the
;; sentinel, if there was an error.
;;
;; 
;; Properties of compilation jobs
;;
;;   'name            - some unique string, only used for debugging
;;   'queueitems      - holds items from proof-action-list on
;;                      top-level jobs
;;   'obj-file        - the .vo that this job has to make up-to-date
;;   'obj-mod-time    - modification time of the .vo file, stored
;;                      here, to avoid double stat calls;
;;                      contains 'obj-does-not-exist in case .vo is absent
;;   'type            - the type of the job, either 'clone or 'file
;;                      for real compilation jobs
;;   'state           - the state of the job, see below
;;   'coqc-dependants - list of parent jobs that depend on this job
;;                      when this job finishes it propagates the
;;                      necessary information to it's parent jobs and
;;                      decreases their 'coqc-dependency-count
;;   'coqc-dependency-count - number of unfinished child jobs
;;                            increased for every subjob spawned
;;                            during coqdep output processing
;;                            This job waits with coqc until this
;;                            count reaches 0 again
;;   'youngest-coqc-dependency - slot to accumulate the most recent
;;                               modification time of some ancestor
;;                               value might be an Emacs time or
;;                               'just-compiled
;;   'queue-dependant - next top-level job, only present in top-level jobs 
;;   'queue-dependant-waiting - t if this is a top-level job that has
;;                              to wait until previous top-level jobs
;;                              finish. In this waiting time, modules
;;                              are compiled, but queue items are only
;;                              put back into proof-action-list when
;;                              this property becomes nil
;;   'src-file        - the .v file name
;;   'load-path       - value of coq-load-path, propagated to all
;;                      dependencies 
;;   'ancestor-files  - list of ancestors, including the source file
;;                      of this job
;;   'require-span    - present for top-level jobs only, there it
;;                      contains the span that must finally store the
;;                      ancestors
;;   'visited         - used in the dependency cycle detection to mark
;;                      visited jobs
;;
;; 
;; State transition of real compilation jobs
;;
;;     'enqueued-coqdep -> 'waiting-dep -> 'enqueued-coqc
;;                      -> 'waiting-queue -> 'ready
;;
;;   'enqueued-coqdep - coqdep is running or the job enqueued, waiting
;;                      for a slot to start coqdep
;;   'waiting-dep     - the job is waiting for all Coq dependencies to
;;                      finish
;;   'enqueued-coqc   - coqc is running, or the job is enqueued,
;;                      waiting for a slot to start coqc
;;   'waiting-queue   - the job is waiting until all top-level queue
;;                      dependencies finish (if there are any)
;;   'ready           - ready
;;
;;
;; State transition for clone jobs
;; 
;;     'waiting-dep -> 'waiting-queue -> 'ready
;;
;;   'waiting-dep   - the clone is waiting until the real job finishes
;;   'waiting-queue - the job is waiting until all top-level queue
;;                    dependencies finish
;;   'ready         - ready
;;
;;
;; 
;; Properties of processes
;;
;; A lot of the necessary actions are started from inside a process
;; sentinel. The property list of processes stores the necessary
;; information for that in the following properties.
;;
;;   'coq-compilation-job       - the compilation job that started
;;                                this process
;;   'coq-process-continuation  - the continuation to be called when
;;                                the process finishes. Either
;;                                coq-par-process-coqdep-result or
;;                                coq-par-coqc-continuation 
;;   'coq-process-output        - the output of the process
;;   'coq-process-command       - the command for error reporting
;;                                (as string list) 
;;   'coq-par-process-killed    - t if this process has been killed
;;
;;
;; Symbols in the coq-par-ancestor-files hash
;;
;; This hash maps file names to symbols. A file is present in the
;; hash, if it has been locked.
;;
;;   'locked   - the file is not yet stored in the
;;               'coq-locked-ancestors property of some span
;;   'asserted - the file has been stored in some span
;;
;;
;; To print the states of the compilation jobs for debugging, eval
;; 
;; (let ((clones))
;;   (maphash (lambda (k v)
;; 	     (message "%s type %s for %s state %s dep of %s queue dep of %s"
;; 		      (get v 'name)
;; 		      (get v 'type)
;; 		      (get v 'src-file)
;; 		      (get v 'state)
;; 		      (mapcar (lambda (p) (get p 'name)) 
;; 			      (get v 'coqc-dependants))
;; 		      (get v 'queue-dependant))
;; 	     (mapc (lambda (p) (when (eq (get p 'type) 'clone)
;; 				 (push p clones)))
;; 		   (get v 'coqc-dependants)))
;; 	   coq-compilation-object-hash)
;;   (mapc (lambda (v)
;; 	  (message "%s type %s for %s state %s dep of %s queue dep of %s"
;; 		   (get v 'name)
;; 		   (get v 'type)
;; 		   (get v 'src-file)
;; 		   (get v 'state)
;; 		   (mapcar (lambda (p) (get p 'name)) 
;; 			   (get v 'coqc-dependants))
;; 		   (get v 'queue-dependant)))
;; 	clones))

;;; Variables

(defvar coq-par-ancestor-files nil
  "Hash remembering the state of locked ancestor files.
This hash maps true file names (in the sense of `file-truename')
to either 'locked or 'asserted.

'locked means that this ancestor file has been locked
already (because it appeared in the dependency tree somewhere and
coqdep has been started on it) but has not been assigned to the
'coq-locked-ancestors property of some span. That is, 'locked
ancestors are not an ancestor of any required module in the
asserted region.

'asserted means that this ancestor is the ancestor of some
asserted required module (and is in some 'coq-locked-ancestors
property).")

(defvar coq-current-background-jobs 0
  "Number of currently running background jobs.")

(defvar coq-compilation-object-hash nil
  "Hash for storing the compilation jobs.
The hash will only store real compilation jobs and no clones.
They are stored in order to avoid double compilation. The jobs
stored in here are uninterned symbols that carry all important
information in their property list. See the documentation in the
source file \"coq-par-compile.el\"")

(defvar coq-last-compilation-job nil
  "Pointer to the last top-level compilation job.
Used to link top-level jobs with queue dependencies.")

(defvar coq-par-next-id 1
  "Increased for every job and process, to get unique job names.
The names are only used for debugging.")


;;; utility functions

(defun split-list-at-predicate (l pred)
  "Split L into several lists at points where PRED is t.
Splits L into several lists, such that
- their concatenation equals the original L
- every element for which PRED returns t starts a new list
- except for the first list, PRED is t for every car of every result list
- the first result list contains the first elements of L for which PRED is nil
L is modified in place and the list structure in L is reused for
the result."
  (let ((result (list l))
	previous
	(current l))
    (while current
      (when (funcall pred (car current))
	(if previous
	    (progn
	      (setcdr previous nil)
	      (push current result))
	  ;; handle case where pred is t for the car of the original l
	  (setq result (list l nil))))
      (setq previous current)
      (setq current (cdr current)))
    (nreverse result)))

(defun coq-par-time-less (time-1 time-2)
  "Compare extended times.
The arguments can be an emacs time (a list of 2 or 3 integers,
see `file-attributes') or the symbol 'just-compiled, where the
latter greater then everything else."
  (cond
   ((eq time-2 'just-compiled) t)
   ((eq time-1 'just-compiled) nil)
   (t (time-less-p time-1 time-2))))

(defun coq-par-init-compilation-hash ()
  "(Re-)Initialize `coq-compilation-object-hash'."
  (setq coq-compilation-object-hash (make-hash-table :test 'equal)))

(defun coq-par-init-ancestor-hash ()
  "(Re-)Initialize `coq-par-ancestor-files'"
  (setq coq-par-ancestor-files (make-hash-table :test 'equal))
  (mapc
   (lambda (locked-anc)
     (puthash locked-anc 'asserted coq-par-ancestor-files))
   proof-included-files-list))


;;; job queue

(defun coq-par-new-compilation-queue ()
  "Create a new empty queue for `coq-par-compilation-queue'"
  (cons nil nil))  

(defvar coq-par-compilation-queue (coq-par-new-compilation-queue)
  "Queue of compilation jobs with in and out end.
Use `coq-par-enqueue' and `coq-par-dequeue' to access the queue.")

(defun coq-par-enqueue (job)
  "Insert job in the queue of waiting compilation jobs."
  (push job (car coq-par-compilation-queue))
  (if coq-debug-auto-compilation
      (message "%s: enqueue job in waiting queue" (get job 'name))))

(defun coq-par-dequeue ()
  "Dequeue the next job from the compilation queue."
  (let ((res (pop (cdr coq-par-compilation-queue))))
    (unless res
      (setq coq-par-compilation-queue
	    (cons nil (nreverse (car coq-par-compilation-queue))))
      (setq res (pop (cdr coq-par-compilation-queue))))
    (if coq-debug-auto-compilation
	(if res
	    (message "%s: dequeue" (get res 'name))
	  (message "compilation queue empty")))
    res))


;;; error symbols

;; coq-compile-error-coqdep
;;
;; This error is signaled with one data item -- the file name

(put 'coq-compile-error-coqdep 'error-conditions
     '(error coq-compile-error coq-compile-error-coqdep))
(put 'coq-compile-error-coqdep 'error-message
     "Coq compilation error: coqdep fails in")

;; coq-compile-error-coqc
;;
;; This error is signaled with one data item -- the file name

(put 'coq-compile-error-coqc 'error-conditions
     '(error coq-compile-error coq-compile-error-coqc))
(put 'coq-compile-error-coqc 'error-message
     "Coq compilation error: coqc fails in")

;; coq-compile-error-command-start
;;
;; This error is signaled with two data items --
;; a list consisting of the command and the system error message,
;; the command itself is a string list of the command name and the options

(put 'coq-compile-error-command-start 'error-conditions
     '(error coq-compile-error coq-compile-error-command-start))
(put 'coq-compile-error-command-start 'error-message
     "Coq compilation error:")

;; coq-compile-error-circular-dep
;;
;; This error is signaled with one data item -- an indication about
;; the circularity, which is the error message to be appended to the
;; contents of 'error-message.

(put 'coq-compile-error-circular-dep 'error-conditions
     '(error coq-compile-error coq-compile-error-circular-dep))
(put 'coq-compile-error-circular-dep 'error-message
     "Coq compilation error: Circular dependency")


;;; find circular dependencies in non-ready compilation jobs

(defun coq-par-find-dependency-circle-for-job (job path)
  "Find a dependency cycle in the dependency subtree of JOB.
Do a depth-first-search to find the cycle. JOB is the current
node and PATH the stack of visited nodes."
  (let (cycle (p path))
    ;; path is reversed. A potential cycle goes from the beginning of
    ;; path to the first occurence of job.
    (while p
      (when (eq (car p) job)
	(setcdr p nil)
	(setq cycle path))
      (setq p (cdr p)))
    (if cycle
	cycle
      (setq path (cons job path))
      (setq p (get job 'coqc-dependants))
      (while (and p (not cycle))
	(when (eq (get (car p) 'state) 'waiting-dep)
	  (setq cycle (coq-par-find-dependency-circle-for-job (car p) path)))
	(setq p (cdr p)))
      (put job 'visited t)
      cycle)))

(defun coq-par-find-dependency-circle ()
  "Find a dependency cycle in compilation jobs of state 'waiting-dep.
If no circle is found return nil, otherwise the list of files
belonging to the circle."
  (let (cycle result)
    (maphash (lambda (key job) (put job 'visited nil))
	     coq-compilation-object-hash)
    (maphash
     (lambda (key job)
       (when (and (not cycle) (not (get job 'visited))
		  (eq (get job 'state) 'waiting-dep))
	 (setq cycle (coq-par-find-dependency-circle-for-job job nil))))
     coq-compilation-object-hash)
    (dolist (j cycle)
      (when (eq (get j 'type) 'file)
	(push (get j 'src-file) result)))
    (nreverse result)))


;;; map coq module names to files, using synchronously running coqdep 

(defun coq-par-coq-arguments (lib-src-file coq-load-path)
  "Compute the command line arguments for invoking coqdep on LIB-SRC-FILE.
Argument COQ-LOAD-PATH must be `coq-load-path' from the buffer
that triggered the compilation, in order to provide correct
load-path options to coqdep."
  (nconc (coq-include-options lib-src-file coq-load-path)
	 (list lib-src-file)))

(defun coq-par-analyse-coq-dep-exit (status output command)
  "Analyse output OUTPUT of coqdep command COMMAND with exit status STATUS.
Returns the list of dependencies if there is no error. Otherwise,
writes an error message into `coq-compile-response-buffer', makes
this buffer visible and returns a string."
  (if (or
       (not (eq status 0))
       (string-match coq-coqdep-error-regexp output))
      (progn
	;; display the error
	(coq-init-compile-response-buffer (mapconcat 'identity command " "))
	(let ((inhibit-read-only t))
	  (with-current-buffer coq-compile-response-buffer (insert output)))
	(coq-display-compile-response-buffer)
	"unsatisfied dependencies")
    (if (string-match ": \\(.*\\)$" output)
	(cdr-safe (split-string (match-string 1 output)))
      ())))

(defun coq-par-get-library-dependencies (lib-src-file coq-load-path
						      &optional command-intro)
  "Compute dependencies of LIB-SRC-FILE.
Invoke \"coqdep\" on LIB-SRC-FILE and parse the output to
compute the compiled coq library object files on which
LIB-SRC-FILE depends. The return value is either a string or a
list. If it is a string then an error occurred and the string is
the core of the error message. If the return value is a list no
error occurred and the returned list is the (possibly empty) list
of file names LIB-SRC-FILE depends on.

Argument COQ-LOAD-PATH must be `coq-load-path' from the buffer
that triggered the compilation, in order to provide correct
load-path options to coqdep.

If an error occurs this funtion displays
`coq-compile-response-buffer' with the complete command and its
output. The optional argument COMMAND-INTRO is only used in the
error case. It is prepended to the displayed command.

LIB-SRC-FILE should be an absolute file name. If it is, the
dependencies are absolute too and the simplified treatment of
`coq-load-path-include-current' in `coq-include-options' won't
break."
  (let* ((coqdep-arguments
	  (coq-par-coq-arguments lib-src-file coq-load-path))
	 (this-command (cons coq-dependency-analyzer coqdep-arguments))
	 (full-command (if command-intro
			   (cons command-intro this-command)
			 this-command))
	 coqdep-status coqdep-output)
    ;; (if coq-debug-auto-compilation
    ;;     (message "call coqdep arg list: %s" coqdep-arguments))
    (with-temp-buffer
      (setq coqdep-status
            (apply 'call-process
                   coq-dependency-analyzer nil (current-buffer) nil
                   coqdep-arguments))
      (setq coqdep-output (buffer-string)))
    ;; (if coq-debug-auto-compilation
    ;;     (message "coqdep status %s, output on %s: %s"
    ;;              coqdep-status lib-src-file coqdep-output))
    (coq-par-analyse-coq-dep-exit coqdep-status coqdep-output full-command)))

(defun coq-par-map-module-id-to-obj-file (module-id coq-load-path)
  "Map MODULE-ID to the appropriate coq object file.
The mapping depends of course on `coq-load-path'. The current
implementation invokes coqdep with a one-line require command.
This is probably slower but much simpler than modelling coq file
loading inside ProofGeneral. Argument SPAN is only used for error
handling. It provides the location information of MODULE-ID for a
decent error message. Argument COQ-LOAD-PATH must be
`coq-load-path' from the buffer that triggered the compilation,
in order to provide correct load-path options to coqdep.

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
                (coq-par-get-library-dependencies
                 temp-require-file
		 coq-load-path
                 (concat "echo \"" coq-string "\" > " temp-require-file))))
      (delete-file temp-require-file))
    (if (stringp result)
        ;; Error handling: coq-par-get-library-dependencies was not able to
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
          ;; (coq-seq-display-compile-response-buffer)
          (error error-message)))
    (assert (<= (length result) 1)
            "Internal error in coq-seq-map-module-id-to-obj-file")
    (car-safe result)))


;;; manage background jobs

(defun coq-par-kill-all-processes ()
  "Kill all background coqc and coqdep compilation processes."
  ;; need to first mark processes as killed, because delete process
  ;; starts running sentinels in the order processes terminated, so
  ;; after the first delete-process we see sentinentels of non-killed
  ;; processes running
  (let ((kill-needed))
    (mapc
     (lambda (process)
       (when (process-get process 'coq-compilation-job)
	 (process-put process 'coq-par-process-killed t)
	 (setq kill-needed t)))
     (process-list))
    (when kill-needed
      (message "Kill all Coq background compilation processes"))
    (mapc
     (lambda (process)
       (when (process-get process 'coq-compilation-job)
	 (process-put process 'coq-par-process-killed t)
	 (delete-process process)
	 (when coq-debug-auto-compilation
	   (message "%s %s: kill it"
		    (get (process-get process 'coq-compilation-job) 'name)
		    (process-name process)))))
     (process-list))
    (setq coq-current-background-jobs 0)))

(defun coq-par-unlock-ancestors-on-error ()
  "Unlock ancestors which are not in an asserted span.
Used for unlocking ancestors on compilation errors."
  (maphash
   (lambda (ancestor state)
     (when (eq state 'locked)
       (coq-unlock-ancestor ancestor)
       (puthash ancestor nil coq-par-ancestor-files)))
   coq-par-ancestor-files))

(defun coq-par-emergency-cleanup ()
  "Emergency cleanup for parallel background compilation.
Kills all processes, unlocks ancestors, clears the queue region
and resets the internal state."
  (coq-par-kill-all-processes)
  (setq coq-par-compilation-queue (coq-par-new-compilation-queue))
  (setq coq-last-compilation-job nil)
  (when proof-action-list
    (setq proof-shell-interrupt-pending t))
  (coq-par-unlock-ancestors-on-error)
  (proof-release-lock)
  (proof-detach-queue)
  (setq proof-second-action-list-active nil)
  (coq-par-init-compilation-hash))

(defun coq-par-process-filter (process output)
  "Store output from coq background compilation."
  (process-put process 'coq-process-output
	       (concat (process-get process 'coq-process-output) output)))

(defun coq-par-start-process (command arguments continuation job)
  "Start asynchronous compilation job for COMMAND.
This function starts COMMAND with arguments ARGUMENTS for
compilation job JOB, making sure that CONTINUATION runs when the
process finishes successfully."
  (let ((process-connection-type nil)	; use pipes
	(process-name (format "pro-%s" coq-par-next-id))
	process)
    (with-current-buffer (or proof-script-buffer (current-buffer))
      (if coq-debug-auto-compilation
	  (message "%s %s: start %s %s"
		   (get job 'name) process-name
		   command (mapconcat 'identity arguments " ")))
      (condition-case err
	  ;; If the command is wrong, start-process aborts with an
	  ;; error. However, in Emacs 23.4.1. it will leave a process
	  ;; behind, which is in a very strange state: running with no
	  ;; pid. Emacs 24.2 fixes this.
	  (setq process (apply 'start-process process-name
			       nil	; no process buffer
			       command arguments))
	(error
	 (signal 'coq-compile-error-command-start
		 (list (cons command arguments) (nth 2 err)))))
      (set-process-filter process 'coq-par-process-filter)
      (set-process-sentinel process 'coq-par-process-sentinel)
      (set-process-query-on-exit-flag process nil)
      (setq coq-par-next-id (1+ coq-par-next-id))
      (setq coq-current-background-jobs (1+ coq-current-background-jobs))
      (process-put process 'coq-compilation-job job)
      (process-put process 'coq-process-continuation continuation)
      (process-put process 'coq-process-command (cons command arguments))
      (process-put process 'coq-process-output ""))))

(defun coq-par-process-sentinel (process event)
  "Sentinel for all background processes.
Runs when process PROCESS terminated because of EVENT. It
determines the exit status and calls the continuation function
that has been registered with that process. Normal compilation
errors are reported with an error message."
  (condition-case err
      (if (process-get process 'coq-par-process-killed)
	  (if coq-debug-auto-compilation
	      (message "%s %s: skip sentinel, process killed"
		       (get (process-get process 'coq-compilation-job) 'name)
		       (process-name process)))
	(let (exit-status)
	  (if coq-debug-auto-compilation
	      (message "%s %s: process status changed to %s"
		       (get (process-get process 'coq-compilation-job) 'name)
		       (process-name process)
		       event))
	  (cond
	   ((eq (process-status process) 'exit)
	    (setq exit-status (process-exit-status process)))
	   (t (setq exit-status "abnormal termination")))
	  (setq coq-current-background-jobs
		(max 0 (1- coq-current-background-jobs)))
	  (funcall (process-get process 'coq-process-continuation)
		   process exit-status)
	  (coq-par-start-jobs-until-full)
	  (when (and
		 (eq coq-current-background-jobs 0)
		 coq-last-compilation-job)
	    (let ((cycle (coq-par-find-dependency-circle)))
	      (if cycle
		  (signal 'coq-compile-error-circular-dep
			  (mapconcat 'identity cycle " -> "))
		(error "deadlock in parallel compilation"))))))
    (coq-compile-error-command-start
     (coq-par-emergency-cleanup)
     (message "%s \"%s\" in \"%s\""
	      (get (car err) 'error-message)
	      (nth 2 err) (mapconcat 'identity (cadr err) " ")))
    (coq-compile-error
     (coq-par-emergency-cleanup)
     (message "%s %s" (get (car err) 'error-message) (cdr err)))
    (error
     (message "error in sentinel of process %s, error %s"
	      (process-name process) err)
     (coq-par-emergency-cleanup)
     (signal (car err) (cdr err)))))


;;; background job tasks

(defun coq-par-job-is-ready (job)
  "t if compilation job JOB is ready."
  (eq (get job 'state) 'ready))

(defun coq-par-dependencies-ready (job)
  "t if all dependencies of compilation job JOB are ready."
  (eq (get job 'coqc-dependency-count) 0))

(defun coq-par-add-coqc-dependency (dependee dependant)
  "Add normal Coq dependency from child job DEPENDEE to parent job DEPENDANT."
  (put dependant 'coqc-dependency-count
       (1+ (get dependant 'coqc-dependency-count)))
  (push dependant (get dependee 'coqc-dependants))
  (if coq-debug-auto-compilation
      (message "%s -> %s: add coqc dependency"
	       (get dependee 'name) (get dependant 'name))))

(defun coq-par-add-queue-dependency (dependee dependant)
  "Add queue dependency from child job DEPENDEE to parent job DEPENDANT."
  (assert (and (not (get dependant 'queue-dependant-waiting))
	       (not (get dependee 'queue-dependant))))
  (put dependant 'queue-dependant-waiting t)
  (put dependee 'queue-dependant dependant)
  (if coq-debug-auto-compilation
      (message "%s -> %s: add queue dependency"
	       (get dependee 'name) (get dependant 'name))))

(defun coq-par-get-obj-mod-time (job)
  "Return modification time of the object file as `file-attributes' would do.
Making sure that file-attributes is called at most once for every job."
  (let ((obj-time (get job 'obj-mod-time)))
    (cond
     ((consp obj-time) obj-time)
     ((eq obj-time 'obj-does-not-exist) nil)
     ((not obj-time)
      (setq obj-time (nth 5 (file-attributes (get job 'obj-file))))
      (if obj-time
	  (put job 'obj-mod-time obj-time)
	(put job 'obj-mod-time 'obj-does-not-exist))
      obj-time))))

(defun coq-par-job-needs-compilation (job)
  "Determine whether job needs to get compiled."
  (let (src-time obj-time)
    (if (eq (get job 'youngest-coqc-dependency) 'just-compiled)
	(progn
	  (if coq-debug-auto-compilation
	      (message "%s: needs compilation because a dep was just compiled"
		       (get job 'name)))
	  t)
      (setq src-time (nth 5 (file-attributes (get job 'src-file))))
      (setq obj-time (coq-par-get-obj-mod-time job))
      (if coq-debug-auto-compilation
      	  (message
      	   (concat "%s: compare mod times: obj mod %s, src mod %s, "
      		   "youngest dep %s; obj <= src : %s, obj < dep : %s")
      	   (get job 'name)
      	   (current-time-string obj-time)
      	   (current-time-string src-time)
      	   (current-time-string (get job 'youngest-coqc-dependency))
      	   (if obj-time (time-less-or-equal obj-time src-time) "-")
      	   (if obj-time
      	       (time-less-p obj-time (get job 'youngest-coqc-dependency))
      	     "-")))
      (or
       (not obj-time)				  ; obj does not exist
       (time-less-or-equal obj-time src-time)	  ; src is newer
					      ; youngest dep is newer than obj
       (time-less-p obj-time (get job 'youngest-coqc-dependency))))))

(defun coq-par-kickoff-queue-maybe (job)
  "Try transition 'waiting-queue -> 'ready for job JOB.
This transition is only possible if JOB is in state
'waiting-queue and if it has no queue dependee. If this is the
case, the following actions are taken:
- for top-level jobs (non-nil 'require-span property), ancestors
  are registered in `coq-par-ancestor-files' and in the span in
  'queue-span
- processing of items in 'queueitems is started
- a possible queue dependant gets it's dependency cleared, and,
  if possible the 'waiting-queue -> 'ready transition
  is (recursively) done for the dependant
- if this job is the last top-level compilation
  job (`coq-last-compilation-job') then the last compilation job
  and `proof-second-action-list-active' are cleared."
  (if (or (not (eq (get job 'state) 'waiting-queue))
	  (get job 'queue-dependant-waiting))
      (if coq-debug-auto-compilation
	  (if (not (eq (get job 'state) 'waiting-queue))
	      (message "%s: no queue kickoff because in state %s"
		       (get job 'name) (get job 'state))
	    (message
	     "%s: no queue kickoff because waiting for queue dependency"
	     (get job 'name))))
    (if coq-debug-auto-compilation
	(message "%s: has itself no queue dependency" (get job 'name)))
    (when (and (get job 'require-span) coq-lock-ancestors)
      (let ((span (get job 'require-span)))
	(dolist (f (get job 'ancestor-files))
	  (unless (eq (gethash f coq-par-ancestor-files) 'asserted)
	    (puthash f 'asserted coq-par-ancestor-files)
	    (span-set-property
	     span 'coq-locked-ancestors
	     (cons f (span-property span 'coq-locked-ancestors)))))))
    (when (get job 'queueitems)
      (proof-add-to-queue (get job 'queueitems) 'advancing)
      (if coq-debug-auto-compilation
	  (message "%s: add %s items to action list"
		   (get job 'name) (length (get job 'queueitems))))
      (put job 'queueitems nil))
    (put job 'state 'ready)
    (if coq-debug-auto-compilation
	(message "%s: ready" (get job 'name)))
    (let ((dependant (get job 'queue-dependant)))
      (if dependant
	  (progn
	    (assert (not (eq coq-last-compilation-job job)))
	    (put dependant 'queue-dependant-waiting nil)
	    (if coq-debug-auto-compilation
		(message
		 "%s -> %s: clear queue dependency, kickoff queue at %s"
		 (get job 'name) (get dependant 'name) (get dependant 'name)))
	    (coq-par-kickoff-queue-maybe dependant)
	    (if coq-debug-auto-compilation
		(message "%s: queue kickoff finished"
			 (get job 'name))))
	(when (eq coq-last-compilation-job job)
	  (setq coq-last-compilation-job nil)
	  (setq proof-second-action-list-active nil)
	  (if coq-debug-auto-compilation
	      (message "clear last compilation job")))
	(if coq-debug-auto-compilation
	    (message "%s: no queue dependant, queue kickoff finished"
		     (get job 'name)))))))

(defun coq-par-compile-job-maybe (job)
  "Choose next action for JOB after dependencies are ready.
First JOB is put into state 'enqueued-coqc. Then, if JOB needs
compilation, compilation is started or enqueued and JOB stays in
'enqueued-coqc for the time being. Otherwise, the transition
'enqueued-coqc -> 'waiting-queue is done and, if possible, also
'waiting-queue -> 'ready."
  (put job 'state 'enqueued-coqc)
  (if (coq-par-job-needs-compilation job)
      (coq-par-start-or-enqueue job)
    (if coq-debug-auto-compilation
	(message "%s: up-to-date, no compilation" (get job 'name)))
    (coq-par-kickoff-coqc-dependants job (get job 'youngest-coqc-dependency))))  

(defun coq-par-decrease-coqc-dependency (dependant dependee-time
						   dependee-ancestor-files)
  "Clear Coq dependency and update dependee information in DEPENDANT.
This function handles a Coq dependency from child dependee to
parent dependant when the dependee has finished compilation (ie.
is in state 'waiting-queue). DEPENDANT must be in state
'waiting-dep. The time of the most recent ancestor is updated, if
necessary using DEPENDEE-TIME. DEPENDEE-TIME must be an Emacs
time or 'just-compiled. The ancestors of dependee are propagated
to DEPENDANT. The dependency count of DEPENDANT is decreased and,
if it reaches 0, the next transition is triggered for DEPENDANT.
For 'file jobs this is 'waiting-dep -> 'enqueued-coqc and for
'clone jobs this 'waiting-dep -> 'waiting-queue."
  ;(message "%s: CPDCD with time %s" (get dependant 'name) dependee-time)
  (assert (eq (get dependant 'state) 'waiting-dep))
  (when (coq-par-time-less (get dependant 'youngest-coqc-dependency)
			   dependee-time)
    (put dependant 'youngest-coqc-dependency dependee-time))
  (put dependant 'ancestor-files
       (append dependee-ancestor-files (get dependant 'ancestor-files)))
  (put dependant 'coqc-dependency-count
       (1- (get dependant 'coqc-dependency-count)))
  (assert (<= 0 (get dependant 'coqc-dependency-count)))
  (if coq-debug-auto-compilation
      (message "%s: coqc dependency count down to %d"
	       (get dependant 'name) (get dependant 'coqc-dependency-count)))
  (when (coq-par-dependencies-ready dependant)
    (cond
     ((eq (get dependant 'type) 'file)
      (coq-par-compile-job-maybe dependant))
     ((eq (get dependant 'type) 'clone)
      (coq-par-kickoff-coqc-dependants
       dependant
       (get dependant 'youngest-coqc-dependency))))))

(defun coq-par-kickoff-coqc-dependants (job dep-time)
  "Handle transition to state 'waiting-queue for JOB.
For 'file jobs, this function is called when compilation finished
or was not necessary to make the transition 'enqueued-coqc ->
'waiting-queue. For 'clone jobs, this function is called when its
real 'file job has completed compilation and is in state
'waiting-queue to make the transition 'waiting-dep ->
waiting-queue for JOB.

DEP-TIME is either 'just-compiled, when JOB has just finished
compilation, or the most recent modification time of all
dependencies of JOB.

This function makes the following actions.
- Clear the dependency from JOB to all its dependants, thereby
  propagating the ancestors of JOB and the maximum of DEP-TIME
  and the modification time of the .vo of JOB.
- put JOB into state 'waiting-queue
- try to trigger the transition 'waiting-queue -> ready for JOB"
  (let ((ancestor-files (get job 'ancestor-files)))
    (if coq-debug-auto-compilation
	(message "%s: kickoff %d coqc dependencies with time %s"
		 (get job 'name) (length (get job 'coqc-dependants)) dep-time))
    ;; take max of dep-time and obj-mod-time
    ;; 
    ;; dep-time is either 'just-compiled or 'youngest-coqc-dependency of
    ;; the dependee, in the latter case obj-mod-time is greater than
    ;; dep-time, because otherwise we would have compiled the file. For
    ;; a clone job the max has already been taken when processing the
    ;; original file.
    (unless (or (eq dep-time 'just-compiled) (eq (get job 'type) 'clone))
      (setq dep-time (coq-par-get-obj-mod-time job)))
    (put job 'state 'waiting-queue)
    (mapc
     (lambda (dependant)
       (coq-par-decrease-coqc-dependency dependant dep-time ancestor-files))
     (get job 'coqc-dependants))
    (if coq-debug-auto-compilation
	(message "%s: coqc kickoff finished, maybe kickoff queue"
		 (get job 'name)))
    (coq-par-kickoff-queue-maybe job)))

(defun coq-par-start-coqdep (job)
  "Start coqdep for JOB.
Besides starting the background process, the source file is
locked, registered in the 'ancestor-files property of JOB and in
`coq-par-ancestor-files'"
  (let ((true-src (file-truename (get job 'src-file))))
    (when coq-lock-ancestors
      (proof-register-possibly-new-processed-file true-src)
      (put job 'ancestor-files (list true-src))
      (unless (gethash true-src coq-par-ancestor-files)
	(puthash true-src 'locked coq-par-ancestor-files)))
    (coq-par-start-process
     coq-dependency-analyzer
     (coq-par-coq-arguments (get job 'src-file) (get job 'load-path))
     'coq-par-process-coqdep-result
     job)))

(defun coq-par-start-task (job)
  "Start the background job for which JOB is waiting.
JOB was at the head of the compilation queue and now either
coqdep or coqc are started for it."
  (let ((job-state (get job 'state)))
    (cond
     ((eq job-state 'enqueued-coqdep)
      (coq-par-start-coqdep job))
     ((eq job-state 'enqueued-coqc)
      (message "Recompile %s" (get job 'src-file))
      (coq-par-start-process
       coq-compiler
       (coq-par-coq-arguments (get job 'src-file) (get job 'load-path))
       'coq-par-coqc-continuation
       job)))))

(defun coq-par-start-jobs-until-full ()
  "Start background jobs until the limit is reached."
  (let ((next-job t))
    (while (and next-job
		(< coq-current-background-jobs coq-internal-max-jobs))
      (setq next-job (coq-par-dequeue))
      (when next-job
	(coq-par-start-task next-job)))))
  
(defun coq-par-start-or-enqueue (new-job)
  "Start NEW-JOB or put it into the queue of waiting jobs.
NEW-JOB goes already into the waiting queue, if the number of
background jobs is one below the limit. This is in order to leave
room for Proof General."
  (if (< (1+ coq-current-background-jobs) coq-internal-max-jobs)
      (coq-par-start-task new-job)
    (coq-par-enqueue new-job)))

(defun coq-par-create-library-job (module-obj-file coq-load-path queue-dep
						   require-span dependant)
  "Create a new compilation job for MODULE-OBJ-FILE.
If there is already a job for MODULE-OBJ-FILE a new clone job is
created. This function initializes all necessary properties of
the new job.

COQ-LOAD-PATH must be the load path from the source file that
originally initiated the compilation. QUEUE-DEP must be a
compilation job or nil. If non-nil, this function makes a queue
dependency from QUEUE-DEP to the new compilation job. If nil, a
newly created clone job will proceed to state ready if the
original job is ready. Argument REQUIRE-SPAN should be present
when the new job should update the ancestor list in some span.
Argument DEPENDANT tells who required MODULE-OBJ-FILE, this is
used only for the error message, in case MODULE-OBJ-FILE refers
to the current scriping buffer.

If the new job is a clone job, its state is
- 'waiting-dep if the original file job is not 'ready yet
- 'waiting-queue if the original file job is ready, but there is
  a queue dependency QUEUE-DEP (which cannot be ready yet)
- 'ready otherwise

If the new job is a 'file job it's state is 'enqueued-coqdep. If
there is space, coqdep is started immediately, otherwise the new
job is put into the compilation queue.

This function returns the newly created job."
  (let* ((orig-job (gethash module-obj-file coq-compilation-object-hash))
	 (new-job (make-symbol "coq-compile-job-symbol")))
    (put new-job 'name (format "job-%d" coq-par-next-id))
    (setq coq-par-next-id (1+ coq-par-next-id))
    (put new-job 'obj-file module-obj-file)
    (put new-job 'coqc-dependency-count 0)
    (put new-job 'require-span require-span)
    (if orig-job
	;; there is already a compilation job for module-obj-file
	(progn
	  (put new-job 'type 'clone)
	  (if coq-debug-auto-compilation
	      (message "%s: create %s compilation job for %s"
		       (get new-job 'name) (get new-job 'type) module-obj-file))
	  (when queue-dep
	    (coq-par-add-queue-dependency queue-dep new-job))
	  (if (coq-par-job-is-ready orig-job)
	      (progn
		(if queue-dep
		    (put new-job 'state 'waiting-queue)
		  (put new-job 'state 'ready))
		(put new-job 'youngest-coqc-dependency
		     (get orig-job 'youngest-coqc-dependency))
		(put new-job 'ancestor-files (get orig-job 'ancestor-files)))
	    (coq-par-add-coqc-dependency orig-job new-job)
	    (put new-job 'state 'waiting-dep)
	    (put new-job 'youngest-coqc-dependency '(0 0))))
      ;; there is no compilation for this file yet
      (put new-job 'type 'file)
      (put new-job 'state 'enqueued-coqdep)
      (put new-job 'src-file (coq-library-src-of-obj-file module-obj-file))
      (when (equal (get new-job 'src-file)
		   (buffer-file-name proof-script-buffer))
	(signal 'coq-compile-error-circular-dep
		(concat dependant " -> scripting buffer")))
      (message "Check %s" (get new-job 'src-file))
      (put new-job 'load-path coq-load-path)
      (put new-job 'youngest-coqc-dependency '(0 0))
      (puthash module-obj-file new-job coq-compilation-object-hash)
      (if coq-debug-auto-compilation
	  (message "%s: create %s compilation for %s"
		   (get new-job 'name) (get new-job 'type) module-obj-file))
      (when queue-dep
	(coq-par-add-queue-dependency queue-dep new-job))
      (coq-par-start-or-enqueue new-job))
    new-job))

(defun coq-par-process-coqdep-result (process exit-status)
  "Coqdep continuation function: Process coqdep output.
This function analyses the coqdep output of PROCESS and signals
an error if necessary. If there was no coqdep error, the
following actions are taken.
- the job that started PROCESS is put into sate 'waiting-dep
- a new job is created for every dependency. If this new job is
  not immediately ready, a Coq dependency is registered from the
  new job to the current job. For dependencies that are 'ready
  already, the most recent ancestor modification time is
  propagated.
- if there are no dependencies or all dependencies are ready
  already, the next transition to 'enqueued-coqc is triggered for
  the current job
- otherwise the current job is left alone until somebody
  decreases its dependency count to 0

The argument EXIT-STATUS must be the exit status of PROCESS, it
is directly passed to `coq-par-analyse-coq-dep-exit'."
  (let ((job (process-get process 'coq-compilation-job))
	(dependencies-or-error
	 (coq-par-analyse-coq-dep-exit
	  exit-status
	  (process-get process 'coq-process-output)
	  (process-get process 'coq-process-command)))
	job-max-time)
    (if (stringp dependencies-or-error)
	(signal 'coq-compile-error-coqdep (get job 'src-file))

      ;; no coqdep error -- work on dependencies
      (if coq-debug-auto-compilation
	  (message "%s: dependencies of %s are %s"
		   (get job 'name) (get job 'src-file) dependencies-or-error))
      (put job 'state 'waiting-dep)
      (setq job-max-time (get job 'youngest-coqc-dependency))
      (mapc
       (lambda (dep-obj-file)
	 (unless (coq-compile-ignore-file dep-obj-file)
	   (let* ((dep-job (coq-par-create-library-job dep-obj-file
						       (get job 'load-path)
						       nil nil
						       (get job 'src-file)))
		  (dep-time (get dep-job 'youngest-coqc-dependency)))
	     (when (coq-par-time-less job-max-time dep-time)
	       (setq job-max-time dep-time))
	     (unless (coq-par-job-is-ready dep-job)
	       (coq-par-add-coqc-dependency dep-job job)))))
       dependencies-or-error)
      (put job 'youngest-coqc-dependency job-max-time)
      (if (coq-par-dependencies-ready job)
	  (progn
	    (if coq-debug-auto-compilation
		(message "%s: coqc dependencies finished" (get job 'name)))
	    (coq-par-compile-job-maybe job))
	(if coq-debug-auto-compilation
	    (message "%s: wait for %d dependencies"
		     (get job 'name) (get job 'coqc-dependency-count)))))))

(defun coq-par-coqc-continuation (process exit-status)
  "Coqc Continuation function.
Signal an error, if coqc failed. Otherwise, trigger the
transition 'enqueued-coqc -> 'waiting-queue for the job behind
PROCESS."
  (if (eq exit-status 0)
      ;; coqc success
      (coq-par-kickoff-coqc-dependants
       (process-get process 'coq-compilation-job)
       'just-compiled)
    ;; coqc error
    (coq-init-compile-response-buffer
     (mapconcat 'identity (process-get process 'coq-process-command) " "))
    (let ((inhibit-read-only t))
      (with-current-buffer coq-compile-response-buffer
	(insert (process-get process 'coq-process-output))))
    (coq-display-compile-response-buffer)
    (signal 'coq-compile-error-coqc
	    (get (process-get process 'coq-compilation-job) 'src-file))))


;;; handle Require commands when queue is extended

(defun coq-par-handle-module (module-id span)
  "Handle compilation of module MODULE-ID.
This function translates MODULE-ID to a file name. If compilation
for this file is not ignored, a new top-level compilation job is
created. If there is a new top-level compilation job, it is saved
in `coq-last-compilation-job'.

This function must be evaluated with the buffer that triggered
the compilation as current, otherwise a wrong `coq-load-path'
might be used."
  (let ((module-obj-file
	 (coq-par-map-module-id-to-obj-file module-id coq-load-path))
	module-job)
    (if coq-debug-auto-compilation
        (message "check compilation for module %s from object file %s"
		 module-id module-obj-file))
    ;; coq-par-map-module-id-to-obj-file currently returns () for
    ;; standard library modules!
    (when (and module-obj-file
	       (not (coq-compile-ignore-file module-obj-file)))
      (setq module-job
	    (coq-par-create-library-job module-obj-file coq-load-path
					coq-last-compilation-job span
					"scripting buffer"))
      (setq coq-last-compilation-job module-job)
      (if coq-debug-auto-compilation
	  (message "%s: this job is the last compilation job now"
		   (get coq-last-compilation-job 'name))))))

(defun coq-par-handle-require-list (require-items)
  "Start compilation for the required modules in the car of REQUIRE-ITEMS.
REQUIRE-ITEMS is a list of queue items, eventually to be added to
`proof-action-list', that contains just one require command in
the first element. This function starts the compilation process
for all modules in this require command.

This function parses the Require command, translates module names
to file names and creates one top-level compilation job for each
required module that is not ignored (eg via
`coq-compile-ignored-directories'). Jobs are started immediately
if possible. The last such created job is remembered in
`coq-last-compilation-job'. The REQUIRE-ITEMS are attached to
this last top-level job or directly to proof-action-list, if
there is no last compilation job."
  (let* ((item (car require-items))
	 (string (mapconcat 'identity (nth 1 item) " "))
	 (span (car item))
	 start)
    ;; We know there is a require in string. But we have to match it
    ;; again in order to get the end position.
    (string-match coq-require-command-regexp string)
    (setq start (match-end 0))
    (span-add-delete-action
     span
     `(lambda ()
	(coq-unlock-all-ancestors-of-span ,span)))
    ;; add a compilation job for all required modules
    (while (string-match coq-require-id-regexp string start)
      (setq start (match-end 0))
      (coq-par-handle-module (match-string 1 string) span))
    ;; add the asserted items to the last compilation job
    (if coq-last-compilation-job
	(progn
	  (assert (not (coq-par-job-is-ready coq-last-compilation-job)))
	  (put coq-last-compilation-job 'queueitems require-items)
	  (if coq-debug-auto-compilation
	      (message "%s: attach %s items"
		       (get coq-last-compilation-job 'name)
		       (length require-items))))
      ;; or add them directly to queueitems if there is no compilation job
      (setq queueitems (nconc queueitems require-items))
      (if coq-debug-auto-compilation
	  (message "attach %s items to queueitems" (length require-items))))))


(defun coq-par-item-require-predicate (item)
  "Return t if ITEM contains a require command.
Predicate for `split-list-at-predicate', used to split the new
queue items at each Require command."
  (let ((string (mapconcat 'identity (nth 1 item) " ")))
    (and string
	 (string-match coq-require-command-regexp string))))


(defun coq-par-preprocess-require-commands-internal ()
  "Worker for `coq-par-preprocess-require-commands'.
This function does all the work for
`coq-par-preprocess-require-commands', except for error
reporting.

If `coq-compile-before-require' is non-nil, this function starts
the compilation (if necessary) of the dependencies
ansynchronously in parallel in the background.

If there is a last compilation job (`coq-last-compilation-job')
then the queue region is extended, while some background
compilation is still running. In this case I have to preserve the
internal state. Otherwise the hash of the compilation jobs and
the ancestor hash are initialized.

As next action the new queue items are splitted at each Require
command. The items before the first Require are appended to the
last compilation job or put back into proof-action-list. The
remaining batches of items that each start with a Require are
then processed by `coq-par-handle-require-list', which creates
top-level compilation jobs as necessary. Before processing the
first of these batches, buffers are saved with
`coq-compile-save-some-buffers'.

Finally, `proof-second-action-list-active' is set if I keep some
queue items because they have to wait for a compilation job. Then
the maximal number of background compilation jobs is started."
  (when coq-debug-auto-compilation
    (message "%d items were added to the queue, scan for require"
	     (length queueitems)))
  (unless coq-last-compilation-job
    (coq-par-init-compilation-hash)
    (coq-par-init-ancestor-hash))
  (let ((splitted-items
	 (split-list-at-predicate queueitems
				  'coq-par-item-require-predicate)))
    (if coq-last-compilation-job
	(progn
	  (put coq-last-compilation-job 'queueitems
	       (nconc (get coq-last-compilation-job 'queueitems)
		      (car splitted-items)))
	  (setq queueitems nil)
	  (message "attach first %s items to job %s"
		   (length (car splitted-items))
		   (get coq-last-compilation-job 'name)))
      (setq queueitems (car splitted-items))
      (if coq-debug-auto-compilation
	  (message "attach first %s items directly to queue"
		   (length (car splitted-items)))))
    ;; XXX handle external compilation here, compile everything
    ;; with one command, use compilation-finish-functions to get
    ;; notification
    (when (cdr splitted-items)
      ;; save buffers before invoking the first coqdep
      (coq-compile-save-some-buffers)
      (mapc (lambda (require-items)
	      (coq-par-handle-require-list require-items))
	    (cdr splitted-items)))
    (when coq-last-compilation-job
      (setq proof-second-action-list-active t))
    (coq-par-start-jobs-until-full)
    (if coq-debug-auto-compilation
	(if coq-last-compilation-job
	    (message "return control, waiting for background jobs")
	  (message "return control, no background jobs")))))

(defun coq-par-preprocess-require-commands ()
  "Coq function for `proof-shell-extend-queue-hook' doing parallel compilation.
If `coq-compile-before-require' is non-nil, this function starts
the compilation (if necessary) of the dependencies
ansynchronously in parallel in the background. This function only
does the error checking/reporting for
`coq-par-preprocess-require-commands-internal', which does all the work."
  (when coq-compile-before-require
    (condition-case err
	(coq-par-preprocess-require-commands-internal)
      (coq-compile-error
       (coq-par-emergency-cleanup)
       (message "%s %s" (get (car err) 'error-message) (cdr err)))
      (error
       (message "unexpected error during parallel compilation: %s"
		err)
       (coq-par-emergency-cleanup)
       (signal (car err) (cdr err))))))


(provide 'coq-par-compile)


;;   Local Variables: ***
;;   coding: utf-8 ***
;;   End: ***

;;; coq-par-compile.el ends here
