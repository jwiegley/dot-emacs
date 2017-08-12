;;; coq-par-compile.el --- parallel compilation of required modules

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
;; Note that all argument computations inherit `coq-autodetected-version': when
;; changing compilers, all compilation jobs must be terminated.  This is
;; consistent with the fact that the _CoqProject file is not reparsed.

;;; Code:

(eval-when-compile
  (require 'proof-compat))

(eval-when-compile
  (defvar queueitems))       ; dynamic scope in p-s-extend-queue-hook

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
;; 4- using -quick and the handling of .vo/.vio prerequisites
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
;; A problem occurs with "Require a. Require a.", where two different
;; action list pieces must be stored with the job for a. The solution
;; here is to clone the original job when it is needed more than one
;; time. This cloning is done in general and not only for top-level
;; jobs. So also when a.v and b.v both depend on c.v, the second
;; dependency link is managed by a clone of the job for c.v. Every
;; real job has dependency links to all its clones. All clones wait
;; until the original job has finished. (In retrospect it seems a
;; design without clone jobs might have been cleaner.)
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
;; spans that contain Require commands. Ancestors in the
;; 'coq-locked-ancestors property are unlocked when this span is
;; retracted. As locking is done eagerly (as soon as coqdep runs first
;; on the file), I only have to make sure the right files appear in
;; 'coq-locked-ancestors.
;;
;; Ancestors accumulate in compilation jobs when the compilation walks
;; upwards the dependency tree. In the end, every top-level job
;; contains a list of all its direct and indirect ancestors in its
;; 'ancestors property. Because of eager locking, all its ancestors
;; are already locked, when a top-level job is about to be retired.
;; Every job records in his 'locked propery whether the file
;; corresponding to this job has been registered in some
;; 'coq-locked-ancestors property already.
;;
;; For 3- error reporting:
;;
;; Depending on `coq-compile-keep-going' compilation can continue
;; after an error or stop immediately. For stopping immediately,
;; processing is aborted with a signal that eventually leads to
;; `coq-par-emergency-cleanup', which kills all compilation jobs,
;; retracts the queue region and resets all internal data.
;;
;; For `coq-compile-keep-going', the failing job and all dependants
;; are marked as 'failed. Queue dependants are marked with
;; 'queue-failed. These marked jobs continue with their normal state
;; transition, but omit certain steps (eg., running coqc). The first
;; tricky part is how to unlock ancestors. When marking jobs as
;; failed, their ancestors (and thereby also the files for the jobs
;; themselves) are unlocked, unless they are still participating in an
;; ongoing compilation. If a coqc compilation finishes and all
;; dependants are marked as failed, ancestors are also unlocked in the
;; same way. If a top-level job is marked as 'queue-failed, its
;; ancestors are unlocked when this job finishes coqc compilation.
;;
;; The second tricky part is how to delete the queue region. For that
;; the last top-level job is delayed until proof-action-list is empty.
;; Then the whole queue is deleted.
;;
;; For 4- using -quick and the handling of .vo/.vio prerequisites
;;
;; Coq accepts both .vo and .vio files for importing modules
;; regardless of it is running with -quick or not. However, it is
;; unclear which file is loaded when both, .vo and .vio, of a
;; dependency are present. Therefore I delete a .vio file when I
;; decide to rebuild a .vo file and vica versa. coqdep delivers
;; dependencies for both, .vio and .vo files. These dependencies are
;; identical for .vio and vo (last checked for coq trunk in October
;; 2016). For deciding whether prerequisites must be recompiled the
;; full path returned form coqdep is relevant. Because it seems odd to
;; store a full path without a .vo or .vio suffix I decided to always
;; store the .vo object file name in the 'vo-file property of
;; compilation jobs. Only when all dependencies are ready, in
;; `coq-par-job-needs-compilation' I decide whether to build a .vio or
;; .vo file and if already present .vo or .vio files must be deleted.
;; Only at that point the relevant property 'required-obj-file is set.
;;
;; 
;; Properties of compilation jobs
;;
;;   'name            - some unique string, only used for debugging
;;   'queueitems      - holds items from proof-action-list on
;;                      top-level jobs
;;   'vo-file         - the .vo file for the module that this job has
;;                      to make up-to-date. This slot is filled when the
;;                      job is created and independent of whether a .vio
;;                      or .vo file must be made up-to-date.
;;   'required-obj-file - contains the .vio or .vo to be produced or nil
;;                        if that has not yet been decided. Does also contain
;;                        nil if no file needs to be rebuild at all.
;;   'obj-mod-time    - modification time of 'required-obj-file, stored
;;                      here, to avoid double stat calls;
;;                      contains 'obj-does-not-exist in case that file is absent
;;   'use-quick       - t if `coq-par-job-needs-compilation' decided to use
;;                      -quick
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
;;   'ancestors       - list of ancestor jobs, for real compilation jobs
;;                      this list includes the job itself; may contain
;;                      duplicates
;;   'lock-state      - nil for clone jobs, 'unlocked if the file
;;                      corresponding to job is not locked, 'locked if that
;;                      file has been locked, 'asserted if it has been
;;                      registered in some span in the 'coq-locked-ancestors
;;                      property already
;;   'require-span    - present precisely for top-level jobs only, there it
;;                      contains the span that must finally store the
;;                      ancestors
;;   'vio2vo-needed   - t if a subsequent vio2vo process is required to
;;                      build the .vo file. Otherwiese nil.
;;   'failed          - t if coqdep or coqc for the job or one dependee failed.
;;   'queue-failed    - t if some direct or indirect queue dependee is
;;                      marked 'failed
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
;;   'waiting-queue   - coqc is finished and the job is waiting until
;;                      all top-level queue dependencies finish (if
;;                      there are any)
;;   'ready           - ready, the .vo file might be missing though
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
;;   'coq-process-rm            - if not nil, a file to be deleted when
;;                                the process is killed
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
;; 	   coq--compilation-object-hash)
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

(defvar coq--current-background-jobs 0
  "Number of currently running background jobs.")

(defvar coq--compilation-object-hash nil
  "Hash for storing the compilation jobs.
This hash only stores real compilation jobs and no clones. They
are stored in order to avoid double compilation. The jobs stored
in here are uninterned symbols that carry all important
information in their property list. See the documentation in the
source file \"coq-par-compile.el\". The hash always maps .vo file
names to compilation jobs, regardless of ``-quick''.")

(defvar coq--last-compilation-job nil
  "Pointer to the last top-level compilation job.
Used to link top-level jobs with queue dependencies.")

(defvar coq--compile-vio2vo-in-progress nil
  "Set to t iff vio2vo is running in background.")

(defvar coq--compile-vio2vo-delay-timer nil
  "Holds the timer for the vio2vo delay.")

(defvar coq--compile-vio2vo-start-id 0
  "Integer counter to detect races for `coq-par-require-processed'.
Assume compilation for the last top-level ``Require'' command
finishes but executing the ``Require'' takes so long that the
user can assert a next ``Require'' and that the second
compilation finishes before the first ``Require'' has been
processed. In this case there are two `coq-par-require-processed'
callbacks active, of which the first one must be ignored. For
each new callback this counter is incremented and when there is a
difference the call to `coq-par-require-processed' is ignored.")

(defvar coq--par-next-id 1
  "Increased for every job and process, to get unique job names.
The names are only used for debugging.")

(defvar coq--par-delayed-last-job nil
  "Inform the cycle detection that there is a delayed top-level job.
If t, there is a delayed top-level job (for which the compilation failed).")


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
  "(Re-)Initialize `coq--compilation-object-hash'."
  (setq coq--compilation-object-hash (make-hash-table :test 'equal)))

;;; generic queues
;; Standard implementation with two lists.

(defun coq-par-new-queue ()
  "Create a new empty queue."
  (cons nil nil))

(defun coq-par-enqueue (queue x)
  "Insert x in queue QUEUE."
  (push x (car queue)))

(defun coq-par-dequeue (queue)
  "Dequeue the next item from QUEUE."
  (let ((res (pop (cdr queue))))
    (unless res
      (setcdr queue (nreverse (car queue)))
      (setcar queue nil)
      (setq res (pop (cdr queue))))
    res))


;;; job queue

(defvar coq-par-compilation-queue (coq-par-new-queue)
  "Queue of compilation jobs that wait for a free core to get started.
Use `coq-par-job-enqueue' and `coq-par-job-dequeue' to access the
queue.")

(defun coq-par-job-enqueue (job)
  "Insert job in the queue of waiting compilation jobs."
  (coq-par-enqueue coq-par-compilation-queue job)
  (when coq--debug-auto-compilation
    (message "%s: enqueue job in waiting queue" (get job 'name))))

(defun coq-par-job-dequeue ()
  "Dequeue the next job from the compilation queue."
  (let ((res (coq-par-dequeue coq-par-compilation-queue)))
    (when coq--debug-auto-compilation
      (if res
	  (message "%s: dequeue" (get res 'name))
	(message "compilation queue empty")))
    res))


;;; vio2vo queue

(defvar coq-par-vio2vo-queue (coq-par-new-queue)
  "Queue of jobs that need a vio2vo process.
Use `coq-par-vio2vo-enqueue' and `coq-par-vio2vo-dequeue' to
access the queue.")

(defun coq-par-vio2vo-enqueue (job)
  "Insert JOB in the queue for vio2vo processing."
  (coq-par-enqueue coq-par-vio2vo-queue job)
  (when coq--debug-auto-compilation
    (message "%s: enqueue job in vio2vo queue" (get job 'name))))

(defun coq-par-vio2vo-dequeue ()
  "Dequeue the next job from the vio2vo queue."
  (let ((res (coq-par-dequeue coq-par-vio2vo-queue)))
    (when coq--debug-auto-compilation
      (if res
	  (message "%s: vio2vo dequeue" (get res 'name))
	(message "vio2vo queue empty")))
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

;; coq-compile-error-rm
;;
;; Signaled when we have to delete a .vio or .vo file for consistency and
;; that deletion fails.
;;
;; This error is signaled with one data item -- the file-error error
;; description. Its car is the error symbol `file-error' and the cdr are
;; the data items for this error. They seem to be a list of strings with
;; different parts of the error message.

(put 'coq-compile-error-rm 'error-conditions
     '(error coq-compile-error coq-compile-error-rm))
(put 'coq-compile-error-rm 'error-message
     "Cannot remove outdated file.")


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
	     coq--compilation-object-hash)
    (maphash
     (lambda (key job)
       (when (and (not cycle) (not (get job 'visited))
		  (eq (get job 'state) 'waiting-dep))
	 (setq cycle (coq-par-find-dependency-circle-for-job job nil))))
     coq--compilation-object-hash)
    (dolist (j cycle)
      (when (eq (get j 'type) 'file)
	(push (get j 'src-file) result)))
    (nreverse result)))


;;; map coq module names to files, using synchronously running coqdep

(defun coq-par-coqdep-arguments (lib-src-file coq-load-path)
  "Compute the command line arguments for invoking coqdep on LIB-SRC-FILE.
Argument COQ-LOAD-PATH must be `coq-load-path' from the buffer
that triggered the compilation, in order to provide correct
load-path options to coqdep."
  (nconc (coq-coqdep-prog-args coq-load-path (file-name-directory lib-src-file) (coq--pre-v85))
         (list lib-src-file)))

(defun coq-par-coqc-arguments (lib-src-file coq-load-path)
  "Compute the command line arguments for invoking coqc on LIB-SRC-FILE.
Argument COQ-LOAD-PATH must be `coq-load-path' from the buffer
that triggered the compilation, in order to provide correct
load-path options to coqdep."
  (nconc (coq-coqc-prog-args coq-load-path (file-name-directory lib-src-file) (coq--pre-v85))
         (list lib-src-file)))

(defun coq-par-analyse-coq-dep-exit (status output command)
  "Analyse output OUTPUT of coqdep command COMMAND with exit status STATUS.
Returns the list of .vo dependencies if there is no error. Otherwise,
writes an error message into `coq-compile-response-buffer', makes
this buffer visible and returns a string.

This function does always return .vo dependencies, regardless of the
value of `coq-compile-quick'. If necessary, the conversion into .vio
files must be done elsewhere."
  ;; (when coq--debug-auto-compilation
  ;;   (message "analyse coqdep output \"%s\"" output))
  (if (or
       (not (eq status 0))
       (string-match coq-coqdep-error-regexp output))
      (progn
	;; display the error
	(coq-compile-display-error (mapconcat 'identity command " ") output t)
	"unsatisfied dependencies")
    ;; In 8.5, coqdep produces two lines. Match with .* here to
    ;; extract only a part of the first line.
    ;; We could match against (concat "^[^:]*" obj-file "[^:]*: \\(.*\\)")
    ;; to select the right line for either .vo or .vio dependencies.
    ;; However, we want to accept a .vo prerequisite for a .vio target
    ;; if it is recent enough. Therefore we actually need module dependencies
    ;; instead of file dependencies and we derive them from the .vo line.
    (when (string-match "\\`[^:]*: \\(.*\\)" output)
      (cl-remove-if-not
       (lambda (f) (string-match-p "\\.vo\\'" f))
       (split-string (match-string 1 output))))))

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
break.

This function always computes the .vo file names. Conversion into .vio,
depending on `coq-compile-quick', must be done elsewhere."
  (let* ((coqdep-arguments
	  (coq-par-coqdep-arguments lib-src-file coq-load-path))
	 (this-command (cons coq-dependency-analyzer coqdep-arguments))
	 (full-command (if command-intro
			   (cons command-intro this-command)
			 this-command))
	 coqdep-status coqdep-output)
    (when coq--debug-auto-compilation
      (message "Run synchronously: %s"
	       (mapconcat 'identity full-command " ")))
    ;; (when coq--debug-auto-compilation
    ;;     (message "CPGLD: call coqdep arg list: %s" coqdep-arguments))
    (with-temp-buffer
      (setq coqdep-status
            (apply 'call-process
                   coq-dependency-analyzer nil (current-buffer) nil
                   coqdep-arguments))
      (setq coqdep-output (buffer-string)))
    ;; (when coq--debug-auto-compilation
    ;;     (message "CPGLD: coqdep status %s, output on %s: %s"
    ;;              coqdep-status lib-src-file coqdep-output))
    (coq-par-analyse-coq-dep-exit coqdep-status coqdep-output full-command)))

(defun coq-par-map-module-id-to-vo-file (module-id coq-load-path &optional from)
  "Map MODULE-ID to the appropriate coq object (.vo) file.
The mapping depends of course on `coq-load-path'. The current
implementation invokes coqdep with a one-line require command.
This is probably slower but much simpler than modelling coq file
loading inside ProofGeneral. Argument SPAN is only used for error
handling. It provides the location information of MODULE-ID for a
decent error message. Argument COQ-LOAD-PATH must be
`coq-load-path' from the buffer that triggered the compilation,
in order to provide correct load-path options to coqdep.

This function always computes the .vo file name. Conversion into .vio,
depending on `coq-compile-quick', must be done elsewhere.

A peculiar consequence of the current implementation is that this
function returns () if MODULE-ID comes from the standard library."
  (let ((coq-load-path
         (if (and coq-load-path-include-current (coq--pre-v85))
             (cons default-directory coq-load-path)
           coq-load-path))
        (coq-load-path-include-current nil)
        (temp-require-file (make-temp-file "ProofGeneral-coq" nil ".v"))
        (coq-string (concat (if from (concat "From " from " ") "")
                            "Require " module-id "."))
        result)
    (unwind-protect
        (progn
          (with-temp-file temp-require-file
            (insert coq-string))
          (setq result
                (coq-par-get-library-dependencies
                 temp-require-file
		 coq-load-path
                 (concat "echo \"" coq-string "\" > " temp-require-file ";"))))
      (delete-file temp-require-file))
    (when coq--debug-auto-compilation
	(message "coq-par-get-library-dependencies delivered \"%s\"" result))
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
	    nil "Internal error in coq-seq-map-module-id-to-obj-file")
    (car-safe result)))


;;; manage background jobs

(defun coq-par-kill-all-processes ()
  "Kill all background coqc, coqdep or vio2vo compilation processes.
Return t if some process was killed."
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
	 (when coq--debug-auto-compilation
	   (message "%s %s: kill it"
		    (get (process-get process 'coq-compilation-job) 'name)
		    (process-name process)))))
     (process-list))
    (setq coq--current-background-jobs 0)
    kill-needed))

(defun coq-par-unlock-all-ancestors-on-error ()
  "Unlock ancestors which are not in an asserted span.
Used for unlocking ancestors on compilation errors."
  (when coq--compilation-object-hash
    (maphash
     (lambda (key job)
       (when (eq (get job 'lock-state) 'locked)
         (coq-unlock-ancestor (get job 'src-file))
	 (put job 'lock-state 'unlocked)))
     coq--compilation-object-hash)))

(defun coq-par-kill-and-cleanup ()
  "Kill all background compilation, cleanup internal state and unlock ancestors.
This is the common core of `coq-par-emergency-cleanup' and
`coq-par-user-interrupt'. Returns t if there actually was a
background job that was killed."
  (let (proc-killed)
    (when coq--debug-auto-compilation
      (message "kill all jobs and cleanup state"))
    (setq proc-killed (coq-par-kill-all-processes))
    (setq coq-par-compilation-queue (coq-par-new-queue))
    (setq coq--last-compilation-job nil)
    (setq coq-par-vio2vo-queue (coq-par-new-queue))
    (setq coq--compile-vio2vo-in-progress nil)
    (when coq--compile-vio2vo-delay-timer
      (cancel-timer coq--compile-vio2vo-delay-timer)
      (setq coq--compile-vio2vo-delay-timer nil))
    (coq-par-unlock-all-ancestors-on-error)
    (setq proof-second-action-list-active nil)
    (coq-par-init-compilation-hash)
    proc-killed))

(defun coq-par-emergency-cleanup ()
  "Emergency cleanup for errors in parallel background compilation.
This is the function that cleans everything up when some
background compilation process detected a severe error. When
`coq-compile-keep-going' is nil, all errors are severe. When
`coq-compile-keep-going' is t, coqc and some coqdep errors are
not severe. This function is also used for the user action to
kill all background compilation.

On top of `coq-par-kill-and-cleanup', this function resets the
queue region (and thus `proof-action-list' and signals an
interrupt to the proof shell."
  (interactive)				; needed for menu
  (when coq--debug-auto-compilation
    (message "emergency cleanup"))
  (coq-par-kill-and-cleanup)
  (when proof-action-list
    (setq proof-shell-interrupt-pending t))
  (proof-release-lock)
  (proof-detach-queue))

(defun coq-par-user-interrupt ()
  "React to a generic user interrupt with cleaning up everything.
This function cleans up background compilation when the proof
assistant died (`proof-shell-handle-error-or-interrupt-hook') or
when the user interrupted Proof General (with C-c C-c or
`proof-interrupt-process' leading to
`proof-shell-signal-interrupt-hook').

On top of `coq-par-kill-and-cleanup', this function only sets the
dynamic variable `prover-was-busy' to tell the proof shell that
the user actually had a reason to interrupt. However, in the
special case where `proof-action-list' is nil and
`coq--last-compilation-job' not, this function also clears the
queue region and releases the proof shell lock. This has the nice
side effect, that `proof-interrupt-process' does not send an
interrupt signal to the prover."
  (let (proc-killed
	(was-busy (or coq--last-compilation-job
		      coq--compile-vio2vo-in-progress
		      coq--compile-vio2vo-delay-timer)))
    (when coq--debug-auto-compilation
      (message "cleanup on user interrupt"))
    (setq proc-killed (coq-par-kill-and-cleanup))
    (unless proof-action-list
      (when coq--debug-auto-compilation
	(message "clear queue region and proof shell lock"))
      (proof-release-lock)
      (proof-detach-queue))
    (when (and (boundp 'prover-was-busy)
	       (or proc-killed was-busy))
      (setq prover-was-busy t))))

(defun coq-par-process-filter (process output)
  "Store output from coq background compilation."
  (process-put process 'coq-process-output
	       (concat (process-get process 'coq-process-output) output)))

(defun coq-par-start-process (command arguments continuation job file-rm)
  "Start asynchronous compilation job for COMMAND.
This function starts COMMAND with arguments ARGUMENTS for
compilation job JOB, making sure that CONTINUATION runs when the
process finishes successfully. FILE-RM, if not nil, denotes a
file to be deleted when the process is killed."
  (let ((process-connection-type nil)	; use pipes
	(process-name (format "pro-%s" coq--par-next-id))
	process)
    (with-current-buffer (or proof-script-buffer (current-buffer))
      (when coq--debug-auto-compilation
	(message "%s %s: start %s %s in %s"
		 (get job 'name) process-name
		 command (mapconcat 'identity arguments " ")
		 default-directory))
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
      (setq coq--par-next-id (1+ coq--par-next-id))
      (setq coq--current-background-jobs (1+ coq--current-background-jobs))
      (process-put process 'coq-compilation-job job)
      (process-put process 'coq-process-continuation continuation)
      (process-put process 'coq-process-command (cons command arguments))
      (process-put process 'coq-process-output "")
      (process-put process 'coq-process-rm file-rm))))

(defun coq-par-process-sentinel (process event)
  "Sentinel for all background processes.
Runs when process PROCESS terminated because of EVENT. It
determines the exit status and calls the continuation function
that has been registered with that process. Normal compilation
errors are reported with an error message."
  (condition-case err
      (if (process-get process 'coq-par-process-killed)
	  (progn
	    (when coq--debug-auto-compilation
	      (message "%s %s: skip sentinel, process killed, %s"
		       (get (process-get process 'coq-compilation-job) 'name)
		       (process-name process)
		       (if (process-get process 'coq-process-rm)
			   (format "rm %s"
				   (process-get process 'coq-process-rm))
			 "no file removal")))
	    (if (process-get process 'coq-process-rm)
		(ignore-errors
		  (delete-file (process-get process 'coq-process-rm))))
	    (when (eq (process-get process 'coq-process-continuation)
		      'coq-par-vio2vo-continuation)
	      (when coq--debug-auto-compilation
		(message "%s: reenqueue for vio2vo"
			 (get (process-get process 'coq-compilation-job) 'name)))
	      (coq-par-vio2vo-enqueue
	       (process-get process 'coq-compilation-job))))
	(let (exit-status)
	  (when coq--debug-auto-compilation
	    (message "%s %s: process status changed to %s"
		     (get (process-get process 'coq-compilation-job) 'name)
		     (process-name process)
		     event))
	  (cond
	   ((eq (process-status process) 'exit)
	    (setq exit-status (process-exit-status process)))
	   (t (setq exit-status "abnormal termination")))
	  (setq coq--current-background-jobs
		(max 0 (1- coq--current-background-jobs)))
	  (funcall (process-get process 'coq-process-continuation)
		   process exit-status)
	  (coq-par-start-jobs-until-full)
	  (when (and coq--compile-vio2vo-in-progress
		     (eq coq--current-background-jobs 0))
	    (setq coq--compile-vio2vo-in-progress nil)
	    (message "vio2vo compilation finished"))
	  (when (and
		 (not coq--par-delayed-last-job)
		 (eq coq--current-background-jobs 0)
		 coq--last-compilation-job)
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


;;; vio2vo compilation

(defun coq-par-run-vio2vo-queue ()
  "Start delayed vio2vo compilation."
  (assert (not coq--last-compilation-job)
	  nil "normal compilation and vio2vo in parallel 3")
  (setq coq--compile-vio2vo-in-progress t)
  (setq coq--compile-vio2vo-delay-timer nil)
  (when coq--debug-auto-compilation
    (message "Start vio2vo processing for %d jobs"
	     (+ (length (car coq-par-vio2vo-queue))
		(length (cdr coq-par-vio2vo-queue)))))
  (coq-par-start-jobs-until-full))

(defun coq-par-require-processed (race-counter)
  "Callback for `proof-action-list' to signal completion of the last require.
This function ensures that vio2vo compilation starts after
`coq-compile-vio2vo-delay' seconds after the last module has been
loaded into Coq. When background compilation is successful, this
callback is inserted with a dummy item into proof-action-list
somewhere after the last require command."
  ;; When the user asserts new stuff while the (previously) last
  ;; require command is being processed, `coq--last-compilation-job'
  ;; might get non-nil. In this case there is a new last compilation
  ;; job that will eventually trigger vio2vo compilation.
  (unless (or coq--last-compilation-job
	      (not (eq race-counter coq--compile-vio2vo-start-id)))
    (setq coq--compile-vio2vo-delay-timer
	  (run-at-time coq-compile-vio2vo-delay nil
		       'coq-par-run-vio2vo-queue))))

(defun coq-par-callback-queue-item (callback)
  ;; A proof-action-list item has the form of
  ;;            (SPAN COMMANDS ACTION [DISPLAYFLAGS])
  ;; If COMMANDS is nil, the item is processed as comment and not sent
  ;; to the proof assistant, only the callback is called, see
  ;; proof-shell.el.
  (list nil nil callback))


;;; background job tasks

(defun coq-par-job-coqc-finished (job)
  "t if JOB has state 'waiting-queue or 'ready."
  (or (eq (get job 'state) 'waiting-queue)
      (eq (get job 'state) 'ready)))

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
  (when coq--debug-auto-compilation
    (message "%s -> %s: add coqc dependency"
	     (get dependee 'name) (get dependant 'name))))

(defun coq-par-add-queue-dependency (dependee dependant)
  "Add queue dependency from child job DEPENDEE to parent job DEPENDANT."
  (assert (and (not (get dependant 'queue-dependant-waiting))
	       (not (get dependee 'queue-dependant)))
	  nil "queue dependency cannot be added")
  (put dependant 'queue-dependant-waiting t)
  (put dependee 'queue-dependant dependant)
  (when coq--debug-auto-compilation
    (message "%s -> %s: add queue dependency"
	     (get dependee 'name) (get dependant 'name))))

(defun coq-par-job-needs-compilation (job)
  "Determine whether job needs to get compiled and do some side effects.
This function contains most of the logic nesseary to support
quick compilation according to `coq-compile-quick'. Taking
`coq-compile-quick' into account, it determines if a compilation
is necessary. The property 'required-obj-file is set either to
the file that we need to produce or to the up-to-date object
file. If compilation is needed, property 'use-quick is set when
-quick will be used. If no compilation is needed, property
'obj-mod-time remembers the time stamp of 'required-obj-file.
Indepent of whether compilation is required, .vo or .vio files
that are in the way are deleted. Note that the coq documentation
does not contain a statement, about what file is loaded, if both
a .vo and a .vio file are present. To be on the safe side, I
therefore delete a file if it might be in the way. Sets the
'vio2vo property on job if necessary."
  (let* ((vo-file (get job 'vo-file))
	 (vio-file (coq-library-vio-of-vo-file vo-file))
	 (vo-obj-time (nth 5 (file-attributes vo-file)))
	 (vio-obj-time (nth 5 (file-attributes vio-file)))
	 (dep-time (get job 'youngest-coqc-dependency))
	 (src-time (nth 5 (file-attributes (get job 'src-file))))
	 file-to-delete max-obj-time vio-is-newer
	 other-file other-obj-time result)
    (when coq--debug-auto-compilation
      (message
       (concat "%s: compare mod times: vo mod %s, vio mod %s, src mod %s, "
	       "youngest dep %s; vo < src : %s, vio < src : %s, "
	       "vo < dep : %s, vio < dep : %s")
       (get job 'name)
       (if vo-obj-time (current-time-string vo-obj-time) "-")
       (if vio-obj-time (current-time-string vio-obj-time) "-")
       (if src-time (current-time-string src-time) "-")
       (if (eq dep-time 'just-compiled) "just compiled"
	 (current-time-string dep-time))
       (if vo-obj-time (time-less-p vo-obj-time src-time) "-")
       (if vio-obj-time (time-less-p vio-obj-time src-time) "-")
       (if vo-obj-time (coq-par-time-less vo-obj-time dep-time) "-")
       (if vio-obj-time (coq-par-time-less vio-obj-time dep-time) "-")))
    ;; Compute first the max of vo-obj-time and vio-obj-time and remember
    ;; which of both is newer. This is only meaningful if at least one of
    ;; the .vo or .vio file exists.
    (cond
     ((and vio-obj-time vo-obj-time
	   (time-less-or-equal vo-obj-time vio-obj-time))
      (setq max-obj-time vio-obj-time)
      (setq vio-is-newer t))
     ((and vio-obj-time vo-obj-time)
      (setq max-obj-time vo-obj-time))
     (vio-obj-time
      (setq max-obj-time vio-obj-time)
      (setq vio-is-newer t))
     (t
      (setq max-obj-time vo-obj-time)))
    ;; Decide if and what to compile.
    (if (or (eq dep-time 'just-compiled) ; a dep has been just compiled
	    (and (not vo-obj-time) (not vio-obj-time)) ; no obj exists
	    ;; src younger than any obj?
	    (time-less-or-equal max-obj-time src-time)
	    ;; dep younger than any obj?
	    (time-less-or-equal max-obj-time dep-time))
	;; compilation is definitely needed
	(progn
	  (setq result t)
	  (if (coq-compile-prefer-quick)
	      (progn
		(put job 'required-obj-file vio-file)
		(put job 'use-quick t)
		(when vo-obj-time
		  (setq file-to-delete vo-file))
		(when (eq coq-compile-quick 'quick-and-vio2vo)
		  (put job 'vio2vo-needed t)))
	    (put job 'required-obj-file vo-file)
	    (when vio-obj-time
	      (setq file-to-delete vio-file)))
	  (when coq--debug-auto-compilation
	    (message
	     (concat "%s: definitely need to compile to %s; delete %s")
	     (get job 'name)
	     (get job 'required-obj-file)
	     (if file-to-delete file-to-delete "noting"))))
      ;; Either the .vio or the .vo file exists and one of .vio or .vo is
      ;; younger than the source and the youngest dependency. Might not
      ;; need to compile.
      (if (eq coq-compile-quick 'ensure-vo)
	  (progn
	    (put job 'required-obj-file vo-file)
	    (if (or (not vio-is-newer) ; vo is newest
		    (and vo-obj-time   ; vo is older than vio
			               ; but still newer than src or dep
			 (time-less-p src-time vo-obj-time)
			 (time-less-p dep-time vo-obj-time)))
		;; .vo is newer than src and youngest dep - don't compile
		(progn
		  (put job 'obj-mod-time vo-obj-time)
		  ;; delete vio if it is outdated or newer than vo
		  (when (and vio-obj-time
			     (or vio-is-newer
				 (time-less-or-equal vio-obj-time src-time)
				 (time-less-or-equal vio-obj-time dep-time)))
		    (setq file-to-delete vio-file))
		  (when coq--debug-auto-compilation
		    (message "%s: vo up-to-date 1; delete %s"
			     (get job 'name)
			     (if file-to-delete file-to-delete "noting"))))
	      ;; .vo outdated - need to compile
	      (setq result t)
	      ;; delete vio if it is outdated
	      (when (and vio-obj-time
			 (or (time-less-or-equal vio-obj-time src-time)
			     (time-less-or-equal vio-obj-time dep-time)))
		(setq file-to-delete vio-file))
	      (when coq--debug-auto-compilation
		(message "%s: need to compile to vo; delete %s"
			 (get job 'name)
			 (if file-to-delete file-to-delete "noting")))))
	;; There is an up-to-date .vio or .vo file and the user does not
	;; insist on either .vio or .vo - no need to compile.
	;; Ensure to delete outdated .vio or .vo files.
	;; First store the other obj file in other-file and other-obj-time.
	(if vio-is-newer
	    (setq other-file vo-file
		  other-obj-time vo-obj-time)
	  (setq other-file vio-file
		other-obj-time vio-obj-time))
	(if (and other-obj-time
		 (time-less-p src-time other-obj-time)
		 ;; dep-time is neither nil nor 'just-compiled here
		 (time-less-p dep-time other-obj-time))
	    ;; Both the .vio and .vo exist and are up-to-date. Coq
	    ;; loads the younger one but we continue with the older
	    ;; one to avoid recompilation for the case where a vio2vo
	    ;; process took a long time for a dependency.
	    (progn
	      (put job 'required-obj-file other-file)
	      (put job 'obj-mod-time other-obj-time)
	      (when coq--debug-auto-compilation
		(message (concat "%s: .vio and .vo up-to-date, "
				 "continue with the older %s")
			 (get job 'name)
			 (if vio-is-newer ".vio" ".vo"))))
	  ;; The other obj file does not exist or is outdated.
	  ;; Delete the outdated if it exists.
	  (when other-obj-time
	    (setq file-to-delete other-file))
	  (if vio-is-newer
	      (progn
		(put job 'required-obj-file vio-file)
		(put job 'obj-mod-time vio-obj-time)
		(when (eq coq-compile-quick 'quick-and-vio2vo)
		  (put job 'vio2vo-needed t))
		(when coq--debug-auto-compilation
		  (message "%s: vio up-to-date; delete %s"
			   (get job 'name)
			   (if file-to-delete file-to-delete "noting"))))
	    (put job 'required-obj-file vo-file)
	    (put job 'obj-mod-time vo-obj-time)
	    (when coq--debug-auto-compilation
	      (message "%s: vo up-to-date 2; delete %s"
		       (get job 'name)
		       (if file-to-delete file-to-delete "noting")))))))
    (when file-to-delete
      (condition-case err
	  (delete-file file-to-delete)
	(file-error
	 (signal 'coq-compile-error-rm err))))
    result))

(defun coq-par-retire-top-level-job (job)
  "Register ancestors and start queue items.
This function performs the essential tasks for top-level jobs
when they transition from 'waiting-queue to 'ready:
- Registering ancestors in the span and recording this fact in
  the 'lock-state property.
- Moving queue items back to `proof-action-list' and start their
  execution.
- Insert `coq-par-require-processed' as callback if this is the
  last top-level job, such that vio2vo compilation will start
  eventually.

This function can safely be called for non-top-level jobs. This
function must not be called for failed jobs."
  (assert (not (get job 'failed))
	  nil "coq-par-retire-top-level-job precondition failed")
  (let ((span (get job 'require-span))
	(items (get job 'queueitems)))
    (when (and span coq-lock-ancestors)
      (dolist (anc-job (get job 'ancestors))
	(assert (not (eq (get anc-job 'lock-state) 'unlocked))
		nil "bad ancestor lock state")
	(when (eq (get anc-job 'lock-state) 'locked)
	  (put anc-job 'lock-state 'asserted)
	  (push (get anc-job 'src-file)
		(span-property span 'coq-locked-ancestors)))))
    (when items
      (when (and (eq coq-compile-quick 'quick-and-vio2vo)
		 (eq coq--last-compilation-job job))
	(let ((vio2vo-counter
	       (setq coq--compile-vio2vo-start-id
		     (1+ coq--compile-vio2vo-start-id))))
	  ;; Insert a notification callback for when the last require
	  ;; queue item has been processed.
	  (setq items
		(cons
		 (car items)		; this is the require
		 (cons
		  (coq-par-callback-queue-item
		   `(lambda (span) (coq-par-require-processed ,vio2vo-counter)))
		  (cdr items))))))
      (proof-add-to-queue items 'advancing)
      (when coq--debug-auto-compilation
	(message "%s: add %s items to action list"
		 (get job 'name) (length items)))
      (put job 'queueitems nil))))

(defun coq-par-kickoff-queue-maybe (job)
  "Try transition 'waiting-queue -> 'ready for job JOB.
This transition is only possible if JOB is in state
'waiting-queue and if it has no queue dependee. If this is the
case, the following actions are taken:
- for successful top-level jobs (non-nil 'require-span property), ancestors
  are registered in the 'queue-span and marked as 'asserted in their
  'lock-state property
- processing of items in 'queueitems is started (if JOB is successful)
- a possible queue dependant gets it's dependency cleared, and,
  if possible the 'waiting-queue -> 'ready transition
  is (recursively) done for the dependant
- if this job is the last top-level compilation
  job (`coq--last-compilation-job') then the last compilation job
  and `proof-second-action-list-active' are cleared and vio2vo
  processing is triggered.
- If compilation failed, the (failing) last top-level job is
  delayed until `proof-action-list' is empty, possibly by
  registering this call as a callback in an empty
  proof-action-list item. When proof-action-list is empty, the
  queue span is deleted, remaining spans are cleared and the
  `proof-shell-busy' lock is freed."
  (if (or (not (eq (get job 'state) 'waiting-queue))
	  (get job 'queue-dependant-waiting))
      (when coq--debug-auto-compilation
	(if (not (eq (get job 'state) 'waiting-queue))
	    (message "%s: no queue kickoff because in state %s"
		     (get job 'name) (get job 'state))
	  (message
	   "%s: no queue kickoff because waiting for queue dependency"
	   (get job 'name))))
    (when coq--debug-auto-compilation
      (message "%s: has itself no queue dependency" (get job 'name)))
    (unless (get job 'failed)
      (coq-par-retire-top-level-job job))
    (when (and (get job 'failed) (get job 'require-span))
      (setq coq--par-delayed-last-job nil))
    (if (and (get job 'failed)
	     (eq coq--last-compilation-job job)
	     proof-action-list)
	(progn
	  (when coq--debug-auto-compilation
	    (message "%s: delay queue kickoff until action list is empty"
		     (get job 'name)))
	  (setq coq--par-delayed-last-job t)
	  (proof-add-to-queue
	   (list (coq-par-callback-queue-item
		  `(lambda (span) (coq-par-kickoff-queue-maybe ',job))))
	   'advancing))
      (put job 'state 'ready)
      (when coq--debug-auto-compilation
	(message "%s: ready" (get job 'name)))
      (let ((dependant (get job 'queue-dependant)))
	(if dependant
	    (progn
	      (assert (not (eq coq--last-compilation-job job))
		      nil "coq--last-compilation-job invariant error")
	      (put dependant 'queue-dependant-waiting nil)
	      (when coq--debug-auto-compilation
		(message
		 "%s -> %s: clear queue dependency, kickoff queue at %s"
		 (get job 'name) (get dependant 'name) (get dependant 'name)))
	      (coq-par-kickoff-queue-maybe dependant)
	      (when coq--debug-auto-compilation
		(message "%s: queue kickoff finished"
			 (get job 'name))))
	  (when (eq coq--last-compilation-job job)
	    (when (get job 'failed)
	      ;; proof-action-list is empty, see above
	      ;; variables that hold the queue span are buffer local
	      (with-current-buffer (or proof-script-buffer (current-buffer))
		(proof-script-clear-queue-spans-on-error nil))
	      (proof-release-lock)
	      (when (eq coq-compile-quick 'quick-and-vio2vo)
		(assert (not coq--compile-vio2vo-delay-timer)
			nil "vio2vo timer set before last compilation job")
		(setq coq--compile-vio2vo-delay-timer
		      (run-at-time coq-compile-vio2vo-delay nil
				   'coq-par-run-vio2vo-queue))))
	    (setq coq--last-compilation-job nil)
	    (setq proof-second-action-list-active nil)
	    (when coq--debug-auto-compilation
	      (message "clear last compilation job"))
	    (message "Library compilation %s"
		     (if (get job 'failed) "failed" "finished successfully")))
	  (when coq--debug-auto-compilation
	    (message "%s: no queue dependant, queue kickoff finished"
		     (get job 'name))))))))

(defun coq-par-compile-job-maybe (job)
  "Choose next action for JOB after dependencies are ready.
First JOB is put into state 'enqueued-coqc. Then it is determined
if JOB needs compilation, what file must be produced (depending
on `coq-compile-quick') and if a .vio or .vo file must be
deleted. If necessary, deletion happens immediately. If JOB needs
compilation, compilation is started or the JOB is enqueued and
JOB stays in 'enqueued-coqc for the time being. Otherwise, the
transition 'enqueued-coqc -> 'waiting-queue is done and, if
possible, also 'waiting-queue -> 'ready."
  (put job 'state 'enqueued-coqc)
  ;; Note that coq-par-job-needs-compilation sets 'required-obj-file
  ;; as a side effect and deletes .vo or .vio files that are in the way.
  ;; It also sets the 'vio2vo-needed property if needed.
  (if (and (not (get job 'failed)) (coq-par-job-needs-compilation job))
      (coq-par-start-or-enqueue job)
    (when coq--debug-auto-compilation
      (message "%s: %s, no compilation"
	       (get job 'name)
	       (if (get job 'failed) "failed" "up-to-date")))
    (when (get job 'vio2vo-needed)
      (coq-par-vio2vo-enqueue job))
    (coq-par-kickoff-coqc-dependants job (get job 'youngest-coqc-dependency))))

(defun coq-par-decrease-coqc-dependency (dependant dependee-time
						   dependee-ancestors)
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
  (assert (eq (get dependant 'state) 'waiting-dep)
	  nil "wrong state of parent dependant job")
  (when (coq-par-time-less (get dependant 'youngest-coqc-dependency)
			   dependee-time)
    (put dependant 'youngest-coqc-dependency dependee-time))
  (put dependant 'ancestors
       (append dependee-ancestors (get dependant 'ancestors)))
  (put dependant 'coqc-dependency-count
       (1- (get dependant 'coqc-dependency-count)))
  (assert (<= 0 (get dependant 'coqc-dependency-count))
	  nil "dependency count below zero")
  (when coq--debug-auto-compilation
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
dependencies of JOB. (If compilation for JOB failed, DEP-TIME is
meaningless but should nevertheless be a non-nil valid argument.)

This function makes the following actions.
- Clear the dependency from JOB to all its dependants, thereby
  propagating the ancestors of JOB and the maximum of DEP-TIME
  and the modification time of the .vo of JOB.
- save the maximum of DEP-TIME and .vo modification time in
  'youngest-coqc-dependency, in case we later create a clone of this job
- put JOB into state 'waiting-queue
- try to trigger the transition 'waiting-queue -> ready for JOB
- If JOB is successful but all dependants have failed, unlock all
  ancestors in case they are not participating in a still ongoing
  compilation."
  (let ((ancestors (get job 'ancestors))
	(dependant-alive nil))
    (put job 'state 'waiting-queue)
    ;; take max of dep-time and obj-mod-time
    ;; 
    ;; dep-time is either 'just-compiled or 'youngest-coqc-dependency of
    ;; the dependee, in the latter case obj-mod-time is greater than
    ;; dep-time, because otherwise we would have compiled the file. For
    ;; a clone job the max has already been taken when processing the
    ;; original file. If coqdep failed, 'obj-mod-time is not set.
    (unless (or (eq dep-time 'just-compiled) (eq (get job 'type) 'clone)
		(get job 'failed))
      (setq dep-time (get job 'obj-mod-time)))
    (put job 'youngest-coqc-dependency dep-time)
    (when coq--debug-auto-compilation
      (message "%s: kickoff %d coqc dependencies with time %s"
	       (get job 'name) (length (get job 'coqc-dependants))
	       (if (eq dep-time 'just-compiled)
		   'just-compiled
		 (current-time-string dep-time))))
    (dolist (dependant (get job 'coqc-dependants))
      (coq-par-decrease-coqc-dependency dependant dep-time ancestors)
      (unless (get dependant 'failed)
	(setq dependant-alive t)))
    (when coq--debug-auto-compilation
      (message (concat "%s: coqc kickoff finished, %s dependant alive, "
		       "maybe kickoff queue")
	       (get job 'name)
	       (if dependant-alive "some" "no")))
    (assert (or (not (get job 'failed)) (not dependant-alive))
	    nil "failed job with non-failing dependant")
    (when (or (and (not dependant-alive)
		   (not (get job 'require-span))
		   (not (get job 'failed)))
	      (and (get job 'queue-failed) (not (get job 'failed))))
      ;; job has not failed, but all dependants have 'failed set, or
      ;; top-level job marked with 'queue-failed changes to 'failed
      (when (get job 'queue-failed)
	(when coq--debug-auto-compilation
	  (message "%s: queue-failed -> failed, unlock ancestors"
		   (get job 'name)))
	(put job 'failed t))
      (coq-par-unlock-job-ancestors-on-error job))
    (coq-par-kickoff-queue-maybe job)))

(defun coq-par-start-coqdep (job)
  "Start coqdep for JOB.
Lock the source file and start the coqdep background process"
  (when (and coq-lock-ancestors
	     (eq (get job 'lock-state) 'unlocked))
    (proof-register-possibly-new-processed-file (get job 'src-file))
    (push job (get job 'ancestors))
    (put job 'lock-state 'locked))
  (coq-par-start-process
   coq-dependency-analyzer
   (coq-par-coqdep-arguments (get job 'src-file) (get job 'load-path))
   'coq-par-process-coqdep-result
   job
   nil))

(defun coq-par-start-vio2vo (job)
  "Start vio2vo background job."
  (let ((arguments (coq-include-options (get job 'load-path)))
	(module (coq-module-of-src-file (get job 'src-file)))
	(default-directory
	  (file-name-directory (file-truename (get job 'src-file)))))
    (when coq--debug-auto-compilation
      (message "%s: start vio2vo for %s"
	       (get job 'name)
	       (get job 'src-file)))
    (message "vio2vo %s" (get job 'src-file))
    (coq-par-start-process
     coq-prog-name
     (nconc arguments (list "-schedule-vio2vo" "1" module))
     'coq-par-vio2vo-continuation
     job
     (get job 'vo-file))))

(defun coq-par-start-task (job)
  "Start the background job for which JOB is waiting.
JOB was at the head of the compilation queue and now either
coqdep or coqc are started for it."
  (let ((job-state (get job 'state)))
    (cond
     ((eq job-state 'enqueued-coqdep)
      (coq-par-start-coqdep job))
     ((eq job-state 'enqueued-coqc)
      (message "Recompile %s%s"
	       (if (get job 'use-quick) "-quick " "")
	       (get job 'src-file))
      (let ((arguments
	     (coq-par-coqc-arguments (get job 'src-file) (get job 'load-path))))
	(when (get job 'use-quick)
	  (push "-quick" arguments))
	(coq-par-start-process
	 coq-compiler
	 arguments
	 'coq-par-coqc-continuation
	 job
	 (get job 'required-obj-file))))
     ((eq job-state 'ready)
      (coq-par-start-vio2vo job))
     (t (assert nil nil "coq-par-start-task with invalid job")))))

(defun coq-par-start-jobs-until-full ()
  "Start background jobs until the limit is reached."
  (let ((max-jobs (if coq--compile-vio2vo-in-progress
		      coq--internal-max-vio2vo-jobs
		    coq--internal-max-jobs))
	next-job)
    (while (and (< coq--current-background-jobs max-jobs)
		(setq next-job (if coq--compile-vio2vo-in-progress
				   (coq-par-vio2vo-dequeue)
				 (coq-par-job-dequeue))))
      (coq-par-start-task next-job))))
  
(defun coq-par-start-or-enqueue (new-job)
  "Start NEW-JOB or put it into the queue of waiting jobs.
NEW-JOB goes already into the waiting queue, if the number of
background jobs is one below the limit. This is in order to leave
room for Proof General."
  (if (< (1+ coq--current-background-jobs) coq--internal-max-jobs)
      (coq-par-start-task new-job)
    (coq-par-job-enqueue new-job)))

(defun coq-par-create-library-job (module-vo-file coq-load-path queue-dep
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

If the new job is a 'file job its state is 'enqueued-coqdep. If
there is space, coqdep is started immediately, otherwise the new
job is put into the compilation queue.

This function returns the newly created job."
  (let* ((orig-job (gethash module-vo-file coq--compilation-object-hash))
	 (new-job (make-symbol "coq-compile-job-symbol")))
    (put new-job 'name (format "job-%d" coq--par-next-id))
    (setq coq--par-next-id (1+ coq--par-next-id))
    (put new-job 'vo-file module-vo-file)
    (put new-job 'coqc-dependency-count 0)
    (put new-job 'require-span require-span)
    ;; fields 'required-obj-file and obj-mod-time are implicitely set to nil
    (if orig-job
	;; there is already a compilation job for module-vo-file
	(progn
	  (put new-job 'type 'clone)
	  (when coq--debug-auto-compilation
	    (message "%s: create %s compilation job for %s"
		     (get new-job 'name) (get new-job 'type) module-vo-file))
	  (when queue-dep
	    (coq-par-add-queue-dependency queue-dep new-job))
	  (if (coq-par-job-coqc-finished orig-job)
	      (progn
		(if queue-dep
		    (put new-job 'state 'waiting-queue)
		  (put new-job 'state 'ready))
		(put new-job 'youngest-coqc-dependency
		     (get orig-job 'youngest-coqc-dependency))
		(put new-job 'ancestors (get orig-job 'ancestors)))
	    (coq-par-add-coqc-dependency orig-job new-job)
	    (put new-job 'state 'waiting-dep)
	    (put new-job 'youngest-coqc-dependency '(0 0))))
      ;; there is no compilation job for this file yet
      (put new-job 'type 'file)
      (put new-job 'state 'enqueued-coqdep)
      (put new-job 'src-file (coq-library-src-of-vo-file module-vo-file))
      (when (equal (get new-job 'src-file)
		   (buffer-file-name proof-script-buffer))
	(signal 'coq-compile-error-circular-dep
		(concat dependant " -> scripting buffer")))
      (put new-job 'load-path coq-load-path)
      (put new-job 'youngest-coqc-dependency '(0 0))
      (puthash module-vo-file new-job coq--compilation-object-hash)
      (when coq--debug-auto-compilation
	(message "%s: create %s compilation for %s"
		 (get new-job 'name) (get new-job 'type) module-vo-file))
      (if (member (file-truename (get new-job 'src-file))
		  proof-included-files-list)
	  (put new-job 'lock-state 'asserted)
	(put new-job 'lock-state 'unlocked))
      (when queue-dep
	(coq-par-add-queue-dependency queue-dep new-job))
      (message "Check %s" (get new-job 'src-file))
      (coq-par-start-or-enqueue new-job))
    new-job))

(defun coq-par-ongoing-compilation (job)
  "Determine if the source file for JOB needs to stay looked.
Return t if job has a direct or indirect dependant that has not
failed yet and that is in a state before 'waiting-queue. Also,
return t if JOB has a dependant that is a top-level job which has
not yet failed."
  (assert (not (eq (get job 'lock-state) 'asserted))
	  nil "coq-par-ongoing-compilation precondition failed")
  (cond
   ((get job 'failed)
    nil)
   ((or (eq (get job 'state) 'waiting-dep)
	(eq (get job 'state) 'enqueued-coqc)
	;; top-level job that has compilation finished but has not
	;; been asserted yet
	(and (eq (get job 'state) 'waiting-queue) (get job 'require-span))
	;; Note that job cannot be a top-level in state 'ready,
	;; because we started from job with 'lock-state property equal
	;; to 'locked. Top-level job in state 'ready have all
	;; dependees with 'lock-state equal to 'asserted.
	)
    t)
   ;; Note that non-top-level jobs switch to 'waiting-queue as soon as
   ;; all dependencies are ready, before they start to deal with the
   ;; ancestors. We might therefore see here non-top-level jobs in
   ;; state 'waiting-queue: they have successfully finished their
   ;; compilation and are about to go to state 'ready.
   ((or (eq (get job 'state) 'ready)
	(eq (get job 'state) 'waiting-queue))
    ;; internal ready job
    (let ((dependants (get job 'coqc-dependants))
	  (res nil)
	  dep)
      (while (and (not res) (setq dep (pop dependants)))
	(setq res (coq-par-ongoing-compilation dep)))
      res))
   (t
    (assert nil nil
	    "impossible ancestor state %s on job %s"
	    (get job 'state) (get job 'name)))))

(defun coq-par-unlock-job-ancestors-on-error (job)
  "Unlock those ancestors of JOB that need to be unlocked.
For a failing job JOB, an ancestor need to stay looked if there
is still some compilation going on for which this ancestor is a
dependee or if a top level job with JOB as ancestor has finished
it's compilation successfully. In all other cases the ancestor
must be unlocked."
  (dolist (anc-job (get job 'ancestors))
    (when (and (eq (get anc-job 'lock-state) 'locked)
	       (not (coq-par-ongoing-compilation anc-job)))
      (when coq--debug-auto-compilation
	(message "%s: %s unlock because no ongoing compilation"
		 (get anc-job 'name) (get anc-job 'src-file)))
      (coq-unlock-ancestor (get anc-job 'src-file))
      (put anc-job 'lock-state 'unlocked))))

(defun coq-par-mark-queue-failing (job)
  "Mark JOB with 'queue-failed.
Mark JOB with 'queue-failed, and, if JOB is in state
'waiting-queue, transition to 'failed and unlock ancestors as
appropriate."
  (unless (or (get job 'failed) (get job 'queue-failed))
    (put job 'queue-failed t)
    (assert (not (eq (get job 'state) 'ready))
	    nil "coq-par-mark-queue-failing impossible state")
    (when coq--debug-auto-compilation
      (message "%s: mark as queue-failed, %s"
	       (get job 'name)
	       (if (eq (get job 'state) 'waiting-queue)
		   "failed, and unlock ancestors"
		 "wait")))
    (when (eq (get job 'state) 'waiting-queue)
      (put job 'failed t)
      (coq-par-unlock-job-ancestors-on-error job))
    (when (get job 'queue-dependant)
      (coq-par-mark-queue-failing (get job 'queue-dependant)))))

(defun coq-par-mark-job-failing (job)
  "Mark all dependants of JOB as failing and unlock ancestors as appropriate.
Set the 'failed property on all direct and indirect dependants of
JOB. Along the way, unlock ancestors as determined by
`coq-par-ongoing-compilation'. Mark queue dependants with
'queue-failed."
  (unless (get job 'failed)
    (put job 'failed t)
    (when coq--debug-auto-compilation
      (message "%s: mark as failed and unlock free ancestors" (get job 'name)))
    (coq-par-unlock-job-ancestors-on-error job)
    (dolist (dependant (get job 'coqc-dependants))
      (coq-par-mark-job-failing dependant))
    (when (get job 'queue-dependant)
      (coq-par-mark-queue-failing (get job 'queue-dependant)))))

(defun coq-par-process-coqdep-result (process exit-status)
  "Coqdep continuation function: Process coqdep output.
This function analyses the coqdep output of PROCESS. In case of
error, the job is marked as failed or compilation is aborted via
a signal (depending on `coq-compile-keep-going'). If there was no
coqdep error, the following actions are taken.
- the job that started PROCESS is put into sate 'waiting-dep
- a new job is created for every dependency. If this new job is
  not immediately ready, a Coq dependency is registered from the
  new job to the current job. For dependencies that are 'ready
  already, the most recent ancestor modification time is
  propagated.
- if there are no dependencies (especially if coqdep failed) or
  all dependencies are ready already, the next transition to
  'enqueued-coqc is triggered for the current job
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
	(if coq-compile-keep-going
	    (coq-par-mark-job-failing job)
	  (signal 'coq-compile-error-coqdep (get job 'src-file)))

      ;; no coqdep error -- work on dependencies
      (when coq--debug-auto-compilation
	(message "%s: dependencies of %s are %s"
		 (get job 'name) (get job 'src-file) dependencies-or-error))
      (setq job-max-time (get job 'youngest-coqc-dependency))
      (dolist (dep-vo-file dependencies-or-error)
	(unless (coq-compile-ignore-file dep-vo-file)
	  (let* ((dep-job (coq-par-create-library-job dep-vo-file
						      (get job 'load-path)
						      nil nil
						      (get job 'src-file)))
		 (dep-time (get dep-job 'youngest-coqc-dependency)))
	    (when (coq-par-time-less job-max-time dep-time)
	      (setq job-max-time dep-time))
	    (unless (coq-par-job-coqc-finished dep-job)
	      (coq-par-add-coqc-dependency dep-job job)))))
      (put job 'youngest-coqc-dependency job-max-time))
    ;; common part for job where coqdep was successful and where
    ;; coqdep failed (when coq-compile-keep-going)
    (put job 'state 'waiting-dep)
    (if (coq-par-dependencies-ready job)
	(progn
	  (when coq--debug-auto-compilation
	    (message "%s: coqc dependencies finished" (get job 'name)))
	  (coq-par-compile-job-maybe job))
      (when coq--debug-auto-compilation
	(message "%s: wait for %d dependencies"
		 (get job 'name) (get job 'coqc-dependency-count))))))

(defun coq-par-coqc-continuation (process exit-status)
  "Coqc continuation function.
If coqc failed, signal an error or mark the job as 'failed, and
unlock ancestors as appropriate. If coqc was successful, trigger
the transition 'enqueued-coqc -> 'waiting-queue for the job
behind PROCESS."
  (let ((job (process-get process 'coq-compilation-job)))
    (if (eq exit-status 0)
	(progn
	  ;; coqc success
	  (when (get job 'vio2vo-needed)
	    (coq-par-vio2vo-enqueue job))
	  (coq-par-kickoff-coqc-dependants job 'just-compiled))
      ;; coqc error
      (coq-compile-display-error
       (mapconcat 'identity (process-get process 'coq-process-command) " ")
       (process-get process 'coq-process-output)
       t)
      (if coq-compile-keep-going
	  (progn
	    (coq-par-mark-job-failing job)
	    (coq-par-kickoff-coqc-dependants
	     job
	     (get job 'youngest-coqc-dependency)))
	(signal 'coq-compile-error-coqc
		(get (process-get process 'coq-compilation-job) 'src-file))))))

(defun coq-par-vio2vo-continuation (process exit-status)
  "vio2vo continuation function."
  (let ((job (process-get process 'coq-compilation-job)))
    (if (eq exit-status 0)
	;; success - nothing to do
	(when coq--debug-auto-compilation
	  (message "%s: vio2vo finished successfully" (get job 'name)))
      (when coq--debug-auto-compilation
	(message "%s: vio2vo failed" (get job 'name)))
      (coq-compile-display-error
       (concat
	"cd "
	(file-name-directory (file-truename (get job 'src-file)))
	"; "
	(mapconcat 'identity (process-get process 'coq-process-command) " "))
       (process-get process 'coq-process-output)
       t)
      ;; don't signal an error or abort other vio2vo processes
      )))


;;; handle Require commands when queue is extended

(defun coq-par-handle-module (module-id span &optional from)
  "Handle compilation of module MODULE-ID.
This function translates MODULE-ID to a file name. If compilation
for this file is not ignored, a new top-level compilation job is
created. If there is a new top-level compilation job, it is saved
in `coq--last-compilation-job'.

This function must be evaluated with the buffer that triggered
the compilation as current, otherwise a wrong `coq-load-path'
might be used."
  (when coq--debug-auto-compilation
    (if from
	(message "handle required module \"%s\" from \"%s\"" module-id from)
      (message "handle required module \"%s\" without from clause" module-id)))
  (let ((module-vo-file
	 (coq-par-map-module-id-to-vo-file module-id coq-load-path from))
	module-job)
    (when coq--debug-auto-compilation
      (if module-vo-file
	  (message "check compilation for module %s from object file %s"
		   module-id module-vo-file)
	(message "nothing to check for module %s" module-id)))
    ;; coq-par-map-module-id-to-vo-file currently returns () for
    ;; standard library modules!
    (when (and module-vo-file
	       (not (coq-compile-ignore-file module-vo-file)))
      (setq module-job
	    (coq-par-create-library-job module-vo-file coq-load-path
					coq--last-compilation-job span
					"scripting buffer"))
      (setq coq--last-compilation-job module-job)
      (when coq--debug-auto-compilation
	(message "%s: this job is the last compilation job now"
		 (get coq--last-compilation-job 'name))))))

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
`coq--last-compilation-job'. The REQUIRE-ITEMS are attached to
this last top-level job or directly to proof-action-list, if
there is no last compilation job."
  (let* ((item (car require-items))
	 (string (mapconcat 'identity (nth 1 item) " "))
	 (span (car item))
         prefix start)
    (when coq--debug-auto-compilation
      (message "handle require command \"%s\"" string))
    ;; We know there is a require in string. But we have to match it
    ;; again in order to get the end position.
    (string-match coq-require-command-regexp string)
    (setq start (match-end 0))
    (setq prefix (match-string 1 string))
    (span-add-delete-action
     span
     `(lambda ()
	(coq-unlock-all-ancestors-of-span ,span)))
    ;; add a compilation job for all required modules
    (while (string-match coq-require-id-regexp string start)
      (setq start (match-end 0))
      (coq-par-handle-module (match-string 1 string) span prefix))
    ;; add the asserted items to the last compilation job
    (if coq--last-compilation-job
	(progn
	  (assert (not (coq-par-job-is-ready coq--last-compilation-job))
		  nil "last compilation job from previous compilation ready")
	  (put coq--last-compilation-job 'queueitems
	       (nconc (get coq--last-compilation-job 'queueitems)
		      require-items))
	  (when coq--debug-auto-compilation
	    (message "%s: attach %s items (containing now %s items)"
		     (get coq--last-compilation-job 'name)
		     (length require-items)
		     (length (get coq--last-compilation-job 'queueitems)))))
      ;; or add them directly to queueitems if there is no compilation job
      ;; (this happens if the modules are ignored for compilation)
      (setq queueitems (nconc queueitems require-items))
      (when coq--debug-auto-compilation
	(message "attach %s items to queueitems (containing now %s items)"
		 (length require-items)
		 (length queueitems))))))


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

If there is a last compilation job (`coq--last-compilation-job')
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
  (when coq--debug-auto-compilation
    (message "%d items were added to the queue, scan for require"
	     (length queueitems)))
  (unless coq--last-compilation-job
    (coq-par-init-compilation-hash)
    (coq-init-compile-response-buffer))
  (let ((splitted-items
	 (split-list-at-predicate queueitems
				  'coq-par-item-require-predicate)))
    (if coq--last-compilation-job
	(progn
	  (put coq--last-compilation-job 'queueitems
	       (nconc (get coq--last-compilation-job 'queueitems)
		      (car splitted-items)))
	  (setq queueitems nil)
	  (message "attach first %s items to job %s"
		   (length (car splitted-items))
		   (get coq--last-compilation-job 'name)))
      (setq queueitems (car splitted-items))
      (when coq--debug-auto-compilation
	(message "attach first %s items directly to queue"
		 (length (car splitted-items)))))
    ;; XXX handle external compilation here, compile everything
    ;; with one command, use compilation-finish-functions to get
    ;; notification
    (when (cdr splitted-items)
      (when coq--compile-vio2vo-delay-timer
	(cancel-timer coq--compile-vio2vo-delay-timer)
	(setq coq--compile-vio2vo-delay-timer nil))
      (when coq--compile-vio2vo-in-progress
	(assert (not coq--last-compilation-job)
		nil "normal compilation and vio2vo in parallel 2")
	;; there are only vio2vo background processes
	(coq-par-kill-all-processes)
	(setq coq--compile-vio2vo-in-progress nil))
      ;; save buffers before invoking the first coqdep
      (coq-compile-save-some-buffers)
      (dolist (require-items (cdr splitted-items))
	(coq-par-handle-require-list require-items)))
    (when coq--last-compilation-job
      (setq proof-second-action-list-active t))
    (coq-par-start-jobs-until-full)
    (when coq--debug-auto-compilation
      (if coq--last-compilation-job
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
      (coq-unclassifiable-version
       (coq-par-emergency-cleanup)
       (if (equal (cdr err) "trunk")
	   (message
	    (concat "your Coq version \"trunk\" is too unspecific for "
		    "Proof General; please customize coq-pinned-version"))
	 (message "%s \"%s\"; consider customizing coq-pinned-version"
		  (get (car err) 'error-message) (cdr err))))
      (file-error
       (coq-par-emergency-cleanup)
       (message "Error: %s" (mapconcat 'identity (cdr err) ": ")))
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
