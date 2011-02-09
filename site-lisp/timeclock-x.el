;;; timeclock-x.el --- Extra features for John Wiegley's timeclock package

;; Copyright (C) 2001, 2002, 2003 Free Software Foundation, Inc.
;; Author: Kahlil (Kal) HODGSON <dorge@tpg.com.au>
;; Keywords: convenience, data
;; X-URL: http://www.emacswiki.org/elisp/timeclock-x.el
;; Time-stamp: <2003-05-29 17:15:23 kahlil>

;; This file is NOT part of GNU Emacs.

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This file is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;; Extra features for John Wiegley's timeclock package:
;;
;; (1) Implement history lists for `timeclock-ask-for-project', and
;; `timeclock-ask-for-reason' (for people who prefer to go [up] rather
;; than [tab]).  Calls to `timeclock-completing-read' now give the
;; first element of the corresponding history list as the default. Our
;; history mechanism also skips duplicates and null strings.
;;
;; (2) Provide `timeclock-query-in' -- a useful function to add to the
;; end of your .emacs file.  Extended `timeclock-query-out' to ask for
;; a reason as well.
;;
;; (3) Facility for managing multiple timelog files (corresponding to
;; distinct jobs -- very useful if you have more than one employer who
;; wants to know how you've been spending your time).  See the
;; documentation for the variables `timeclock-directory',
;; `timeclock-default-log', `timeclock-multiple-jobs', and
;; `timeclock-job-list'.
;;
;; (4) Make safe versions of `timeclock-in', `timeclock-out', and
;; `timeclock-change' that don't screw up your log files if you do a
;; keyboard quit part way through:-)
;;
;; (5) Make `timeclock-visit-timelog' ignore `require-final-newline'
;; which can sometimes bugger up you files.
;;
;; (6) Make `timeclock-read-moment' skip non-moment lines (nice if you
;; like to beautify your timelog files).
;;
;; (7) Extended comment facillity controlled by the boolean variable
;; `timeclock-multiline-comments'.  If this is set then you will be
;; prompted for a multiline comment whenever you clock out or change
;; project.  Comments in your time log file are simply lines beginning
;; with white space (see (6) above). Project comments are inserted
;; after the "clock-in" time stamp but before the "clock-out" time
;; stamp, and are indented to the same column as the project name
;;
;; (8) Implements periodic project confirmation for those of us who
;; often forget to change projects at the right time. This really
;; helps to keep the timelog files accurate. See the documentation for
;; the variable `timeclock-query-interval' and the functions
;; `timeclock-query-project-on', `timeclock-query-project-off', and
;; `timeclock-toggle-query-project'.
;;
;; (9) Alternative `timeclock-update-modeline' function which tells
;; you which project (and job) you are clocked into and how long you
;; have been working on that project for.
;;
;; (10) Provide a convenience function `timeclock-setup-keys' to bind
;; interactive timeclock functions to a "C-x t-" prefix.
;;
;; Bugs
;;
;; Odd behavior using timeclock `timeclock-query-in' in .emacs file.
;; A query during startup causes GNU Emacs to wait for keyboard input
;; finishes).  I think this is one for the Emacs Developers.

;;; Installation:
;;
;; Plcae the following somewhere in your .emacs files
;;
;; (require 'timeclock-x)
;; (timeclock-modeline-display 1) ;; if you want modline display
;; (timeclock-initialize)
;;
;; and see the timeclock doco:-)

;;; Code:

;;;_ * Dependencies

(provide 'timeclock-x)
(require 'timeclock)

;;;_ * User variables

(defcustom timeclock-directory (convert-standard-filename "~/.timeclock")
  "*Directory for storing job specific timelog files.
Will be created if it does not already exist and
`timeclock-multiple-jobs' is t. "
  :type 'file
  :group 'timeclock)

(defcustom timeclock-default-log
  (convert-standard-filename (concat timeclock-directory "/default.log"))
  "*Name of the default timeclock log file."
  :type 'file
  :group 'timeclock)

(defcustom timeclock-multiple-jobs nil
  "Set to t if you want to track multiple jobs in the same session.
This can be useful if you need to clock time for different sets of projects
e.g. if you have more than one employer.  If set to t you will be asked for
a job whenever you clock in.  If nil you can still clock into another job
via `timeclock-change-job', but this resets its value to t.  The last job
is stored in the \".session\" file in the `timeclock-directory'.  Note, you
can only clock into jobs defined in `timeclock-job-list'"
  :type 'boolean
  :group 'timeclock)

(defcustom timeclock-job-list '()
  "List of distinct jobs you may wish to clock time in.  Separate
timelog files are kept for each job, and are placed in
`timeclock-directory' and named after the job suffixed with \".log\".
Its generally a good idea to include a job corresponding to
`timeclock-default-log'."
  :type '(repeat string)
  :group 'timeclock)

(defcustom timeclock-query-project-interval (* 15 60)
  "*Interval in seconds between periodic project confirmation.  Use
the function `timeclock-toggle-query-project' to interactively turn
this feature on or off.  The function `timeclock-query-project-on'
is all so suitable for inclusion in your `timeclock-first-in-hook'."

  :type 'integer
  :group 'timeclock)

(defcustom timeclock-multiline-comments t
  "Enable multiline comment extension.
Set to t if you would like to be prompted for a multiline comment
whenever you clock out or change project."
  :set (lambda (symbol value)
	 (if value
	     (add-hook 'timeclock-out-hook 'timeclock-query-comment)
	   (remove-hook 'timeclock-out-hook 'timeclock-query-comment))
	 (setq timeclock-multiline-comments value))
  :type 'boolean
  :group 'timeclock)

;; do the right thing on load even if we don't use custom
(if timeclock-multiline-comments
    (add-hook 'timeclock-out-hook 'timeclock-query-comment)
  (remove-hook 'timeclock-out-hook 'timeclock-query-comment))

;;;_ * Utilities

(defsubst timeclock-currently-in-p ()
  "Return non-nil if the user is currently clocked in."
  (and timeclock-last-event
       (equal (car-safe timeclock-last-event) "i")))

;; ... and its inverse
(defsubst timeclock-currently-out-p ()
  "Return non-nil if the user is currently clocked out."
  (or (null timeclock-last-event)
      (equal (downcase (car timeclock-last-event)) "o")))

(defun timeclock-setup-keys ()
  "Setup keys for timeclock."

  (autoload 'timeclock-generate-latex-report "timeclock-report")

  (define-key ctl-x-map "ti" 'timeclock-in-safe)
  (define-key ctl-x-map "to" 'timeclock-out-safe)
  (define-key ctl-x-map "tc" 'timeclock-change-safe)
  (define-key ctl-x-map "tC" 'timeclock-change-job)
  (define-key ctl-x-map "tr" 'timeclock-reread-log)
  (define-key ctl-x-map "tu" 'timeclock-update-modeline)
  (define-key ctl-x-map "tw" 'timeclock-when-to-leave-string)
  (define-key ctl-x-map "th" 'timeclock-pop-up-help)
  (define-key ctl-x-map "ts" 'timeclock-status-string)
  (define-key ctl-x-map "tv" 'timeclock-visit-timelog)
  (define-key ctl-x-map "tp" 'timeclock-toggle-query-project))

(defun timeclock-pop-up-help ()
  "Display a helpful non-technical usage message for the timeclock package."
  (interactive)
  (if (get-buffer "*Time Clock Help*")
      (pop-to-buffer (get-buffer "*Time Clock Help*"))
    (pop-to-buffer (get-buffer-create "*Time Clock Help*"))
    (insert
     "TIMECLOCK-MODE
--------------

This mode is for keeping track of time intervals.  You can use it for
whatever purpose you like, but the typical scenario is to keep track
of how much time you spend working on certain projects.  Use
`timeclock-in' when you start on a project, `timeclock-out' when
you're done, `timeclock-change' to clock out of one project and into
another, and `timeclock-status-string' to see your current status in
the echo area.  Once you've collected some data, you can use
`timeclock-workday-remaining' to see how much time is left to be
worked today (assuming a typical average of 8 hours a day), and
`timeclock-when-to-leave' which will calculate when you're free.  This
information can be automatically included in your modeline (see the
customizable option `timeclock-modeline-display') and you can force an
update of this display with `timeclock-update-modeline'.  Finally you
can pop up a summary of a fortnights timeclock data with the command
`timeclock-generate-report', or an ANU time-sheet with
`timeclock-generate-timesheet'.

A time-stamped record of these actions will be stored in the file
\".timelog\".  If you change your .timelog file without using timeclock's
functions, or if you change the value of any of timeclock's customizable
variables, you should run the command `timeclock-reread-log'.  This will
recompute any discrepancies in your average working time, and will make
sure that the various display functions return the correct value. You can
visit and manually edit this file with `timeclock-visit-timelog'. This may
be useful if you forget to clock-in or accidentally use an incorrect
project name, however, the format of this data-file is quite strict so be
careful:-)

The above operations are bound to the following keys:

    control x  t  h   timeclock-pop-up-help     (pop-up this help message)

    control x  t  i   timeclock-in
    control x  t  o   timeclock-out
    control x  t  c   timeclock-change
    control x  t  C   timeclock-change-job

    control x  t  s   timeclock-status-string
    control x  t  w   timeclock-when-to-leave

    control x  t  v   timeclock-visit-timelog
    control x  t  r   timeclock-reread-log
    control x  t  u   timeclock-update-modeline

    control x  t  g  t timeclock-generate-timesheet
    control x  t  g  r timeclock-generate-report

Emacs will display the amount of time \"left\" in your workday in the
modeline.

You may wish to change the following with the `customize-option' function:

    `timeclock-file'
    `timeclock-workday'
    `timeclock-modeline-display'
    `timeclock-ask-before-exiting'
")
    (goto-char (point-min))
    (set-buffer-modified-p nil)

    (help-mode))
  (delete-other-windows))

(defun timeclock-visit-timelog ()
  "Open up the current `timeclock-file' file in another window."
  (interactive)
  (make-variable-buffer-local 'require-final-newline)
  (find-file-other-window timeclock-file)
  (setq require-final-newline nil)
  (end-of-buffer))

;;;_ * Modeline format

(defun timeclock-update-modeline ()
  "Update the `timeclock-mode-string' displayed in the modeline to
include the current project and the current amount of time spent in
that project."
  (interactive)

  (let ((time-string (timeclock-seconds-to-string (timeclock-last-period)))
	(job-string (if (and timeclock-multiple-jobs
			     timeclock-last-job)
			(concat timeclock-last-job ":")))
	(bang (if timeclock-query-project-timer "!")))

    (setq timeclock-mode-string
	  (if (timeclock-currently-in-p)
	      (concat "[" job-string
		      (nth 2 timeclock-last-event) " "
		      time-string "]" bang)
	    (concat "<" job-string
		    (car timeclock-reason-history)
		    ">" bang))))
  ;; called from various places so ...
  (force-mode-line-update))

;;;_ * Time log format

;; Redefine so we can beautify timelog files

(defsubst timeclock-read-moment ()
  "Skip forward until text under point matches `timeclock-moment-regexp',
then read that moment."

  ;; silently skip lines that are not log entries
  (while (and (not (eobp))
	      (not (looking-at timeclock-moment-regexp)))
    (forward-line 1))

  (if (looking-at timeclock-moment-regexp)
      (let ((code (match-string 1))
	    (year (string-to-number (match-string 2)))
	    (mon  (string-to-number (match-string 3)))
	    (mday (string-to-number (match-string 4)))
	    (hour (string-to-number (match-string 5)))
	    (min  (string-to-number (match-string 6)))
	    (sec  (string-to-number (match-string 7)))
	    (project (match-string 8)))
	(list code (encode-time sec min hour mday mon year) project))))


;; since timeclock-read-moment is a defsubst there is no real way
;; around having to recompile the following to functions (Oow nasty
;; hack:-)

(eval-and-compile
  (save-window-excursion
    (save-excursion
      (let ((load-path
	     (if (boundp 'load-path-sans-setup)
		 load-path-sans-setup
	       load-path)))
	(find-function 'timeclock-log-data)
	(message "Recompiling `timeclock-log-data'")
	(compile-defun nil)
	(find-function 'timeclock-find-discrep)
	(message "Recompiling `timeclock-find-discrep'")
	(compile-defun nil)
	(kill-this-buffer)))))

;;;_ * History lists

(defun timeclock-completing-read
  (prompt history-var &optional require-match dummy)
  "A version of `completing-read' that works on both Emacs and XEmacs.

Queries for a string to read using PROMPT. Accepts completion on, and
history reference to, the contents of the history list that
HISTORY-VAR points to. The default value will be the first element in
the history list (if it exists).  A match in the history list is
required is REQUIRE-MATCH is non-nil.  Null strings and duplicate
entries in the history list are removed before use."

  ;; Does this work across windows?
  (raise-frame (window-frame (minibuffer-window)))

  (let* ((history-list (symbol-value history-var)) ;; dereference
	 (alist (mapcar 'list history-list)) ;; so we can use completion
	 (default (car history-list))
	 result element copy)

    ;; use the history list to derive default value
    (when default
      (setq prompt (concat prompt "(default \"" default "\") ")))

    ;; Delete duplicates and null strings (O.K. there is probably some
    ;; super fast and sexy way of doing this, and that the highly
    ;; lisp-savvy would laugh derisively at this piece of amateurish
    ;; tripe, but at least I know that it works:-)
    (while (setq element (pop history-list))
      (unless (equal element "")
	(add-to-list 'copy element 'append)))
    (set history-var copy)

    (if (featurep 'xemacs)
	(setq result (completing-read prompt alist))
      (setq result (completing-read prompt alist nil require-match
				    nil history-var default
				    'inherit-input-method)))
    ;; handle default response
    (if (or (null result)
	    (equal result ""))
	default
      result)
    ))

(defvar timeclock-project-history nil
  "History list use to record projects.")

(defvar timeclock-reason-history nil
  "History list use to record reasons for clocking out.")

(defun timeclock-ask-for-project ()
  "Ask the user for the project they are clocking into."
  (timeclock-completing-read
   "Clock into which project? " 'timeclock-project-history))

(defun timeclock-ask-for-reason ()
  "Ask the user for the reason they are clocking out."
  (timeclock-completing-read
   "Reason for clocking out: " 'timeclock-reason-history))

(defun timeclock-init-history ()
  "Read `timeclock-file' and initialize history variables.
Called on start up and every time `timeclock-file' changes."

  ;; Prep for `timeclock-reread-log'
  ;; (and in case of new empty timelog files)
  (setq timeclock-last-project nil
	timeclock-project-list nil
	timeclock-reason-list nil
	timeclock-last-event '("o" (0 0 0) nil)
	timeclock-discrepancy 0
	timeclock-project-history nil
	timeclock-reason-history nil)

  (unless timeclock-job-history
    (setq timeclock-job-history  timeclock-job-list))

  (when (file-exists-p timeclock-file)
    (condition-case nil ;; this sometimes gets garbled
	(progn

	  ;; to get discrepancy
	  (timeclock-reread-log) ;; may be superfluous

	  ;; Set history lists to something sensible. Collect these by
	  ;; scanning backward (c.f. `timeclock-project-list' and
	  ;; `timeclock-reason-list' which are collected by scanning
	  ;; forward).
	  (save-excursion
	    (set-buffer (find-file-noselect timeclock-file))
	    (end-of-buffer)
	    (beginning-of-line)
	    (while (not (bobp))
	      (when (looking-at timeclock-moment-regexp)
		(let ((project (match-string 8))
		      (code (match-string 1)))
		  (cond ((string-equal code "i")
			 (add-to-list 'timeclock-project-history
				      project 'append))
			((string-equal code "o")
			 (add-to-list 'timeclock-reason-history
				      project 'append)))))
	      (forward-line -1))))

      (error "Error reading log file %s" timeclock-file))))

;;;_ * Multiple Jobs

(defvar timeclock-job-history nil
  "History list use to record jobs you may wish to clock time in.")

(defvar timeclock-last-job nil
  "Track the current job.")

(defun timeclock-ask-for-job ()
  "Ask the user for a job from `timeclock-job-list' to clock time in."
  (timeclock-completing-read
   "Which job would you like to clock into? "
   'timeclock-job-history 'require-match))

(defun timeclock-set-timelog (job)
  "Set `timeclock-last-job' to JOB and `timeclock-file' to the timelog
file corresponding to JOB.

If JOB is non-nil, stores the string JOB in a file for reference in
the next session.  If JOB is different from the previous value of job
then the time log is reread and history lists are reinitialized."

  ;; Called by `timeclock-in-safe' and `timeclock-change' assumes
  ;; `timeclock-initialize' has been called at least once this
  ;; session.  this does nothing if we are not tracking multiple jobs.

  (when job
    (setq timeclock-file (concat timeclock-directory "/" job ".log"))
    (save-excursion ;; store the result in a file
      (let ((require-final-newline nil))
	(set-buffer (find-file-noselect
		     (concat timeclock-directory "/.session")))
	(erase-buffer)
	(insert job)
	(save-buffer)
	(kill-buffer (current-buffer)))))

  (unless (equal job timeclock-last-job)
    (timeclock-init-history))

  ;; new job is now the current job
  (setq timeclock-last-job job))


(defun timeclock-initialize ()
  "Set `timeclock-file' file to the last timelog file used in the last
session but only if tracking multiple jobs.

Should be called exactly once by either `timeclock-in-safe' or
`timeclock-query-in' to retrieve the name of the log file use in the
last session."

;;; pre:  `timeclock-last-event' is nil.
;;; post: `timeclock-last-event' is non-nil.

  (if (null timeclock-multiple-jobs)
      (setq timeclock-last-job nil
	    timeclock-file timeclock-default-log)

    ;; else track down a job file ...

    ;; sanity check for first time users
    (when (null timeclock-directory)
      (error "The variable `timeclock-directory' must be no-nil"))
    (when (null timeclock-default-log)
      (error "The variable `timeclock-default-log' must be no-nil"))
    ;; may end in "/" but may not, so normalize
    (setq timeclock-directory
	  (convert-standard-filename
	   (directory-file-name timeclock-directory)))

    ;; create the timelog directory if it doesn't already exist
    (unless (file-accessible-directory-p timeclock-directory)
      (make-directory timeclock-directory))

    ;; we make the session record a dot file in case
    ;; `timeclock-directory' is set to $HOME
    (let ((session-record (concat timeclock-directory "/.session")))
      ;; Use the log file for the job in the session record
      (when (file-exists-p session-record)
	(save-excursion
	  (set-buffer (find-file-noselect session-record))
	  (setq timeclock-last-job (buffer-string)
		timeclock-file (concat timeclock-directory "/"
				       timeclock-last-job
				       ".log"))
	  (unless (file-exists-p timeclock-file)
	    (setq timeclock-file nil))
	  (kill-buffer (current-buffer)))))

    ;; first timers
    (setq timeclock-last-job (timeclock-ask-for-job)
	  timeclock-file (concat timeclock-directory "/"
				 timeclock-last-job
				 ".log"))) ;; end if (null ...

  (timeclock-init-history)) ;; end `timeclock-initialize'

;;;_ * Hooks

;; extended version which asks for a reason
(defun timeclock-query-out ()
  "Ask the user before clocking out.
This is a useful function for adding to `kill-emacs-query-functions'."
  (if (and (timeclock-currently-in-p)
	   (y-or-n-p "You are currently clocking time, clock out? "))
      (timeclock-out-safe)
    t)) ;; only fails on keyboard quit or error

;; timeclock.el puts this on the wrong hook!
(remove-hook `kill-emacs-hook 'timeclock-query-out )

(defun timeclock-query-in ()
  "Ask the user if they wish to clock in.  This is a useful function
for adding to your `emacs-startup-hook' in your .emacs file.

Note: using `emacs-startup-hook' avoids confusing various timers!"

  (when (null timeclock-last-event)
    (timeclock-initialize))   ;; usually only called once per session

  (when (and (timeclock-currently-out-p)
	     (y-or-n-p "You are not currently clocking time, clock in? "))
    (timeclock-in-safe))

  (when (and (null timeclock-query-project-timer)
	     (y-or-n-p "Turn on periodic project confirmation? "))
    (timeclock-query-project-on))

  ;; handle resuming a session that we didn't clock out of
  (when timeclock-modeline-display
    (setq timeclock-modeline-display (timeclock-modeline-display 1))
    (timeclock-update-modeline))

  ;; For some reason the above hangs waiting for input i.e. when
  ;; called form a timer. This hack seems to de-confuse things
  (condition-case nil
      (throw 'exit nil)
    (error nil))
  )

;;;_ * Extended comment support

(defvar timeclock-comment-point
  "Stores the value of (point-max) in `timeclock-file' at the time
  `timeclock-query-comment' was called.")

(defun timeclock-submit-comment ()
  "Insert current buffer as a comment beneath the last entry in
`timeclock-file'.  Called from \" *timeclock-comment*\" buffer."
  (interactive)
  (let ((string (buffer-string)))
    (unless (string-equal string "")
      (save-excursion
	(find-file timeclock-file)
	(goto-char timeclock-comment-point)
	(unless (bolp) (insert "\n"))
	(insert "\n") ;; spacer
	(let ((start (point)))
	  (insert string)
	  (unless (eolp)
	    (insert "\n")
	    (forward-line -1))
	  (beginning-of-line)
	  (string-rectangle start (point) ">> "))
	(insert "\n") ;; spacer
	(save-buffer (current-buffer))
	(kill-buffer (current-buffer)))))
  (unless (one-window-p) (delete-window)))

(defun timeclock-query-comment ()
  "Add a multiline comment for the current project.
Ideal for tracking details of progress with various projects.  This
functions is suitable for addition to `timeclock-out-hook'."
  (interactive)

  (when (and timeclock-multiline-comments
	     (y-or-n-p "Add a comment for last timeclock period? "))

    ;; Save the position of the end of `timeclock-file' the time
    ;; `timeclock-query-comment' was called.
    (setq timeclock-comment-point
	  (save-excursion
	    (set-buffer (find-file timeclock-file))
	    (point-max)))

    ;; hack to avoid poping from the minibuffer
    (select-window (frame-first-window))

    ;; set up comment buffer
    (let ((buffer (get-buffer " *timeclock-comment*")))
      (if (and buffer (pop-to-buffer buffer nil 'norecord))
	  (erase-buffer)
	;; first time setup
	(pop-to-buffer (get-buffer-create " *timeclock-comment*")
		       nil 'norecord)

	(text-mode)
	;; setup a fancy header
	(setq header-line-format
	      (propertize
	       (concat
		"   "
		"Comment for project \"" timeclock-last-project "\"."
		" Enter C-c C-c to submit or C-c C-q to quit.")
	       'face 'font-lock-keyword-face))

	(set-fill-column (- fill-column (length ">>  ")))
	;; copy the current keymap
	(use-local-map (copy-keymap (current-local-map)))
	(local-set-key [(control c) (control c)] #'timeclock-submit-comment)
	(local-set-key [(control c) (control q)] #'bury-buffer)
	))
    ))

;;;_ * Keyboard quit safe versions of interactive functions

;; Also supports multiple jobs

(defun timeclock-in-safe (&optional arg)
  "Call `timeclock-in' but catch keyboard quit.
Also queries request for job change.
Returns t if succeeds, nil otherwise."
  (interactive "P")

  (when (null timeclock-last-event)
    (timeclock-initialize)) ;; usually called only once per session

  (if (timeclock-currently-in-p)
      (progn (message "You are already clocking time!") nil)
    ;; save the current state
    (let ((last-job timeclock-last-job)
	  (job-history timeclock-job-history)
	  (project-history timeclock-project-history))

      (condition-case value ;; catch keyboard quit
	  (progn
	    (timeclock-set-timelog
	     (and timeclock-multiple-jobs (timeclock-ask-for-job)))

	    ;; if our job has changed, everything gets reinitialized
	    (timeclock-in arg nil 'ask-for-project)
	    t) ;; success

	((list quit error)
	 (progn ;; reset to saved state
	   (when (equal (car value) 'error)
	     (message "Error in timeclock-in-safe: %s" (cadr value))) ;; debug
	   (when timeclock-multiple-jobs
	     (timeclock-set-timelog last-job))
	   (setq timeclock-last-job last-job
		 timeclock-job-history job-history
		 timeclock-project-history project-history)
	   (timeclock-update-modeline)
	   nil)))))) ;; failure

(defun timeclock-change-job (&optional arg)
    "Change to working on a different job, by clocking out, changing
`timeclock-file', and then clocking back in.  With a prefix arg, consider
the previous project as having been finished at the time of changeover.
Calls `timeclock-ask-for-job' to determine the new `timelog-file'."
    (interactive "P")

    (if (timeclock-currently-out-p)
	(message "You are not currently clocking time!")
      ;; save the current state
      (let ((multiple-jobs timeclock-multiple-jobs)
	    ;; this must be non-nil
	    (last-job (or timeclock-last-job
			  (file-name-sans-extension
			   (file-name-nondirectory timeclock-file))))
	    (job-history timeclock-job-history)
	    (last-project timeclock-last-project)
	    (project-history timeclock-project-history))

	;; calling this function turns this user variable on
	(setq timeclock-multiple-jobs t)

	(condition-case value ;; catch keyboard quit
	    (let (project new-job)
	      (setq new-job (timeclock-ask-for-job))
	      (timeclock-set-timelog new-job) ;; sets up history lists
	      (setq project (and timeclock-get-project-function
				 (funcall timeclock-get-project-function)))

	      ;; if we get this far, we haven't done a keyboard quit
	      (timeclock-set-timelog last-job) ;; so we can clock out
	      (timeclock-out arg)
	      (timeclock-set-timelog new-job)  ;; damn! have to do this twice
	      (timeclock-in nil project)
	      t) ;; sucess

	  ((list quit error)  ;; reset to saved state
	   (progn
	     (when (equal (car value) 'error)
	       (message "Error in timeclock-change-job: %s" (cadr value)))
	     (timeclock-set-timelog last-job)
	     ;; rereads log only if changed
	     (setq timeclock-multiple-jobs multiple-jobs
		   timeclock-job-history job-history
		   timeclock-last-job last-job
		   timeclock-last-project last-project
		   timeclock-project-history project-history)
	     (timeclock-update-modeline)
	     nil)))))) ;; failure

(defun timeclock-change-safe (&optional arg)
  "Same as `timeclock-change' but catch keyboard quits."
  (interactive "P")
  (if (timeclock-currently-out-p)
      (message "You are not currently clocking time!")
    (condition-case value ;; catch keyboard quit
	(let ((project (and timeclock-get-project-function
			    (funcall timeclock-get-project-function))))
	  (timeclock-out arg "")
	  (timeclock-in arg project)
	  t) ;; success
      ((list quit error)
       (when (equal (car value) 'error)
	 (message "Error in timeclock-change-safe: %s" (cadr value))) ;; debug
       nil)))) ;; failure

(defun timeclock-out-safe (&optional arg)
  "Same as `timeclock-out' but catch keyboard quit."
  (interactive "P")
  (if (timeclock-currently-out-p)
      (message "You are not currently clocking time!")
    (condition-case value ;; catch keyboard quit
	(let ((reason (and timeclock-get-reason-function
			   (funcall timeclock-get-reason-function))))
	  (timeclock-out arg reason)
	  t) ;; success
      ((list quit error)
       (when (equal (car value) 'error)
	 (message "Error in timeclock-out-safe: %s" (cadr value))) ;; debug
       nil)))) ;; failure

;;;_ * Periodic project confirmation

(defvar timeclock-query-project-timer nil
  "Variable to hold the periodic project confirmation timer")

(defun timeclock-query-project-on (&optional quiet)
   "*Turn periodic project confirmation on."
   (setq timeclock-query-project-timer
	 (run-at-time timeclock-query-project-interval
		      timeclock-query-project-interval
		      'timeclock-query-project))
   (unless quiet
     (message "Timeclock periodic project confirmation is on")
     (timeclock-update-modeline)))

(defun timeclock-query-project-off (&optional quiet)
  "*Turn periodic project confirmation off."
  (cancel-function-timers 'timeclock-query-project-do-it) ;; catch pile ups
  (cancel-function-timers 'timeclock-query-project) ;; catch pile ups
  (setq timeclock-query-project-timer nil)
  (unless quiet
    (message "Timeclock periodic project confirmation is off")
    (timeclock-update-modeline)))

(defun timeclock-toggle-query-project ()
  "*Toggle periodic project confirmation."
  (interactive)
  (if timeclock-query-project-timer
      (timeclock-query-project-off)
    (timeclock-query-project-on)))

(defun timeclock-query-project-reset ()
  "*If periodic project confirmation is on, reset the timer."
  (when timeclock-query-project-timer
    (timeclock-query-project-off)
    (timeclock-query-project-on)))

;; interacts poorly with window manager

(defun timeclock-query-project-do-it ()
  "Confirm clocking time in current project.
Called by the idle timer started by `timeclock-query-project'."
  (timeclock-query-project-off 'quietly)

  (unwind-protect ;; catch keyboard quit
      (let ((last-nonmenu-event nil)) ;; force pop-up dialog
	  (if (or (null timeclock-last-event)
		  (equal (downcase (car timeclock-last-event)) "i"))

	      ;; clocking time
	      (cond ((y-or-n-p-with-timeout
		      (concat "Continue clocking time for \""
			      (nth 2 timeclock-last-event)
			      "\"? " ) 30 nil))
		    ((not (y-or-n-p (concat "Clock out? ")))
		     (if timeclock-multiple-jobs
			 (timeclock-change-job nil)
		       (timeclock-change-safe nil)))
		    (t (timeclock-out-safe nil)))

	    ;; not clocking time
	    (if (y-or-n-p-with-timeout
		 (concat "Clocked out for \""
			 (nth 2 timeclock-last-event)
			 "\".  Clock back in? " ) 30 nil)
		(timeclock-in-safe))))
    (timeclock-query-project-on 'quietly)
    (message nil)))

(defun timeclock-query-project ()
  "Confirm clocking time in current project.

Called by `timeclock-query-timer'.  Waits for at least 3 seconds of
idle time before querying to prevent the query from disrupting typing."

  ;; don't pile up queries during lunch
  (timeclock-query-project-off 'quiet)

  ;; `run-with-idle-timer' but activate immediately
  (let ((function 'timeclock-query-project-do-it)
	(secs 3)
	(repeat nil)
	(args nil)
	(timer (timer-create)))
    (timer-set-function timer function args)
    (timer-set-idle-time timer secs repeat)
    (timer-activate-when-idle timer 'dont-wait)))

;; Reset the timer every time we explicitly change the project status
(add-hook 'timeclock-in-hook 'timeclock-query-project-reset t)
(add-hook 'timeclock-out-hook 'timeclock-query-project-reset t)

(provide 'timeclock-x)

;;; timeclock-x.el ends here
