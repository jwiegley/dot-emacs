;; proof.el Major mode for proof assistants
;; Copyright (C) 1994 - 1998 LFCS Edinburgh. 
;; Authors: David Aspinall, Yves Bertot, Healfdene Goguen,
;;          Thomas Kleymann and Dilip Sequeira
;;
;; Maintainer:  Proof General maintainer <proofgen@dcs.ed.ac.uk>
;;
;; Thanks to Robert Boyer, Rod Burstall,
;;           James McKinna, Mark Ruys, Martin Steffen, Perdita Stevens
;;
;; $Id$

(require 'proof-site)

; FIXME da: I think some of these should be autoloaded (etags,...)
(require 'cl)
(require 'compile)
(require 'comint)
(require 'etags)			
(cond ((fboundp 'make-extent) (require 'span-extent))
      ((fboundp 'make-overlay) (require 'span-overlay))
      (t nil))
(require 'proof-syntax)
(require 'proof-indent)
(require 'easymenu)

(autoload 'w3-fetch "w3" nil t)

(defmacro deflocal (var value docstring)
 (list 'progn
   (list 'defvar var 'nil docstring)
   (list 'make-variable-buffer-local (list 'quote var))
   (list 'setq var value)))

;; Load toolbar code if running XEmacs in X
(and (featurep 'x)
     (string-match "XEmacs" emacs-version)
     (require 'proof-toolbar))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Proof General configuration for proof assistant		    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar proof-assistant ""
  "Name of the proof assistant Proof General is using.")

(defvar proof-www-home-page ""
  "Web address for information on proof assistant")

(defvar proof-shell-cd nil
  "Command to the inferior process to change the directory.")

(defvar proof-shell-process-output-system-specific nil
  "Set this variable to handle system specific output.
Errors, start of proofs, abortions of proofs and completions of
proofs are recognised in the function `proof-shell-process-output'.
All other output from the proof engine is simply reported to the
user in the RESPONSE buffer.

To catch further special cases, set this variable to a tuple of
functions '(condf . actf). Both are given (cmd string) as arguments.
`cmd' is a string containing the currently processed command.
`string' is the response from the proof system. To change the
behaviour of `proof-shell-process-output', (condf cmd string) must
return a non-nil value. Then (actf cmd string) is invoked. See the
documentation of `proof-shell-process-output' for the required
output format.")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Proof General user options                                     ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defcustom proof-prog-name-ask-p nil
  "*If non-nil, query user which program to run for the inferior process."
  :type 'boolean
  :group 'proof-general)

(defcustom proof-one-command-per-line nil
  "*If non-nil, format for newlines after each proof command in a script."
  :type 'boolean
  :group 'proof-general)
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Other buffer-local variables used by proof mode                 ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; These should be set before proof-config-done is called

;; FIXME da: I don't think we should have both proof-terminal-char and
;; proof-terminal-string.
(defvar proof-terminal-char nil
  "Character which terminates a proof command in a script buffer.")

(defvar proof-comment-start nil
  "String which starts a comment in the proof assistant command language.
The script buffer's comment-start is set to this string plus a space.")

(defvar proof-comment-end nil
  "String which starts a comment in the proof assistant command language.
The script buffer's comment-end is set to this string plus a space.")

(defvar proof-save-command-regexp nil 
  "Matches a save command")
(defvar proof-save-with-hole-regexp nil 
  "Matches a named save command")
(defvar proof-goal-with-hole-regexp nil 
  "Matches a saved goal command")

(defvar proof-goal-command-p nil 
  "Is this a goal")
(defvar proof-count-undos-fn nil 
  "Compute number of undos in a target segment")

(defvar proof-find-and-forget-fn nil
  "Function returning a command string to forget back to before its argument span.
The special string proof-no-command means there is nothing to do.")

(defvar proof-goal-hyp-fn nil
  "A function which returns cons cell if point is at a goal/hypothesis.
First element of cell is a symbol, 'goal' or 'hyp'.  The second
element is a string: the goal or hypothesis itself.  This is used
when parsing the proofstate output")

(defvar proof-kill-goal-command nil 
  "How to kill a goal.")

(defvar proof-global-p nil
  "Is this a global declaration")

(defvar proof-state-preserving-p nil
  "A predicate, non-nil if its argument preserves the proof state")

(defvar pbp-change-goal nil
  "*Command to change to the goal %s")

;; these should be set in proof-pre-shell-start-hook

(defvar proof-prog-name nil "program name for proof shell")
(defvar proof-mode-for-shell nil "mode for proof shell")
(defvar proof-mode-for-pbp nil "The actual mode for Proof-by-Pointing.")
(defvar proof-shell-insert-hook nil 
  "Function to config proof-system to interface")

(defvar proof-pre-shell-start-hook)
(defvar proof-post-shell-exit-hook)

(defvar proof-shell-prompt-pattern nil 
   "comint-prompt-pattern for proof shell")

(defvar proof-shell-init-cmd nil
   "The command for initially configuring the proof process")

(defvar proof-shell-handle-delayed-output-hook
  '(proof-pbp-focus-on-first-goal)
  "*This hook is called after output from the PROOF process has been
  displayed in the RESPONSE buffer.")

(defvar proof-shell-handle-error-hook
  '(proof-goto-end-of-locked-if-pos-not-visible-in-window)
  "*This hook is called after an error has been reported in the
  RESPONSE buffer.")  


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Generic config for script management                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; FIXME da: replace this with wakeup-regexp or prompt-regexp?
;; May not need next regexp.
(defvar proof-shell-wakeup-char nil
  "A character terminating the prompt in annotation mode")

(defvar proof-shell-annotated-prompt-regexp ""
  "Annotated prompt pattern")

(defvar proof-shell-abort-goal-regexp nil
  "*Regular expression indicating that the proof of the current goal
  has been abandoned.")

(defvar proof-shell-error-regexp nil
  "A regular expression indicating that the PROOF process has
  identified an error.") 

(defvar proof-shell-interrupt-regexp nil
  "A regular expression indicating that the PROOF process has
  responded to an interrupt.") 

(defvar proof-shell-proof-completed-regexp nil
  "*Regular expression indicating that the proof has been completed.")

(defvar proof-shell-result-start ""
  "String indicating the start of an output from the prover following
  a `pbp-goal-command' or a `pbp-hyp-command'.")

(defvar proof-shell-result-end ""
  "String indicating the end of an output from the prover following a
  `pbp-goal-command' or a `pbp-hyp-command'.") 

(defvar proof-shell-start-goals-regexp ""
  "String indicating the start of the proof state.")

(defvar proof-shell-end-goals-regexp ""
  "String indicating the end of the proof state.")

(defvar pbp-error-regexp nil
  "A regular expression indicating that the PROOF process has
  identified an error.")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Internal variables used by scripting and pbp                    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst proof-mode-name "Proof-General")

(defvar proof-shell-echo-input t
  "If nil, input to the proof shell will not be echoed")

;; FIXME da: remove this variable.  Assume commands are terminated
;; properly at the specific level.
(defvar proof-terminal-string nil 
  "End-of-line string for proof process.")

(defvar proof-re-end-of-cmd nil 
  "Regexp matching end of command.  Based on proof-terminal-string.
Set in proof-config-done.")

(defvar proof-re-term-or-comment nil 
  "Regexp matching terminator, comment start, or comment end.
Set in proof-config-done.")

(defvar proof-marker nil 
  "Marker in proof shell buffer pointing to previous command input.")

(defvar proof-shell-buffer nil
  "Process buffer where the proof assistant is run.")

(defvar proof-script-buffer nil
  "Currently-active scripting buffer.")

(defvar proof-pbp-buffer nil
  "The response buffer (also known as the goals or pbp buffer).")

(defvar proof-shell-busy nil 
  "A lock indicating that the proof shell is processing.
When this is non-nil, proof-check-process-available will give
an error.")

(deflocal proof-buffer-type nil 
  "Symbol indicating the type of this buffer: script, shell, or pbp.")

(defvar proof-action-list nil "action list")

(defconst proof-no-command "COMMENT"
  "String used as a nullary action (send no command to the proof assistant)")

(defvar proof-included-files-list nil 
  "List of files currently included in proof process.
Each element in the list is a tuple of the form (module . file) where
module is identifies the buffer and file is the file name of the module.")

(deflocal proof-active-buffer-fake-minor-mode nil
  "An indication in the modeline that this is the *active* buffer")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; A few small utilities					    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun proof-message (str)
  "Output STR in minibuffer."
  (message (concat "[Proof] " str)))

;; append-element in tl-list
(defun proof-append-element (ls elt)
  "Append ELT to last of LS if ELT is not nil. [proof.el]
This function coincides with `append-element' in the package
[tl-list.el.]"
  (if elt
      (append ls (list elt))
    ls))

(defun proof-define-keys (map kbl)
  "Adds keybindings KBL in MAP.
The argument KBL is a list of tuples (k . f) where `k' is a keybinding
(vector) and `f' the designated function."
  (mapcar
   (lambda (kbl)
     (let ((k (car kbl)) (f (cdr kbl)))
         (define-key map k f)))
   kbl))

(defun proof-string-to-list (s separator) 
  "Return the list of words in S separated by SEPARATOR."
  (let ((end-of-word-occurence (string-match (concat separator "+") s)))
    (if (not end-of-word-occurence)
        (if (string= s "") 
            nil
          (list s))
      (cons (substring s 0 end-of-word-occurence) 
            (proof-string-to-list 
             (substring s
                        (string-match (concat "[^" separator "]")
                                      s end-of-word-occurence)) separator)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Basic code for the locked region and the queue region            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar proof-locked-hwm nil
  "Upper limit of the locked region")

(defvar proof-queue-loose-end nil
  "Limit of the queue region that is not equal to proof-locked-hwm.")

(defvar proof-locked-span nil
  "Upper limit of the locked region")

(defvar proof-queue-span nil
  "Upper limit of the locked region")

(make-variable-buffer-local 'proof-locked-span)
(make-variable-buffer-local 'proof-queue-span)

(defun proof-init-segmentation ()
  (setq proof-queue-loose-end nil)
  (if (not proof-queue-span)
      (setq proof-queue-span (make-span 1 1)))
  (set-span-property proof-queue-span 'start-closed t)
  (set-span-property proof-queue-span 'end-open t)
  (span-read-only proof-queue-span)

  (make-face 'proof-queue-face)
  (cond ((proof-have-color)
	 (set-face-background 'proof-queue-face "mistyrose"))
	(t (progn
	     (set-face-background 'proof-queue-face "Black")
	     (set-face-foreground 'proof-queue-face "White"))))
  (set-span-property proof-queue-span 'face 'proof-queue-face)

  (detach-span proof-queue-span)
  
  (setq proof-locked-hwm nil)
  (if (not proof-locked-span)
      (setq proof-locked-span (make-span 1 1)))
  (set-span-property proof-locked-span 'start-closed t)
  (set-span-property proof-locked-span 'end-open t)
  (span-read-only proof-locked-span)

  (make-face 'proof-locked-face)
  (cond ((proof-have-color)
	 (set-face-background 'proof-locked-face "lavender"))
	(t (set-face-property 'proof-locked-face 'underline t)))
  (set-span-property proof-locked-span 'face 'proof-locked-face)

  (detach-span proof-locked-span))

(defsubst proof-lock-unlocked ()
  (span-read-only proof-locked-span))

(defsubst proof-unlock-locked ()
  (span-read-write proof-locked-span))

(defsubst proof-set-queue-endpoints (start end)
  (set-span-endpoints proof-queue-span start end))

(defsubst proof-set-locked-endpoints (start end)
  (set-span-endpoints proof-locked-span start end))

(defsubst proof-detach-queue ()
  (and proof-queue-span (detach-span proof-queue-span)))

(defsubst proof-detach-locked ()
  (and proof-locked-span (detach-span proof-locked-span)))

(defsubst proof-set-queue-start (start)
  (set-span-endpoints proof-queue-span start (span-end proof-queue-span)))

(defsubst proof-set-queue-end (end)
  (set-span-endpoints proof-queue-span (span-start proof-queue-span) end))

(defun proof-detach-segments ()
  (proof-detach-queue)
  (proof-detach-locked))

(defsubst proof-set-locked-end (end)
  (if (>= (point-min) end)
      (proof-detach-locked)
    (set-span-endpoints proof-locked-span (point-min) end)))

(defun proof-unprocessed-begin ()
  "Return end of locked region in script buffer or (point-min) otherwise."
  (or 
   (and (eq proof-script-buffer (current-buffer))
	proof-locked-span (span-end proof-locked-span))
   (point-min)))

(defun proof-locked-end ()
  "Return end of the locked region.  Only call this from a scripting buffer."
  (if (eq proof-script-buffer (current-buffer))
      (proof-unprocessed-begin)
    (error "bug: proof-locked-end called from wrong buffer")))

(defsubst proof-end-of-queue ()
  (and proof-queue-span (span-end proof-queue-span)))

(defun proof-dont-show-annotations ()
  "Set display values of annotations (characters 128-255) to be invisible."
  (let ((disp (make-display-table))
	(i 128))
	(while (< i 256)
	  (aset disp i [])
	  (incf i))
	(cond ((fboundp 'add-spec-to-specifier)
	       (add-spec-to-specifier current-display-table disp
				      (current-buffer)))
	      ((boundp 'buffer-display-table)
	       (setq buffer-display-table disp)))))

;;; in case Emacs is not aware of read-shell-command-map

;; FIXME da: nasty, this might obliterate user's customizations
;; to read-shell-command-map.
(defvar read-shell-command-map
  (let ((map (make-sparse-keymap)))
    (if (not (fboundp 'set-keymap-parents))
        (setq map (append minibuffer-local-map map))
      (set-keymap-parents map minibuffer-local-map)
      (set-keymap-name map 'read-shell-command-map))
    (define-key map "\t" 'comint-dynamic-complete)
    (define-key map "\M-\t" 'comint-dynamic-complete)
    (define-key map "\M-?" 'comint-dynamic-list-completions)
    map)
  "Minibuffer keymap used by shell-command and related commands.")


;;; in case Emacs is not aware of the function read-shell-command
(or (fboundp 'read-shell-command)
    ;; from minibuf.el distributed with XEmacs 19.11
    (defun read-shell-command (prompt &optional initial-input history)
      "Just like read-string, but uses read-shell-command-map:
\\{read-shell-command-map}"
      (let ((minibuffer-completion-table nil))
        (read-from-minibuffer prompt initial-input read-shell-command-map
                              nil (or history
                              'shell-command-history)))))

;; The package fume-func provides a function with the same name and
;; specification. However, fume-func's version is incorrect.
;; da: make this hack more prominent so someone remembers to remove it
;; later on.
(and (fboundp 'fume-match-find-next-function-name)
(defun fume-match-find-next-function-name (buffer)
  "General next function name in BUFFER finder using match.
  The regexp is assumed to be a two item list the car of which is the regexp
  to use, and the cdr of which is the match position of the function name"
  (set-buffer buffer)
  (let ((r (car fume-function-name-regexp))
        (p (cdr fume-function-name-regexp)))
    (and (re-search-forward r nil t)
	 (cons (buffer-substring (setq p (match-beginning p)) (point)) p)))))

;; FIXME da: these next two functions slightly different, why?
;; (unprocessed-begin vs proof-locked-end)
(defun proof-goto-end-of-locked-interactive ()
  "Jump to the end of the locked region."
  (interactive)
  (switch-to-buffer proof-script-buffer)
  (goto-char (proof-locked-end)))

(defun proof-goto-end-of-locked ()
  "Jump to the end of the locked region."
  (goto-char (proof-unprocessed-begin)))

(defun proof-in-locked-region-p ()
  "Non-nil if point is in locked region.  Assumes proof script buffer current."
  (< (point) (proof-locked-end)))

(defun proof-goto-end-of-locked-if-pos-not-visible-in-window ()
  "If the end of the locked region is not visible, jump to the end of it."
  (interactive)
  (let ((pos (save-excursion
	       (set-buffer proof-script-buffer)
	       (proof-locked-end))))
    (or (pos-visible-in-window-p pos (get-buffer-window
				      proof-script-buffer t))
        (proof-goto-end-of-locked-interactive))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Starting and stopping the proof-system shell                    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun proof-shell-live-buffer ()
  "Return buffer of active proof assistant, or nil if none running."
  (and proof-shell-buffer
       (comint-check-proc proof-shell-buffer)
       proof-shell-buffer))

(defun proof-start-shell ()
  "Initialise a shell-like buffer for a proof assistant."
  (if (proof-shell-live-buffer)
      ()
    (run-hooks 'proof-pre-shell-start-hook)
    (setq proof-included-files-list nil)
    (if proof-prog-name-ask-p
	(save-excursion
	  (setq proof-prog-name (read-shell-command "Run process: "
						    proof-prog-name))))
    (let ((proc
	   (concat "Inferior "
		   (substring proof-prog-name
			      (string-match "[^/]*$" proof-prog-name)))))
      (while (get-buffer (concat "*" proc "*"))
	(if (string= (substring proc -1) ">")
	    (aset proc (- (length proc) 2) 
		  (+ 1 (aref proc (- (length proc) 2))))
	  (setq proc (concat proc "<2>"))))

      (message (format "Starting %s process..." proc))

      ;; Starting the inferior process (asynchronous)
      (let ((prog-name-list (proof-string-to-list proof-prog-name " ")))
	(apply 'make-comint  (append (list proc (car prog-name-list) nil)
				     (cdr prog-name-list))))
      ;; To send any initialisation commands to the inferior process,
      ;; consult proof-shell-config-done...

      (setq proof-shell-buffer (get-buffer (concat "*" proc "*")))
      (setq proof-pbp-buffer (get-buffer-create (concat "*" proc "-goals*")))

      (save-excursion
	(set-buffer proof-shell-buffer)
	(funcall proof-mode-for-shell)
	(set-buffer proof-pbp-buffer)
	(funcall proof-mode-for-pbp))

      (setq proof-script-buffer (current-buffer))
      (proof-init-segmentation)
      (setq proof-active-buffer-fake-minor-mode t)

      (if (fboundp 'redraw-modeline)
	  (redraw-modeline)
	(force-mode-line-update))

      (or (assq 'proof-active-buffer-fake-minor-mode minor-mode-alist)
	  (setq minor-mode-alist
		(append minor-mode-alist
			(list '(proof-active-buffer-fake-minor-mode 
				" Scripting")))))

      (message 
       (format "Starting %s process... done." proc)))))
  

(defun proof-stop-shell ()
  "Exit the proof process.  Runs proof-shell-exit-hook if non nil"
  (interactive)
  (save-excursion
    (let ((buffer (proof-shell-live-buffer)) (proc))
      (if buffer
	  (progn
	    (save-excursion
	      (set-buffer buffer)
	      (setq proc (process-name (get-buffer-process)))
	      (comint-send-eof)
	      (save-excursion
		(set-buffer proof-script-buffer)
		(proof-detach-segments))
	      (kill-buffer))
	    (run-hooks 'proof-shell-exit-hook)

             ;;it is important that the hooks are
	     ;;run after the buffer has been killed. In the reverse
	     ;;order e.g., intall-shell-fonts causes problems and it
	     ;;is impossible to restart the PROOF shell

	    (message (format "%s process terminated." proc)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;          Proof by pointing                                       ;;
;;          All very lego-specific at present                       ;;
;;          To make sense of this code, you should read the         ;;
;;          relevant LFCS tech report by tms, yb, and djs           ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defvar pbp-goal-command nil
  "Command informing the prover that `pbp-button-action' has been
  requested on a goal.")

(defvar pbp-hyp-command nil
  "Command informing the prover that `pbp-button-action' has been
  requested on an assumption.")

(defun pbp-button-action (event)
   (interactive "e")
   (mouse-set-point event)
   (pbp-construct-command))

; Using the spans in a mouse behavior is quite simple: from the
; mouse position, find the relevant span, then get its annotation
; and produce a piece of text that will be inserted in the right
; buffer.  

(defun proof-expand-path (string)
  (let ((a 0) (l (length string)) ls)
    (while (< a l) 
      (setq ls (cons (int-to-string (aref string a)) 
		     (cons " " ls)))
      (incf a))
    (apply 'concat (nreverse ls))))

(defun proof-send-span (event)
  (interactive "e")
  (let* ((span (span-at (mouse-set-point event) 'type))
	 (str (span-property span 'cmd)))
    (cond ((and (eq proof-script-buffer (current-buffer)) (not (null span)))
	   (proof-goto-end-of-locked)
	   (cond ((eq (span-property span 'type) 'vanilla)
		  (insert str)))))))

(defun pbp-construct-command ()
  (let* ((span (span-at (point) 'proof))
	 (top-span (span-at (point) 'proof-top-element))
	 top-info)
    (if (null top-span) ()
      (setq top-info (span-property top-span 'proof-top-element))
      (pop-to-buffer proof-script-buffer)
      (cond
       (span
	(proof-invisible-command 
	 (format (if (eq 'hyp (car top-info)) pbp-hyp-command 
		                              pbp-goal-command)
		 (concat (cdr top-info) (proof-expand-path 
					 (span-property span 'proof))))))
       ((eq (car top-info) 'hyp)
	(proof-invisible-command (format pbp-hyp-command (cdr top-info))))
       (t
	 (proof-insert-pbp-command (format pbp-change-goal (cdr top-info))))))
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;          Turning annotated output into pbp goal set              ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;









(defvar proof-shell-first-special-char nil "where the specials start")
(defvar proof-shell-goal-char nil "goal mark")
(defvar proof-shell-start-char nil "annotation start")
(defvar proof-shell-end-char nil "annotation end")
(defvar proof-shell-field-char nil "annotated field end")

(defvar proof-shell-eager-annotation-start nil
  "Eager annotation field start.  A regular expression or nil.
An eager annotation indicates to Emacs that some following output
should be displayed immediately and not accumulated for parsing.
Set to nil if the proof to disable this feature.")

(defvar proof-shell-eager-annotation-end "$"
  "Eager annotation field end.  A regular expression or nil.
An eager annotation indicates to Emacs that some following output
should be displayed immediately and not accumulated for parsing.
Set to nil if the proof to disable this feature.

The default value is \"$\" to match up to the end of the line.")

(defvar proof-shell-assumption-regexp nil
  "A regular expression matching the name of assumptions.")

;; FIXME da: where is this variable used?  
;;	      dropped in favour of goal-char?
(defvar proof-shell-goal-regexp nil
  "A regular expressin matching the identifier of a goal.")

(defvar proof-shell-noise-regexp nil
  "Unwanted information output from the proof process within
  `proof-start-goals-regexp' and `proof-end-goals-regexp'.")

(defun pbp-make-top-span (start end)
  (let (span name)
    (goto-char start)
    ;; FIXME da: why name?  This is a character function
    (setq name (funcall proof-goal-hyp-fn))
    (beginning-of-line)
    (setq start (point))
    (goto-char end)
    (beginning-of-line)
    (backward-char)
    (setq span (make-span start (point)))
    (set-span-property span 'mouse-face 'highlight)
    (set-span-property span 'proof-top-element name)))


;; Need this for processing error strings and so forth

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   The filter. First some functions that handle those few         ;;
;;   occasions when the glorious illusion that is script-management ;;
;;   is temporarily suspended                                       ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;   Output from the proof process is handled lazily, so that only  
;;   the output from the last of multiple commands is actually      
;;   processed (assuming they're all successful)



(defvar proof-shell-delayed-output nil
  "The last interesting output the proof process output, and what to do
   with it.")

(defvar proof-shell-proof-completed nil
  "Flag indicating that a completed proof has just been observed.")

(defvar proof-analyse-using-stack nil
  "Are annotations sent by proof assistant local or global")

(defun proof-shell-analyse-structure (string)
  (save-excursion
    (let* ((ip 0) (op 0) ap (l (length string)) 
	   (ann (make-string (length string) ?x))
           (stack ()) (topl ()) 
	   (out (make-string l ?x)) c span)
      (while (< ip l)	
	(if (< (setq c (aref string ip)) 128)
	    (progn (aset out op c)
		   (incf op)))
	(incf ip))
      (display-buffer (set-buffer proof-pbp-buffer))
      (erase-buffer)
      (insert (substring out 0 op))

      (setq ip 0
	    op 1)
      (while (< ip l)
	(setq c (aref string ip))
	(cond
	 ((= c proof-shell-goal-char)
	  (setq topl (cons op topl))
	  (setq ap 0))
	 ((= c proof-shell-start-char)
	  (if proof-analyse-using-stack
	      (setq ap (- ap (- (aref string (incf ip)) 128)))
	    (setq ap (- (aref string (incf ip)) 128)))
	  (incf ip)
	  (while (not (= (setq c (aref string ip)) proof-shell-end-char))
	    (aset ann ap (- c 128))
	    (incf ap)
	    (incf ip))
	  (setq stack (cons op (cons (substring ann 0 ap) stack))))
	 ((= c proof-shell-field-char)
	  (setq span (make-span (car stack) op))
	  (set-span-property span 'mouse-face 'highlight)
	  (set-span-property span 'proof (car (cdr stack)))
	  ;; Pop annotation off stack
	  (and proof-analyse-using-stack
	       (progn
		 (setq ap 0)
		 (while (< ap (length (cadr stack)))
		   (aset ann ap (aref (cadr stack) ap))
		   (incf ap))))
	  ;; Finish popping annotations
	  (setq stack (cdr (cdr stack))))
	 (t (incf op)))
	(incf ip))
      (setq topl (reverse (cons (point-max) topl)))
      ;; If we want Coq pbp: (setq coq-current-goal 1)
      (while (setq ip (car topl) 
		   topl (cdr topl))
	(pbp-make-top-span ip (car topl))))))

(defun proof-shell-strip-annotations (string)
  (let* ((ip 0) (op 0) (l (length string)) (out (make-string l ?x )))
    (while (< ip l)
      (if (>= (aref string ip) proof-shell-first-special-char)
	  (if (char-equal (aref string ip) proof-shell-start-char)
	      (progn (incf ip)
		     (while (< (aref string ip) proof-shell-first-special-char)
		       (incf ip))))
	(aset out op (aref string ip))
	(incf op))
      (incf ip))
    (substring out 0 op)))

(defun proof-shell-handle-output (start-regexp end-regexp append-face)
  "Pretty print output in PROCESS buffer in specified region.
The region begins with the match for START-REGEXP and is delimited by
END-REGEXP. The match for END-REGEXP is not part of the specified region.
Removes any annotations in the region.
Fontifies the region.
Appends APPEND-FACE to the text property of the region .
Returns the string (with faces) in the specified region."
  (let (start end string)
    (save-excursion
      (set-buffer proof-shell-buffer)
      (goto-char (point-max))
      (setq start (search-backward-regexp start-regexp))
      (save-excursion (setq end (- (search-forward-regexp end-regexp)
				   (length (match-string 0)))))
      (setq string
	    (proof-shell-strip-annotations (buffer-substring start end)))
      (delete-region start end)
      (insert string)
      (setq end (+ start (length string)))
      (font-lock-fontify-region start end)
      (font-lock-append-text-property start end 'face append-face)
      (buffer-substring start end))))

(defun proof-shell-handle-delayed-output ()
  (let ((ins (car proof-shell-delayed-output))
	(str (cdr proof-shell-delayed-output)))
    (display-buffer proof-pbp-buffer)
    (save-excursion
      (cond 
       ((eq ins 'insert)
	(setq str (proof-shell-strip-annotations str))
	(set-buffer proof-pbp-buffer)
	(erase-buffer)
	(insert str))
       ((eq ins 'analyse)
	(proof-shell-analyse-structure str))
       (t (set-buffer proof-pbp-buffer)
	  (insert "\n\nbug???")))))
  (run-hooks 'proof-shell-handle-delayed-output-hook)
  (setq proof-shell-delayed-output (cons 'insert "done")))

;; Notes on markup in the scripting buffer. (da)
;;
;; The locked region is covered by a collection of non-overlaping
;; spans (our abstraction of extents/overlays).
;;
;; For an unfinished proof, there is one extent for each command 
;; or comment outside a command.   For a finished proof, there
;; is one extent for the whole proof.
;;
;; Each command span has a 'type property, one of:
;;
;;     'vanilla      Initialised in proof-semis-to-vanillas, for
;;     'goalsave 
;;     'comment      A comment outside a command.
;;
;;  All spans except those of type 'comment have a 'cmd property,
;;  which is set to a string of its command.  This is the
;;  text in the buffer stripped of leading whitespace and any comments.
;;
;; 

(defun proof-shell-handle-error (cmd string)
  "React on an error message triggered by the prover.
We display the process buffer, scroll to the end, beep and fontify the
error message. At the end it calls `proof-shell-handle-error-hook'. "
    ;; We extract all text between text matching
    ;; `proof-shell-error-regexp' and the following prompt.
    ;; Alternatively one could higlight all output between the
    ;; previous and the current prompt.
    ;; +/- of our approach
    ;; + Previous not so relevent output is not highlighted
    ;; - Proof systems have to conform to error messages whose start  can be
    ;;   detected by a regular expression.
  (proof-shell-handle-output
   proof-shell-error-regexp proof-shell-annotated-prompt-regexp
   'font-lock-error-face)
  (save-excursion (display-buffer proof-shell-buffer))
  (beep)

  ;; unwind script buffer
  (set-buffer proof-script-buffer)
  (proof-detach-queue)
  (delete-spans (proof-locked-end) (point-max) 'type)
  (proof-release-lock)
  (run-hooks 'proof-shell-handle-error-hook))

(defun proof-shell-handle-interrupt ()
  (save-excursion 
    (display-buffer (set-buffer proof-pbp-buffer))
    (goto-char (point-max))
    (newline 2)
    (insert-string 
     "Interrupt: Script Management may be in an inconsistent state\n")
    (beep))
  (set-buffer proof-script-buffer)
  (if proof-shell-busy
      (progn (proof-detach-queue)
	     (delete-spans (proof-locked-end) (point-max) 'type)
	     (proof-release-lock))))


(defun proof-goals-pos (span maparg)
  "Given a span, this function returns the start of it if corresponds
  to a goal and nil otherwise."
 (and (eq 'goal (car (span-property span 'proof-top-element)))
		(span-start span)))

(defun proof-pbp-focus-on-first-goal ()
  "If the `proof-pbp-buffer' contains goals, the first one is brought
  into view."
  (and (fboundp 'map-extents)
       (let
	   ((pos (map-extents 'proof-goals-pos proof-pbp-buffer
			      nil nil nil nil 'proof-top-element)))
	 (and pos (set-window-point
		   (get-buffer-window proof-pbp-buffer t) pos)))))

           

(defun proof-shell-process-output (cmd string)
  "Deals with errors, start of proofs, abortions of proofs and
  completions of proofs. All other output from the proof engine is
  simply reported to the user in the RESPONSE buffer. To extend this
  function, set `proof-shell-process-output-system-specific'.

  The basic output processing function - it can return one of 4  
  things: 'error, 'interrupt, 'loopback, or nil. 'loopback means this
  was output from pbp, and should be inserted into the script buffer
  and sent back to the proof assistant."
  (cond 
   ((string-match proof-shell-error-regexp string)
    (cons 'error (proof-shell-strip-annotations 
		  (substring string (match-beginning 0)))))

   ((string-match proof-shell-interrupt-regexp string)
    'interrupt)

   ((and proof-shell-abort-goal-regexp
	 (string-match proof-shell-abort-goal-regexp string))
    (setq proof-shell-delayed-output (cons 'insert "\n\nAborted"))
    ())
	 
   ((string-match proof-shell-proof-completed-regexp string)
    (setq proof-shell-proof-completed t)
    (setq proof-shell-delayed-output
	  (cons 'insert (concat "\n" (match-string 0 string)))))

   ((string-match proof-shell-start-goals-regexp string)
    (setq proof-shell-proof-completed nil)
    (let (start end)
      (while (progn (setq start (match-end 0))
		    (string-match proof-shell-start-goals-regexp 
				  string start)))
      (setq end (string-match proof-shell-end-goals-regexp string start))
      (setq proof-shell-delayed-output 
	    (cons 'analyse (substring string start end)))))
       
   ((string-match proof-shell-result-start string)
    (setq proof-shell-proof-completed nil)
    (let (start end)
      (setq start (+ 1 (match-end 0)))
      (string-match proof-shell-result-end string)
      (setq end (- (match-beginning 0) 1))
      (cons 'loopback (substring string start end))))
   
   ;; hook to tailor proof-shell-process-output to a specific proof
   ;; system  
   ((and proof-shell-process-output-system-specific
	 (funcall (car proof-shell-process-output-system-specific)
		  cmd string))
    (funcall (cdr proof-shell-process-output-system-specific)
	     cmd string))

   (t (setq proof-shell-delayed-output (cons 'insert string)))))
         
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Low-level commands for shell communication                     ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; FIXME da: Should this kind of ordinary input go onto the queue of
;; things to do?  Then errors during processing would prevent it being
;; sent.  Also the proof shell lock would be set automatically, which
;; might be nice?
(defun proof-shell-insert (string)
  (set-buffer proof-shell-buffer)
  (goto-char (point-max))

  (run-hooks 'proof-shell-insert-hook)
  (insert string)

  ;; xemacs and emacs19 have different semantics for what happens when
  ;; shell input is sent next to a marker
  ;; the following code accommodates both definitions
  (if (marker-position proof-marker)
      (let ((inserted (point)))
	(comint-send-input)
	(set-marker proof-marker inserted))
    (comint-send-input)))

;; da: This function strips carriage returns from string, then
;; sends it.  (Why strip CRs?)
(defun proof-send (string)
  (let ((l (length string)) (i 0))
    (while (< i l)
      (if (= (aref string i) ?\n) (aset string i ?\ ))
      (incf i)))
  (save-excursion (proof-shell-insert string)))

(defun proof-check-process-available (&optional relaxed)
  "Checks whether the proof process is available.
Specifically:
     (1) Is a proof process running?
     (2) Is the proof process idle?
     (3) Does the current buffer own the proof process?
     (4) Is the current buffer a proof script?
It signals an error if at least one of the conditions is not
fulfilled. If optional arg RELAXED is set, only (1) and (2) are 
tested.
Note that this is not really intended for anything complicated -
just to stop the user accidentally sending a command while the
queue is running."
  (if (proof-shell-live-buffer)
      (cond
       (proof-shell-busy (error "Proof Process Busy!"))
       (relaxed ())			;exit cond
       ((not (eq proof-script-buffer (current-buffer)))
	(error "Don't own proof process"))))
  (if (not (or relaxed (eq proof-buffer-type 'script)))
      (error "Must be running in a script buffer")))

(defun proof-grab-lock (&optional relaxed)
  (proof-start-shell)
  (proof-check-process-available relaxed)
  (setq proof-shell-busy t))

(defun proof-release-lock ()
  (if (proof-shell-live-buffer)
      (progn
	(if (not proof-shell-busy)
	    ; (error "Bug in proof-release-lock: Proof process not busy")
	    (message "Nag, nag, nag: proof-release-lock: Proof process not busy"))
	(if (not (eq proof-script-buffer (current-buffer)))
	    (error "Bug in proof-release-lock: Don't own process"))
	(setq proof-shell-busy nil))))

; Pass start and end as nil if the cmd isn't in the buffer.

(defun proof-start-queue (start end alist &optional relaxed)
  (if start
      (proof-set-queue-endpoints start end))
  (let (item)
    (while (and alist (string= 
		       (nth 1 (setq item (car alist))) 
		       proof-no-command))
    (funcall (nth 2 item) (car item))
    (setq alist (cdr alist)))
  (if alist
      (progn
	(proof-grab-lock relaxed) 
	(setq proof-shell-delayed-output (cons 'insert "Done."))
	(setq proof-action-list alist)
	(proof-send (nth 1 item))))))

; returns t if it's run out of input

(defun proof-shell-exec-loop ()
  (save-excursion
    (set-buffer proof-script-buffer)
    (if (null proof-action-list) (error "Non Sequitur"))
    (let ((item (car proof-action-list)))
      (funcall (nth 2 item) (car item))
      (setq proof-action-list (cdr proof-action-list))
      (while (and proof-action-list
		(string= 
		 (nth 1 (setq item (car proof-action-list))) 
		 proof-no-command))
	(funcall (nth 2 item) (car item))
	(setq proof-action-list (cdr proof-action-list)))
      (if (null proof-action-list)
	  (progn (proof-release-lock)
		 (proof-detach-queue)
		 t)
	(proof-send (nth 1 item))
	nil))))

(defun proof-shell-insert-loopback-cmd  (cmd)
  "Insert command sequence triggered by the proof process
at the end of locked region (after inserting a newline and indenting)."
  (save-excursion
    (set-buffer proof-script-buffer)
    (let (span)
      (proof-goto-end-of-locked)
      (newline-and-indent)
      (insert cmd)
      (setq span (make-span (proof-locked-end) (point)))
      (set-span-property span 'type 'pbp)
      (set-span-property span 'cmd cmd)
      (proof-set-queue-endpoints (proof-locked-end) (point))
      (setq proof-action-list 
	    (cons (car proof-action-list) 
		  (cons (list span cmd 'proof-done-advancing)
			(cdr proof-action-list)))))))

;; ******** NB **********
;;  While we're using pty communication, this code is OK, since all
;; eager annotations are one line long, and we get input a line at a
;; time. If we go over to piped communication, it will break.

;; FIXME: highlight eager annotation-end : fix proof-shell-handle-output
;; to highlight whole string.
(defun proof-shell-popup-eager-annotation ()
  "Eager annotations are annotations which the proof system produces
while it's doing something (e.g. loading libraries) to say how much
progress it's made. Obviously we need to display these as soon as they
arrive."
  (let ((str (proof-shell-handle-output
	      proof-shell-eager-annotation-start
	      proof-shell-eager-annotation-end
	      'font-lock-eager-annotation-face))
	file module)
    (proof-message str)
    ;;FIXME: LEGO specific regular expression to detect that LEGO is
    ;;processing a new module
    (if (string-match "Creating mark \"\\(.*\\)\" \\[\\(.*\\)\\]" str)
	(progn
	  (setq file (match-string 2 str)
		module (match-string 1 str))
	  (if (string= file "") 
	      (setq file (buffer-file-name proof-script-buffer)))
	  (setq file (expand-file-name file))
	  (if (string-match "\\(.*\\)\\.." file)
	      (setq file (match-string 1 file)))
	  (setq proof-included-files-list (cons (cons module file)
						proof-included-files-list))))))

(defun proof-shell-filter (str) 
  "Filter for the proof assistant shell-process.
We sleep until we get a wakeup-char in the input, then run
proof-shell-process-output, and set proof-marker to keep track of
how far we've got."
  (and proof-shell-eager-annotation-start
       (string-match proof-shell-eager-annotation-start str)
       (proof-shell-popup-eager-annotation))
  (if (or
       ;; Some proof systems can be hacked to have annotated prompts;
       ;; for these we set proof-shell-wakeup-char to the annotation special.  
       (and proof-shell-wakeup-char
	   (string-match (char-to-string proof-shell-wakeup-char) str))
       ;; Others rely on a standard top-level (e.g. SML) whose prompt can't
       ;; be hacked.  For those we use the annotated prompt regexp.
       (string-match proof-shell-annotated-prompt-regexp str))
      (if (null (marker-position proof-marker))
	  ;; Set marker to first prompt in output buffer, and sleep again.
	  (progn
	    (goto-char (point-min))
	    (re-search-forward proof-shell-annotated-prompt-regexp)
	    (set-marker proof-marker (point)))
	;; We've matched against a second prompt in str now.  Search
	;; the output buffer for the second prompt after the one previously
	;; marked.
	(let (string res cmd)	
	  (goto-char (marker-position proof-marker))
	  (re-search-forward proof-shell-annotated-prompt-regexp nil t)
	  (backward-char (- (match-end 0) (match-beginning 0)))
	  (setq string (buffer-substring (marker-position proof-marker)
					 (point)))
	  (goto-char (point-max))	; da: assumed to be after a prompt?
	  (setq cmd (nth 1 (car proof-action-list)))
	  (save-excursion
	    (setq res (proof-shell-process-output cmd string))
	    ;; da: Added this next line to redisplay, for proof-toolbar
	    ;; FIXME: should do this for all frames displaying the script
	    ;; buffer!
	    ;; ODDITY: has strange effect on highlighting, leave it.
	    ;; (redisplay-frame (window-buffer  t)
	    (cond
	     ((eq (car-safe res) 'error)
	      (proof-shell-handle-error cmd (cdr res)))
	     ((eq res 'interrupt)
	      (proof-shell-handle-interrupt))
	     ((eq (car-safe res) 'loopback)
	      (proof-shell-insert-loopback-cmd (cdr res))
	      (proof-shell-exec-loop))
	     (t (if (proof-shell-exec-loop)
		    (proof-shell-handle-delayed-output)))))))))

(defun proof-last-goal-or-goalsave ()
  (save-excursion
    (let ((span (span-at-before (proof-locked-end) 'type)))
    (while (and span 
		(not (eq (span-property span 'type) 'goalsave))
		(or (eq (span-property span 'type) 'comment)
		    (not (funcall proof-goal-command-p
				       (span-property span 'cmd)))))
      (setq span (prev-span span 'type)))
    span)))
    
;; This needs some work to make it generic, since most of the code
;; doesn't apply to Coq at all.  (Never mind Isabelle!)
(defun proof-steal-process ()
  "This allows us to steal the process if we want to change the buffer
in which script management is running."
  (proof-start-shell)
  (if proof-shell-busy (error "Proof Process Busy!"))
  (if (not (eq proof-buffer-type 'script))
      (error "Must be running in a script buffer"))
  (cond
   ((eq proof-script-buffer (current-buffer))
    nil)
   (t
    (let ((flist proof-included-files-list) 
	  (file (expand-file-name (buffer-file-name))) span (cmd ""))
      (if (string-match "\\(.*\\)\\.." file) (setq file (match-string 1 file)))
      (while (and flist (not (string= file (cdr (car flist)))))
	(setq flist (cdr flist)))
      (if (null flist) 
	  (if (not (y-or-n-p "Steal script management? " )) (error "Aborted"))
	(if (not (y-or-n-p "Reprocess this file? " )) (error "Aborted")))
      (if (not (buffer-name proof-script-buffer))
	  (message "Warning: Proof script buffer deleted: proof state may be inconsistent")
	(save-excursion
	  (set-buffer proof-script-buffer)
	  (setq proof-active-buffer-fake-minor-mode nil)
	  (setq span (proof-last-goal-or-goalsave))
	  ;; This won't work for Coq if we have recursive goals in progress
	  (if (and span (not (eq (span-property span 'type) 'goalsave)))
	      (setq cmd proof-kill-goal-command))
	  (proof-detach-segments)
	  (delete-spans (point-min) (point-max) 'type)))

      (setq proof-script-buffer (current-buffer))
      (proof-init-segmentation)
      (setq proof-active-buffer-fake-minor-mode t)

      (cond 
       (flist
	(list nil (concat cmd "ForgetMark " (car (car flist)) ";")
	      `(lambda (span) (setq proof-included-files-list 
				    (quote ,(cdr flist))))))
       ((not (string= cmd ""))
	(list nil cmd 'proof-done-invisible))
       (t nil))))))

(defun proof-done-invisible (span) ())

(defun proof-invisible-command (cmd &optional relaxed)
  "Send cmd to the proof process without responding to the user."
  (proof-check-process-available relaxed)
  (if (not (string-match proof-re-end-of-cmd cmd))
      (setq cmd (concat cmd proof-terminal-string)))
  (proof-start-queue nil nil (list (list nil cmd
  'proof-done-invisible)) relaxed))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;          User Commands                                           ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	
; Script management uses two major segments: Locked, which marks text
; which has been sent to the proof assistant and cannot be altered
; without being retracted, and Queue, which contains stuff being
; queued for processing.  proof-action-list contains a list of
; (span,command,action) triples. The loop looks like: Execute the
; command, and if it's successful, do action on span.  If the
; command's not successful, we bounce the rest of the queue and do
; some error processing.
;
; when a span has been processed, we classify it as follows:
; 'goalsave - denoting a 'goalsave pair in the locked region
;    a 'goalsave region has a 'name property which is the name of the goal
; 'comment - denoting a comment
; 'pbp - denoting a span created by pbp
; 'vanilla - denoting any other span.
;   'pbp & 'vanilla spans have a property 'cmd, which says what
;   command they contain. 

; We don't allow commands while the queue has anything in it.  So we
; do configuration by concatenating the config command on the front in
; proof-send

;;         proof-assert-until-point, and various gunk for its       ;;
;;         setup and callback                                       ;;

;; This code is for nested goals in Coq, and shouldn't affect things
;; in LEGO.  It lifts "local" lemmas from inside goals out to top
;; level.
;; FIXME da: belongs in coq.el

(defun proof-lift-global (glob-span)
  (let (start (next (span-at 1 'type)) str (goal-p nil))
    (while (and next (and (not (eq next glob-span)) (not goal-p)))
      (if (and (eq (span-property next 'type) 'vanilla)
	       (funcall proof-goal-command-p (span-property next 'cmd)))
	  (setq goal-p t)
	(setq next (next-span next 'type))))

    (if (and next (not (eq next glob-span)))
	(progn
	  (proof-unlock-locked)
	  (setq str (buffer-substring (span-start glob-span)
				      (span-end glob-span)))
	  (delete-region (span-start glob-span) (span-end glob-span))
	  (goto-char (span-start next))
	  (setq start (point))
	  (insert str "\n")
	  (set-span-endpoints glob-span start (point))
	  (set-span-start next (point))
	  (proof-lock-unlocked)))))

;; This is the actual callback for assert-until-point.

(defun proof-done-advancing (span)
  (let ((end (span-end span)) nam gspan next cmd)
    (proof-set-locked-end end)
    (proof-set-queue-start end)
    (setq cmd (span-property span 'cmd))
    (cond
     ((eq (span-property span 'type) 'comment)
      (set-span-property span 'mouse-face 'highlight))
     ((string-match proof-save-command-regexp cmd)
      ;; In coq, we have the invariant that if we've done a save and
      ;; there's a top-level declaration then it must be the
      ;; associated goal.  (Notice that because it's a callback it
      ;; must have been approved by the theorem prover.)
      (if (string-match proof-save-with-hole-regexp cmd)
	  (setq nam (match-string 2 cmd)))
      (setq gspan span)
      (while (or (eq (span-property gspan 'type) 'comment)
		 (not (funcall proof-goal-command-p 
				    (setq cmd (span-property gspan 'cmd)))))
	(setq next (prev-span gspan 'type))
	(delete-span gspan)
	(setq gspan next))

      (if (null nam)
	  (if (string-match proof-goal-with-hole-regexp
			    (span-property gspan 'cmd))
	      (setq nam (match-string 2 (span-property gspan 'cmd)))
	    ;; This only works for Coq, but LEGO raises an error if
	    ;; there's no name.
	    ;; FIXME: a nonsense for Isabelle.
	    (setq nam "Unnamed_thm")))

      (set-span-end gspan end)
      (set-span-property gspan 'mouse-face 'highlight)
      (set-span-property gspan 'type 'goalsave)
      (set-span-property gspan 'name nam)

      (proof-lift-global gspan))
     (t
      (set-span-property span 'mouse-face 'highlight)
      (if (funcall proof-global-p cmd)
	  (proof-lift-global span))))))

; depth marks number of nested comments. quote-parity is false if
; we're inside ""'s.  Only one of (depth > 0) and (not quote-parity)
; should be true at once. -- hhg

;; FIXME da: Below it would probably be faster to use the primitive
;; skip-chars-forward rather than scanning character-by-character 
;; with a lisp loop over the whole region. Also I'm not convinced that
;; Emacs should be better at skipping whitespace and comments than the
;; proof process itself!

(defun proof-segment-up-to (pos &optional next-command-end)
  "Create a list of (type,int,string) tuples from end of locked region to POS.
Each tuple consists of denotes the command and the position of its terminator,
type is one of 'comment, or 'cmd. 'unclosed-comment may be consed onto
the start if the segment finishes with an unclosed comment.
If optional NEXT-COMMAND-END is non-nil, we contine past POS until
the next command end."
  (save-excursion
    (let ((str (make-string (- (buffer-size)
			       (proof-unprocessed-begin) -10) ?x))
	  (i 0) (depth 0) (quote-parity t) done alist c)
     (proof-goto-end-of-locked)
     (while (not done)
       (cond
	;; Case 1. We've reached POS, not allowed to go past it,
	;; and are inside a comment
	((and (not next-command-end) (= (point) pos) (> depth 0))
	 (setq done t alist (cons 'unclosed-comment alist)))
	;; Case 2. We've reached the end of the buffer while
	;; scanning inside a comment or string
	((= (point) (point-max))
	 (cond
	  ((not quote-parity)
	   (message "Warning: unclosed quote"))
	  ((> depth 0)
	   (setq done t alist (cons 'unclosed-comment alist))))
	 (setq done t))
	;; Case 3. Found a comment end, not inside a string
	((and (looking-at (regexp-quote proof-comment-end)) quote-parity)
	 (if (= depth 0) 
	     (progn
	       (message "Warning: extraneous comment end")
	       (setq done t))
	   (setq depth (- depth 1))
	   (forward-char (length proof-comment-end))
	   (if (eq i 0) 
	       (setq alist (cons (list 'comment "" (point)) alist))
	     (aset str i ?\ )
	     (incf i))))
	;; Case 4. Found a comment start, not inside a string
	((and (looking-at (regexp-quote proof-comment-start)) quote-parity)
	 (setq depth (+ depth 1))
	 (forward-char (length proof-comment-start)))
	;; Case 5. Inside a comment. 
	((> depth 0)
	 (forward-char))
	;; Case 6. Anything else
	(t
	 ;; Skip whitespace before the start of a command, otherwise
	 ;; other characters in the accumulator string str
	 (setq c (char-after (point)))
	 (if (or (> i 0) (not (= (char-syntax c) ?\ )))
	     (progn
	       (aset str i c)
	       (incf i)))
	 
	 (if (looking-at "\"")		; FIXME da: should this be more generic?
	     (setq quote-parity (not quote-parity)))
	 
	 (forward-char)

	 ;; Found the end of a command
	 (if (and (= c proof-terminal-char) quote-parity)
	     (progn 
	       (setq alist 
		     (cons (list 'cmd (substring str 0 i) (point)) alist))
	       (if (>= (point) pos)
		   (setq done t)
		 (setq i 0)))))))
     alist)))

(defun proof-semis-to-vanillas (semis &optional callback-fn)
  "Convert a sequence of semicolon positions (returned by the above
function) to a set of vanilla extents."
  (let ((ct (proof-locked-end)) span alist semi)
    (while (not (null semis))
      (setq semi (car semis)
            span (make-span ct (nth 2 semi))
	    ct (nth 2 semi))
      (if (eq (car (car semis)) 'cmd)
	  (progn
	    (set-span-property span 'type 'vanilla)
	    (set-span-property span 'cmd (nth 1 semi))
	    (setq alist (cons (list span (nth 1 semi) 
				    (or callback-fn 'proof-done-advancing))
			      alist)))
	(set-span-property span 'type 'comment)
	(setq alist (cons (list span proof-no-command 'proof-done-advancing) alist)))
	(setq semis (cdr semis)))
    (nreverse alist)))

; Assert until point - We actually use this to implement the 
; assert-until-point, active terminator keypress, and find-next-terminator. 
; In different cases we want different things, but usually the information
; (i.e. are we inside a comment) isn't available until we've actually run
; proof-segment-up-to (point), hence all the different options when we've
; done so.

(defun proof-assert-until-point
  (&optional unclosed-comment-fun ignore-proof-process-p)
  "Process the region from the end of the locked-region until point.
   Default action if inside a comment is just to go until the start of
   the comment. If you want something different, put it inside
   unclosed-comment-fun. If ignore-proof-process-p is set, no commands
   will be added to the queue."
  (interactive)
  (let ((pt (point))
	(crowbar (or ignore-proof-process-p (proof-steal-process)))
	semis)
    (save-excursion
      (if (not (re-search-backward "\\S-" (proof-unprocessed-begin) t))
	  (progn (goto-char pt)
		 (error "Nothing to do!")))
      (setq semis (proof-segment-up-to (point))))
    (if (and unclosed-comment-fun (eq 'unclosed-comment (car semis)))
	(funcall unclosed-comment-fun)
      (if (eq 'unclosed-comment (car semis)) (setq semis (cdr semis)))
      (if (and (not ignore-proof-process-p) (not crowbar) (null semis))
	  (error "Nothing to do!"))
      (goto-char (nth 2 (car semis)))
      (and (not ignore-proof-process-p)
	   (let ((vanillas (proof-semis-to-vanillas (nreverse semis))))
	     (if crowbar (setq vanillas (cons crowbar vanillas)))
	     (proof-start-queue (proof-locked-end) (point) vanillas))))))

;; da: This is my alternative/additional version of the above.
;; It works from the locked region too.
;; I find it more convenient to assert up to the current command (command
;; point is inside), and move to the character past the terminator.
;; This means proofs can be easily replayed with point at the start
;; of lines.  Above function gives stupid "nothing to do error." when
;; point is on the start of line or in the locked region.
(defun proof-assert-next-command ()
  "Experimental variant of proof-assert-until-point.
Works in locked region and at start of commands."
  (interactive)
  (let ((crowbar (proof-steal-process))	semis)
    (save-excursion
      ;; CHANGE from proof-assert-until-point: don't bother check
      ;; for non-whitespace between locked region and point.
      ;; CHANGE: ask proof-segment-up-to to scan until command end
      ;; (which it used to do anyway, except in the case of a comment)
      (setq semis (proof-segment-up-to (point) t)))
    (if (eq 'unclosed-comment (car semis)) (setq semis (cdr semis)))
    (if (and (not crowbar) (null semis))
	(error "Nothing to do!"))
    (goto-char (nth 2 (car semis)))
    ;; ADDITION from proof-assert-until-point: skip whitespace
    (skip-chars-forward (if proof-one-command-per-line " \t" " \t\n"))
    (let ((vanillas (proof-semis-to-vanillas (nreverse semis))))
      (if crowbar (setq vanillas (cons crowbar vanillas)))
      (proof-start-queue (proof-locked-end) (point) vanillas))))

;;         insert-pbp-command - an advancing command, for use when  ;;
;;         PbpHyp or Pbp has executed in LEGO, and returned a       ;;
;;         command for us to run                                    ;;

(defun proof-insert-pbp-command (cmd)
  (proof-check-process-available)
  (let (span)
    (proof-goto-end-of-locked)
    (insert cmd)
    (setq span (make-span (proof-locked-end) (point)))
    (set-span-property span 'type 'pbp)
    (set-span-property span 'cmd cmd)
    (proof-start-queue (proof-locked-end) (point) 
		       (list (list span cmd 'proof-done-advancing)))))


;;         proof-retract-until-point and associated gunk            ;;
;;         most of the hard work (i.e computing the commands to do  ;;
;;         the retraction) is implemented in the customisation      ;;
;;         module (lego.el or coq.el) which is why this looks so    ;;
;;         straightforward                                          ;;


(defun proof-done-retracting (span)
  "Updates display after proof process has reset its state. See also
the documentation for `proof-retract-until-point'. It optionally
deletes the region corresponding to the proof sequence."
  (let ((start (span-start span))
        (end (span-end span))
	(kill (span-property span 'delete-me)))
    (proof-set-locked-end start)
    (proof-set-queue-end start)
    (delete-spans start end 'type)
    (delete-span span)
    (if kill (delete-region start end))))

(defun proof-setup-retract-action (start end proof-command delete-region)
  (let ((span (make-span start end)))
    (set-span-property span 'delete-me delete-region)
    (list (list span proof-command 'proof-done-retracting))))

(defun proof-retract-target (target delete-region)
  (let ((end (proof-locked-end))
	(start (span-start target))
	(span (proof-last-goal-or-goalsave))
	actions)
    
    (if (and span (not (eq (span-property span 'type) 'goalsave)))
	(if (< (span-end span) (span-end target))
	    (progn
	      (setq span target)
	      (while (and span (eq (span-property span 'type) 'comment))
		(setq span (next-span span 'type)))
	      (setq actions (proof-setup-retract-action
			     start end 
			     (if (null span) proof-no-command
			       (funcall proof-count-undos-fn span))
			     delete-region)
		    end start))
	  
	  (setq actions (proof-setup-retract-action (span-start span) end
						    proof-kill-goal-command
						    delete-region)
		end (span-start span))))
    
    (if (> end start) 
	(setq actions
	      (nconc actions (proof-setup-retract-action 
			      start end
			      (funcall proof-find-and-forget-fn target)
			      delete-region))))
      
    (proof-start-queue (min start end) (proof-locked-end) actions)))

;; FIXME da:  I would rather that this function moved point to
;; the start of the region retracted?

(defun proof-retract-until-point (&optional delete-region)
  "Sets up the proof process for retracting until point. In
   particular, it sets a flag for the filter process to call
   `proof-done-retracting' after the proof process has actually
   successfully reset its state. It optionally deletes the region in
   the proof script corresponding to the proof command sequence. If
   this function is invoked outside a locked region, the last
   successfully processed command is undone."
  (interactive)
  (proof-check-process-available)
  (let ((span (span-at (point) 'type)))
    (if (null (proof-locked-end)) (error "No locked region"))
    (and (null span)
	 (progn (proof-goto-end-of-locked) (backward-char)
		(setq span (span-at (point) 'type))))
    (proof-retract-target span delete-region)))

;;         proof-try-command                                        ;;
;;         this isn't really in the spirit of script management,    ;;
;;         but sometimes the user wants to just try an expression   ;;
;;         without having to undo it in order to try something      ;;
;;         different. Of course you can easily lose sync by doing   ;;
;;         something here which changes the proof state             ;;

(defun proof-done-trying (span)
  (delete-span span)
  (proof-detach-queue))
			
(defun proof-try-command
  (&optional unclosed-comment-fun) 

  "Process the command at point,
   but don't add it to the locked region. This will only happen if
   the command satisfies proof-state-preserving-p.

   Default action if inside a comment is just to go until the start of
   the comment. If you want something different, put it inside
   unclosed-comment-fun."
  (interactive)
  (let ((pt (point)) semis crowbar test)
    (setq crowbar (proof-steal-process))
    (save-excursion
      (if (not (re-search-backward "\\S-" (proof-locked-end) t))
	  (progn (goto-char pt)
		 (error "Nothing to do!")))
      (setq semis (proof-segment-up-to (point))))
    (if (and unclosed-comment-fun (eq 'unclosed-comment (car semis)))
	(funcall unclosed-comment-fun)
      (if (eq 'unclosed-comment (car semis)) (setq semis (cdr semis)))
      (if (and (not crowbar) (null semis)) (error "Nothing to do!"))
      (setq test (car semis))
      (if (not (funcall proof-state-preserving-p (nth 1 test)))
	  (error "Command is not state preserving"))
      (goto-char (nth 2 test))
      (let ((vanillas (proof-semis-to-vanillas (list test)
					       'proof-done-trying)))
	(if crowbar (setq vanillas (cons crowbar vanillas)))
	(proof-start-queue (proof-locked-end) (point) vanillas)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;         misc other user functions                                ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defun proof-undo-last-successful-command (&optional no-delete)
  "Undo last successful command at end of locked region.a
Unless optional NO-DELETE is set, the text is also deleted from
the proof script."
  (interactive "p")
  (goto-char (span-start (span-at-before (proof-locked-end) 'type)))
  (proof-retract-until-point (not no-delete)))

(defun proof-interrupt-process ()
  (interactive)
  (if (not (proof-shell-live-buffer))
      (error "Proof Process Not Started!"))
  (if (not (eq proof-script-buffer (current-buffer)))
      (error "Don't own process!"))
  (if (not proof-shell-busy)
      (error "Proof Process Not Active!"))
  (save-excursion
    (set-buffer proof-shell-buffer)
    (comint-interrupt-subjob)))
  
    
(defun proof-find-next-terminator ()
  "Set point after next `proof-terminal-char'."
  (interactive)
  (let ((cmd (span-at (point) 'type)))
    (if cmd (goto-char (span-end cmd))
      (and (re-search-forward "\\S-" nil t)
	   (proof-assert-until-point nil 'ignore-proof-process)))))

(defun proof-goto-command-start ()
  "Move point to start of current command."
  (interactive)
  (let ((cmd (span-at (point) 'type)))
    (if cmd (goto-char (span-start cmd)) ; BUG: only works for unclosed proofs.
      (let ((semis (proof-segment-up-to (point) t)))
	(if (eq 'unclosed-comment (car semis)) (setq semis (cdr semis)))
	(if (and semis (car semis) (car (car semis)))
	    (progn
	      (goto-char (nth 2 (car (car semis))))
	      (skip-chars-forward " \t\n")))))))

(defun proof-process-buffer ()
  "Process the current buffer and set point at the end of the buffer."
  (interactive)
  (goto-char (point-max))
  (proof-assert-until-point))

;; For when things go horribly wrong
(defun proof-restart-script ()
  "Restart Proof General.
Kill off the proof assistant process and remove all markings in the
script buffer."
  (interactive)
  (save-excursion
    (if (buffer-live-p proof-script-buffer)
	(progn
	  (set-buffer proof-script-buffer)
	  (setq proof-active-buffer-fake-minor-mode nil)
	  (delete-spans (point-min) (point-max) 'type)
	  (proof-detach-segments)))
    (setq proof-shell-busy nil
	  proof-shell-proof-completed nil
	  proof-script-buffer nil)
    (if (buffer-live-p proof-shell-buffer) 
	(kill-buffer proof-shell-buffer))
    (if (buffer-live-p proof-pbp-buffer)
	(kill-buffer proof-pbp-buffer))))

;; For when things go not-quite-so-horribly wrong
;; FIXME: this may need work, and maybe isn't needed at
;; all (proof-retract-file when it appears may be enough).
(defun proof-restart-script-same-process ()
  (interactive)
  (save-excursion
    (if (buffer-live-p proof-script-buffer)
	(progn
	  (set-buffer proof-script-buffer)
	  (setq proof-active-buffer-fake-minor-mode nil)
	  (delete-spans (point-min) (point-max) 'type)
	  (proof-detach-segments)))))

;; A command for making things go horribly wrong - it moves the
;; end-of-locked-region marker backwards, so user had better move it
;; correctly to sync with the proof state, or things will go all
;; pear-shaped.

(defun proof-frob-locked-end ()
  (interactive)
  "Move the end of the locked region backwards. 
Only for use by consenting adults."
  (cond
   ((not (eq proof-script-buffer (current-buffer)))
    (error "Not in proof buffer"))
   ((> (point) (proof-locked-end))
    (error "Can only move backwards"))
   (t (proof-set-locked-end (point))
      (delete-spans (proof-locked-end) (point-max) 'type))))

(defvar proof-minibuffer-history nil
  "History of proof commands read from the minibuffer")

(defun proof-execute-minibuffer-cmd ()
  (interactive)
  (let (cmd)
    (proof-check-process-available 'relaxed)
    (setq cmd (read-string "Command: " nil 'proof-minibuffer-history))
    (proof-invisible-command cmd 'relaxed)))

;; da: below functions for input history simulation are quick hacks.
;; Could certainly be made more efficient.

(defvar proof-command-history nil
  "History used by proof-previous-matching-command and friends.")

(defun proof-build-command-history ()
  "Construct proof-command-history from script buffer.
Based on position of point."
  ;; let
  )

(defun proof-previous-matching-command (arg)
  "Search through previous commands for new command matching current input."
  (interactive))
  ;;(if (not (memq last-command '(proof-previous-matching-command
  ;; proof-next-matching-command)))
      ;; Start a new search
      
  

(defun proof-next-matching-command (arg)
  "Search through following commands for new command matching current input."
  (interactive "p")
  (proof-previous-matching-command (- arg)))
	  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Popup and Pulldown Menu ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Menu commands for the underlying proof assistant

;;; These are defcustom'd so that users may re-configure
;;; the system to their liking.
(defcustom proof-ctxt-string ""
  "*Command to display the context in proof assistant."
  :type 'string
  :group 'proof-general)

(defcustom proof-help-string ""
  "*Command to ask for help in proof assistant."
  :type 'string
  :group 'proof-general)

(defcustom proof-prf-string ""
  "Command to display proof state in proof assistant."
  :type 'string
  :group 'proof-general)

(defvar proof-goal-command nil
  "Command to set a goal in the proof assistant.  String or fn.
If a string, the format character %s will be replaced by the
goal string. If a function, should return a command string to
insert when called interactively.")

(defvar proof-save-command nil
  "Command to save a proved theorem in the proof assistant.  String or fn.
If a string, the format character %s will be replaced by the
theorem name. If a function, should return a command string to
insert when called interactively.")

;;; Functions using the above 

(defun proof-ctxt ()
  "List context."
  (interactive) 
  (proof-invisible-command (concat proof-ctxt-string proof-terminal-string)))

(defun proof-help ()
  "Print help message giving syntax."
  (interactive)
  (proof-invisible-command (concat proof-help-string proof-terminal-string)))

(defun proof-prf ()
  "List proof state."
  (interactive)
  (proof-invisible-command (concat proof-prf-string proof-terminal-string)))



;; FIXME: da: add more general function for inserting into the
;; script buffer and the proof process together, and using
;; a choice of minibuffer prompting (hated by power users, perfect
;; for novices).
;; Add named goals.
;; TODO:
;;   Add named goals.
;;   Coherent policy for movement here and elsewhere based on
;;    proof-one-command-per-line user option.
;;   Coherent policy for sending to process after writing into
;;    script buffer.  Could have one without the other.
;;    For example, may be more easy to edit complex goal string
;;    first in the script buffer.  Ditto for tactics, etc.

(defvar proof-issue-goal-history nil
  "History of goals for proof-issue-goal.")

(defun proof-issue-goal (goal-cmd)
  "Insert a goal command into the script buffer, issue it to prover."
  (interactive
   (if proof-goal-command 
       (if (stringp proof-goal-command)
	   (list (format proof-goal-command
			 (read-string "Goal: " ""
				      proof-issue-goal-history)))
	 (proof-goal-command))
     (error
      "Proof General not configured for goals: set proof-goal-command.")))
  (let ((proof-one-command-per-line t))   ; Goals always start at a new line
    (proof-issue-new-command goal-cmd)))

(defvar proof-issue-save-history nil
  "History of theorem names for proof-issue-save.")

(defun proof-issue-save (thmsave-cmd)
  "Insert a save theorem command into the script buffer, issue it."
  (interactive
   (if proof-save-command
       (if (stringp proof-save-command)
	   (list (format proof-save-command
			 (read-string "Save as: " ""
				      proof-issue-save-history)))
	 (proof-save-command))
     (error
      "Proof General not configured for save theorem: set proof-save-command.")))
  (let ((proof-one-command-per-line t))   ; Goals always start at a new line
    (proof-issue-new-command thmsave-cmd)))

(defun proof-script-new-command-advance ()
  "Move point to a nice position for a new command.
Assumes that point is at the end of a command."
  (interactive)
  (if proof-one-command-per-line
      ;; One command per line: move to next new line,
      ;; creating one if at end of buffer.
      (if (forward-line)
	  (newline))
    ;; Multiple commands per line: skip spaces at point,
    ;; if no spaces there already, add one.
    (if (skip-chars-forward " \t")
	(insert " "))))

(defun proof-issue-new-command (cmd)
  "Insert CMD into the script buffer and issue it to the proof assistant.
If point is in the locked region, move to the end of it first.
Start up the proof assistant if necessary."
  ;; FIXME: da: I think we need a (proof-script-switch-to-buffer)
  ;; function (so there is some control over display).
  (switch-to-buffer proof-script-buffer)
  (if (proof-in-locked-region-p)
      (proof-goto-end-of-locked-interactive))
  (proof-script-new-command-advance)
  ;; FIXME: fixup behaviour of undo here.  Really want
  ;; to temporarily disable undo for insertion.
  ;; (buffer-disable-undo) this trashes whole undo list!
  (insert cmd)
  ;; FIXME: could do proof-indent-line here, but let's
  ;; wait until indentation is fixed.
  (proof-assert-until-point))




;;; To be called from menu
(defun proof-info-mode ()
  "Call info on Proof General."
  (interactive)
  (info "ProofGeneral"))

(defun proof-exit ()
  "Exit Proof-assistant."
  (interactive)
  (proof-restart-script))

(defvar proof-help-menu
  '("Help"
	     ["Proof assistant web page"
	      (w3-fetch proof-www-home-page) t]
	     ["Help on Emacs proof-mode" proof-info-mode t]
	     )
  "The Help Menu in Script Management.")

(defvar proof-shared-menu
  (proof-append-element '(
            ["Display context" proof-ctxt
	      :active (proof-shell-live-buffer)]
            ["Display proof state" proof-prf
	      :active (proof-shell-live-buffer)]
	    ["Exit proof assistant" proof-exit
	      :active (proof-shell-live-buffer)]
	    "----"
	    ["Find definition/declaration" find-tag-other-window t]
	    )
	  proof-help-menu))

(defvar proof-menu  
  (append '("Commands"
            ["Toggle active terminator" proof-active-terminator-minor-mode
	     :active t
	     :style toggle
             :selected proof-active-terminator-minor-mode]
            "----")
          (list (if (string-match "XEmacs 19.1[2-9]" emacs-version)
		    "--:doubleLine" "----"))
          proof-shared-menu
          )
  "*The menu for the proof assistant.")

(defvar proof-shell-menu proof-shared-menu
  "The menu for the Proof-assistant shell")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;          Active terminator minor mode                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deflocal proof-active-terminator-minor-mode nil 
  "active terminator minor mode flag")

(defun proof-active-terminator-minor-mode (&optional arg)
  "Toggle PROOF's Active Terminator minor mode.
With arg, turn on the Active Terminator minor mode if and only if arg
is positive.

If Active terminator mode is enabled, a terminator will process the
current command."

 (interactive "P")
 
;; has this minor mode been registered as such?
  (or (assq 'proof-active-terminator-minor-mode minor-mode-alist)
      (setq minor-mode-alist
            (append minor-mode-alist
                    (list '(proof-active-terminator-minor-mode
			    (concat " " proof-terminal-string))))))

  (setq proof-active-terminator-minor-mode
        (if (null arg) (not proof-active-terminator-minor-mode)
          (> (prefix-numeric-value arg) 0)))
  (if (fboundp 'redraw-modeline)
      (redraw-modeline)
    (force-mode-line-update)))

(defun proof-process-active-terminator ()
  "Insert the proof command terminator, and assert up to it.
Fire up proof process if necessary."
  (let ((mrk (point)) ins)
    (if (looking-at "\\s-\\|\\'\\|\\w") 
	(if (not (re-search-backward "\\S-" (proof-unprocessed-begin) t))
	    (error "Nothing to do!")))
    (if (not (= (char-after (point)) proof-terminal-char))
	(progn (forward-char) (insert proof-terminal-string) (setq ins t)))
    (proof-assert-until-point
     (function (lambda ()
		 (if ins (backward-delete-char 1))
		 (goto-char mrk) (insert proof-terminal-string))))))

(defun proof-active-terminator ()
  "Insert the terminator, perhaps sending the command to the assistant.
If proof-active-terminator-minor-mode is non-nil, the command will be
sent to the assistant."
  (interactive)
  (if proof-active-terminator-minor-mode 
      (proof-process-active-terminator)
    (self-insert-command 1)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Proof General scripting mode configuration			    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; da: this isn't so nice if a scripting buffer should inherit
;; from another mode: e.g. for Isabelle, we would like to use
;; sml-mode.
;; FIXME: add more doc to the mode below, to give hints on
;; configuring for new assistants.
(define-derived-mode proof-mode fundamental-mode 
  proof-mode-name
  "Proof General major mode for proof scripts.
\\{proof-mode-map}
"
  (setq proof-buffer-type 'script))

;; FIXME: da: could we put these into another keymap already?
;; FIXME: da: it's offensive to experience users to rebind global stuff
;;        like meta-tab, this should be removed.
(defconst proof-universal-keys
  '(([(control c) (control c)] . proof-interrupt-process)
    ([(control c) (control v)] . proof-execute-minibuffer-cmd)
    ([(meta tab)]	       . tag-complete-symbol))
"List of keybindings which for the script and response buffer. 
Elements of the list are tuples (k . f) 
where `k' is a keybinding (vector) and `f' the designated function.")

;; Fixed definitions in proof-mode-map, which don't depend on
;; prover configuration.
;;; INDENT HACK: font-lock only recognizes define-key at start of line
(let ((map proof-mode-map))
(define-key map [(control c) (control e)] 'proof-find-next-terminator)
(define-key map [(control c) (control a)] 'proof-goto-command-start)
(define-key map [(control c) (control return)] 'proof-assert-next-command)
(define-key map [(control c) (return)]	  'proof-assert-until-point)
(define-key map [(control c) (control t)] 'proof-try-command)
(define-key map [(control c) ?u]	  'proof-retract-until-point)
(define-key map [(control c) (control u)] 'proof-undo-last-successful-command)
(define-key map [(control c) ?\']	  'proof-goto-end-of-locked-interactive)
(define-key map [(control button1)]	  'proof-send-span)
(define-key map [(control c) (control b)] 'proof-process-buffer)
(define-key map [(control c) (control z)] 'proof-frob-locked-end)
(define-key map [(control c) (control p)] 'proof-prf)
(define-key map [(control c) ?c]	  'proof-ctxt)
(define-key map [(control c) ?h]	  'proof-help)
(define-key map [(meta p)]		  'proof-previous-matching-command)
(define-key map [(meta n)]		  'proof-next-matching-command)
;; FIXME da: this shouldn't need setting, because it works
;; via indent-line-function which is set below.  Check this.
(define-key map [tab] 'proof-indent-line)
(proof-define-keys map proof-universal-keys))



;; the following callback is an irritating hack - there should be some
;; elegant mechanism for computing constants after the child has
;; configured.

(defun proof-config-done () 
  "Finish setup of Proof General scripting mode.
Call this function in the derived mode for the proof assistant to
finish setup which depends on specific proof assistant configuration."
  ;; calculate some strings and regexps for searching
  (setq proof-terminal-string (char-to-string proof-terminal-char))

  ;; FIXME: these are LEGO specific!
  (setq pbp-goal-command (concat "Pbp %s" proof-terminal-string))
  (setq pbp-hyp-command (concat "PbpHyp %s" proof-terminal-string))

  ;; FIXME da: I'm not sure we ought to add spaces here, but if
  ;; we don't, there would be trouble overloading these settings
  ;; to also use as regexps for finding comments.
  ;; 
  (make-local-variable 'comment-start)
  (setq comment-start (concat proof-comment-start " "))
  (make-local-variable 'comment-end)
  (setq comment-end (concat " " proof-comment-end))
  (make-local-variable 'comment-start-skip)
  (setq comment-start-skip 
    (concat (regexp-quote proof-comment-start) "+\\s_?"))

  (setq proof-re-end-of-cmd (concat "\\s_*" proof-terminal-string "\\s_*\\\'"))
  (setq proof-re-term-or-comment 
	(concat proof-terminal-string "\\|" (regexp-quote proof-comment-start)
		"\\|" (regexp-quote proof-comment-end)))

  ;; func-menu --- Jump to a goal within a buffer
  (and (boundp 'fume-function-name-regexp-alist)
       (defvar fume-function-name-regexp-proof
	 (cons proof-goal-with-hole-regexp 2))
       (push (cons major-mode 'fume-function-name-regexp-proof)
	     fume-function-name-regexp-alist))
  (and (boundp 'fume-find-function-name-method-alist)
       (push (cons major-mode 'fume-match-find-next-function-name)
	     fume-find-function-name-method-alist))

  ;; Additional key definitions which depend on configuration for
  ;; specific proof assistant.
  (define-key proof-mode-map
    (vconcat [(control c)] (vector proof-terminal-char))
    'proof-active-terminator-minor-mode)

  (define-key proof-mode-map (vector proof-terminal-char)
    'proof-active-terminator)
  ;; NEW da: added proof-assert-next-command binding here.

  (make-local-variable 'indent-line-function)
  (setq indent-line-function 'proof-indent-line)

  ;; Toolbar
  (if (featurep 'proof-toolbar)
      (proof-toolbar-setup))

  ;; Menu
  (easy-menu-define proof-mode-menu  
		    proof-mode-map
		    "Menu used in Proof General scripting mode."
		    (cons proof-mode-name (cdr proof-menu)))
  (easy-menu-add proof-mode-menu proof-mode-map)

  ;; For fontlock
  ;; FIXME (da): zap commas support is too specific, should be enabled
  ;; by each proof assistant as it likes.
  (remove-hook 'font-lock-after-fontify-buffer-hook 'proof-zap-commas-buffer t)
  (add-hook 'font-lock-after-fontify-buffer-hook 
	    'proof-zap-commas-buffer nil t)
  (remove-hook 'font-lock-mode-hook 'proof-unfontify-separator t)
  (add-hook 'font-lock-mode-hook 'proof-unfontify-separator nil t)

  ;; if we don't have the following, zap-commas fails to work.
  ;; FIXME (da): setting this to t everywhere is too brutal.  Should
  ;; probably make it local.
  (and (boundp 'font-lock-always-fontify-immediately)
       (setq font-lock-always-fontify-immediately t))

  (run-hooks 'proof-mode-hook))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Proof General shell mode configuration			    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This has to come after proof-mode is defined
(define-derived-mode proof-shell-mode comint-mode 
  "proof-shell" "Proof shell mode - not standalone"
  (setq proof-buffer-type 'shell)
  (setq proof-shell-busy nil)
  (setq proof-shell-delayed-output (cons 'insert "done"))
  (setq proof-shell-proof-completed nil)

  ;;; COMINT customisation
  (setq comint-prompt-regexp proof-shell-prompt-pattern)

  ;; An article by Helen Lowe in UITP'96 suggests that the user should
  ;; not see all output produced by the proof process. 
  (remove-hook 'comint-output-filter-functions
	       'comint-postoutput-scroll-to-bottom 'local)

  (add-hook 'comint-output-filter-functions 'proof-shell-filter nil 'local)
  (setq comint-get-old-input (function (lambda () "")))
  (proof-dont-show-annotations)
  (setq proof-marker (make-marker)))

(easy-menu-define proof-shell-menu
		  proof-shell-mode-map
		  "Menu used in Proof General shell mode."
		  (cons proof-mode-name (cdr proof-shell-menu)))

(defun proof-shell-config-done ()
  (accept-process-output (get-buffer-process (current-buffer)))

  ;; If the proof process in invoked on a different machine e.g.,
  ;; for proof-prog-name="rsh fastmachine proofprocess", one needs
  ;; to adjust the directory:
  (and proof-shell-cd
       (proof-shell-insert (format proof-shell-cd
       ;; under Emacs 19.34 default-directory contains "~" which causes
       ;; problems with LEGO's internal Cd command
				   (expand-file-name default-directory))))

  (if proof-shell-init-cmd
       (proof-shell-insert proof-shell-init-cmd))

  ;; Note that proof-marker actually gets set in proof-shell-filter.
  ;; This is manifestly a hack, but finding somewhere more convenient
  ;; to do the setup is tricky.

  (while (null (marker-position proof-marker))
    (if (accept-process-output (get-buffer-process (current-buffer)) 15)
	()
      (error "Failed to initialise proof process"))))

(define-derived-mode pbp-mode fundamental-mode 
  proof-mode-name "Proof by Pointing"
  ;; defined-derived-mode pbp-mode initialises pbp-mode-map
  (setq proof-buffer-type 'pbp)
  (suppress-keymap pbp-mode-map 'all)
;  (define-key pbp-mode-map [(button2)] 'pbp-button-action)
  (proof-define-keys pbp-mode-map proof-universal-keys)
  (erase-buffer))


(provide 'proof)
