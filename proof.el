;; proof.el Major mode for proof assistants
;; Copyright (C) 1994 - 1997 LFCS Edinburgh. 
;; Authors: Yves Bertot, Healfdene Goguen, Thomas Kleymann and Dilip Sequeira

;; Maintainer: LEGO Team <lego@dcs.ed.ac.uk>
;; Thanks to David Aspinall, Robert Boyer, Rod Burstall,
;;           James McKinna, Mark Ruys, Martin Steffen, Perdita Stevens  



;; $Log$
;; Revision 1.32  1998/01/15 12:23:57  hhg
;; Updated method of defining proof-shell-cd to be consistent with other
;; proof-assistant-dependent variables.
;; Added ctrl-button1 to copy selected region to end of locked region
;;
;; Revision 1.31  1998/01/12 11:07:53  tms
;; o added support for remote proof processes
;; o bound C-c C-z to 'proof-frob-locked-end
;;
;; Revision 1.30  1998/01/05 15:01:31  tms
;; improved fume support
;;
;; Revision 1.29  1997/12/18 13:16:41  tms
;; o introduced proof-shell-handle-error-hook and bount it by default to
;;   proof-goto-end-of-locked-if-pos-not-visible-in-window (also new)
;;
;; o proof-find-next-terminator now also works inside a locked region
;;
;; o implemented proof-process-buffer which is by default bount to C-c C-b
;;
;; Revision 1.28  1997/11/26 14:19:45  tms
;; o The response buffer focusses on the first goal
;; o If proof-retract-until-point is is invoked outside a locked region,
;;   the last successfully processed command is undone.
;; o Added support for func-menu
;;
;; Revision 1.27  1997/11/24 19:15:16  djs
;; Added proof-execute-minibuffer-cmd and scripting minor mode.
;;
;; Revision 1.26  1997/11/20 16:47:48  hhg
;; Added proof-global-p to test whether a 'vanilla should be lifted above
;; active lemmas.
;; Separated proof-lift-global as separate command to lift global
;; declarations above active lemmas.
;; Fixed usual problem that 'cmd is nil for comments in this code.
;; Made lifting globals start from beginning of file rather than go
;; backwards.
;; Fixed bug in pbp code proof-shell-analyse-structure, where stack
;; wasn't cleared for new goal-hyp's.
;;
;; Revision 1.25  1997/11/17 17:11:21  djs
;; Added some magic commands: proof-frob-locked-end, proof-try-command,
;; proof-interrupt-process. Added moving nested lemmas above goal for coq.
;; Changed the key mapping for assert-until-point to C-c RET.
;;
;; Revision 1.24  1997/11/13 10:23:49  hhg
;; Includes commented code for Coq version of extent protocol
;;
;; Revision 1.23  1997/11/10 18:36:21  djs
;; Started modifications for emacs19 port.
;;
;; Revision 1.22  1997/11/10 15:51:09  djs
;; Put in a workaround for a strange bug in comint which was finding a bunch
;; of ^G's from comint-get-old-input for some inexplicable reason. THIS IS
;; STILL BROKEN AND A BUG REPORT HAS BEEN SUBMITTED TO XEMACS.ORG
;;
;; Revision 1.21  1997/11/06 16:56:59  hhg
;; Parameterize by proof-goal-hyp-fn in pbp-make-top-span, to handle
;; Coq goals which start with text rather than simply ?n
;;
;; Updated 'let (ap 0)' in proof-shell-analyse structure, to be slightly
;; more compatible with Coq pbp code
;;
;; Revision 1.20  1997/10/31 15:11:28  tms
;; o implemented proof-find-next-terminator available via C-c C-e
;; o fixed a bug in proof-done-retracting
;;
;; Revision 1.19  1997/10/30 15:58:33  hhg
;; Updates for coq, including:
;; 	* pbp-goal-command and pbp-hyp-command use proof-terminal-string
;; 	* updates to keywords
;; 	* fix for goal regexp
;;
;; Revision 1.18  1997/10/24 14:51:13  hhg
;; Updated comment about span types
;;
;; Revision 1.17  1997/10/22 16:43:54  hhg
;; Updated proof-segment-up-to to take ""'s into account
;; Hence, << Cd "../x". >> works in Coq, and
;;        << echo "hello; world"; >> should work in LEGO
;; But maybe we don't want "Cd"'s at all...
;;
;; Revision 1.16  1997/10/17 15:15:57  djs
;; proof-active-terminator inside comment case fixed. Also maybe the
;; continuous pbp-buffer update bug.
;;
;; Revision 1.15  1997/10/17 14:38:33  tms
;; fixed a bug in proof-process-active-terminator. Notice that it still
;; doesn't work when you are inside a comment and press the
;; proof-terminal-char
;;
;; Revision 1.14  1997/10/16 14:12:04  djs
;; Figured out display tables.
;;
;; Revision 1.13  1997/10/16 08:48:56  tms
;; merged script management (1.10.2.18) with main branch
;;
;; Revision 1.10.2.18  1997/10/14 19:30:55  djs
;; Bug fixes for comments.
;;
;; Revision 1.10.2.17  1997/10/14 17:30:15  djs
;; Fixed a bunch of bugs to do with comments, moved annotations out-of-band
;; to exploit a feature which will exist in XEmacs 20. (One day there *will
;; be* lemon-scented paper napkins). Added code to detect failing imports.
;;
;; Revision 1.10.2.16  1997/10/10 19:24:33  djs
;; Attempt to create a fresh branch because of Attic-Attack.
;;
;; Revision 1.10.2.15  1997/10/10 19:20:01  djs
;; Added multiple file support, changed the way comments work, fixed a
;; few minor bugs, and merged in coq support by hhg.
;;
;; Revision 1.10.2.13  1997/10/07 13:27:51  hhg
;; New structure sharing as much as possible between LEGO and Coq.
;;
;; Revision 1.10.2.12  1997/10/03 14:52:53  tms
;; o Replaced (string= "str" (substring cmd 0 n))
;;         by (string-match "^str" cmd)
;;   The latter doesn't raise an exception if cmd is too short
;;
;; o lego-count-undos: now depends on lego-undoable-commands-regexp
;;                     with special treatment of Equiv
;;
;; Revision 1.10.2.11  1997/09/19 11:23:23  tms
;; o replaced ?\; by proof-terminal-char
;; o fixed a bug in proof-process-active-terminator
;;
;; Revision 1.10.2.10  1997/09/12 12:33:41  tms
;; improved lego-find-and-forget
;;
;; Revision 1.10.2.9  1997/09/11 15:39:19  tms
;; fixed a bug in proof-retract-until-point
;;

(require 'compile)
(require 'comint)
(require 'etags)
(require 'proof-dependencies)
(require 'proof-fontlock)

(autoload 'w3-fetch "w3" nil t)

(defmacro deflocal (var value docstring)
 (list 'progn
   (list 'defvar var 'nil docstring)
   (list 'make-variable-buffer-local (list 'quote var))
   (list 'setq var value)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;               Configuration                                      ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar proof-shell-cd nil
  "*Command of the inferior process to change the directory.") 

(defvar proof-prog-name-ask-p nil
  "*If t, you will be asked which program to run when the inferior
 process starts up.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Other buffer-local variables used by proof mode                 ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; These should be set before proof-config-done is called

(defvar proof-terminal-char nil "terminator character")

(defvar proof-comment-start nil "Comment start")
(defvar proof-comment-end nil "Comment end")

(defvar proof-save-command-regexp nil "Matches a save command")
(defvar proof-save-with-hole-regexp nil "Matches a named save command")
(defvar proof-goal-command-regexp nil "Matches a goal command")
(defvar proof-goal-with-hole-regexp nil "Matches a saved goal command")

(defvar proof-retract-target-fn nil "Compute how to retract a target segment")
(defvar proof-goal-hyp-fn nil "Is point at goal or hypothesis")
(defvar proof-kill-goal-command nil "How to kill a goal.")
(defvar proof-global-p nil "Is this a global declaration")

(defvar proof-state-preserving-p nil
  "whether a command preserves the proof state")

(defvar pbp-change-goal nil
  "*Command to change to the goal %s")

;; these should be set in proof-pre-shell-start-hook

(defvar proof-prog-name nil "program name for proof shell")
(defvar proof-mode-for-shell nil "mode for proof shell")
(defvar proof-mode-for-pbp nil "The actual mode for Proof-by-Pointing.")
(defvar proof-shell-config nil 
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

(defvar proof-shell-echo-input t
  "If nil, input to the proof shell will not be echoed")

(defvar proof-terminal-string nil 
  "You are not authorised for this information.")

(defvar proof-re-end-of-cmd nil 
  "You are not authorised for this information.")

(defvar proof-re-term-or-comment nil 
  "You are not authorised for this information.")

(defvar proof-marker nil 
  "You are not authorised for this information.")

(defvar proof-shell-buffer nil
  "You are not authorised for this information.")

(defvar proof-script-buffer nil
  "You are not authorised for this information.")

(defvar proof-pbp-buffer nil
  "You are not authorised for this information.")

(defvar proof-shell-busy nil 
  "You are not authorised for this information.")

(deflocal proof-buffer-type nil 
  "You are not authorised for this information.")

(defvar proof-action-list nil "action list")

(defvar proof-included-files-list nil 
  "Files currently included in proof process")

(deflocal proof-active-buffer-fake-minor-mode nil
  "An indication in the modeline that this is the *active* buffer")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;               Bridging the emacs19/xemacs gulf                   ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar running-xemacs  nil)
(defvar running-emacs19 nil)

(setq running-xemacs  (string-match "XEmacs\\|Lucid" emacs-version))
(or running-xemacs
    (setq running-emacs19 (string-match "^19\\." emacs-version)))

;; courtesy of Mark Ruys 
(defun emacs-version-at-least (major minor)
  "Test if emacs version is at least major.minor"
  (or (> emacs-major-version major)
      (and (= emacs-major-version major) (>= emacs-minor-version minor)))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; A couple of small utilities                                      ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The package fume-func provides a function with the same name and
;; specification. However, fume-func's version is incorrect.
(defun fume-match-find-next-function-name (buffer)
  ;; General next function name in BUFFER finder using match.
  ;; The regexp is assumed to be a two item list the car of which is the regexp
  ;; to use, and the cdr of which is the match position of the function name
  (set-buffer buffer)
  (let ((r (car fume-function-name-regexp))
        (p (cdr fume-function-name-regexp)))
    (and (re-search-forward r nil t)
	 (cons (buffer-substring (setq p (match-beginning p)) (point)) p))))


(defun string-to-list (s separator) 
  "converts strings `s' separated by the character `separator' to a
  list of words" 
  (let ((end-of-word-occurence (string-match (concat separator "+") s)))
    (if (not end-of-word-occurence)
        (if (string= s "") 
            nil
          (list s))
      (cons (substring s 0 end-of-word-occurence) 
            (string-to-list 
             (substring s
                        (string-match (concat "[^" separator "]")
                                      s end-of-word-occurence)) separator)))))

(defun w3-remove-file-name (address)
  "remove the file name in a World Wide Web address"
  (string-match "://[^/]+/" address)
  (concat (substring address 0 (match-end 0))
          (file-name-directory (substring address (match-end 0)))))

(defun proof-goto-end-of-locked ()
  "Jump to the end of the locked region."
  (interactive)
  (goto-char (proof-locked-end) proof-script-buffer))

(defun proof-goto-end-of-locked-if-pos-not-visible-in-window ()
  "If the end of the locked region is not visible, jump to the end of
  the locked region."
  (interactive)
  (let ((pos (proof-locked-end)))
    (or (pos-visible-in-window-p pos (get-buffer-window
				      proof-script-buffer t))
	;; see code of proof-goto-end-of-locked
	(goto-char pos proof-script-buffer))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Starting and stopping the proof-system shell                    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun proof-shell-live-buffer () 
  (if (and proof-shell-buffer
	   (comint-check-proc proof-shell-buffer))
       proof-shell-buffer))

(defun proof-start-shell ()
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
      (let ((prog-name-list (string-to-list proof-prog-name " ")))
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
      (redraw-modeline)

      (or (assq 'proof-active-buffer-fake-minor-mode minor-mode-alist)
	  (setq minor-mode-alist
		(append minor-mode-alist
			(list '(proof-active-buffer-fake-minor-mode 
				" Scripting")))))

      (message 
       (format "Starting %s process... done." proc)))))
  

(defun proof-stop-shell ()
  "Exit the PROOF process

  Runs proof-shell-exit-hook if non nil"

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
  (let* ((ext (span-at (mouse-set-point event) 'type))
	 (str (span-property ext 'cmd)))
    (cond ((and (eq proof-script-buffer (current-buffer)) (not (null ext)))
	   (proof-goto-end-of-locked)
	   (cond ((eq (span-property ext 'type) 'vanilla)
		  (insert str)))))))

(defun pbp-construct-command ()
  (let* ((ext (span-at (point) 'proof))
	 (top-ext (span-at (point) 'proof-top-element))
	 top-info)
    (if (null top-ext) ()
      (setq top-info (span-property top-ext 'proof-top-element))
      (pop-to-buffer proof-script-buffer)
      (cond
       (ext
	(proof-invisible-command 
	 (format (if (eq 'hyp (car top-info)) pbp-hyp-command 
		                              pbp-goal-command)
		 (concat (cdr top-info) (proof-expand-path 
					 (span-property ext 'proof))))))
       ((eq (car top-info) 'hyp)
	(proof-invisible-command (format pbp-hyp-command (cdr top-info))))
       (t
	 (proof-insert-pbp-command (format pbp-change-goal (cdr top-info))))))
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;          Turning annotated output into pbp goal set              ;;
;;          All very lego-specific at present                       ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar proof-shell-first-special-char nil "where the specials start")
(defvar proof-shell-goal-char nil "goal mark")
(defvar proof-shell-start-char nil "annotation start")
(defvar proof-shell-end-char nil "annotation end")
(defvar proof-shell-field-char nil "annotated field end")
(defvar proof-shell-eager-annotation-start nil "eager ann. field start")
(defvar proof-shell-eager-annotation-end nil "eager ann. field end")

(defvar proof-shell-assumption-regexp nil
  "A regular expression matching the name of assumptions.")

(defvar proof-shell-goal-regexp nil
  "A regular expressin matching the identifier of a goal.")

(defvar proof-shell-noise-regexp nil
  "Unwanted information output from the proof process within
  `proof-start-goals-regexp' and `proof-end-goals-regexp'.")

(defun pbp-make-top-span (start end)
  (let (span name)
    (goto-char start)
    (setq name (funcall proof-goal-hyp-fn))
    (beginning-of-line)
    (setq start (point))
    (goto-char end)
    (beginning-of-line)
    (backward-char)
    (setq span (make-span start (point)))
    (set-span-property span 'mouse-face 'highlight)
    (set-span-property span 'proof-top-element name)))

(defun proof-shell-analyse-structure (string)
  (save-excursion
    (let* ((ip 0) (op 0) ap (l (length string)) 
	   (ann (make-string (length string) ?x))
           (stack ()) (topl ()) 
	   (out (make-string l ?x )) c ext)
      (while (< ip l)	
	(if (< (setq c (aref string ip)) 128) (progn (aset out op c)
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
					; Set ap to 0 for Coq
	  (setq ap 0))
	 ((= c proof-shell-start-char)
					; Subtract from current length for Coq
;	  (setq ap (- ap (- (aref string (incf ip)) 128)))
	  (setq ap (- (aref string (incf ip)) 128))
	  (incf ip)
	  (while (not (= (setq c (aref string ip)) proof-shell-end-char))
	    (aset ann ap (- c 128))
	    (incf ap)
	    (incf ip))
	  (setq stack (cons op (cons (substring ann 0 ap) stack))))
	 ((= c proof-shell-field-char)
	  (setq ext (make-span (car stack) op))
	  (set-span-property ext 'mouse-face 'highlight)
	  (set-span-property ext 'proof (car (cdr stack)))
					; Pop annotation off stack, for Coq
;	  (setq ap 0)
;	  (while (< ap (length (cadr stack)))
;	    (aset ann ap (aref (cadr stack) ap))
;	    (incf ap))
					; Finish popping annotations
	  (setq stack (cdr (cdr stack))))
	 (t (incf op)))
	(incf ip))
      (setq topl (reverse (cons (point-max) topl)))
;      (setq coq-current-goal 1)
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

(defun proof-shell-handle-error (cmd string)
  (save-excursion 
    (display-buffer (set-buffer proof-pbp-buffer))
    (goto-char (point-max))
    (if (re-search-backward pbp-error-regexp nil t) 
	(delete-region (- (point) 2) (point-max)))
    (newline 2)
    (insert-string string)
    (beep))
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

(defvar proof-shell-delayed-output nil
  "The last interesting output the proof process output, and what to do
   with it.")

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

(defun proof-goals-pos (span maparg)
  "Given a span, this function returns the start of it if corresponds
  to a goal and nil otherwise."
 (and (eq 'goal (car (span-property span 'proof-top-element)))
		(span-start span)))

(defun proof-pbp-focus-on-first-goal ()
  "If the `proof-pbp-buffer' contains goals, the first one is brought
  into view."
  (let
      ((pos (map-extents 'proof-goals-pos proof-pbp-buffer
			 nil nil nil nil 'proof-top-element)))
    (and pos (set-window-point (get-buffer-window proof-pbp-buffer t) pos))))

(defun proof-shell-process-output (cmd string)
  (cond 
   ((string-match proof-shell-error-regexp string)
    (cons 'error (proof-shell-strip-annotations 
		  (substring string (match-beginning 0)))))

   ((string-match proof-shell-interrupt-regexp string)
    'interrupt)

   ((string-match proof-shell-abort-goal-regexp string)
    (setq proof-shell-delayed-output (cons 'insert "\n\nAborted"))
    ())
	 
   ((string-match proof-shell-proof-completed-regexp string)
    (setq proof-shell-delayed-output
	  (cons 'insert (concat "\n" (match-string 0 string)))))

   ((string-match proof-shell-start-goals-regexp string)
    (let (start end)
      (while (progn (setq start (match-end 0))
		    (string-match proof-shell-start-goals-regexp 
				  string start)))
      (setq end (string-match proof-shell-end-goals-regexp string start))
      (setq proof-shell-delayed-output 
	    (cons 'analyse (substring string start end)))))
       
   ((string-match proof-shell-result-start string)
    (let (start end)
      (setq start (+ 1 (match-end 0)))
      (string-match proof-shell-result-end string)
      (setq end (- (match-beginning 0) 1))
      (cons 'loopback (substring string start end))))
   
   ((string-match "^Module" cmd)
    (setq proof-shell-delayed-output (cons 'insert "Imports done!")))

   (t (setq proof-shell-delayed-output (cons 'insert string)))))
         
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;   Low-level commands for shell communication                     ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun proof-shell-insert (string)
  (set-buffer proof-shell-buffer)
  (goto-char (point-max))
  (insert (funcall proof-shell-config) string)
  (if (marker-position proof-marker) 
      (set-marker proof-marker (point)))
  (comint-send-input))

(defun proof-send (string)
  (let ((l (length string)) (i 0))
    (while (< i l)
      (if (= (aref string i) ?\n) (aset string i ?\ ))
      (incf i)))
  (save-excursion (proof-shell-insert string)))

;; grab the process and return t, otherwise return nil. Note that this
;; is not really intended for anything complicated - just to stop the
;; user accidentally sending a command while the queue is running.

(defun proof-check-process-available ()
  (if (proof-shell-live-buffer)
      (cond
       (proof-shell-busy (error "Proof Process Busy!"))
       ((not (eq proof-script-buffer (current-buffer)))
	(error "Don't own proof process"))))
  (if (not (eq proof-buffer-type 'script))
      (error "Must be running in a script buffer")))

(defun proof-grab-lock ()
  (proof-start-shell)
  (proof-check-process-available)
  (setq proof-shell-busy t))

(defun proof-release-lock ()
  (if (proof-shell-live-buffer)
      (progn
	(if (not proof-shell-busy)
	    (error "Bug: Proof process not busy"))
	(if (not (eq proof-script-buffer (current-buffer)))
	    (error "Bug: Don't own process"))
	(setq proof-shell-busy nil))))
  
; Pass start and end as nil if the cmd isn't in the buffer.

(defun proof-start-queue (start end alist)
  (if start
      (proof-set-queue-endpoints start end))
  (let (item)
    (while (and alist (string= 
		       (nth 1 (setq item (car alist))) 
		       "COMMENT"))
    (funcall (nth 2 item) (car item))
    (setq alist (cdr alist)))
  (if alist
      (progn
	(proof-grab-lock) 
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
		 "COMMENT"))
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
    (let (ext)
      (proof-goto-end-of-locked)
      (newline-and-indent)
      (insert cmd)
      (setq ext (make-span (proof-locked-end) (point)))
      (set-span-property ext 'type 'pbp)
      (set-span-property ext 'cmd cmd)
      (proof-set-queue-endpoints (proof-locked-end) (point))
      (setq proof-action-list 
	    (cons (car proof-action-list) 
		  (cons (list ext cmd 'proof-done-advancing)
			(cdr proof-action-list)))))))

(defun proof-shell-popup-eager-annotation ()
  (let (mrk str file module)
    (save-excursion ;; BROKEN - THERE MAY BE MULTIPLE EAGER ANNOTATIONS
      (goto-char (point-max))
      (search-backward proof-shell-eager-annotation-start)
      (setq mrk (+ 1 (point)))
      (search-forward proof-shell-eager-annotation-end)
      (setq str (buffer-substring mrk (- (point) 1)))
      (display-buffer (set-buffer proof-pbp-buffer))
      (goto-char (point-max))
      (insert str "\n"))
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
  (if (string-match proof-shell-eager-annotation-end str)
      (proof-shell-popup-eager-annotation))
  (if (string-match (char-to-string proof-shell-wakeup-char) str)
      (if (null (marker-position proof-marker))
	  (progn
	    (goto-char (point-min))
	    (re-search-forward proof-shell-annotated-prompt-regexp)
	    (backward-delete-char 1)
	    (set-marker proof-marker (point)))
	(let (string res cmd)	
	  (goto-char (marker-position proof-marker))
	  (re-search-forward proof-shell-annotated-prompt-regexp nil t)
	  (backward-char (- (match-end 0) (match-beginning 0)))
	  (setq string (buffer-substring (marker-position proof-marker)
					 (point)))
	  (goto-char (point-max))
	  (backward-delete-char 1)
	  (setq cmd (nth 1 (car proof-action-list)))
	  (save-excursion
	    (setq res (proof-shell-process-output cmd string))
	    (cond
	     ((and (consp res) (eq (car res) 'error))
	      (proof-shell-handle-error cmd (cdr res)))
	     ((eq res 'interrupt)
	      (proof-shell-handle-interrupt))
	     ((and (consp res) (eq (car res) 'loopback))
	      (proof-shell-insert-loopback-cmd (cdr res))
	      (proof-shell-exec-loop))
	     (t (if (proof-shell-exec-loop)
		    (proof-shell-handle-delayed-output)))))))))

(defun proof-last-goal-or-goalsave ()
  (save-excursion
    (let ((ext (span-at-before (proof-locked-end) 'type)))
    (while (and ext 
		(not (eq (span-property ext 'type) 'goalsave))
		(or (eq (span-property ext 'type) 'comment)
		    (not (string-match proof-goal-command-regexp 
				       (span-property ext 'cmd)))))
      (setq ext (prev-span ext 'type)))
    ext)))
    
(defun proof-steal-process ()
  (proof-start-shell)
  (if proof-shell-busy (error "Proof Process Busy!"))
  (if (not (eq proof-buffer-type 'script))
      (error "Must be running in a script buffer"))
  (cond
   ((eq proof-script-buffer (current-buffer))
    nil)
   (t 
    (let ((flist proof-included-files-list) 
	  (file (expand-file-name (buffer-file-name))) ext cmd)
      (if (string-match "\\(.*\\)\\.." file) (setq file (match-string 1 file)))
      (while (and flist (not (string= file (cdr (car flist)))))
	(setq flist (cdr flist)))
      (if (null flist) 
	  (if (not (y-or-n-p "Steal script management? " )) (error "Aborted"))
	(if (not (y-or-n-p "Reprocess this file? " )) (error "Aborted")))
      (save-excursion
	(set-buffer proof-script-buffer)
	(setq ext (proof-last-goal-or-goalsave))
	(setq cmd (if (and ext (not (eq (span-property ext 'type) 'goalsave)))
		      proof-kill-goal-command ""))
	(proof-detach-segments)
	(delete-spans (point-min) (point-max) 'type)
	(setq proof-active-buffer-fake-minor-mode nil))      
      (setq proof-script-buffer (current-buffer))
      (proof-detach-segments)
      (proof-init-segmentation)
      (setq proof-active-buffer-fake-minor-mode t)

      (cond 
       (flist
	 (list nil (concat cmd "ForgetMark " (car (car flist)) ";")
	       `(lambda (ext) (setq proof-included-files-list 
				    (quote ,(cdr flist))))))
	((not (string= cmd ""))
	 (list nil cmd 'proof-done-invisible))
	(t nil))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;          Script management                                     ;;
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

(defun proof-done-invisible (ext) ())

(defun proof-invisible-command (cmd)
  (proof-check-process-available)
  (if (not (string-match proof-re-end-of-cmd cmd))
      (setq cmd (concat cmd proof-terminal-string)))
  (proof-start-queue nil nil (list (list nil cmd 'proof-done-invisible))))

(defun proof-insert-pbp-command (cmd)
  (proof-check-process-available)
  (let (ext)
    (proof-goto-end-of-locked)
    (insert cmd)
    (setq ext (make-span (proof-locked-end) (point)))
    (set-span-property ext 'type 'pbp)
    (set-span-property ext 'cmd cmd)
    (proof-start-queue (proof-locked-end) (point) 
		       (list (list ext cmd 'proof-done-advancing)))))

;; This code's for nested goals in Coq, and shouldn't affect things in LEGO
(defun proof-lift-global (glob-ext)
  (let (start (next (span-at 1 'type)) str (goal-p nil))
    (while (and next (and (not (eq next glob-ext)) (not goal-p)))
      (if (and (eq (span-property next 'type) 'vanilla)
	       (string-match proof-goal-command-regexp 
			     (span-property next 'cmd)))
	  (setq goal-p t)
	(setq next (next-span next 'type))))

    (if (and next (not (eq next glob-ext)))
	(progn
	  (proof-unlock-locked)
	  (setq str (buffer-substring (span-start glob-ext)
				      (span-end glob-ext)))
	  (delete-region (span-start glob-ext) (span-end glob-ext))
	  (goto-char (span-start next))
	  (setq start (point))
	  (insert str "\n")
	  (set-span-endpoints glob-ext start (point))
	  (set-span-start next (point))
	  (proof-lock-unlocked)))))

(defun proof-done-advancing (ext)
  (let ((end (span-end ext)) nam gext next cmd)
    (proof-set-locked-end end)
    (proof-set-queue-start end)
    (setq cmd (span-property ext 'cmd))
    (cond
     ((eq (span-property ext 'type) 'comment)
      (set-span-property ext 'highlight 'mouse-face))
     ((string-match proof-save-command-regexp cmd)
      (if (string-match proof-save-with-hole-regexp cmd)
	  (setq nam (match-string 2 cmd)))
      (setq gext ext)
      (while (or (eq (span-property gext 'type) 'comment)
		 (not (string-match proof-goal-command-regexp 
				    (setq cmd (span-property gext 'cmd)))))
	(setq next (prev-span gext 'type))
	(delete-span gext)
	(setq gext next))

      (if (null nam)
	  (if (string-match proof-goal-with-hole-regexp
			    (span-property gext 'cmd))
	      (setq nam (match-string 2 cmd))
	    (error "Oops... can't find Goal name!!!")))

      (set-span-end gext end)
      (set-span-property gext 'highlight 'mouse-face)
      (set-span-property gext 'type 'goalsave)
      (set-span-property gext 'name nam)

      (proof-lift-global gext))
     (t
      (set-span-property ext 'highlight 'mouse-face)
      (if (funcall proof-global-p cmd)
	  (proof-lift-global ext))))))
  
; Create a list of (type,int,string) pairs from the end of the locked
; region to pos, denoting the command and the position of its
; terminator. type is one of comment, or cmd. 'unclosed-comment may be
; consed onto the start if the segment finishes with an unclosed
; comment.
; depth marks number of nested comments. quote-parity is false if
; we're inside ""'s.  Only one of (depth > 0) and (not quote-parity)
; should be true at once. -- hhg

(defun proof-segment-up-to (pos)
  (save-excursion
    (let ((str (make-string (- (buffer-size) (proof-locked-end) -10) ?x))
	  (i 0) (depth 0) (quote-parity t) done alist c)
     (proof-goto-end-of-locked)
     (while (not done)
       (cond 
	((and (= (point) pos) (> depth 0))
	 (setq done t alist (cons 'unclosed-comment alist)))
	((= (point) (point-max))
	 (if (not quote-parity)
	     (message "Warning: unclosed quote"))
	 (setq done t))
	((and (looking-at "\\*)") quote-parity)
	 (if (= depth 0) 
	     (progn (message "Warning: extraneous comment end") (setq done t))
	   (setq depth (- depth 1)) (forward-char 2)
	   (if (eq i 0) 
	       (setq alist (cons (list 'comment "" (point)) alist))
	     (aset str i ?\ ) (incf i))))
	((and (looking-at "(\\*") quote-parity)
	 (setq depth (+ depth 1)) (forward-char 2))
	((> depth 0) (forward-char))
	(t
	 (setq c (char-after (point)))
	 (if (or (> i 0) (not (= (char-syntax c) ?\ )))
	     (progn (aset str i c) (incf i)))
	 (if (looking-at "\"")
	     (setq quote-parity (not quote-parity)))
	 (forward-char)
	 (if (and (= c proof-terminal-char) quote-parity)
	     (progn 
	       (setq alist 
		     (cons (list 'cmd (substring str 0 i) (point)) alist))
	       (if (>= (point) pos) (setq done t) (setq i 0)))))))
     alist)))

(defun proof-semis-to-vanillas (semis &optional callback-fn)
  (let ((ct (proof-locked-end)) ext alist semi)
    (while (not (null semis))
      (setq semi (car semis)
            ext (make-span ct (nth 2 semi))
	    ct (nth 2 semi))
      (if (eq (car (car semis)) 'cmd)
	  (progn
	    (set-span-property ext 'type 'vanilla)
	    (set-span-property ext 'cmd (nth 1 semi))
	    (setq alist (cons (list ext (nth 1 semi) 
				    (or callback-fn 'proof-done-advancing))
			      alist)))
	(set-span-property ext 'type 'comment)
	(setq alist (cons (list ext "COMMENT" 'proof-done-advancing) alist)))
	(setq semis (cdr semis)))
    (nreverse alist)))


(defun proof-assert-until-point
  (&optional unclosed-comment-fun ignore-proof-process-p)
  "Process the region from the end of the locked-region until point.
   Default action if inside a comment is just to go until the start of
   the comment. If you want something different, put it inside
   unclosed-comment-fun. If ignore-proof-process-p is set, no commands
   will be added to the queue."
  (interactive)
  (let ((pt  (point))
	(crowbar (or ignore-proof-process-p (proof-steal-process)))
	semis)
    (save-excursion
      (if (not (re-search-backward "\\S-" (proof-locked-end) t))
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

(defun proof-done-trying (ext)
  (proof-detach-queue))
			
(defun proof-try-command
  (&optional unclosed-comment-fun) 

  "Process the command at point,
   but don't add it to the locked region. This will only happen if
   the command passes proof-state-preserving-p.

   Default action if inside a comment is just to go until the start of
   the comment. If you want something different, put it inside
   unclosed-comment-fun."
  (interactive)
  (let ((pt  (point)) semis crowbar test)
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

(defun proof-process-buffer ()
  "Process the current buffer and set point at the end of the buffer."
  (interactive)
  (end-of-buffer)
  (proof-assert-until-point))

(defun proof-done-retracting (ext)
  "Updates display after proof process has reset its state. See also
the documentation for `proof-retract-until-point'. It optionally
deletes the region corresponding to the proof sequence."
  (let ((start (span-start ext))
        (end (span-end ext))
	(kill (span-property ext 'delete-me)))
    (proof-set-locked-end start)
    (proof-set-queue-end start)
    (delete-spans start end 'type)
    (delete-span ext)
    (if kill (delete-region start end))))

(defun proof-setup-retract-action (start end proof-command delete-region)
  (let ((span (make-span start end)))
    (set-span-property span 'delete-me delete-region)
    (list (list span proof-command 'proof-done-retracting))))


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
    (let ((sext (span-at (point) 'type)))
      (if (null (proof-locked-end)) (error "No locked region"))
      (and (null sext)
	   (progn (proof-goto-end-of-locked) (backward-char)
		  (setq sext (span-at (point) 'type))))
      (funcall proof-retract-target-fn sext delete-region)))

(defun proof-undo-last-successful-command ()
  "Undo last successful command, both in the buffer recording the
   proof script and in the proof process. In particular, it deletes
   the corresponding part of the proof script."
  (interactive)
  (goto-char (span-start (span-at-before (proof-locked-end) 'type)))
  (proof-retract-until-point t))

(defun proof-restart-script ()
  (interactive)
  (save-excursion
    (if (buffer-live-p proof-script-buffer)
	(progn
	  (set-buffer proof-script-buffer)
	  (delete-spans (point-min) (point-max) 'type)
	  (proof-detach-segments)))
    (setq proof-shell-busy nil
	  proof-script-buffer nil)
    (if (buffer-live-p proof-shell-buffer) 
	(kill-buffer proof-shell-buffer))
    (if (buffer-live-p proof-pbp-buffer)
	(kill-buffer proof-pbp-buffer))))

(defun proof-frob-locked-end ()
  (interactive)
  "Move the end of the locked region backwards. 
   Only for use by consenting adults."
  (if (> (point) (proof-locked-end))
      (error "Can only move backwards")
    (proof-set-locked-end (point))
    (delete-spans (proof-locked-end) (point-max) 'type)))

(defvar proof-minibuffer-history nil
  "The last command read from the minibuffer")

(defun proof-execute-minibuffer-cmd ()
  (interactive)
  (let (cmd)
    (proof-check-process-available)
    (setq cmd (read-string "Command: " nil 'proof-minibuffer-history))
;     proof-minibuffer-history (cons cmd proof-minibuffer-history))
    (proof-invisible-command cmd)))
	  
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
   (if (fboundp 'redraw-modeline) (redraw-modeline) (redraw-modeline)))

(defun proof-active-terminator ()
  (interactive)
  (if proof-active-terminator-minor-mode 
      (proof-process-active-terminator)
    (self-insert-command 1)))

(defun proof-process-active-terminator ()
  "Insert the terminator in an intelligent way and assert until the new terminator."
  (let ((mrk (point)) ins)
    (if (looking-at "\\s-\\|\\'\\|\\w") 
	(if (not (re-search-backward "\\S-" (proof-locked-end) t))
	    (error "Nothing to do!")))
    (if (not (= (char-after (point)) proof-terminal-char))
	(progn (forward-char) (insert proof-terminal-string) (setq ins t)))
    (proof-assert-until-point
     (function (lambda ()
		 (if ins (backward-delete-char 1))
		 (goto-char mrk) (insert proof-terminal-string))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Proof mode configuration                                         ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define-derived-mode proof-mode fundamental-mode 
  "Proof" "Proof mode - not standalone"
  (setq proof-buffer-type 'script))

;; the following callback is an irritating hack - there should be some
;; elegant mechanism for computing constants after the child has
;; configured.

(defun proof-config-done () 

;; calculate some strings and regexps for searching

  (setq proof-terminal-string (char-to-string proof-terminal-char))

  (setq pbp-goal-command (concat "Pbp %s" proof-terminal-string))
  (setq pbp-hyp-command (concat "PbpHyp %s" proof-terminal-string))

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
	       

;; keymap

  (define-key proof-mode-map
    (vconcat [(control c)] (vector proof-terminal-char))
    'proof-active-terminator-minor-mode)

  (define-key proof-mode-map [(control c) (control e)]
    'proof-find-next-terminator)
  (define-key proof-mode-map [(control c) (control c)] 'proof-interrupt-process)
  (define-key proof-mode-map proof-terminal-char 'proof-active-terminator)
  (define-key proof-mode-map [(control c) (return)] 'proof-assert-until-point)
  (define-key proof-mode-map [(control c) (control t)] 'proof-try-command)
  (define-key proof-mode-map [(control c) u] 'proof-retract-until-point)
  (define-key proof-mode-map [(control c) (control u)] 'proof-undo-last-successful-command)
  (define-key proof-mode-map [(control c) (control v)] 'proof-execute-minibuffer-cmd)
  (define-key proof-mode-map [(control c) ?\'] 'proof-goto-end-of-locked)
  (define-key proof-mode-map [(control button1)] 'proof-send-span)
  (define-key proof-mode-map [(control c) (control b)] 'proof-process-buffer)
  (define-key proof-mode-map [(control c) (control z)] 'proof-frob-locked-end)

  ;; For fontlock
  (remove-hook 'font-lock-after-fontify-buffer-hook 'proof-zap-commas-buffer t)
  (add-hook 'font-lock-after-fontify-buffer-hook 'proof-zap-commas-buffer nil t)
  (remove-hook 'font-lock-mode-hook 'proof-unfontify-separator t)
  (add-hook 'font-lock-mode-hook 'proof-unfontify-separator nil t)

;; if we don't have the following, zap-commas fails to work.

  (setq font-lock-always-fontify-immediately t))

(define-derived-mode proof-shell-mode  comint-mode 
  "proof-shell" "Proof shell mode - not standalone"
  (setq proof-buffer-type 'shell)
  (setq proof-shell-busy nil)
  (setq proof-shell-delayed-output (cons 'insert "done"))
  (setq comint-prompt-regexp proof-shell-prompt-pattern)
  (add-hook 'comint-output-filter-functions 'proof-shell-filter nil t)
  (setq comint-get-old-input (function (lambda () "")))
  (proof-dont-show-annotations)
  (setq proof-marker (make-marker)))

(defun proof-shell-config-done ()
  (accept-process-output (get-buffer-process (current-buffer)))

  ;; If the proof process in invoked on a different machine e.g.,
  ;; for proof-prog-name="rsh fastmachine proofprocess", one needs
  ;; to adjust the directory:
  (and proof-shell-cd
       (proof-shell-insert (format proof-shell-cd default-directory)))

  (if proof-shell-init-cmd
       (proof-shell-insert proof-shell-init-cmd))
  (while (null (marker-position proof-marker))
    (if (accept-process-output (get-buffer-process (current-buffer)) 15)
	()
      (error "Failed to initialise proof process"))))

(define-derived-mode pbp-mode fundamental-mode 
  (setq proof-buffer-type 'pbp)
  "Proof" "Proof by Pointing"
  ;; defined-derived-mode pbp-mode initialises pbp-mode-map
  (suppress-keymap pbp-mode-map 'all)
  (define-key pbp-mode-map 'button2 'pbp-button-action)
  (erase-buffer))

(provide 'proof)
