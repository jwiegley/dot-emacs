;; proof.el Major mode for proof assistants
;; Copyright (C) 1994 - 1997 LFCS Edinburgh. 
;; Authors: Yves Bertot, Healfdene Goguen, Thomas Kleymann and Dilip Sequeira

;; Maintainer: LEGO Team <lego@dcs.ed.ac.uk>
;; Thanks to David Aspinall, Robert Boyer, Rod Burstall,
;;           James McKinna, Mark Ruys, Martin Steffen, Perdita Stevens  



;; TO DO:

;; o Need to think about fixing up errors caused by pbp-generated commands

;; o undo support needs to consider Discharge; perhaps unrol to the
;;   beginning of the module? 

;; o pbp code is horribly inefficient and doesn't accord with the tech
;;   report

;; $Log$
;; Revision 1.21  1997/11/06 16:56:59  hhg
;; Parameterize by proof-goal-hyp-fn in pbp-make-top-extent, to handle
;; Coq goals which start with text rather than simply ?n
;;
;; Updated 'let (ap 0)' in proof-shell-analyse structure, to be slightly
;; more compatible with Coq pbp code
;;
;; Revision 1.20  1997/10/31 15:11:28  tms
;; o implented proof-find-next-terminator available via C-c C-e
;; o fixed a bug in proof-done-retracting
;;
;; Revision 1.19  1997/10/30 15:58:33  hhg
;; Updates for coq, including:
;; 	* pbp-goal-command and pbp-hyp-command use proof-terminal-string
;; 	* updates to keywords
;; 	* fix for goal regexp
;;
;; Revision 1.18  1997/10/24 14:51:13  hhg
;; Updated comment about extent types
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

(defvar proof-shell-echo-input t
  "If nil, input to the proof shell will not be echoed")

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

(defvar proof-shell-sanitise nil "sanitise output?")

(defvar pbp-error-regexp nil
  "A regular expression indicating that the PROOF process has
  identified an error.") 

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Internal variables used by scripting and pbp                    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar proof-terminal-string nil 
  "You are not authorised for this information.")

(defvar proof-re-end-of-cmd nil 
  "You are not authorised for this information.")

(defvar proof-re-term-or-comment nil 
  "You are not authorised for this information.")

(defvar proof-locked-hwm nil
  "Upper limit of the locked region")

(defvar proof-queue-loose-end nil
  "Limit of the queue region that is not equal to proof-locked-hwm.")

(defvar proof-mark-ext nil 
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

(defvar extended-shell-command-on-region
  (emacs-version-at-least 19 29)
  "Does `shell-command-on-region' optionally offer to output in an other buffer?")

;; in case Emacs is not aware of read-shell-command-map
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


;; in case Emacs is not aware of the function read-shell-command
(or (fboundp 'read-shell-command)
    ;; from minibuf.el distributed with XEmacs 19.11
    (defun read-shell-command (prompt &optional initial-input history)
      "Just like read-string, but uses read-shell-command-map:
\\{read-shell-command-map}"
      (let ((minibuffer-completion-table nil))
        (read-from-minibuffer prompt initial-input read-shell-command-map
                              nil (or history
                              'shell-command-history)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Spans and segments                                              ;;
;;  Because one day we might wish to port to emacs19                ;;
;;  Note that we need to go back to using marks too                 ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsubst make-span (start end)
  (make-extent start end))

(defsubst set-span-endpoints (span start end)
  (set-extent-endpoints span start end))

(defsubst set-span-start (span value)
  (set-extent-endpoints span value (extent-end-position span)))

(defsubst set-span-end (span value)
  (set-extent-endpoints span (extent-start-position span) value))

(defsubst span-property (span name)
  (extent-property span name))

(defsubst set-span-property (span name value)
  (set-extent-property span name value))

(defsubst delete-span (span)
  (delete-extent span))

(defsubst delete-spans (start end prop)
  (mapcar-extents 'delete-extent nil (current-buffer) start end  nil prop))

(defsubst span-at (pt prop)
  (extent-at pt nil prop))

(defsubst span-at-before (pt prop)
  (extent-at pt nil prop nil 'before))
  
(defsubst span-start (span)
  (extent-start-position span))

(defsubst span-end (span)
  (extent-end-position span))

(defsubst prev-span (span prop)
  (extent-at (extent-start-position span) nil prop nil 'before))

(defsubst next-span (span prop)
  (extent-at (extent-end-position span) nil prop nil 'after))

(defvar proof-locked-ext nil
  "Upper limit of the locked region")

(defvar proof-queue-ext nil
  "Upper limit of the locked region")

(defun proof-init-segmentation ()
  (setq proof-queue-loose-end nil)
  (setq proof-queue-ext (make-extent nil nil (current-buffer)))
  (set-extent-property proof-queue-ext 'start-closed t)
  (set-extent-property proof-queue-ext 'end-open t)
  (set-extent-property proof-queue-ext 'read-only t)
  (make-face 'proof-queue-face)
  (if (eq (device-class (frame-device)) 'color)
	     (set-face-background 'proof-queue-face "mistyrose")
    (set-face-background 'proof-queue-face "Black")
    (set-face-foreground 'proof-queue-face "White"))
  (set-extent-property proof-queue-ext 'face 'proof-queue-face)
  
  (setq proof-locked-hwm nil)
  (setq proof-locked-ext (make-extent nil nil (current-buffer)))
  (set-extent-property proof-locked-ext 'start-closed t)
  (set-extent-property proof-locked-ext 'end-open t)
  (set-extent-property proof-locked-ext 'read-only t)
  (if (eq (device-class (frame-device)) 'color)
      (progn (make-face 'proof-locked-face)
	     (set-face-background 'proof-locked-face "lavender")
	     (set-extent-property proof-locked-ext 'face 'proof-locked-face))
    (set-extent-property proof-locked-ext 'face 'underline)))

(defun proof-segment-buffer (eol eoq)
   (setq proof-locked-hwm eol
         proof-queue-loose-end eoq)
   (if (and (null eoq) (null eol))
       (progn (detach-extent proof-locked-ext)
	      (detach-extent proof-queue-ext))
     (if (eq eol (point-min))
	 (detach-extent proof-locked-ext)
       (set-extent-endpoints proof-locked-ext (point-min) eol 
			     (current-buffer)))
     (if (eq eol eoq)
	 (progn
	   (detach-extent proof-queue-ext)
	   (setq proof-queue-loose-end nil))
       (set-extent-endpoints proof-queue-ext eol eoq (current-buffer)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;          A couple of small utilities                             ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

(defun proof-end-of-locked ()
  "Jump to the end of the locked region."
  (interactive)
  (or proof-locked-hwm (point-min)))

(defun proof-goto-end-of-locked ()
  "Jump to the end of the locked region."
  (interactive)
  (goto-char (proof-end-of-locked)))


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

      (let ((prog-name-list (string-to-list proof-prog-name " ")))
	(apply 'make-comint  (append (list proc (car prog-name-list) nil)
				     (cdr prog-name-list))))

      (setq proof-shell-buffer (get-buffer (concat "*" proc "*")))
      (setq proof-pbp-buffer (get-buffer-create (concat "*" proc "-goals*")))

      (save-excursion
	(set-buffer proof-shell-buffer)
	(funcall proof-mode-for-shell)
	(set-buffer proof-pbp-buffer)
	(funcall proof-mode-for-pbp))

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
		(proof-segment-buffer nil nil))
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

(defvar pbp-keymap (make-keymap 'Pbp-keymap) 
  "Keymap for proof mode")

(defun pbp-button-action (event)
   (interactive "e")
   (mouse-set-point event)
   (pbp-construct-command))

(define-key pbp-keymap 'button2 'pbp-button-action)

; Using the extents in a mouse behavior is quite simple: from the
; mouse position, find the relevant extent, then get its annotation
; and produce a piece of text that will be inserted in the right
; buffer.  Attaching this behavior to the mouse is simply done by
; attaching a keymap to all the extents.

(defun proof-expand-path (string)
  (let ((a 0) (l (length string)) ls)
    (while (< a l) 
      (setq ls (cons (int-to-string (aref string a)) 
		     (cons " " ls)))
      (incf a))
    (apply 'concat (nreverse ls))))

(defun pbp-construct-command ()
  (let* ((ext (span-at (point) 'proof))
	 (top-ext (span-at (point) 'proof-top-element))
	 (top-info (span-property top-ext 'proof-top-element)) 
	 path cmd)
    (if (extentp top-ext)
	(cond 
	 ((extentp ext)
	  (setq path (concat (cdr top-info)
			     (proof-expand-path (span-property ext 'proof))))
	  (setq cmd
		(if (eq 'hyp (car top-info))
		    (format pbp-hyp-command path)
		  (format pbp-goal-command path)))
	  (pop-to-buffer proof-script-buffer)
	  (proof-invisible-command cmd))
	 (t
	  (if (eq 'hyp (car top-info))
	      (progn
		(setq cmd (format pbp-hyp-command (cdr top-info)))
		(pop-to-buffer proof-script-buffer)
		(proof-invisible-command cmd))
	      (setq cmd (format pbp-change-goal (cdr top-info)))
	      (pop-to-buffer proof-script-buffer)
	      (proof-insert-pbp-command cmd)))))))

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

(defun pbp-make-top-extent (start end)
  (let (extent name)
    (goto-char start)
    (setq name (funcall proof-goal-hyp-fn))
    (beginning-of-line)
    (setq start (point))
    (goto-char end)
    (beginning-of-line)
    (backward-char)
    (setq extent (make-extent start (point)))
    (set-span-property extent 'mouse-face 'highlight)
    (set-span-property extent 'keymap pbp-keymap)
    (set-span-property extent 'proof-top-element name)))

(defun proof-shell-analyse-structure (string)
  (save-excursion
    (let* ((ip 0) (op 0) (ap 0) (l (length string)) 
	   (ann (make-string (length string) ?x))
           (stack ()) (topl ()) 
	   (out (make-string l ?x )) c ext)
      (while (< ip l)
	(setq c (aref string ip))
	(if (< c proof-shell-first-special-char)
	    (progn (aset out op c)
		   (incf op))
	  (cond 
	   ((= c proof-shell-goal-char)
	    (setq topl (append topl (list (+ 1 op)))))
	   ((= c proof-shell-start-char)	    
	    (setq ap (- (aref string (incf ip)) 128))
	    (incf ip)
	    (while (not (= (aref string ip) proof-shell-end-char))
	      (aset ann ap (- (aref string ip) 128))
	      (incf ap)
	      (incf ip))
	    (setq stack (cons op (cons (substring ann 0 ap) stack))))
	   ((= c proof-shell-field-char)
	    (setq ext (make-extent (car stack) op out))
	    (set-span-property ext 'mouse-face 'highlight)
	    (set-span-property ext 'keymap pbp-keymap)
	    (set-span-property ext 'proof (cadr stack))
	    (set-span-property ext 'duplicable t)
	    (setq stack (cddr stack)))))
	(incf ip))
      (display-buffer (set-buffer proof-pbp-buffer))
      (erase-buffer)
      (insert (substring out 0 op))
      (while (setq ip (car topl) 
		   topl (cdr topl))
	(pbp-make-top-extent ip (car topl)))
      (pbp-make-top-extent ip (point-max)))))

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
  (proof-segment-buffer proof-locked-hwm proof-locked-hwm)
  (delete-spans (proof-end-of-locked) (point-max) 'type)
  (proof-release-lock))

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
	(insert str))
       ((eq ins 'analyse)
	(proof-shell-analyse-structure str))
       (t (set-buffer proof-pbp-buffer)
	  (insert "\n\nbug???")))))
  (setq proof-shell-delayed-output (cons 'insert "done")))


(defun proof-shell-process-output (cmd string)
  (cond 
   ((string-match proof-shell-error-regexp string)
    (cons 'error (proof-shell-strip-annotations 
		  (substring string (match-beginning 0)))))

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
  (goto-char (point-max))
  (insert (funcall proof-shell-config) string)
  (if (not (span-property proof-mark-ext 'detached))
      (set-span-endpoints proof-mark-ext (point) (point)))
  (comint-send-input))

(defun proof-send (string)
  (let ((l (length string)) (i 0))
    (while (< i l)
      (if (= (aref string i) ?\n) (aset string i ?\ ))
      (incf i)))
  (save-excursion
    (set-buffer proof-shell-buffer)
    (proof-shell-insert string)))

;; grab the process and return t, otherwise return nil. Note that this
;; is not really intended for anything complicated - just to stop the
;; user accidentally sending a command while the queue is running.

(defun proof-check-process-available ()
  (if (proof-shell-live-buffer)
      (if proof-shell-busy (error "Proof Process Busy!")))
  (if (not (eq proof-script-buffer (current-buffer)))
      (error "Don't own proof process"))
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
      (if (eq (proof-end-of-locked) start) 
	  (proof-segment-buffer start end)
	(proof-segment-buffer end start)))
  (while (and alist (string= (cadar alist) "COMMENT"))
    (funcall (caddar alist) (caar alist))
    (setq alist (cdr alist)))
  (if alist
      (progn
	(proof-grab-lock) 
	(erase-buffer proof-pbp-buffer)
	(setq proof-shell-delayed-output (cons 'insert "Done."))
	(setq proof-action-list alist)
	(proof-send (cadar alist)))))

; returns t if it's run out of input

(defun proof-shell-exec-loop ()
  (save-excursion
    (set-buffer proof-script-buffer)
    (if (null proof-action-list) (error "Non Sequitur"))
    (funcall (caddar proof-action-list) (caar proof-action-list))
    (setq proof-action-list (cdr proof-action-list))
    (while (and proof-action-list
		(string= (cadar proof-action-list) "COMMENT"))
      (funcall (caddar proof-action-list) (caar proof-action-list))
      (setq proof-action-list (cdr proof-action-list)))
    (if (null proof-action-list)
	(progn (proof-release-lock)
	       (proof-segment-buffer proof-locked-hwm proof-locked-hwm)
	       t)
      (proof-send (cadar proof-action-list))
      nil)))

(defun proof-shell-insert-loopback-cmd  (cmd)
  "Insert command sequence triggered by the proof process
at the end of locked region (after inserting a newline)."
  (save-excursion
    (set-buffer proof-script-buffer)
    (let (ext)
      (proof-goto-end-of-locked)
      (newline)
      (insert cmd)
      (setq ext (make-span (proof-end-of-locked) (point)))
      (set-span-property ext 'type 'pbp)
      (set-span-property ext 'cmd cmd)
      (proof-segment-buffer (proof-end-of-locked) (point))
      (setq proof-action-list 
	    (cons (car proof-action-list) 
		  (cons (list ext cmd 'proof-done-advancing)
			(cdr proof-action-list)))))))

(defun proof-shell-popup-eager-annotation ()
  (let (mrk str file module)
    (save-excursion ;; BROKEN - MAY BE MULTI
      (goto-char (point-max))
      (search-backward proof-shell-eager-annotation-start)
      (setq mrk (+ 1 (point)))
      (search-forward proof-shell-eager-annotation-end)
      (setq str (buffer-substring mrk (- (point) 1)))
      (display-buffer (set-buffer proof-pbp-buffer))
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
      (if (span-property proof-mark-ext 'detached)
	  (progn
	    (goto-char (point-min))
	    (re-search-forward proof-shell-annotated-prompt-regexp)
	    (set-span-endpoints proof-mark-ext (point) (point))
	    (backward-delete-char 1))
	(let (string mrk res cmd)	
	    (goto-char (setq mrk (span-start proof-mark-ext)))
	    (re-search-forward proof-shell-annotated-prompt-regexp nil t)
	    (set-span-endpoints proof-mark-ext (point) (point))
	    (backward-char (- (match-end 0) (match-beginning 0)))
	    (setq string (buffer-substring mrk (point)))
	    (if proof-shell-sanitise 
		(progn
		  (delete-region mrk (point))
		  (insert (proof-shell-strip-annotations string))))
	    (goto-char (span-start proof-mark-ext))
	    (backward-delete-char 1)
	    (setq cmd (cadar proof-action-list))
	    (save-excursion
	      (setq res (proof-shell-process-output cmd string))
	      (cond
	       ((and (consp res) (eq (car res) 'error))
		(proof-shell-handle-error cmd (cdr res)))
	       ((and (consp res) (eq (car res) 'loopback))
		(proof-shell-insert-loopback-cmd (cdr res))
		(proof-shell-exec-loop))
	       (t (if (proof-shell-exec-loop)
		      (proof-shell-handle-delayed-output)))))))))

(defun proof-last-goal-or-goalsave ()
  (save-excursion
    (let ((ext (span-at-before (proof-end-of-locked) 'type)))
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
   ((or (null proof-script-buffer) (not (buffer-live-p proof-script-buffer)))
    (setq proof-script-buffer (current-buffer))
    (proof-init-segmentation)
    nil)
   (t 
    (let ((flist proof-included-files-list) 
	  (file (expand-file-name (buffer-file-name))) ext cmd)
      (if (string-match "\\(.*\\)\\.." file) (setq file (match-string 1 file)))
      (while (and flist (not (string= file (cdar flist))))
	(setq flist (cdr flist)))
      (if (null flist) 
	  (if (not (y-or-n-p "Steal script management? " )) (error "Aborted"))
	(if (not (y-or-n-p "Reprocess this file? " )) (error "Aborted")))
      (save-excursion
	(set-buffer proof-script-buffer)
	(setq ext (proof-last-goal-or-goalsave))
	(setq cmd (if (and ext (not (eq (span-property ext 'type) 'goalsave)))
		      proof-kill-goal-command ""))
	(proof-segment-buffer nil nil)
	(delete-spans (point-min) (point-max) 'type))      
      (setq proof-script-buffer (current-buffer))
      (proof-segment-buffer nil nil)

      (cond 
       (flist
	 (list nil (concat cmd "ForgetMark " (caar flist) ";")
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
; (extent,command,action) triples. The loop looks like: Execute the
; command, and if it's successful, do action on extent.  If the
; command's not successful, we bounce the rest of the queue and do
; some error processing.
;
; when an extent has been processed, we classify it as follows:
; 'goalsave - denoting a 'goalsave pair in the locked region
;    a 'goalsave region has a 'name property which is the name of the goal
; 'comment - denoting a comment
; 'pbp - denoting an extent created by pbp
; 'vanilla - denoting any other extent.
;   'pbp & 'vanilla extents have a property 'cmd, which says what
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
    (setq ext (make-span (proof-end-of-locked) (point)))
    (set-span-property ext 'type 'pbp)
    (set-span-property ext 'cmd cmd)
    (proof-start-queue (proof-end-of-locked) (point) 
		       (list (list ext cmd 'proof-done-advancing)))))

(defun proof-done-advancing (ext)
  (let ((end (span-end ext)) nam gext next cmd)
    (proof-segment-buffer end proof-queue-loose-end)
    (setq cmd (span-property ext 'cmd))
    (cond
     ((or (eq (span-property ext 'type) 'comment)
	  (not (string-match proof-save-command-regexp cmd)))
      (set-span-property ext 'highlight 'mouse-face))
     (t	
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
	(set-span-property gext 'name nam)))))
  
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
    (let ((str (make-string (- (buffer-size) (proof-end-of-locked) -10) ?x))
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

(defun proof-semis-to-vanillas (semis)
  (let ((ct (proof-end-of-locked)) ext alist)
    (while (not (null semis))
      (setq ext (make-span ct (caddar semis))
	    ct (caddar semis))
      (if (eq (caar semis) 'cmd)
	  (progn
	    (set-span-property ext 'type 'vanilla)
	    (set-span-property ext 'cmd (cadar semis))
	    (setq alist (cons (list ext (cadar semis) 'proof-done-advancing)
			      alist)))
	(set-span-property ext 'type 'comment)
	(setq alist (cons (list ext "COMMENT" 'proof-done-advancing) alist)))
	(setq semis (cdr semis)))
    (nreverse alist)))

; 

(defun proof-assert-until-point
  (&optional unclosed-comment-fun ignore-proof-process-p)
  "Process the region from the end of the locked-region until point.
   Default action if inside a comment is just to go until the start of
   the comment. If you want something different, put it inside
   unclosed-comment-fun. If ignore-proof-process-p is set, no commands
   will be added to the queue."
  (interactive)
  (let ((pt  (point)) semis crowbar)
    (setq crowbar (proof-steal-process))
    (save-excursion
      (if (not (re-search-backward "\\S-" (proof-end-of-locked) t))
	  (progn (goto-char pt)
		 (error "Nothing to do!")))
      (setq semis (proof-segment-up-to (point))))
    (if (and unclosed-comment-fun (eq 'unclosed-comment (car semis)))
	(funcall unclosed-comment-fun)
      (if (eq 'unclosed-comment (car semis)) (setq semis (cdr semis)))
      (if (and (not ignore-proof-process-p) (not crowbar) (null semis))
	  (error "Nothing to do!"))
      (goto-char (caddar semis))
      (and (not ignore-proof-process-p)
	   (let ((vanillas (proof-semis-to-vanillas (nreverse semis))))
	     (if crowbar (setq vanillas (cons crowbar vanillas)))
	     (proof-start-queue (proof-end-of-locked) (point) vanillas))))))
    
(defun proof-find-next-terminator ()
  "Set point after next `proof-terminal-char'."
  (interactive)
  (and (re-search-forward "\\S-" nil t)
       (proof-assert-until-point nil 'ignore-proof-process)))

(defun proof-done-retracting (ext)
  "Updates display after proof process has reset its state. See also
the documentation for `proof-retract-until-point'. It optionally
deletes the region corresponding to the proof sequence."
  (let ((start (span-start ext))
        (end (span-end ext))
	(kill (span-property ext 'delete-me)))
    (proof-segment-buffer start proof-queue-loose-end)
    (delete-spans start end 'type)
    (delete-span ext)
    (and kill (delete-region start end))))

(defun proof-setup-retract-action (start end proof-command delete-region)
  (let ((span (make-span start end)))
    (set-span-property span 'delete-me delete-region)
    (list (list span proof-command 'proof-done-retracting))))


(defun proof-retract-until-point (&optional delete-region)
  "Sets up the proof process for retracting until point. In
   particular, it sets a flag for the filter process to call
   `proof-done-retracting' after the proof process has actually
   successfully reset its state. It optionally deletes the region in
   the proof script corresponding to the proof command sequence."
  (interactive)
  (proof-check-process-available)
  (let ((sext (span-at (point) 'type)))
    (if (null (proof-end-of-locked)) (error "No locked region"))
    (if (null sext) (error "Outside locked region"))
    (funcall proof-retract-target-fn sext delete-region)))


(defun proof-undo-last-successful-command ()
  "Undo last successful command, both in the buffer recording the
   proof script and in the proof process. In particular, it deletes
   the corresponding part of the proof script."
  (interactive)
  (goto-char (span-start (span-at-before (proof-end-of-locked) 'type)))
  (proof-retract-until-point t))

(defun proof-restart-script ()
  (interactive)
  (save-excursion
    (if (buffer-live-p proof-script-buffer)
	(progn
	  (set-buffer proof-script-buffer)
	  (delete-spans (point-min) (point-max) 'type)
	  (proof-segment-buffer nil nil)))
    (setq proof-shell-busy nil
	  proof-script-buffer nil)
    (if (buffer-live-p proof-shell-buffer) 
	(kill-buffer proof-shell-buffer))
    (if (buffer-live-p proof-pbp-buffer)
	(kill-buffer proof-pbp-buffer))))

	  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;          Active terminator minor mode                            ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar proof-active-terminator-minor-mode nil 
"active terminator minor mode flag")

(make-variable-buffer-local 'proof-active-terminator-minor-mode)
(put 'proof-active-terminator-minor-mode 'permanent-local t)

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
	(if (not (re-search-backward "\\S-" (proof-end-of-locked) t))
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


;; keymap

  (define-key proof-mode-map
    (vconcat [(control c)] (vector proof-terminal-char))
    'proof-active-terminator-minor-mode)

  (define-key proof-mode-map [(control c) (control e)]
    'proof-find-next-terminator)

  (define-key proof-mode-map proof-terminal-char 'proof-active-terminator)
  (define-key proof-mode-map [(control c) (control a)]    'proof-assert-until-point)
  (define-key proof-mode-map [(control c) u]    'proof-retract-until-point)
  (define-key proof-mode-map [(control c) (control u)] 'proof-undo-last-successful-command)
  (define-key proof-mode-map [(control c) ?']
  'proof-goto-end-of-locked)

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
;  (add-hook 'comint-output-filter-functions 'comint-truncate-buffer nil t)
;  (setq comint-buffer-maximum-size 10000)
;

  (let ((disp (make-display-table))
	(i 128))
	(while (< i 256)
	  (aset disp i "")
	  (incf i))
	(add-spec-to-specifier current-display-table disp (current-buffer)))
		  
  (setq comint-append-old-input nil)
  (setq proof-mark-ext (make-extent nil nil (current-buffer)))
  (set-span-property proof-mark-ext 'detachable nil)
  (set-span-property proof-mark-ext 'start-closed t)
  (set-span-property proof-mark-ext 'end-open t))

(defun proof-shell-config-done ()
  (accept-process-output (get-buffer-process (current-buffer)))
  (if proof-shell-init-cmd
       (proof-shell-insert proof-shell-init-cmd))
  (while (span-property proof-mark-ext 'detached)
    (if (accept-process-output (get-buffer-process (current-buffer)) 5)
	()
      (error "Failed to initialise proof process"))))

(define-derived-mode pbp-mode fundamental-mode 
  (setq proof-buffer-type 'pbp)
  "Proof" "Proof by Pointing"
  ;; defined-derived-mode pbp-mode initialises pbp-mode-map
  (suppress-keymap pbp-mode-map)
  (erase-buffer))

(provide 'proof)
