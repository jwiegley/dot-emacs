;; pg-response.el --- Proof General response buffer mode.
;;
;; Copyright (C) 1994-2008 LFCS Edinburgh.
;; Authors:   David Aspinall, Healfdene Goguen,
;;		Thomas Kleymann and Dilip Sequeira
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; $Id$
;;
;;; Commentary:
;; 
;; This mode is used for the response buffer proper, and
;; also the trace and theorems buffer. A sub-module of proof-shell.
;;

;;; Code:

(eval-when-compile
  (require 'easymenu)			; easy-menu-add
  (require 'proof-utils))		; deflocal, proof-eval-when-ready-for-assistant

(require 'bufhist)
(require 'pg-assoc)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Local variables
;;

(deflocal pg-response-eagerly-raise t
  "Non-nil if this buffer will be eagerly raised/displayed on startup.")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Response buffer mode
;;

;;;###autoload
(define-derived-mode proof-response-mode proof-universal-keys-only-mode
  "PGResp" "Responses from Proof Assistant"
  (setq proof-buffer-type 'response)
  ;; font-lock-keywords isn't automatically buffer-local in Emacs 21.2
  (make-local-variable 'font-lock-keywords)
  (define-key proof-response-mode-map [(button2)] 'pg-goals-button-action)
  (define-key proof-response-mode-map [q] 'bury-buffer)
  (define-key proof-response-mode-map [c] 'pg-response-clear-displays)
  (add-hook 'kill-buffer-hook 'pg-save-from-death nil t)
  (easy-menu-add proof-response-mode-menu proof-response-mode-map)
  (easy-menu-add proof-assistant-menu proof-response-mode-map)
  (proof-toolbar-setup)
  (setq pg-response-next-error nil)
  (erase-buffer)
  (buffer-disable-undo)
  (if proof-keep-response-history (bufhist-mode)) ; history for contents
  (set-buffer-modified-p nil))

(proof-eval-when-ready-for-assistant ; proof-aux-menu depends on <PA>
    (easy-menu-define proof-response-mode-menu
      proof-response-mode-map
      "Menu for Proof General response buffer."
      (proof-aux-menu)))

;;;###autoload
(defun proof-response-config-done ()
  "Complete initialisation of a response-mode derived buffer."
  (proof-font-lock-configure-defaults nil)
  (proof-x-symbol-config-output-buffer))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;; Window configuration
;;   -- multiple frames for goals and response buffers,
;;   -- three window mode
;;

;; FIXME: 3.5: things are better than before but still quite bad.
;; To really do this well I think we simply have to write specialised
;; frame handling code --- and do it twice, once for each Emacs.
;;
;; Choice comment from XEmacs frame.el before special-display-popup-frame:
;; "#### Change, not compatible with FSF: This stuff is all so incredibly
;; junky anyway that I doubt it makes any difference."

(defvar pg-response-special-display-regexp nil
  "Regexp for `special-display-regexps' for multiple frame use.
Internal variable, setting this will have no effect!")

;; NB: this list uses XEmacs defaults in the non-multiframe case.
;; We handle specifiers quit crudely, bute (1) to set for the
;; frame specifically we'd need to get hold of the frame,
;; (2) specifiers have been (still are) quite buggy.
(defconst proof-multiframe-specifiers
  (if (featurep 'xemacs)
      (list
       (list has-modeline-p nil nil) ;; nil even in ordinary case.
       (list menubar-visible-p nil t)
       (list default-gutter-visible-p nil t)
       (list default-toolbar-visible-p nil t)))
  "List of XEmacs specifiers and their values for non-multiframe and multiframe.")

(defun proof-map-multiple-frame-specifiers (multiframep locale)
  "Set XEmacs specifiers according to MULTIFRAMEP in LOCALE."
  (dolist (spec proof-multiframe-specifiers)
    ;; FIXME: Unfortunately these specifiers seem to get lost very
    ;; easily --- the toolbar, gutter, modeline all come back
    ;; for no good reason.  Can we construct a simple bug example?
    (if (fboundp 'set-specifier) ; nuke compile warning
	(set-specifier (car spec)
		       (if multiframep (cadr spec) (caddr spec))
		       locale))))

(defconst proof-multiframe-parameters
  '((minibuffer . nil)
    (modeline . nil)			; ignored?
    (unsplittable . t)
    (menu-bar-lines . 0)
    (tool-bar-lines . nil)
    (proofgeneral . t)) ;; indicates generated for/by PG  FIXME!!
  "List of GNU Emacs frame parameters for secondary frames.")

(defun proof-multiple-frames-enable ()
  (if (featurep 'xemacs)
      (proof-map-buffers
       (proof-associated-buffers)
       (proof-map-multiple-frame-specifiers proof-multiple-frames-enable
					    (current-buffer))))
  (let ((spdres
	 (if (featurep 'xemacs)
	     pg-response-special-display-regexp
	   (cons ; GNU Emacs uses this to set frame params too, handily
	    pg-response-special-display-regexp
	    proof-multiframe-parameters))))
    (if proof-multiple-frames-enable
	(add-to-list 'special-display-regexps spdres)
      (setq special-display-regexps
	    (delete spdres special-display-regexps))))
  (proof-layout-windows))

(defun proof-three-window-enable ()
  (proof-layout-windows))


(defun proof-select-three-b (b1 b2 b3 &optional nohorizontalsplit)
  "Select three buffers. Put them into three windows, selecting the last one."
  (interactive "bBuffer1:\nbBuffer2:\nbBuffer3:")
  (delete-other-windows)
  (if nohorizontalsplit
      (split-window-vertically)
    (split-window-horizontally))
  (switch-to-buffer b1)
  (other-window 1)
  (split-window-vertically)
  (switch-to-buffer b2)
  (other-window 1)
  (switch-to-buffer b3)
  (other-window 1))

(defun proof-display-three-b (&optional nohorizontalsplit)
  "Layout three buffers in a single frame."
  (interactive)
  (proof-select-three-b
   (or proof-script-buffer (first (buffer-list)))
   ;; Pierre had response buffer first, I think goals
   ;; is a bit nicer though?
   (if (buffer-live-p proof-goals-buffer)
       proof-goals-buffer (first (buffer-list)))
   (if (buffer-live-p proof-response-buffer)
       proof-response-buffer (first (buffer-list)))
   nohorizontalsplit))
   

(defvar pg-frame-configuration nil
  "Variable storing last used frame configuration.")

;; FIXME: would be nice to try storing this persistently.
(defun pg-cache-frame-configuration ()
  "Cache the current frame configuration, between prover restarts."
  (setq pg-frame-configuration (current-frame-configuration)))

(defun proof-layout-windows (&optional nohorizontalsplit)
  "Refresh the display of windows according to current display mode.

For single frame mode, this uses a canonical layout made by splitting
Emacs windows vertically in equal proportions.  You can then adjust
the proportions by dragging the separating bars.  In three pane mode,
the canonical layout is to split both horizontally and vertically, to
display the prover responses in two panes on the right-hand side, and
the proof script in a taller pane on the left.  A prefix argument will
prevent the horizontal split, and result in three windows spanning the
full width of the Emacs frame.

For multiple frame mode, this function obeys the setting of
`pg-response-eagerly-raise', which see."
  (interactive "P")
  (cond
   (proof-multiple-frames-enable
    (delete-other-windows) ;; hope we're on the right frame/window
    (if proof-script-buffer
	(switch-to-buffer proof-script-buffer))
    (proof-map-buffers (proof-associated-buffers)
      (if pg-response-eagerly-raise
	  (proof-display-and-keep-buffer (current-buffer))))
    ;; Restore an existing frame configuration (seems buggy, typical)
    (if pg-frame-configuration
	(set-frame-configuration pg-frame-configuration 'nodelete)))
   ;; Three window mode: use the Pierre-layout by default
   (proof-three-window-enable
    (proof-delete-other-frames)
    (set-window-dedicated-p (selected-window) nil)
    (proof-display-three-b nohorizontalsplit))
   ;; Two-of-three window mode.
   ;; Show the response buffer as first in preference order.
   (t
    (proof-delete-other-frames)
    (set-window-dedicated-p (selected-window) nil)
    (delete-other-windows)
    (if (buffer-live-p proof-response-buffer)
	(proof-display-and-keep-buffer proof-response-buffer))))
  (pg-hint (pg-response-buffers-hint)))

(defun proof-delete-other-frames ()
  "Delete frames showing associated buffers."
  (save-selected-window
    ;; FIXME: this is a bit too brutal.  If there is no
    ;; frame for the associated buffer, we may delete
    ;; the main frame!!
    (let ((mainframe
	   (window-frame
	    (if proof-script-buffer
		(proof-get-window-for-buffer proof-script-buffer)
	      ;; We may lose with just selected window
	      (selected-window)))))
      (proof-map-buffers (proof-associated-buffers)
	(let* ((win
		;; NB: g-w-f-b will re-display in new frame if
		;; the buffer isn't selected/visible.  This causes
		;; new frame to flash up and be deleted if already
		;; deleted!
		;; (proof-get-window-for-buffer (current-buffer))
		;; This next choice is probably better:
		(get-buffer-window (current-buffer) 'visible))
	       (fm (and win (window-frame win))))
	  (unless (equal mainframe fm)
	    (if fm (delete-frame fm))))))))
	
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;; Displaying in the response buffer
;;

;; Flag and function to keep response buffer tidy.
(defvar pg-response-erase-flag nil
  "Non-nil means the response buffer should be cleared before next message.")

;;;###autoload
(defun pg-response-maybe-erase
  (&optional erase-next-time clean-windows force)
  "Erase the response buffer according to pg-response-erase-flag.
ERASE-NEXT-TIME is the new value for the flag.
If CLEAN-WINDOWS is set, use proof-clean-buffer to do the erasing.
If FORCE, override pg-response-erase-flag.

If the user option proof-tidy-response is nil, then
the buffer is only cleared when FORCE is set.

No effect if there is no response buffer currently.
Returns non-nil if response buffer was cleared."
  (when (buffer-live-p proof-response-buffer)
    (let ((doit (or (and
		     proof-tidy-response
		     (not (eq pg-response-erase-flag 'invisible))
		     pg-response-erase-flag)
		    force)))
      (if doit
	  (if clean-windows
	      (proof-clean-buffer proof-response-buffer)
	  ;; NB: useful optional arg to erase buffer is XEmacs specific, 8-(.
	  ;; (erase-buffer proof-response-buffer)
	    (with-current-buffer proof-response-buffer
	      (setq pg-response-next-error nil)	; all error msgs lost!
	      (if (> (buffer-size) 0)
		  (bufhist-checkpoint-and-erase))
	      (set-buffer-modified-p nil))))
      (setq pg-response-erase-flag erase-next-time)
      doit)))

(defun pg-response-display (str)
  "Show STR as a response in the response buffer."
  (unless (or proof-shell-unicode
	      pg-use-specials-for-fontify)
    (setq str (pg-assoc-strip-subterm-markup str)))
  (pg-response-maybe-erase t nil)
  ;;(unless (or (string-equal str "") (string-equal str "\n"))
    ;; don't display an empty buffer [ NB: above test repeated below,
    ;; but response-display reused elsewhere ]
  (pg-response-display-with-face str)
  ;; NB: this displays an empty buffer sometimes when it's not
  ;; so useful.  It _is_ useful if the user has requested to
  ;; see the proof state and there is none
  ;; (Isabelle/Isar displays nothing: might be better if it did).
  (proof-display-and-keep-buffer proof-response-buffer))
  
;; TODO: this function should be combined with
;; pg-response-maybe-erase-buffer.
(defun pg-response-display-with-face (str &optional face)
  "Display STR with FACE in response buffer."
  (cond
   ((string-equal str ""))
   ((string-equal str "\n"))		; quick exit, no display.
   (t
    (let (start end)
      (with-current-buffer proof-response-buffer
	;; da: I've moved newline before the string itself, to match
	;; the other cases when messages are inserted and to cope
	;; with warnings after delayed output (non newline terminated).
	(goto-char (point-max))
	;; insert a newline before the new message unless the
	;; buffer is empty
	(unless (eq (point-min) (point-max))
	  (newline))
	(setq start (point))
	(insert str)
	(unless (bolp) (newline))

	;; Do pbp markup here, e.g. for "sendback" commands.
	;; NB: we might loose if markup has been split between chunks, but this
	;; will could only happen in cases of huge (spilled) output
	(pg-assoc-analyse-structure start (point-max))
	
	(proof-fontify-region start (point))

	;; This is one reason why we don't keep the buffer in font-lock
	;; minor mode: it destroys this hacky property as soon as it's
	;; made!  (Using the minor mode is much more convenient, tho')
	(if (and face proof-output-fontify-enable)
	    (font-lock-append-text-property
	     start (point-max) 'face face))

	(set-buffer-modified-p nil))))))


(defun pg-response-clear-displays ()
  "Clear Proof General response and tracing buffers.
You can use this command to clear the output from these buffers when
it becomes overly long.  Particularly useful when `proof-tidy-response'
is set to nil, so responses are not cleared automatically."
  (interactive)
  (proof-map-buffers (list proof-response-buffer proof-trace-buffer)
    (if (> (buffer-size) 0)
	(bufhist-checkpoint-and-erase))
    (set-buffer-modified-p nil)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Next error function.
;;

;;;###autoload
(defun proof-next-error (&optional argp)
  "Jump to location of next error reported in the response buffer.

A prefix arg specifies how many error messages to move;
negative means move back to previous error messages.

Optional argument ARGP means reparse the error message buffer
and start at the first error."
  (interactive "P")
  (if (and ;; At least one setting must be configured
       pg-next-error-regexp
       ;; Response buffer must be live
       (or
	(buffer-live-p proof-response-buffer)
	(error "Next error: no response buffer to parse!")))
      (let ((wanted-error    (or (and (not (consp argp))
				      (+ (prefix-numeric-value argp)
					 (or pg-response-next-error 0)))
				 (and (consp argp) 1)
				 (or pg-response-next-error 1)))
	    line column file errpos)
	(set-buffer proof-response-buffer)
	(goto-char (point-min))
	(if (re-search-forward pg-next-error-regexp
			       nil t wanted-error)
	    (progn
	      (setq errpos (save-excursion
			     (goto-char (match-beginning 0))
			     (beginning-of-line)
			     (point)))
	      (setq line (match-string 2)) ; may be unset
	      (if line (setq line (string-to-number line)))
	      (setq column (match-string 3)) ; may be unset
	      (if column (setq column (string-to-number column)))
	      (setq pg-response-next-error wanted-error)
	      (if (and
		   pg-next-error-filename-regexp
		     ;; Look for the most recently mentioned filename
		     (re-search-backward
		      pg-next-error-filename-regexp nil t))
		    (setq file
			  (if (file-exists-p (match-string 2))
			      (match-string 2)
			    ;; May need post-processing to extract filename
			    (if pg-next-error-extract-filename
				(format
				 pg-next-error-extract-filename
				 (match-string 2))))))
		;; Now find the other buffer we need to display
		(let*
		    ((errbuf
		      (if file
			  (find-file-noselect file)
			(or proof-script-buffer
			    ;; We could make more guesses here,
			    ;; e.g. last script buffer active
			    ;; (keep a record of it?)
			    (error
			     "Next error: can't guess file for error message"))))
		     (pop-up-windows t)
		     (rebufwindow
		      (or (get-buffer-window proof-response-buffer 'visible)
			  ;; Pop up a window.
			  (display-buffer proof-response-buffer))))
		  ;; Make sure the response buffer stays where it is,
		  ;; and make sure source buffer is visible
		  (select-window rebufwindow)
		  (pop-to-buffer errbuf)
		  ;; Display the error message in the response buffer
		  (set-window-point rebufwindow errpos)
		  (set-window-start rebufwindow errpos)
		  ;; Find the error location in the error buffer
		  (set-buffer errbuf)
		  ;; FIXME: no handling of selective display here
		  (goto-line line)
		  (if (and column (> column 1))
		      (move-to-column (1- column)))))
	    (setq pg-response-next-error nil)
	    (error "Next error: couldn't find a next error")))))

;;;###autoload
(defun pg-response-has-error-location ()
  "Return non-nil if the response buffer has an error location.
See `pg-next-error-regexp'."
  (if (and pg-next-error-regexp
	   (buffer-live-p proof-response-buffer))
      (save-excursion
	(set-buffer proof-response-buffer)
	(goto-char (point-min))
	(re-search-forward pg-next-error-regexp nil t))))
	

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Tracing buffers
;;

;; NB: fontifying massive trace output can be expensive: might be nice
;; to have heuristic here (or use lazy-shot style mode) to see if we
;; can fontify less eagerly.  Actually, this might be solved best by
;; actually using the lazy-shot mechanism and having buffers in
;; x-symbool and font-lock modes.  To fix that, though, we would have
;; to fix up the cut-and-paste behaviour somehow.

(defvar proof-trace-last-fontify-pos nil)

(defun proof-trace-fontify-pos ()
  "Return the position to fontify from in the tracing buffer, if any."
  (if proof-trace-last-fontify-pos
      (if (> proof-trace-last-fontify-pos (point))
	  (point-min);; in case buffer cleared
	proof-trace-last-fontify-pos)))

;; An analogue of pg-response-display-with-face
(defun proof-trace-buffer-display (str)
  "Output STR in the trace buffer, moving the pointer downwards.
We fontify the output only if we're not too busy to do so."
  (with-current-buffer proof-trace-buffer
    (goto-char (point-max))
    (newline)
    (or proof-trace-last-fontify-pos
	(setq proof-trace-last-fontify-pos (point)))
    (insert str)
    (unless (bolp)
      (newline))
    ;; If tracing output is prolific, we try to avoid
    ;; fontifying every chunk and batch it up instead.
    (unless pg-tracing-slow-mode ; defined in proof-shell.el
      (let ((fontifystart (proof-trace-fontify-pos)))
	;; Catch errors here: this is to deal with ugly problem when
	;; fontification of large output gives error Nesting too deep
	;; for parser [see etc/isar/nesting-too-deep-for-parser.txt],
	;; a serious flaw in XEmacs version of parse-partial-sexp
	(unwind-protect
	    (proof-fontify-region fontifystart (point))
	  (setq proof-trace-last-fontify-pos nil))
	(set-buffer-modified-p nil)))))

(defun proof-trace-buffer-finish ()
  "Complete fontification in tracing buffer now that there's time to do so."
  (let ((fontifystart (proof-trace-fontify-pos)))
    (if (and fontifystart (not quit-flag));; may be done already/user desparately trying to avoid
	(save-excursion
	   (set-buffer proof-trace-buffer)
	   (proof-fontify-region fontifystart (point-max))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Theorems buffer
;;
;; [ INCOMPLETE ]
;;
;; Revives an old idea from Isamode: a buffer displaying a bunch
;; of theorem names.
;;
;; 

(defun pg-thms-buffer-clear ()
  "Clear the theorems buffer."
  (with-current-buffer proof-thms-buffer
    (let (start str)
      (goto-char (point-max))
      (newline)
      (setq start (point))
      (insert str)
      (unless (bolp) (newline))
      (proof-fontify-region start (point))
      (set-buffer-modified-p nil))))


(provide 'pg-response)
;;; pg-response.el ends here
