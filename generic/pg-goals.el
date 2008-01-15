;; pg-goals.el ---  Proof General goals buffer mode.
;;
;; Copyright (C) 1994-2008 LFCS Edinburgh.
;; Authors:   David Aspinall, Yves Bertot, Healfdene Goguen,
;;            Thomas Kleymann and Dilip Sequeira
;; License:   GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; $Id$
;;

;;; Code:
(eval-when-compile
  (require 'easymenu)			; easy-menu-add, etc
  (require 'cl)				; incf
  (require 'span)			; span-*
  (require 'proof-utils))


;;; Commentary:
;; 

(require 'proof-site)
(require 'bufhist)
;(require 'pg-assoc)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Goals buffer mode
;;

;;;###autload
(define-derived-mode proof-goals-mode proof-universal-keys-only-mode
  proof-general-name
  "Mode for goals display.
May enable proof-by-pointing or similar features.
\\{proof-goals-mode-map}"
  (setq proof-buffer-type 'goals)
  ;; font-lock-keywords isn't automatically buffer-local in Emacs 21.2
  (make-local-variable 'font-lock-keywords)
  (add-hook 'kill-buffer-hook 'pg-save-from-death nil t)
  (easy-menu-add proof-goals-mode-menu proof-goals-mode-map)
  (easy-menu-add proof-assistant-menu proof-goals-mode-map)
  (proof-toolbar-setup)
  (erase-buffer)
  (buffer-disable-undo)
  (if proof-keep-response-history (bufhist-mode)) ; history for contents
  (set-buffer-modified-p nil))

;;
;; Menu for goals buffer
;;
(proof-eval-when-ready-for-assistant ; proof-aux-menu depends on <PA>
    (easy-menu-define proof-goals-mode-menu
      proof-goals-mode-map
      "Menu for Proof General goals buffer."
      (proof-aux-menu)))


;;
;; Keys for goals buffer
;;
(define-key proof-goals-mode-map [q] 'bury-buffer)

(cond
 ((featurep 'xemacs)
  (define-key proof-goals-mode-map [(button2)] 'pg-goals-button-action)
  (define-key proof-goals-mode-map [(control button2)] 'proof-undo-and-delete-last-successful-command)
  ;; button 2 is a nuisance on 2 button mice, so we'll do 1 as well.
  ;; Actually we better hadn't, people like to use it for cut and paste.
  ;; (define-key proof-goals-mode-map [(button1)] 'pg-goals-button-action)
  ;; (define-key proof-goals-mode-map [(control button1)] 'proof-undo-and-delete-last-successful-command)
  ;; C Raffalli: The next key on button3 will be remapped to proof by contextual
  ;; menu by pg-pbrpm.el.  In this case, control button3 is mapped to
  ;; 'pg-goals-yank-subterm
  (define-key proof-goals-mode-map [(button3)] 'pg-goals-yank-subterm))
 (t
  (define-key proof-goals-mode-map [mouse-2] 'pg-goals-button-action)
  (define-key proof-goals-mode-map [C-mouse-2] 'proof-undo-and-delete-last-successful-command)
  ;; (define-key proof-goals-mode-map [mouse-1] 'pg-goals-button-action)
  ;; (define-key proof-goals-mode-map [C-mouse-1] 'proof-undo-and-delete-last-successful-command)
  ;; C Raffalli: The next key on button3 will be remapped to proof by contextual
  ;; menu by pg-pbrpm.el.  In this case, control button3 is mapped to
  ;; 'pg-goals-yank-subterm
  (define-key proof-goals-mode-map [mouse-3] 'pg-goals-yank-subterm)))



;;
;; The completion of init
;;
;;;###autoload
(defun proof-goals-config-done ()
  "Initialise the goals buffer after the child has been configured."
  (proof-font-lock-configure-defaults nil)
  (proof-x-symbol-config-output-buffer))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Goals buffer processing
;;
(defun pg-goals-display (string)
  "Display STRING in the proof-goals-buffer, properly marked up.
Converts term substructure markup into mouse-highlighted extents,
and properly fontifies STRING using proof-fontify-region."
  (save-excursion
    ;; Response buffer may be out of date. It may contain (error)
    ;; messages relating to earlier proof states
    
    ;; NB: this isn't always the case.  In Isabelle
    ;; we get <WARNING MESSAGE> <CURRENT GOALS> output,
    ;; or <WARNING MESSAGE> <ORDINARY MESSAGE>.  Both times
    ;; <WARNING MESSAGE> would be relevant.
    ;; We should only clear the output that was displayed from
    ;; the *previous* prompt.
    
    ;; Erase the response buffer if need be, maybe removing the
    ;; window.  Indicate it should be erased before the next output.
    (pg-response-maybe-erase t t)

    ;; Erase the goals buffer and add in the new string
    (set-buffer proof-goals-buffer)

    (unless (eq 0 (buffer-size))
      (bufhist-checkpoint-and-erase))

    ;; Only display if string is non-empty.
    (unless (string-equal string "")
      (insert string)

      (if pg-use-specials-for-fontify
	  ;; With special chars for fontification, do that first,
	  ;; but keep specials in case also used for subterm markup.
	  (proof-fontify-region (point-min) (point-max) 'keepspecials))
	
      ;; Markup for PBP-style interaction.  This currently only works
      ;; for special characters 128-255, which is inconsistent with
      ;; UTF-8 interaction.
      (unless proof-shell-unicode
	(pg-assoc-analyse-structure (point-min) (point-max)))

      (unless pg-use-specials-for-fontify
	;; provers which use ordinary keywords to fontify output must
	;; do fontification second after subterm specials are removed.
	(proof-fontify-region (point-min) (point-max)))
      
      ;; Record a cleaned up version of output string
      (setq proof-shell-last-output
	    (buffer-substring (point-min) (point-max)))
      
      (set-buffer-modified-p nil)	; nicety
      
      ;; Keep point at the start of the buffer.
      (proof-display-and-keep-buffer
       proof-goals-buffer (point-min)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Commands to prover based on subterm markup (inc PBP).
;;
;;

;; Fairly specific to the mechanism implemented in LEGO
;; To make (more) sense of this code, you should read the
;; relevant LFCS tech report by tms, yb, and djs

(defun pg-goals-yank-subterm (event)
  "Copy the subterm indicated by the mouse-click EVENT.
This function should be bound to a mouse button in the Proof General
goals buffer.

The EVENT is used to find the smallest subterm around a point.  The
subterm is copied to the `kill-ring', and immediately yanked (copied)
into the current buffer at the current cursor position.

In case the current buffer is the goals buffer itself, the yank
is not performed.  Then the subterm can be retrieved later by an
explicit yank."
  (interactive "e")
  (let (span)
    (save-window-excursion
      (save-excursion
	(mouse-set-point event)
	;; Get either the proof body or whole goalsave
	(setq span (or
		    (span-at (point) 'proof)
		    (span-at (point) 'goalsave)))
	(if span (copy-region-as-kill
		  (span-start span)
		  (span-end span)))))
    (if (and span (not (eq proof-buffer-type 'goals)))
	(yank))))

(defun pg-goals-button-action (event)
  "Construct a proof-by-pointing command based on the mouse-click EVENT.
This function should be bound to a mouse button in the Proof General
goals buffer.

The EVENT is used to find the smallest subterm around a point.  A
position code for the subterm is sent to the proof assistant, to ask
it to construct an appropriate proof command.  The command which is
constructed will be inserted at the end of the locked region in the
proof script buffer, and immediately sent back to the proof assistant.
If it succeeds, the locked region will be extended to cover the
proof-by-pointing command, just as for any proof command the
user types by hand."
   (interactive "e")
   (mouse-set-point event)
   (pg-goals-construct-command))

;; Using the spans in a mouse behavior is quite simple: from the mouse
;; position, find the relevant span, then get its annotation and
;; produce a piece of text that will be inserted in the right buffer.

(defun proof-expand-path (string)
  (let ((a 0) (l (length string)) ls)
    (while (< a l)
      (setq ls (cons (int-to-string
		      (char-to-int (aref string a)))
		     (cons " " ls)))
      (incf a))
    (apply 'concat (nreverse ls))))

(defun pg-goals-construct-command ()
  "Examine the goals "
  (let* ((span (span-at (point) 'goalsave)) ;; goalsave means subgoal no/name
	 (top-span (span-at (point) 'proof-top-element))
	 top-info)
    (if (null top-span) ()
      (setq top-info (span-property top-span 'proof-top-element))
      (pop-to-buffer proof-script-buffer)
      (cond
       (span
	(proof-shell-invisible-command
	 (format (if (eq 'hyp (car top-info)) pbp-hyp-command
		                              pbp-goal-command)
		 (concat (cdr top-info) (proof-expand-path
					 (span-property span 'goalsave))))))
       ((eq (car top-info) 'hyp)
	;; Switch focus to another subgoal; a non-scripting command
	(proof-shell-invisible-command
	 (format pbp-hyp-command (cdr top-info))))
       ((eq (car top-info) 'goal)
	;; A scripting command to change goal
	 (proof-insert-pbp-command
	  (format pg-goals-change-goal (cdr top-info))))
       ((eq (car top-info) 'lit)
	;; A literal command to insert
	(proof-insert-pbp-command (cdr top-info)))))))



(defun pg-goals-get-subterm-help (spanorwin &optional obj pos)
  "Return a help string for subterm, called via 'help-echo property."
  (let ((span  (or obj spanorwin))) ;; GNU Emacs vs XEmacs interface
    (if (and pg-subterm-help-cmd (span-live-p span))
	(or (span-property span 'cachedhelp) ;; already got
	    (progn
	      (if (proof-shell-available-p)
		  (let ((result
			 (proof-shell-invisible-cmd-get-result
			  (format pg-subterm-help-cmd (span-string span))
			  'ignorerrors)))
		    ;; FIXME: generalise, and make output readable
		    ;; (fontify?  does that work for GNU Emacs?
		    ;;  how can we do it away from a buffer?)
		    (setq result
			  (replace-in-string
			   result
			   (concat "\n\\|" pg-special-char-regexp) ""))
		    (span-set-property span 'cachedhelp result)
		    result)))))))



(provide 'pg-goals)

;;; pg-goals.el ends here
