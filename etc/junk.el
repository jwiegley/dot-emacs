;;; junk.el
;;;
;;;  $Id$
;;;
;;; Bits and pieces of code 
;;; removed from main PG (or never added).
;;; Left here in case they're useful later.
;;;
;;; Also some testing code.
;;;

;;; TESTING FRAGMENTS

;;; special display regexps
(setq special-display-regexps
     (cons "\\*isabelle-\\(goals\\|response\\)\\*"
	     special-display-regexps))


;;; dump str to buffer ug for testing.
(defun ugit (str)
  (save-excursion
    (set-buffer (get-buffer-create "ug"))
    (goto-char (point-max))
    (insert str)
    (newline)
    (newline)))




;;; OLD CODE

(defun proof-set-toggle (sym value)
  "Try to set a boolean variable <blah>-enable using function <blah>-toggle."
  (save-match-data
    (let* ((nm   (symbol-name sym))
	   (i    (string-match "-enable" nm))
	   (tgfn (if i (intern (concat (substring nm 0 i) "-toggle")))))
      (if (and tgfn (fboundp tgfn))
	  (funcall tgfn (if value 1 0))))))


;; Was in proof-shell.el
(defun proof-shell-popup-eager-annotation ()
  "Process urgent messages.
Eager annotations are annotations which the proof system produces
while it's doing something (e.g. loading libraries) to say how much
progress it's made. Obviously we need to display these as soon as they
arrive."
;; FIXME: highlight eager annotation-end : fix proof-shell-handle-output
;; to highlight whole string.
  (let ((str (proof-shell-handle-output
	      proof-shell-eager-annotation-start
	      proof-shell-eager-annotation-end
	      'proof-eager-annotation-face))
    (proof-shell-message str))))


;  (cond
;   ((string-match "FSF" emacs-version)
;    ;; setting font-lock-defaults explicitly is required by FSF Emacs
;    ;; 20.2's version of font-lock
;    (make-local-variable 'font-lock-defaults)
;    (setq font-lock-defaults '(font-lock-keywords)))
;   ;; In XEmacs, we must make a new variable to hold
;   ;; the defaults.  
;   ;; (FIXME: this makes toggling font-lock robust now, before
;   ;;  it was ropy.  Should check whether this is the right
;   ;;  was for FSF too).
;   (t
;    (let
;	((flks	(intern (concat (symbol-name major-mode)
;				"-font-lock-defaults"))))
;      ;; Take a copy of current font-lock-keywords to make them
;      ;; the default in future.  Then font-lock-mode can be
;      ;; safely switched on and off.
;      (set flks font-lock-keywords)
;      (make-local-variable 'proof-font-lock-defaults)
;      (setq proof-font-lock-defaults font-lock-keywords)
;      (setq font-lock-defaults '(proof-font-lock-defaults)))))
      ; (put major-mode 'font-lock-defaults (list flks)))))



;; was is proof-shell, never used.
(defun proof-shell-strip-eager-annotation-specials (string)
  "Strip special eager annotations from STRING, returning cleaned up string.
The input STRING should be annotated with expressions matching
proof-shell-eager-annotation-start and eager-annotation-end.
We only strip specials from the annotations."
  (let* ((mstart (progn
		   (string-match proof-shell-eager-annotation-start string)
		   (match-end 0)))
	 (mend	 (string-match proof-shell-eager-annotation-end string))
	 (msg	 (substring string mstart mend))
	 (strtan (substring string 0 mstart))
	 (endan	 (substring string mend)))
    (concat
     (proof-shell-strip-special-annotations strtan)
     msg
     (proof-shell-strip-special-annotations endan))))
     


;; 2. proof-find-and-forget-fn
;;
;; This calculates undo operations outwith a proof.  If we retract
;; before a "Goal" command, proof-kill-goal-command is sent, followed
;; by whatever is calculated by this function.
;;
;; Isabelle has no concept of a linear context, and you can happily
;; redeclare values in ML.  So forgetting back to the declaration of a
;; particular something makes no real sense.  
;; The function is given a trivial implementation in this case.
;;
;; Find LEGO or Coq's implementation of this function to see how to
;; write it for proof assistants that can do this.



;; FIXME: this is supposed to be a handy way of swapping
;; between goals and response buffer.  Never mind.
;(defun proof-bury-buffer-after (buf)
;  (if (and (string-match "XEmacs" emacs-version) ; XEmacs speciality
;	   (buffer-live-p buf))
;      (bury-buffer (current-buffer) buf)
;    (bury-buffer)))

;(defun proof-bury-buffer-after-goals ()
;  (interactive)
;  (proof-bury-buffer-after proof-goals-buffer))



;(defun proof-bury-buffer-after-response ()
;  (interactive)
;  (if proof-response-buffer
;      (with-current-buffer proof-response-buffer
;	(proof-bury-buffer-after proof-goals-buffer))))



;; This was added in proof-config.el.
;; 
;; Better strategy to be less zippy about adding hooks is this:
;;
;; 1. Only add a hook if it is needed in *generic* code
;; 2. Only add a hook if it seems likely to be needed for different
;;    provers, with different effects.
;;
;; This hook doesn't meet criteria!

(defcustom proof-xsym-toggle-hook '(proof-x-symbol-toggle-clean-buffers)
  "Hooks run when X-Symbol support is turned on or off."
  :type 'string
  :group 'proof-x-symbol)
