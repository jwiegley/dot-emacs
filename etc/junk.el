;;; junk.el
;;;
;;;  $Id$
;;;
;;; Bits and pieces of code 
;;; removed from main PG (or never added).
;;; Left here in case they're useful later.
;;;

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



;; dump str to buffer ug for testing.
(defun ugit (str)
  (save-excursion
    (set-buffer (get-buffer-create "ug"))
    (goto-char (point-max))
    (insert str)
    (newline)
    (newline)))
