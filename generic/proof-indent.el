;; proof-indent.el Generic Indentation for Proof Assistants
;; Copyright (C) 1997, 1998 LFCS Edinburgh
;; Authors: Healfdene Goguen, Thomas Kleymann and Dilip Sequeira
;; Maintainer:  Proof General maintainer <proofgen@dcs.ed.ac.uk>
;;
;; $Id$
;;

(require 'proof)			; loader
(require 'proof-script)			; indent code is for script editing

;;; FIXME: for compilation might be  nice
;;;
;;; To nuke byte compile warnings
;;;
;(require 'proof-syntax)			; for proof-indent-commands-regexp.
;(require 'proof-script)			; for proof-goto-end-of-locked,
					; proof-locked-end


;; This is quite different from sml-mode, but borrows some bits of
;; code.  It's quite a lot less general, but works with nested
;; comments.

;; parse-to-point: If from is nil, parsing starts from either
;; proof-locked-end if we're in the proof-script-buffer or the
;; beginning of the buffer. Otherwise state must contain a valid
;; triple.

(defun proof-parse-to-point (&optional from state)
  (let ((cmt-level 0) (stack (list (list nil 0)))
	(end (point)) instring c forward-amount
	(cmt-end-regexp (regexp-quote proof-comment-end))
	(cmt-start-regexp (regexp-quote proof-comment-start)))
    (save-excursion
      (if (null from)
	  (goto-char (point-min))
	(goto-char from)
	(setq instring (car state)
	      cmt-level (nth 1 state)
	      stack (nth 2 state)))
      (while (< (point) end)
	(setq c (char-after (point)))
	(setq forward-amount 1)   ; may be subject to dynamic scoping!
	(cond 
	 ;; strings
	 ((and instring (proof-looking-at proof-string-end-regexp))
	  (setq forward-amount (length (match-string 0)))
	  (setq instring nil))
	 (instring)
	 ((proof-looking-at proof-string-start-regexp)
	  (setq forward-amount (length (match-string 0)))
	  (setq instring t))

	 ;; comments
	 ((proof-looking-at cmt-start-regexp)
	  (setq forward-amount (length (match-string 0)))
	  (incf cmt-level))
	 ((proof-looking-at cmt-end-regexp)
	  (setq forward-amount (length (match-string 0)))
	  (decf cmt-level))
	 ((> cmt-level 0))

	 ;; parentheses
	 ((proof-looking-at "\\s(")
	  (setq stack (cons (list c (point)) stack)))
	 ((proof-looking-at "\\s)")
	  (setq stack (cdr stack)))
	 
	 ;; basic indentation for commands
	 ((proof-looking-at proof-indent-commands-regexp)
	  (setq stack (cons (list proof-terminal-char (point)) stack)))
	 ((and (eq c proof-terminal-char)
	       (eq (car (car stack)) proof-terminal-char))
	  (setq stack (cdr stack)))

	 ;; prover specific plugin
	 (proof-parse-indent
	  (setq stack (funcall proof-parse-indent c stack))))

	(forward-char forward-amount))
      (list instring cmt-level stack))))

;;;###autoload      
(defun proof-indent-line ()
  "Indent current line of proof script, if indentation enabled."
  (interactive)
  (unless (not (proof-ass script-indent))
    (if (< (point) (proof-locked-end))
	(if (< (current-column) (current-indentation))
	    (skip-chars-forward "\t "))
      (save-excursion
	(beginning-of-line)
	(let* ((state (proof-parse-to-point))
	       (beg (point))
	       (indent (cond 
			((car state) 1)
			((> (nth 1 state) 0) 1)
			(t (funcall proof-stack-to-indent (nth 2 state))))))
	  (skip-chars-forward "\t ")
	  (if (not (eq (current-indentation) indent))
	      (progn (delete-region beg (point))
		     (indent-to indent)))))
      (skip-chars-forward "\t ")))

;;;###autoload      
(defun proof-indent-region (start end)
  (interactive "r")
  (if (< (point) (proof-locked-end))
      (error "can't indent locked region!"))
  (save-excursion
    (goto-char start)
    (beginning-of-line)
    (let* ((beg (point))
	   (state (proof-parse-to-point))
	   indent)
      ;; End of region changes with new indentation
      (while (< (point) end)
	(setq indent
	      (cond ((car state) 1)
		    ((> (nth 1 state) 0) 1)
		    (t (funcall proof-stack-to-indent (nth 2 state)))))
	(skip-chars-forward "\t ")
	(let ((diff (- (current-indentation) indent)))
	  (if (not (eq diff 0))
	      (progn
		(delete-region beg (point))
		(indent-to indent)
		(setq end (- end diff)))))
	(end-of-line)
	(if (< (point) (point-max)) (forward-char))
	(setq state (proof-parse-to-point beg state)
	      beg (point))))))

(provide 'proof-indent)
