;; proof-indent.el Generic Indentation for Proof Assistants
;; Copyright (C) 1997, 1998 LFCS Edinburgh
;; Authors: Healfdene Goguen, Thomas Kleymann and Dilip Sequeira
;; Maintainer: LEGO Team <lego@dcs.ed.ac.uk>

(require 'cl)
(require 'proof-fontlock)
;; proof-fontlock ought to be renamed to proof-syntax

(defvar proof-stack-to-indent nil
  "Prover-specific code for indentation.")

(defvar proof-parse-indent nil
  "Proof-assistant specific function for parsing characters for
  indentation which is invoked in `proof-parse-to-point.'. Must be a
  function taking two arguments, a character (the current character)
  and a stack reflecting indentation, and must return a stack. The
  stack is a list of the form (c . p) where `c' is a character
  representing the type of indentation and `p' records the column for
  indentation. The generic `proof-parse-to-point.' function supports
  parentheses and commands. It represents these with the characters
  `?\(', `?\[' and `proof-terminal-char'. ")

;; This is quite different from sml-mode, but borrows some bits of
;; code.  It's quite a lot less general, but works with nested
;; comments.

;; parse-to-point: If from is nil, parsing starts from either
;; proof-locked-end if we're in the proof-script-buffer or the
;; beginning of the buffer. Otherwise state must contain a valid
;; triple.

(defun proof-parse-to-point (&optional from state)
  (let ((comment-level 0) (stack (list (list nil 0)))
	(end (point)) instring c)
    (save-excursion
      (if (null from)
	  (if (eq proof-script-buffer (current-buffer))
	      (proof-goto-end-of-locked)
	    (goto-char 1))
	(goto-char from)
	(setq instring (car state)
	      comment-level (nth 1 state)
	      stack (nth 2 state)))
      (while (< (point) end)
	(setq c (char-after (point)))
	(cond 
	 (instring 
	  (if (eq c ?\") (setq instring nil)))
	 (t (cond
	     ((eq c ?\()
	      (cond
	       ((looking-at "(\\*")
		(progn
		  (incf comment-level)
		  (forward-char)))
	       ((eq comment-level 0)
		(setq stack (cons (list ?\( (point)) stack)))))
	     ((and (eq c ?\*) (looking-at "\\*)"))
	      (decf comment-level)
	      (forward-char))
	     ((> comment-level 0))
	     ((eq c ?\") (setq instring t))
	     ((eq c ?\[)
	      (setq stack (cons (list ?\[ (point)) stack)))
	     ((or (eq c ?\)) (eq c ?\]))
	      (setq stack (cdr stack)))
	     ((looking-at proof-commands-regexp)
	      (setq stack (cons (list proof-terminal-char (point)) stack)))
	     ((and (eq c proof-terminal-char)
		   (eq (car (car stack)) proof-terminal-char)) (cdr stack))
	     (proof-parse-indent
	      (setq stack (funcall proof-parse-indent c stack))))))
	(forward-char))
    (list instring comment-level stack))))
      
(defun proof-indent-line ()
  (interactive)
  (if (and (eq proof-script-buffer (current-buffer))
	   (< (point) (proof-locked-end)))
      (if (< (current-column) (current-indentation))
	  (skip-chars-forward "\t "))
    (save-excursion
      (beginning-of-line)
      (let* ((state (proof-parse-to-point))
	     (beg (point))
	     (indent (cond ((car state) 1)
			   ((> (nth 1 state) 0) 1)
			   (t (funcall proof-stack-to-indent (nth 2 state))))))
	(skip-chars-forward "\t ")
	(if (not (eq (current-indentation) indent))
	    (progn (delete-region beg (point))
		   (indent-to indent)))))
    (skip-chars-forward "\t ")))

(defun proof-indent-region (start end)
  (interactive "r")
  (if (and (eq proof-script-buffer (current-buffer))
	   (< (point) (proof-locked-end)))
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