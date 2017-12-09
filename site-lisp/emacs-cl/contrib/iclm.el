;;; iclm.el --- interaction mode for Emacs Lisp

;; Copyright (C) 1994 Free Software Foundation, Inc.

;; Author: David Smith <maa036@lancaster.ac.uk>
;; Maintainer: FSF
;; Created: 25 Feb 1994
;; Keywords: lisp

;; This file is part of GNU Emacs.

;; GNU Emacs is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; GNU Emacs is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;; Provides a nice interface to evaluating Emacs Lisp expressions.
;; Input is handled by the comint package, and output is passed
;; through the pretty-printer.

;; To install: copy this file to a directory in your load-path, and
;; add the following line to your .emacs file:
;;
;;   (autoload 'iclm "iclm" "Start an inferior Emacs Lisp session" t)
;;
;; For completion to work, the comint.el from Emacs 19.23 is
;; required.  If you do not have it, or if you are running Lemacs,
;; also add the following code to your .emacs:
;;
;;    (setq iclm-mode-hook
;; 	    '(lambda nil
;; 		 (define-key iclm-map "\t"
;; 		    '(lambda nil (interactive) (or (iclm-tab)
;;                                                 (lisp-complete-symbol))))))

;; To start: M-x iclm.  Type C-h m in the *iclm* buffer for more info.

;; The latest version is available by WWW from
;;      http://mathssun5.lancs.ac.uk:2080/~maa036/elisp/dir.html
;; or by anonymous FTP from
;;      /anonymous@wingra.stat.wisc.edu:pub/src/emacs-lisp/iclm.el.gz
;; or from the author: David M. Smith <maa036@lancaster.ac.uk>

;;; Code:

(require 'comint)
(require 'pp)

;;; User variables

(defgroup iclm nil
  "Interaction mode for Emacs Lisp."
  :group 'lisp)


(defcustom iclm-noisy t
  "*If non-nil, ICLM will beep on error."
  :type 'boolean
  :group 'iclm)

(defvar iclm-prompt (FORMAT nil "~a> " (PACKAGE-NAME *PACKAGE*))
  "Prompt used in ICLM.")

(defcustom iclm-dynamic-return t
  "*Controls whether \\<iclm-map>\\[iclm-return] has intelligent behaviour in ICLM.
If non-nil, \\[iclm-return] evaluates input for complete sexps, or inserts a newline
and indents for incomplete sexps.  If nil, always inserts newlines."
  :type 'boolean
  :group 'iclm)

(defcustom iclm-dynamic-multiline-inputs t
  "*Force multiline inputs to start from column zero?
If non-nil, after entering the first line of an incomplete sexp, a newline
will be inserted after the prompt, moving the input to the next line.
This gives more frame width for large indented sexps, and allows functions
such as `edebug-defun' to work with such inputs."
  :type 'boolean
  :group 'iclm)

(defcustom iclm-mode-hook nil
  "*Hooks to be run when ICLM (`inferior-emacs-lisp-mode') is started."
  :type 'hook
  :group 'iclm)

;;; System variables

(defvar iclm-working-buffer nil
  "Buffer in which ICLM sexps will be evaluated.
This variable is buffer-local.")

(defvar iclm-header
  "*** Welcome to Common Lisp ***.\n"
  "Message to display when ICLM is started.")

(defvar iclm-map nil)
(unless iclm-map
  (if (string-match "Lucid" emacs-version)
      ;; Lemacs
      (progn
	(setq iclm-map (make-sparse-keymap))
	(set-keymap-parent iclm-map comint-mode-map))
    ;; FSF
    (setq iclm-map (cons 'keymap comint-mode-map)))
  (define-key iclm-map "\t" 'comint-dynamic-complete)
  (define-key iclm-map "\C-m" 'iclm-return)
  (define-key iclm-map "\C-j" 'iclm-send-input)
  (define-key iclm-map "\e\C-x" 'eval-defun)         ; for consistency with
;; TODO
  (define-key iclm-map "\e\t" 'lisp-complete-symbol) ; lisp-interaction-mode
  ;; These bindings are from `lisp-mode-shared-map' -- can you inherit
  ;; from more than one keymap??
  (define-key iclm-map "\e\C-q" 'indent-sexp)
  (define-key iclm-map "\177" 'backward-delete-char-untabify)
  ;; Some convenience bindings for setting the working buffer
  (define-key iclm-map "\C-c\C-b" 'iclm-change-working-buffer)
  (define-key iclm-map "\C-c\C-f" 'iclm-display-working-buffer)
  (define-key iclm-map "\C-c\C-v" 'iclm-print-working-buffer))

(defvar iclm-font-lock-keywords
  (list
   (cons (concat "^" (regexp-quote iclm-prompt)) 'font-lock-keyword-face)
   '("\\(^\\*\\*\\*[^*]+\\*\\*\\*\\)\\(.*$\\)"
     (1 font-lock-comment-face)
     (2 font-lock-constant-face)))
  "Additional expressions to highlight in iclm buffers.")

;;; Completion stuff

(defun iclm-tab nil
  "Possibly indent the current line as lisp code."
  (interactive)
  (when (or (eq (preceding-char) ?\n)
	    (eq (char-syntax (preceding-char)) ? ))
    (iclm-indent-line)
    t))

;; TODO
(defun iclm-complete-symbol nil
  "Complete the lisp symbol before point."
  ;; A wrapper for lisp-complete symbol that returns non-nil if
  ;; completion has occurred
  (let* ((btick (buffer-modified-tick))
	 (cbuffer (get-buffer "*Completions*"))
	 (ctick (and cbuffer (buffer-modified-tick cbuffer))))
    (lisp-complete-symbol)
     ;; completion has occurred if:
    (or
     ;; the buffer has been modified
     (not (= btick (buffer-modified-tick)))
     ;; a completions buffer has been modified or created
     (if cbuffer
	 (not (= ctick (buffer-modified-tick cbuffer)))
       (get-buffer "*Completions*")))))

(defun iclm-complete-filename nil
  "Dynamically complete filename before point, if in a string."
  (if (nth 3 (parse-partial-sexp comint-last-input-start (point)))
      (comint-dynamic-complete-filename)))

(defun iclm-indent-line nil
  "Indent the current line as Lisp code if it is not a prompt line."
  (when (save-excursion (comint-bol) (bolp))
    (lisp-indent-line)))

;;; Working buffer manipulation

(defun iclm-print-working-buffer nil
  "Print the current ICLM working buffer's name in the echo area."
  (interactive)
  (message "The current working buffer is: %s" (buffer-name iclm-working-buffer)))

(defun iclm-display-working-buffer nil
  "Display the current ICLM working buffer.
Don't forget that selecting that buffer will change its value of `point'
to its value of `window-point'!"
  (interactive)
  (display-buffer iclm-working-buffer)
  (iclm-print-working-buffer))

(defun iclm-change-working-buffer (buf)
  "Change the current ICLM working buffer to BUF.
This is the buffer in which all sexps entered at the ICLM prompt are
evaluated.  You can achieve the same effect with a call to
`set-buffer' at the ICLM prompt."
  (interactive "bSet working buffer to: ")
  (setq iclm-working-buffer (or (get-buffer buf) (error "No such buffer")))
  (iclm-print-working-buffer))

;;; Other bindings

(defun iclm-return nil
  "Newline and indent, or evaluate the sexp before the prompt.
Complete sexps are evaluated; for incomplete sexps inserts a newline
and indents.  If however `iclm-dynamic-return' is nil, this always
simply inserts a newline."
  (interactive)
  (if iclm-dynamic-return
      (let ((state
	     (save-excursion
	       (end-of-line)
	       (parse-partial-sexp (iclm-pm)
				   (point)))))
	(if (and (< (car state) 1) (not (nth 3 state)))
	    (iclm-send-input)
	  (if (and iclm-dynamic-multiline-inputs
		   (save-excursion
		     (beginning-of-line)
		     (looking-at comint-prompt-regexp)))
	      (save-excursion
		(goto-char (iclm-pm))
		(newline 1)))
	  (newline-and-indent)))
    (newline)))

(defvar iclm-input)

(defun iclm-input-sender (proc input)
  ;; Just sets the variable iclm-input, which is in the scope of
  ;; `iclm-send-input's call.
  (setq iclm-input input))

(defun iclm-send-input nil
  "Evaluate the Emacs Lisp expression after the prompt."
  (interactive)
  (let ((buf (current-buffer))
	iclm-input)			; set by iclm-input-sender
    (comint-send-input)			; update history, markers etc.
    (iclm-eval-input iclm-input)))

;;; Utility functions

(defun iclm-is-whitespace (string)
  "Return non-nil if STRING is all whitespace."
  (or (string= string "") (string-match "\\`[ \t\n]+\\'" string)))

(defun iclm-format-errors (errlist)
  (let ((result ""))
    (while errlist
      (setq result (concat result (prin1-to-string (car errlist)) ", "))
      (setq errlist (cdr errlist)))
    (substring result 0 -2)))


(defun iclm-format-error (err)
  ;; Return a string form of the error ERR.
  (format "%s%s"
	  (or (get (car err) 'error-message) "Peculiar error")
	  (if (cdr err)
	      (format ": %s" (iclm-format-errors (cdr err)))
	    "")))

;;; Evaluation

(defun iclm-eval-input (iclm-string)
  "Evaluate the Lisp expression ICLM-STRING, and pretty-print the result."
  ;; This is the function that actually `sends' the input to the
  ;; `inferior Lisp process'. All comint-send-input does is works out
  ;; what that input is.  What this function does is evaluates that
  ;; input and produces `output' which gets inserted into the buffer,
  ;; along with a new prompt.  A better way of doing this might have
  ;; been to actually send the output to the `cat' process, and write
  ;; this as in output filter that converted sexps in the output
  ;; stream to their evaluated value.  But that would have involved
  ;; more process coordination than I was happy to deal with.
  ;;
  ;; NOTE: all temporary variables in this function will be in scope
  ;; during the eval, and so need to have non-clashing names.
  (let (iclm-form			; form to evaluate
	iclm-pos			; End posn of parse in string
	iclm-result			; Result, or error message
	iclm-error-type			; string, nil if no error
	(iclm-output	"")		; result to display
	(iclm-wbuf iclm-working-buffer)	; current buffer after evaluation
	(iclm-pmark (iclm-pm)))
    (if (not (iclm-is-whitespace iclm-string))
	(progn
	  (condition-case err
	      (let ((rout (READ-FROM-STRING iclm-string)))
		;; looked different
		(setq iclm-form rout)
		(setq iclm-pos (length iclm-string)))
	    (error (setq iclm-result (iclm-format-error err))
		   (setq iclm-error-type "Read error")))
	  (unless iclm-error-type
	    ;; Make sure working buffer has not been killed
	    (if (not (buffer-name iclm-working-buffer))
		(setq iclm-result "Working buffer has been killed"
		      iclm-error-type "ICLM Error"
		      iclm-wbuf (current-buffer))
	      (if (iclm-is-whitespace (substring iclm-string iclm-pos))
		  (save-excursion
		    (set-buffer iclm-working-buffer)
		    (condition-case err
			(let ((iclm-obuf (current-buffer)))
			  (setq iclm-result (emacs-cl-eval-interactively iclm-form))
			  (setq iclm-wbuf (current-buffer))
			  ;; The eval may have changed current-buffer;
			  ;; need to set it back here to avoid a bug
			  ;; in let.  Don't want to use save-excursion
			  ;; because we want to allow changes in point.
			  (set-buffer iclm-obuf))
		      (error (setq iclm-result (iclm-format-error err))
			     (setq iclm-error-type "Eval error"))
		      (quit (setq iclm-result "Quit during evaluation")
			    (setq iclm-error-type "Eval error"))))
		  (setq iclm-error-type "ICLM error")
		  (setq iclm-result "More than one sexp in input"))))

	  ;; If the eval changed the current buffer, mention it here
	  (if (eq iclm-wbuf iclm-working-buffer) nil
	    (message "current buffer is now: %s" iclm-wbuf)
	    (setq iclm-working-buffer iclm-wbuf))

	  (goto-char iclm-pmark)
	  (if (not iclm-error-type)
	      (condition-case err
		  ;; Self-referential objects cause loops in the printer, so
		  ;; trap quits here. May as well do errors, too
		  (dolist (val iclm-result)
		    (setq iclm-output (concat iclm-output (FORMAT nil "~s~%" val))))
		(error (setq iclm-error-type "ICLM Error")
		       (setq iclm-result  "Error during pretty-printing (bug in pp)"))
		(quit  (setq iclm-error-type "ICLM Error")
		       (setq iclm-result "Quit during pretty-printing"))))
	  (when iclm-error-type
	    (if iclm-noisy (ding))
	    (setq iclm-output (concat iclm-output "*** " iclm-error-type " ***  "))
	    (setq iclm-output (concat iclm-output iclm-result)))
	  (setq iclm-output (concat iclm-output "\n"))))
    (setq iclm-prompt (FORMAT nil "~a> " (PACKAGE-NAME *PACKAGE*)))
    (setq iclm-output (concat iclm-output iclm-prompt))
    ;; MG: emacs-cl might have called the debugger
    (set-marker (process-mark (iclm-process)) (1+ (buffer-size)))
    (end-of-buffer)
    (comint-output-filter (iclm-process) iclm-output)))

;;; Process and marker utilities

(defun iclm-process nil
  ;; Return the current buffer's process.
  (get-buffer-process (current-buffer)))

(defun iclm-pm nil
  ;; Return the process mark of the current buffer.
  (process-mark (get-buffer-process (current-buffer))))

(defun iclm-set-pm (pos)
  ;; Set the process mark in the current buffer to POS.
  (set-marker (process-mark (get-buffer-process (current-buffer))) pos))

;;; Major mode

(put 'inferior-emacs-lisp-mode 'mode-class 'special)

(defun inferior-emacs-lisp-mode nil
  "Major mode for interactively evaluating Emacs Lisp expressions.
Uses the interface provided by `comint-mode' (which see).

* \\<iclm-map>\\[iclm-send-input] evaluates the sexp following the prompt. There must be at most
  one top-level sexp per prompt.

* \\[iclm-return] inserts a newline and indents, or evaluates a
  complete expression (but see variable `iclm-dynamic-return').
  Inputs longer than one line are moved to the line following the
  prompt (but see variable `iclm-dynamic-multiline-inputs').

* \\[comint-dynamic-complete] completes Lisp symbols (or filenames, within strings),
  or indents the line if there is nothing to complete.

During evaluations, the values of the variables `*', `**', and `***'
are the results of the previous, second previous and third previous
evaluations respectively.

The current working buffer may be changed (with a call to
`set-buffer', or with \\[iclm-change-working-buffer]), and its value
is preserved between successive evaluations.  In this way, expressions
may be evaluated in a different buffer than the *iclm* buffer.
Display the name of the working buffer with \\[iclm-print-working-buffer],
or the buffer itself with \\[iclm-display-working-buffer].

Expressions evaluated by ICLM are not subject to `debug-on-quit' or
`debug-on-error'.

The behaviour of ICLM may be customised with the following variables:
* To stop beeping on error, set `iclm-noisy' to nil
* If you don't like the prompt, you can change it by setting `iclm-prompt'.
* Set `iclm-dynamic-return' to nil for bindings like `lisp-interaction-mode'
* Entry to this mode runs `comint-mode-hook' and `iclm-mode-hook'
 (in that order).

Customised bindings may be defined in `iclm-map', which currently contains:
\\{iclm-map}"
  (interactive)
  (comint-mode)
  (setq comint-prompt-regexp (concat "^" (regexp-quote iclm-prompt)))
  (make-local-variable 'paragraph-start)
  (setq paragraph-start comint-prompt-regexp)
  (setq comint-input-sender 'iclm-input-sender)
  (setq comint-process-echoes nil)
  (setq comint-dynamic-complete-functions
	'(iclm-tab comint-replace-by-expanded-history iclm-complete-filename iclm-complete-symbol))
  (setq comint-get-old-input 'iclm-get-old-input)
  (make-local-variable 'comint-completion-addsuffix)
  (setq comint-completion-addsuffix
	(cons (char-to-string directory-sep-char) ""))

  (setq major-mode 'inferior-emacs-lisp-mode)
  (setq mode-name "ICLM")
  (use-local-map iclm-map)
  (set-syntax-table emacs-lisp-mode-syntax-table)

  (make-local-variable 'indent-line-function)
  (make-local-variable 'iclm-working-buffer)
  (setq iclm-working-buffer (current-buffer))
  (setq indent-line-function 'iclm-indent-line)
  (make-local-variable 'fill-paragraph-function)
  (setq fill-paragraph-function 'lisp-fill-paragraph)

  ;; font-lock support
  (make-local-variable 'font-lock-defaults)
  (setq font-lock-defaults
	'(iclm-font-lock-keywords nil nil ((?: . "w") (?- . "w") (?* . "w"))))

  ;; A dummy process to keep comint happy. It will never get any input
  (if (comint-check-proc (current-buffer)) nil
    (start-process "iclm" (current-buffer) "cat")
    (process-kill-without-query (iclm-process))
    (goto-char (point-max))
    ;; Add a silly header
    (insert iclm-header)
    (iclm-set-pm (point-max))
    (comint-output-filter (iclm-process) iclm-prompt)
    (set-marker comint-last-input-start (iclm-pm))
    (set-process-filter (get-buffer-process (current-buffer)) 'comint-output-filter))
  (run-hooks 'iclm-mode-hook))

(defun iclm-get-old-input nil
  ;; Return the previous input surrounding point
  (save-excursion
    (beginning-of-line)
    (if (looking-at comint-prompt-regexp) nil
      (re-search-backward comint-prompt-regexp))
    (comint-skip-prompt)
    (buffer-substring (point) (progn (forward-sexp 1) (point)))))

;;; User command

;;;###autoload (add-hook 'same-window-buffer-names "*iclm*")

;;;###autoload
(defun iclm nil
  "Interactively evaluate Emacs Lisp expressions.
Switches to the buffer `*iclm*', or creates it if it does not exist."
  (interactive)
  (if (comint-check-proc "*iclm*")
      nil
    (save-excursion
      (set-buffer (get-buffer-create "*iclm*"))
      (inferior-emacs-lisp-mode)))
  (pop-to-buffer "*iclm*"))

(provide 'iclm)

;;; iclm.el ends here
