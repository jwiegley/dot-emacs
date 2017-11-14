;;; macrostep.el --- interactive macro stepper for Emacs Lisp

;; Copyright (C) 2012 Jonathan Oddie <j.j.oddie@gmail.com>

;; Author:     Jonathan Oddie <j.j.oddie@gmail.com>
;; Maintainer: Jonathan Oddie <j.j.oddie@gmail.com>
;; Created:    16 January 2012
;; Updated:    02 May 2012
;; Version:    0.2
;; Keywords:   lisp, languages, macro, debugging

;; This file is NOT part of GNU Emacs.

;; This program is free software: you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation, either version 3 of the
;; License, or (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see `http://www.gnu.org/licenses/'.

;;; Commentary:
 
;; `macrostep-mode' is a minor mode for interactively stepping through
;; the expansion of macros in Emacs Lisp source code. It lets you see
;; exactly what happens at each step of the expansion process by
;; pretty-printing the expanded forms inline in the source buffer,
;; which is read-only while macro expansions are visible. You can
;; expand and collapse macro forms one step at a time, and evaluate
;; or instrument them for debugging with Edebug as normal (but see
;; "Bugs and known limitations", below). Single-stepping through the
;; expansion is useful for debugging macros that expand into another
;; macro form, especially one like `lexical-let' that does significant
;; rewriting. These can be difficult to debug with Emacs' built-in
;; `macroexpand' because `macroexpand' continues expansion until the
;; top-level form is no longer a macro call.
;;
;; macrostep-mode adds some simple additional fontification to
;; macro-expanded text. The heads of macro sub-forms are fontified
;; using `macrostep-macro-face'. Uninterned symbols (gensyms) are
;; fontified based on which step in the expansion created them, to
;; distinguish them from normal symbols and from other gensyms with
;; the same print name. Use `customize-group' with the "macrostep"
;; group to customize these faces.
;;
;; The standard macrostep-mode keybindings are the following:
;;
;;     e, =, RET     expand the macro form following point one step
;;     c, u, DEL     collapse the form following point
;;     q, C-c C-c    collapse all expanded forms and exit macrostep-mode
;;     n, TAB        jump to the next macro form in the expansion
;;     p, M-TAB      jump to the previous macro form in the expansion
;;
;; It's not very useful to enable and disable macrostep-mode
;; directly. Instead, bind `macrostep-expand' to a key in
;; `emacs-lisp-mode-map', for example C-c e:
;;
;; (add-hook
;;  'emacs-lisp-mode-hook
;;  (lambda ()
;;    (define-key emacs-lisp-mode-map (kbd "C-c e") 'macrostep-expand)))
;;
;; You can then enter macrostep-mode and expand a macro form
;; completely by typing C-c e e e ...  as many times as necessary.
;;
;; Exit macrostep-mode either with 'q', C-c C-c, or by successively
;; typing 'c' to collapse all expanded forms back to their original
;; text.
;;
;; Note that by moving point around in the macro expansion, you can
;; macro-expand sub-forms before fully expanding their enclosing
;; form. For example, with `cl' loaded, try expanding
;;
;;   (dolist (l list-of-lists)
;;     (incf (car l)))
;;
;; which produces the following expansion:
;;
;;   (block nil
;;     (let
;;         ((--cl-dolist-temp-- list-of-lists)
;;          l)
;;       (while --cl-dolist-temp--
;;         (setq l
;;               (car --cl-dolist-temp--))
;;         (incf
;;          (car l))
;;         (setq --cl-dolist-temp--
;;               (cdr --cl-dolist-temp--)))
;;       nil))
;;
;; where `block' and `incf' are both macros.
;;
;; You can then either continue expanding the `block' form, which
;; corresponds to the real order of macro expansion, or type `n' to
;; move to the unexpanded `incf' and expand it to a `callf' form and
;; finally to a `let*' form.  However, note that the expansion of a
;; form always works on the original, unexpanded text of its
;; sub-forms.  This might look confusing: if you fully expand the
;; `incf' first in the above example, then expand the `block', the
;; result will again have an unexpanded `incf' form in it.  But it
;; corresponds to the way real macro expansion works: the outer form
;; is expanded into a non-macro before any inner forms are
;; evaluated.
;;
;; Why allow expanding sub-forms out of order like this at all? The
;; main reason is for debugging macros which expand into another
;; macro, like `lexical-let', that programmatically expands its
;; contents in order to rewrite them.  In this case, expanding the
;; sub-forms first allows you to see what `lexical-let' would
;; compute via `cl-macroexpand-all'.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Bugs and known limitations:
;;
;; You can evaluate and edebug macro-expanded forms and step through
;; the macro-expanded version, but the form that `eval-defun' and
;; friends read from the buffer won't have the uninterned symbols of
;; the real macro expansion.  This will probably work OK with CL-style
;; (gensym)s, but may cause problems with (make-symbol ...) symbols if
;; they have the same print name as another symbol in the expansion.
;;
;; The macro stepper doesn't bother trying to determine whether or not
;; a sub-form is in an evaluated position before highlighting it as a
;; macro. It does exclude `lambda' from treatment as a macro, since
;; that leads to an endless series of expansions: (function (function
;; ... )). It would be better to recognise `function', `quote' and
;; other special forms using their edebug-form-spec property.
;;
;; Please send other bug reports and feature requests to the author,
;; j.j.oddie@gmail.com

;;; Code:

;; We use `pp-buffer' to pretty-print macro expansions
(require 'pp)


;;; Constants and dynamically bound variables
(defvar macrostep-overlays nil
  "List of all macro stepper overlays in the current buffer.")
(make-variable-buffer-local 'macrostep-overlays)

(defvar macrostep-gensym-depth nil
  "Number of macro expansion levels that have introduced gensyms so far.")
(make-variable-buffer-local 'macrostep-gensym-depth)

(defvar macrostep-gensyms-this-level nil
  "t if gensyms have been encountered during current level of macro expansion.")
(make-variable-buffer-local 'macrostep-gensyms-this-level)


;;; Faces
(defgroup macrostep nil
  "Interactive macro stepper for Emacs Lisp."
  :version 0.1
  :group 'lisp
  :link '(emacs-commentary-link :tag "commentary" "macrostep.el")
  :link '(emacs-library-link :tag "lisp file" "macrostep.el")
  :link '(url-link :tag "web page" "https://github.com/joddie/macrostep"))

(defface macrostep-gensym-1
  '((((min-colors 16581375)) :background "#b0c4de")
    (((min-colors 8)) :background "cyan")
    (t :inverse-video t))
  "Face for gensyms created in the first level of macro expansion."
  :group 'macrostep)

(defface macrostep-gensym-2
  '((((min-colors 16581375)) :background "#8fbc8f")
    (((min-colors 8)) :background "#00cd00")
    (t :inverse-video t))
  "Face for gensyms created in the second level of macro expansion."
  :group 'macrostep)

(defface macrostep-gensym-3
  '((((min-colors 16581375)) :background "#daa520")
    (((min-colors 8)) :background "yellow")
    (t :inverse-video t))
  "Face for gensyms created in the third level of macro expansion."
  :group 'macrostep)

(defface macrostep-gensym-4
  '((((min-colors 16581375)) :background "#cd5c5c")
    (((min-colors 8)) :background "red")
    (t :inverse-video t))
  "Face for gensyms created in the fourth level of macro expansion."
  :group 'macrostep)

(defface macrostep-gensym-5
  '((((min-colors 16581375)) :background "#da70d6")
    (((min-colors 8)) :background "magenta")
    (t :inverse-video t))
  "Face for gensyms created in the fifth level of macro expansion."
  :group 'macrostep)

(defface macrostep-macro-face
  '((t :underline t))
  "Face for macros in macro-expanded code."
  :group 'macrostep)

;; Need the following for making the ring of faces
(defun macrostep-make-ring (&rest items)
  "Make a ring containing all of ITEMS with no empty slots."
  (let ((ring (make-ring (length items))))
    (mapc (lambda (item) (ring-insert ring item)) (reverse items))
    ring))

(defvar macrostep-gensym-faces
  (macrostep-make-ring
   'macrostep-gensym-1 'macrostep-gensym-2 'macrostep-gensym-3
   'macrostep-gensym-4 'macrostep-gensym-5)
  "Ring of all macrostepper faces for fontifying gensyms.")


;;; Define keymap and minor mode
(defvar macrostep-keymap
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "RET") 'macrostep-expand)
    (define-key map "=" 'macrostep-expand)
    (define-key map "e" 'macrostep-expand)

    (define-key map (kbd "DEL") 'macrostep-collapse)
    (define-key map "u" 'macrostep-collapse)
    (define-key map "c" 'macrostep-collapse)

    (define-key map (kbd "TAB") 'macrostep-next-macro)
    (define-key map "n" 'macrostep-next-macro)
    (define-key map (kbd "M-TAB") 'macrostep-prev-macro)
    (define-key map "p" 'macrostep-prev-macro)

    (define-key map "q" 'macrostep-collapse-all)
    (define-key map (kbd "C-c C-c") 'macrostep-collapse-all)
    map)
  "Keymap for `macrostep-mode'.")

;;;###autoload
(define-minor-mode macrostep-mode
  "Minor mode for inline expansion of macros in Emacs Lisp source buffers.

\\<macrostep-keymap>Progressively expand macro forms with \\[macrostep-expand], collapse them with \\[macrostep-collapse],
and move back and forth with \\[macrostep-next-macro] and \\[macrostep-prev-macro].
Use \\[macrostep-collapse-all] or collapse all visible expansions to
quit and return to normal editing.

\\{macrostep-keymap}"
  nil " Macro-Stepper"
  :keymap macrostep-keymap
  :group macrostep
  (setq buffer-read-only macrostep-mode)
  (if macrostep-mode
      (message
       (substitute-command-keys
        "\\<macrostep-keymap>Entering macro stepper mode. Use \\[macrostep-expand] to expand, \\[macrostep-collapse] to collapse, \\[macrostep-collapse-all] to exit."))

    ;; Exiting mode: collapse any remaining overlays
    (when macrostep-overlays (macrostep-collapse-all))))


;;; Interactive functions
;;;###autoload
(defun macrostep-expand ()
  "Expand the Elisp macro form following point by one step.

Enters `macrostep-mode' if it is not already active, making the
buffer temporarily read-only. If macrostep-mode is active and the
form following point is not a macro form, search forward in the
buffer and expand the next macro form found, if any."
  (interactive)
  (let ((sexp (macrostep-sexp-at-point)))
    (when (not (macrostep-macro-form-p sexp))
      (condition-case nil
	  (progn
	    (macrostep-next-macro)
	    (setq sexp (macrostep-sexp-at-point)))
	(error
	 (if (consp sexp)
	     (error "(%s ...) is not a macro form" (car sexp))
	   (error "Text at point is not a macro form.")))))
    (unless macrostep-mode (macrostep-mode t))
    (let* ((buffer-read-only nil)
	   (expansion (macrostep-expand-1 sexp))
	   (existing-ol (macrostep-overlay-at-point))
	   (macrostep-gensym-depth macrostep-gensym-depth)
	   (macrostep-gensyms-this-level nil)
	   text priority)
      (if existing-ol			; expanding an expansion
	  (setq text sexp
		priority (1+ (overlay-get existing-ol 'priority))

		macrostep-gensym-depth
		(overlay-get existing-ol 'macrostep-gensym-depth))
	;; expanding buffer text
	(setq text (buffer-substring (point) (scan-sexps (point) 1))
	      priority 1
	      macrostep-gensym-depth -1))

      (atomic-change-group
	(macrostep-replace-sexp-at-point expansion)
	(let ((new-ol
	       (make-overlay (point)
			     (scan-sexps (point) 1))))
	  (overlay-put new-ol 'evaporate t)
	  (overlay-put new-ol 'priority priority)
	  (overlay-put new-ol 'macrostep-original-text text)
	  (overlay-put new-ol 'macrostep-gensym-depth macrostep-gensym-depth)
	  (push new-ol macrostep-overlays))))))

(defun macrostep-collapse ()
  "Collapse the innermost macro expansion near point to its source text.

If no more macro expansions are visible after this, exit
`macrostep-mode'."
  (interactive)
  (let ((overlay (macrostep-overlay-at-point)))
    (when (not overlay) (error "No macro expansion at point"))
    (let ((buffer-read-only nil))
      (atomic-change-group
	(macrostep-collapse-overlay overlay))))
  (if (not macrostep-overlays)
      (macrostep-mode 0)))

(defun macrostep-collapse-all ()
  "Collapse all visible macro expansions and exit `macrostep-mode'."
  (interactive)
  (let ((buffer-read-only nil))
    (dolist (overlay macrostep-overlays)
      (let ((outermost (= (overlay-get overlay 'priority) 1)))
        ;; We only need restore the original text for the outermost
        ;; overlays
        (macrostep-collapse-overlay overlay (not outermost)))))
  (setq macrostep-overlays nil)
  (macrostep-mode 0))

(defun macrostep-next-macro ()
  "Move point forward to the next macro form in macro-expanded text."
  (interactive)
  (let* ((start 
	 (if (get-text-property (point) 'macrostep-expanded-text)
	     (1+ (point))
	   (point)))
	 (next (next-single-property-change start 'macrostep-expanded-text)))
    (if next
	(goto-char next)
      (error "No more macro forms found"))))

(defun macrostep-prev-macro ()
  "Move point back to the previous macro form in macro-expanded text."
  (interactive)
  (let (prev)
    (save-excursion
      (while
	  (progn
	    (setq prev
		  (previous-single-property-change (point) 'macrostep-expanded-text))
	    (if (or (not prev)
		    (get-text-property (1- prev) 'macrostep-expanded-text))
		nil
	      (prog1 t (goto-char prev))))))
    (if prev
	(goto-char (1- prev))
      (error "No previous macro form found"))))



;;; Utility functions
(defun macrostep-macro-form-p (form)
  "Return t if FORM is a sexp that would be evaluated via macro expansion."
  (if (or (not (consp form))
	  (eq (car form) 'lambda)) 	; hack
      nil
    (condition-case err
	(let ((macro (symbol-function (car form))))
	  (and (consp macro)
	       (eq (car macro) 'macro)))
      (error nil))))

(defun macrostep-macro-definition (form)
  "Return, as a function, the macro definition to apply in expanding FORM."
  (cdr (symbol-function (car form))))
	   
(defun macrostep-expand-1 (form)
  "Return result of macro-expanding the top level of FORM by exactly one step.

Unlike `macroexpand', this function does not continue macro
expansion until a non-macro-call results."
  (if (not (macrostep-macro-form-p form)) form
    (apply (macrostep-macro-definition form) (cdr form))))

(defun macrostep-overlay-at-point ()
  "Return the innermost macro stepper overlay at point."
  (let ((result
	 (get-char-property-and-overlay (point) 'macrostep-original-text)))
    (cdr result)))

(defun macrostep-sexp-at-point ()
  "Return the sexp near point for purposes of macro-stepper expansion.

If the sexp near point is part of a macro expansion, returns the
saved text of the macro expansion, and does not read from the
buffer. This preserves uninterned symbols in the macro expansion,
so that they can be colored consistently. See also
`macrostep-print-sexp'.

Also moves point to the beginning of the returned s-expression."
  (if (not (looking-at "("))
      (backward-up-list 1))
  (or (get-text-property (point) 'macrostep-expanded-text)
      (progn
	;; use scan-sexps for the side-effect of producing an error
	;; message for unbalanced parens, etc.
	(scan-sexps (point) 1)
	(sexp-at-point))))


(defun macrostep-collapse-overlay (overlay &optional no-restore-p)
  "Collapse a macro-expansion overlay and restore the unexpanded source text.

As a minor optimization, does not restore the original source
text if NO-RESTORE-P is non-nil. This is safe to do when
collapsing all the sub-expansions of an outer overlay, since the
outer overlay will restore the original source itself.

Also removes the overlay from `macrostep-overlays'."
  (when (and (overlay-start overlay)
	     (eq (overlay-buffer overlay) (current-buffer)))
      ;; If we're cleaning up we don't need to bother restoring text
      ;; or checking for inner overlays to delete
      (unless no-restore-p
	(macrostep-collapse-overlays-in
	 (overlay-start overlay) (overlay-end overlay))
	(let ((text (overlay-get overlay 'macrostep-original-text)))
	  (goto-char (overlay-start overlay))
	  (macrostep-replace-sexp-at-point text (stringp text))))
      ;; Remove overlay from the list and delete it
      (setq macrostep-overlays
	    (delq overlay macrostep-overlays))
      (delete-overlay overlay)))

(defun macrostep-collapse-overlays-in (start end)
  "Collapse all macrostepper overlays that are strictly between START and END.

Will not collapse overlays that begin at START and end at END."
  (dolist (ol (overlays-in start end))
    (if (and (> (overlay-start ol) start)
	     (< (overlay-end ol) end)
	     (overlay-get ol 'macrostep-original-text))
	(macrostep-collapse-overlay ol t))))

(defun macrostep-replace-sexp-at-point (sexp &optional original)
  "Replace the form following point with SEXP.

If ORIGINAL is non-nil, SEXP is assumed to be a string
representing the original source text, and inserted verbatim as a
replacement for the form following point. Otherwise, if ORIGINAL
is nil, SEXP is treated as the macro expansion of the source,
inserted using `macrostep-print-sexp' and pretty-printed using
`pp-buffer'."
  (let ((print-quoted t))
    (save-excursion
      ;; Insert new text first so that existing overlays don't
      ;; evaporate
      (if original
	  (insert sexp)                 ; insert original source text
	(macrostep-print-sexp sexp))
      ;; Delete the old form and remove any sub-form overlays in it
      (let ((start (point)) (end (scan-sexps (point) 1)))
	(macrostep-collapse-overlays-in start end)
	(delete-region start end)))
	
    (unless original                   ; inserting macro expansion
      ;; point is now before the expanded form; pretty-print it
      (narrow-to-region (point) (scan-sexps (point) 1))
      (save-excursion
	(pp-buffer)
	;; remove the extra newline that pp-buffer inserts
	(goto-char (point-max))
	(delete-region
	 (point)
	 (save-excursion (skip-chars-backward " \t\n") (point))))
      (widen)
      (indent-sexp))))

(defun macrostep-get-gensym-face (symbol)
  "Return the face to use in fontifying SYMBOL in printed macro expansions.

All symbols introduced in the same level of macro expansion are
fontified using the same face (modulo the number of faces; see
`macrostep-gensym-faces')."
  (or (get symbol 'macrostep-gensym-face)
      (progn
	(if (not macrostep-gensyms-this-level)
	    (setq macrostep-gensym-depth (1+ macrostep-gensym-depth)
		  macrostep-gensyms-this-level t))
	(let ((face (ring-ref macrostep-gensym-faces macrostep-gensym-depth)))
	  (put symbol 'macrostep-gensym-face face)
	  face))))

(defun macrostep-print-sexp (sexp)
  "Pretty-print SEXP, a macro expansion, in the current buffer.

Fontifies uninterned symbols and macro forms using
`font-lock-face' property, and saves the actual text of SEXP's
sub-forms as the `macrostep-expanded-text' text property so that
any uninterned symbols can be reused in macro expansions of the
sub-forms. See also `macrostep-sexp-at-point'."
  (cond
   ((symbolp sexp)
    (let ((p (point)))
      (prin1 sexp (current-buffer))
      ;; fontify gensyms
      (when (not (eq sexp (intern-soft (symbol-name sexp))))
	(put-text-property p (point)
			   'font-lock-face
			   (macrostep-get-gensym-face sexp)))))

   ((listp sexp)
    ;; Print quoted and quasiquoted forms nicely.
    (let ((head (car sexp)))
      (cond ((and (eq head 'quote)	; quote
		  (= (length sexp) 2))
	     (insert "'")
	     (macrostep-print-sexp (cadr sexp)))

	    ((and (memq head '(\` \, \,@)) ; quasiquote, unquote etc.
		  (= (length sexp) 2))
	     (princ head (current-buffer))
	     (macrostep-print-sexp (cadr sexp)))

	    (t				; other list form
	     (insert "(")
	     (when (macrostep-macro-form-p sexp)
	       (let ((p (point)))
		 ;; save the real expansion as a text property on the
		 ;; opening paren
		 (put-text-property
		  (1- p) p 'macrostep-expanded-text sexp)	       
		 ;; fontify the head of the macro
		 (prin1 head (current-buffer))
		 (put-text-property
		  p (point) 'font-lock-face 'macrostep-macro-face))
	       (insert " ")
	       (setq sexp (cdr sexp)))
	     ;; print remaining list elements
	     (dolist (inner sexp)
	       (macrostep-print-sexp inner)
	       (insert " "))
	     (backward-delete-char 1)
	     (insert ")")))))

   ;; print non-lists as normal
   (t (prin1 sexp (current-buffer)))))
  


(provide 'macrostep)

;;; macrostep.el ends here
