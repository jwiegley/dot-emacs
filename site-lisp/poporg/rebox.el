;;; Handling of comment boxes in various styles.
;;; Copyright © 1991,92,93,94,95,96,97,98,00 Progiciels Bourbeau-Pinard inc.
;;; François Pinard <pinard@iro.umontreal.ca>, April 1991.

;;; This program is free software; you can redistribute it and/or modify
;;; it under the terms of the GNU General Public License as published by
;;; the Free Software Foundation; either version 2, or (at your option)
;;; any later version.

;;; This program is distributed in the hope that it will be useful,
;;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;;; GNU General Public License for more details.

;;; You should have received a copy of the GNU General Public License
;;; along with this program; if not, write to the Free Software Foundation,
;;; Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

;;;; Introduction:

;; For comments held within boxes, it is painful to fill paragraphs, while
;; stretching or shrinking the surrounding box "by hand", as needed.  This
;; piece of GNU Emacs LISP code eases my life on this.  I find only fair,
;; while giving all sources for a package using such boxed comments, to also
;; give the means I use for nicely modifying comments.  So here they are!

;;;; Installation:

;; For most Emacs language editing modes, refilling does not make sense
;; outside comments, one may redefine the `M-q' command and link it to this
;; file.  For example, I use this in my `.emacs' file:

;;	(add-hook 'c-mode-hook 'fp-c-mode-routine)
;;      (defun fp-c-mode-routine ()
;;	  (local-set-key "\M-q" 'rebox-comment))
;;	(autoload 'rebox-comment "rebox" nil t)
;;	(autoload 'rebox-region "rebox" nil t)

;;;; Usage:

;; The function `rebox-comment' automatically discovers the extent of the
;; boxed comments near the cursor, possibly refills the text, then adjusts the
;; comment box style.  When this command is executed, the cursor should be
;; within a comment, or else it should be between two comments, in which case
;; the command applies to the next comment.  The function `rebox-region' does
;; the same, except that it takes the current region as a boxed comment.  Both
;; commands obey numeric prefixes to add or remove a box, force a particular
;; box style, or to prevent refilling of text.  Without such prefixes, the
;; commands may deduce the current comment box style from the comment itself
;; so the style is preserved.  An unboxed comment is merely one of box styles.

;; A style is identified by three non-zero digits.  The _convention_ about
;; style numbering is such the the hundreds digit roughly represents the
;; programming language, the tens digit roughly represents a box quality (or
;; weight) and the units digit roughly a box type (or figure).  Language,
;; quality and types are collectively referred to as style attributes.

;; When rebuilding a boxed comment, attributes are selected independently of
;; each other.  They may be specified by the digits of the value given as
;; Emacs commands argument prefix.  If there is no such prefix, or if the
;; corresponding digit is zero, the attribute is taken from the value of the
;; default style instead.  If the corresponding digit of the default style is
;; also zero, than the attribute is recognised and taken from the actual
;; comment box, as it existed before prior to the command.  The value 1, which
;; is the simplest attribute, is ultimately taken if the recognition fails.

;; The default style initial value is nil or 0.  It may be preset to another
;; value through setting `rebox-default-style' in Emacs LISP code, or changed
;; to anything else though using a negative value for a prefix, in which case
;; the default style is set to the absolute value of the prefix.

;; A `C-u' prefix avoids refilling the text, but forces using the default box
;; style.  `C-u -' lets the user interact to select one attribute at a time.

;;;; Convention:

;; A programming language is associated with comment delimiters.  Values are
;; 100 for none or unknown, 200 for `/*' and `*/' as in plain C, 300 for `//'
;; as in C++, 400 for `#' as in most scripting languages, 500 for `;' as in
;; LISP or assembler and 600 for `%' as in TeX or PostScript.

;; Box quality differs according to language. For unknown languages (100) or
;; for the C language (200), values are 10 for simple, 20 for rounded, and 30
;; or 40 for starred.  Simple quality boxes (10) use comment delimiters to
;; left and right of each comment line, and also for the top or bottom line
;; when applicable. Rounded quality boxes (20) try to suggest rounded corners
;; in boxes.  Starred quality boxes (40) mostly use a left margin of asterisks
;; or X'es, and use them also in box surroundings.  For all others languages,
;; box quality indicates the thickness in characters of the left and right
;; sides of the box: values are 10, 20, 30 or 40 for 1, 2, 3 or 4 characters
;; wide.  With C++, quality 10 is not useful, you should force 20 instead.

;; Box type values are 1 for fully opened boxes for which boxing is done
;; only for the left and right but not for top or bottom, 2 for half
;; single lined boxes for which boxing is done on all sides except top,
;; 3 for fully single lined boxes for which boxing is done on all sides,
;; 4 for half double lined boxes which is like type 2 but more bold,
;; or 5 for fully double lined boxes which is like type 3 but more bold.

;; The special style 221 is for C comments between a single opening `/*' and a
;; single closing `*/'.  The special style 111 deletes a box.

;;;; History:

;; I first observed rounded corners, as in style 223 boxes, in code from
;; Warren Tucker, a previous maintainer of the `shar' package.  Besides very
;; special files, I was carefully avoiding to use such boxes for real work,
;; as I found them much too hard to maintain.  My friend Paul Provost was
;; working at Taarna, a computer graphics place, which had boxes as part of
;; their coding standards.  He asked that we try something to get out of his
;; misery, and this how `rebox.el' was originally written.  I did not plan to
;; use it for myself, but Paul was so enthusiastic that I timidly started to
;; use boxes in my things, very little at first, but more and more as time
;; passed, yet not fully sure it was a good move.  Later, many friends
;; spontaneously started to use this tool for real, some being very serious
;; workers.  This finally convinced me that boxes are acceptable, after all.

;; Template numbering dependent data.

(defvar rebox-default-style nil
  "*Preferred style for box comments.")

;; Box templates.  First number is style, second is recognition weight.

(defconst rebox-templates

  ;; Generic programming language templates.
  ;; Adding 300 replaces `?' by	`/', for C++ style comments.
  ;; Adding 400 replaces `?' by	`#', for scripting languages.
  ;; Adding 500 replaces `?' by	';', for LISP and assembler.
  ;; Adding 600 replaces `?' by	`%', for TeX and PostScript.

  '((11 115
	"? box")

    (12 215
	"? box ?"
	"? --- ?")

    (13 315
	"? --- ?"
	"? box ?"
	"? --- ?")

    (14 415
	"? box ?"
	"???????")

    (15 515
	"???????"
	"? box ?"
	"???????")

    (21 125
	"?? box")

    (22 225
	"?? box ??"
	"?? --- ??")

    (23 325
	"?? --- ??"
	"?? box ??"
	"?? --- ??")

    (24 425
	"?? box ??"
	"?????????")

    (25 525
	"?????????"
	"?? box ??"
	"?????????")

    (31 135
	"??? box")

    (32 235
	"??? box ???"
	"??? --- ???")

    (33 335
	"??? --- ???"
	"??? box ???"
	"??? --- ???")

    (34 435
	"??? box ???"
	"???????????")

    (35 535
	"???????????"
	"??? box ???"
	"???????????")

    (41 145
	"???? box")

    (42 245
	"???? box ????"
	"???? --- ????")

    (43 345
	"???? --- ????"
	"???? box ????"
	"???? --- ????")

    (44 445
	"???? box ????"
	"?????????????")

    (45 545
	"?????????????"
	"???? box ????"
	"?????????????")

    ;; Textual (non programming) templates.

    (111 113
	 "box")

    (112 213
	 "| box |"
	 "+-----+")

    (113 313
	 "+-----+"
	 "| box |"
	 "+-----+")

    (114 413
	 "| box |"
	 "*=====*")

    (115 513
	 "*=====*"
	 "| box |"
	 "*=====*")

    (121 123
	 "| box |")

    (122 223
	 "| box |"
	 "`-----'")

    (123 323
	 ".-----."
	 "| box |"
	 "`-----'")

    (124 423
	 "| box |"
	 "\\=====/")

    (125 523
	 "/=====\\"
	 "| box |"
	 "\\=====/")

    (141 143
	 "| box ")

    (142 243
	 "* box *"
	 "*******")

    (143 343
	 "*******"
	 "* box *"
	 "*******")

    (144 443
	 "X box X"
	 "XXXXXXX")

    (145 543
	 "XXXXXXX"
	 "X box X"
	 "XXXXXXX")

    ;; C language templates.

    (211 118
	 "/* box */")

    (212 218
	 "/* box */"
	 "/* --- */")

    (213 318
	 "/* --- */"
	 "/* box */"
	 "/* --- */")

    (214 418
	 "/* box */"
	 "/* === */")

    (215 518
	 "/* === */"
	 "/* box */"
	 "/* === */")

    (221 128
	 "/* "
	 "   box"
	 "*/")

    (222 228
	 "/*    ."
	 "| box |"
	 "`----*/")

    (223 328
	 "/*----."
	 "| box |"
	 "`----*/")

    (224 428
	 "/*    \\"
	 "| box |"
	 "\\====*/")

    (225 528
	 "/*====\\"
	 "| box |"
	 "\\====*/")

    (231 138
	 "/*    "
	 " | box"
	 " */   ")

    (232 238
	 "/*       "
	 " | box | "
	 " *-----*/")

    (233 338
	 "/*-----* "
	 " | box | "
	 " *-----*/")

    (234 438
	 "/* box */"
	 "/*-----*/")

    (235 538
	 "/*-----*/"
	 "/* box */"
	 "/*-----*/")

    (241 148
	 "/*    "
	 " * box"
	 " */   ")

    (242 248
	 "/*     * "
	 " * box * "
	 " *******/")

    (243 348
	 "/******* "
	 " * box * "
	 " *******/")

    (244 448
	 "/* box */"
	 "/*******/")

    (245 548
	 "/*******/"
	 "/* box */"
	 "/*******/")

    (251 158
	 "/* "
	 " * box"
	 " */   ")))

;; Template numbering dependent code.

(defvar rebox-language-character-alist
  '((3 . "/") (4 . "#") (5 . ";") (6 . "%"))
  "Alist relating language to comment character, for generic languages.")

;;; Regexp to match the comment start, given a LANGUAGE value as index.

(defvar rebox-regexp-start
  ["^[ \t]*\\(/\\*\\|//+\\|#+\\|;+\\|%+\\)"
   "^"					; 1
   "^[ \t]*/\\*"			; 2
   "^[ \t]*//+"				; 3
   "^[ \t]*#+"				; 4
   "^[ \t]*\;+"				; 5
   "^[ \t]*%+"				; 6
   ])

;;; Request the style interactively, using the minibuffer.

(defun rebox-ask-for-style ()
  (let (key language quality type)
    (while (not language)
      (message "\
Box language is 100-none, 200-/*, 300-//, 400-#, 500-;, 600-%%")
      (setq key (read-char))
      (when (and (>= key ?0) (<= key ?6))
	(setq language (- key ?0))))
    (while (not quality)
      (message "\
Box quality/width is 10-simple/1, 20-rounded/2, 30-starred/3 or 40-starred/4")
      (setq key (read-char))
      (when (and (>= key ?0) (<= key ?4))
	(setq quality (- key ?0))))
    (while (not type)
      (message "\
Box type is 1-opened, 2-half-single, 3-single, 4-half-double or 5-double")
      (setq key (read-char))
      (when (and (>= key ?0) (<= key ?5))
	(setq type (- key ?0))))
    (+ (* 100 language) (* 10 quality) type)))

;; Template ingestion.

;;; Information about registered templates.
(defvar rebox-style-data nil)

;;; Register all box templates.

(defun rebox-register-all-templates ()
  (setq rebox-style-data nil)
  (let ((templates rebox-templates))
    (while templates
      (let ((template (car templates)))
	(rebox-register-template (car template)
				 (cadr template)
				 (cddr template)))
      (setq templates (cdr templates)))))

;;; Register a single box template.

(defun rebox-register-template (style weight lines)
  "Digest and register a single template.
The template is numbered STYLE, and is described by one to three LINES.

If STYLE is below 100, it is generic for a few programming languages and
within lines, `?' is meant to represent the language comment character.
STYLE should be used only once through all `rebox-register-template' calls.

One of the lines should contain the substring `box' to represent the comment
to be boxed, and if three lines are given, `box' should appear in the middle
one.  Lines containing only spaces are implied as necessary before and after
the the `box' line, so we have three lines.

Normally, all three template lines should be of the same length.  If the first
line is shorter, it represents a start comment string to be bundled within the
first line of the comment text.  If the third line is shorter, it represents
an end comment string to be bundled at the end of the comment text, and
refilled with it."

  (cond ((< style 100)
	 (let ((pairs rebox-language-character-alist)
	       language character)
	   (while pairs
	     (setq language (caar pairs)
		   character (cdar pairs)
		   pairs (cdr pairs))
	     (rebox-register-template
	      (+ (* 100 language) style)
	      weight
	      (mapcar (lambda (line)
			(while (string-match "\?" line)
			  (setq line (replace-match character t t line)))
			line)
		      lines)))))
	((assq style rebox-style-data)
	 (error "Style %d defined more than once"))
	(t
	 (let (line1 line2 line3 regexp1 regexp2 regexp3
		     merge-nw merge-se nw nn ne ww ee sw ss se)
	   (if (string-match "box" (car lines))
	       (setq line1 nil
		     line2 (car lines)
		     lines (cdr lines))
	     (setq line1 (car lines)
		   line2 (cadr lines)
		   lines (cddr lines))
	     (unless (string-match "box" line2)
	       (error "Erroneous template for %d style" style)))
	   (setq line3 (and lines (car lines)))
	   (setq merge-nw (and line1 (< (length line1) (length line2)))
		 merge-se (and line3 (< (length line3) (length line2)))
		 nw (cond ((not line1) nil)
			  (merge-nw line1)
			  ((zerop (match-beginning 0)) nil)
			  (t (substring line1 0 (match-beginning 0))))
		 nn (cond ((not line1) nil)
			  (merge-nw nil)
			  (t (let ((x (aref line1 (match-beginning 0))))
			       (if (= x ? ) nil x))))
		 ne (cond ((not line1) nil)
			  (merge-nw nil)
			  ((= (match-end 0) (length line1)) nil)
			  (t (rebox-rstrip (substring line1 (match-end 0)))))
		 ww (cond ((zerop (match-beginning 0)) nil)
			  (t (substring line2 0 (match-beginning 0))))
		 ee (cond ((= (match-end 0) (length line2)) nil)
			  (t (rebox-rstrip (substring line2 (match-end 0)))))
		 sw (cond ((not line3) nil)
			  (merge-se nil)
			  ((zerop (match-beginning 0)) nil)
			  (t (substring line3 0 (match-beginning 0))))
		 ss (cond ((not line3) nil)
			  (merge-se nil)
			  (t (let ((x (aref line3 (match-beginning 0))))
			       (if (= x ? ) nil x))))
		 se (cond ((not line3) nil)
			  (merge-se (rebox-rstrip line3))
			  ((= (match-end 0) (length line3)) nil)
			  (t (rebox-rstrip (substring line3 (match-end 0))))))
	   (setq regexp1 (cond
			  (merge-nw
			   (concat "^[ \t]*" (rebox-regexp-quote nw) ".*\n"))
			  ((and nw (not nn) (not ne))
			   (concat "^[ \t]*" (rebox-regexp-quote nw) "\n"))
			  ((or nw nn ne)
			   (concat "^[ \t]*" (rebox-regexp-quote nw)
				   (rebox-regexp-ruler nn)
				   (rebox-regexp-quote ne) "\n")))
		 regexp2 (and (not (string-equal (rebox-rstrip (concat ww ee))
						 ""))
			      (concat "^[ \t]*" (rebox-regexp-quote ww)
				      ".*" (rebox-regexp-quote ee) "\n"))
		 regexp3 (cond
			  (merge-se
			   (concat "^.*" (rebox-regexp-quote se) "\n"))
			  ((and sw (not ss) (not se))
			   (concat "^[ \t]*" (rebox-regexp-quote sw) "\n"))
			  ((or sw ss se)
			   (concat "^[ \t]*" (rebox-regexp-quote sw)
				   (rebox-regexp-ruler ss)
				   (rebox-regexp-quote se) "\n"))))
	   (setq rebox-style-data
		 (cons (cons style
			     (vector weight regexp1 regexp2 regexp3
				     merge-nw merge-se
				     nw nn ne ww ee sw ss se))
		       rebox-style-data))))))

;; User interaction.

;;; Rebox the current region.

(defun rebox-region (flag)
  (interactive "P")
  (when (eq flag '-)
    (setq flag (rebox-ask-for-style)))
  (when (rebox-validate-flag flag)
    (save-restriction
      (narrow-to-region (region-beginning) (region-end))
      (rebox-engine flag))))

;;; Rebox the surrounding comment.

(defun rebox-comment (flag)
  (interactive "P")
  (when (eq flag '-)
    (setq flag (rebox-ask-for-style)))
  (when (rebox-validate-flag flag)
    (save-restriction
      (rebox-find-and-narrow)
      (rebox-engine flag))))

;;; Validate FLAG and usually return t if not interrupted by errors.
;;; But if FLAG is zero or negative, then change default box style and
;;; return nil.

(defun rebox-validate-flag (flag)
  (cond ((not (numberp flag)))
	((> flag 0))
	(t (setq rebox-default-style (- flag))
	   (message "Default style: %d" rebox-default-style)
	   nil)))

;;; Add, delete or adjust a comment box in the narrowed buffer.
;;; Various FLAG values are explained at beginning of this file.

(defun rebox-engine (flag)
  (let ((undo-list buffer-undo-list)
	(marked-point (point-marker))
	(previous-margin (rebox-left-margin))
	(previous-style (rebox-guess-style))
	(style 111)
	refill)
    (untabify (point-min) (point-max))
    ;; Decide about refilling and the box style to use.
    (when previous-style
      (setq style (rebox-merge-styles style previous-style)))
    (when rebox-default-style
      (setq style (rebox-merge-styles style rebox-default-style)))
    (cond
     ((not flag) (setq refill t))
     ((listp flag) (setq refill nil))
     ((numberp flag)
      (setq refill t
	    style (rebox-merge-styles style flag)))
     (t (error "Unexpected flag value %s" flag)))
    (unless (assq style rebox-style-data)
      (error "Style %d is not known" style))
    (message "Style: %d -> %d" (or previous-style 0) style)
    ;; Remove all previous comment marks.
    (when previous-style
      (rebox-unbuild previous-style))
    ;; Remove all spurious whitespace.
    (goto-char (point-min))
    (while (re-search-forward " +$" nil t)
      (replace-match "" t t))
    (goto-char (point-min))
    (delete-char (- (skip-chars-forward "\n")))
    (goto-char (point-max))
    (when (= (preceding-char) ?\n)
      (forward-char -1))
    (delete-char (- (skip-chars-backward "\n")))
    (goto-char (point-min))
    (while (re-search-forward "\n\n\n+" nil t)
      (replace-match "\n\n" t t))
    ;; Move all the text rigidly to the left for insuring that the left
    ;; margin stays at the same place.
    (let ((indent-tabs-mode nil)
	  (actual-margin (rebox-left-margin)))
      (unless (= previous-margin actual-margin)
	(indent-rigidly (point-min) (point-max)
			(- previous-margin actual-margin))))
    ;; Possibly refill, then build the comment box.
    (let ((indent-tabs-mode nil))
      (rebox-build refill (rebox-left-margin) style))
    ;; Retabify to the left only (adapted from tabify.el).
    (when indent-tabs-mode
      (goto-char (point-min))
      (while (re-search-forward "^[ \t][ \t]+" nil t)
	(let ((column (current-column)))
	  (delete-region (match-beginning 0) (point))
	  (indent-to column))))
    ;; Restore the point position.
    (goto-char (marker-position marked-point))
    ;; Remove all intermediate boundaries from the undo list.
    (unless (eq buffer-undo-list undo-list)
      (let ((cursor buffer-undo-list))
	(while (not (eq (cdr cursor) undo-list))
	  (if (car (cdr cursor))
	      (setq cursor (cdr cursor))
	    (rplacd cursor (cdr (cdr cursor)))))))))

;;; Return style attributes as per DEFAULT, in which attributes have been
;;; overridden by non-zero corresponding style attributes from STYLE.

(defun rebox-merge-styles (default style)
  (let ((default-vector (rebox-style-to-vector default))
	(style-vector (rebox-style-to-vector style)))
    (unless (zerop (aref style-vector 0))
      (aset default-vector 0 (aref style-vector 0)))
    (unless (zerop (aref style-vector 1))
      (aset default-vector 1 (aref style-vector 1)))
    (unless (zerop (aref style-vector 2))
      (aset default-vector 2 (aref style-vector 2)))
    (+ (* 100 (aref default-vector 0))
       (* 10 (aref default-vector 1))
       (aref default-vector 2))))

;;; Transform a style number into a vector triplet.

(defun rebox-style-to-vector (number)
  (vector (/ number 100) (% (/ number 10) 10) (% number 10)))

;; Classification of boxes (and also, construction data).

;;; Find the limits of the block of comments following or enclosing
;;; the cursor, or return an error if the cursor is not within such a
;;; block of comments.  Extend it as far as possible in both
;;; directions, then narrow the buffer around it.

(defun rebox-find-and-narrow ()
  (save-excursion
    (let (start end temp language)
      ;; Find the start of the current or immediately following comment.
      (beginning-of-line)
      (skip-chars-forward " \t\n")
      (beginning-of-line)
      (unless (looking-at (aref rebox-regexp-start 0))
	(setq temp (point))
	(unless (re-search-forward "\\*/" nil t)
	  (error "outside any comment block"))
	(re-search-backward "/\\*")
	(unless (<= (point) temp)
	  (error "outside any comment block"))
	(setq temp (point))
	(beginning-of-line)
	(skip-chars-forward " \t")
	(unless (= (point) temp)
	  (error "text before start of comment"))
	(beginning-of-line))
      (setq start (point)
	    language (rebox-guess-language))
      ;; Find the end of this comment.
      (when (= language 2)
	(search-forward "*/")
	(unless (looking-at "[ \t]*$")
	  (error "text after end of comment")))
      (end-of-line)
      (if (eobp)
	  (insert "\n")
	(forward-char 1))
      (setq end (point))
      ;; Try to extend the comment block backwards.
      (goto-char start)
      (while (and (not (bobp))
		  (cond ((= language 2)
			 (skip-chars-backward " \t\n")
			 (when (and (looking-at "[ \t]*\n[ \t]*/\\*")
				    (> (point) 2))
			   (backward-char 2)
			   (when (looking-at "\\*/")
			     (re-search-backward "/\\*")
			     (setq temp (point))
			     (beginning-of-line)
			     (skip-chars-forward " \t")
			     (when (= (point) temp)
			       (beginning-of-line)
			       t))))
			(t (previous-line 1)
			   (looking-at (aref rebox-regexp-start language)))))
	(setq start (point)))
      ;; Try to extend the comment block forward.
      (goto-char end)
      (while (looking-at (aref rebox-regexp-start language))
	(cond ((= language 2)
	       (re-search-forward "[ \t]*/\\*")
	       (re-search-forward "\\*/")
	       (when (looking-at "[ \t]*$")
		 (beginning-of-line)
		 (forward-line 1)
		 (setq end (point))))
	      (t (forward-line 1)
		 (setq end (point)))))
      ;; Narrow to the whole block of comments.
      (narrow-to-region start end))))

;;; Guess the language in use for the text starting at the cursor position.

(defun rebox-guess-language ()
  (let ((language 1)
	(index (1- (length rebox-regexp-start))))
    (while (not (zerop index))
      (if (looking-at (aref rebox-regexp-start index))
	  (setq language index
		index 0)
	(setq index (1- index))))
    language))

;; Guess the current box style from the text in the whole (narrowed) buffer.

(defun rebox-guess-style ()
  (let ((style-data rebox-style-data)
	best-style best-weight)
    ;; Let's try all styles in turn.  A style has to match exactly to be
    ;; eligible.  More heavy is a style, more prone it is to be retained.
    (while style-data
      (let* ((style (caar style-data))
	     (data (cdar style-data))
	     (weight (aref data 0))
	     (regexp1 (aref data 1))
	     (regexp2 (aref data 2))
	     (regexp3 (aref data 3))
	     (limit (cond ((and best-weight (<= weight best-weight))
			   nil)
			  ((not regexp3)
			   (point-max))
			  ((progn (goto-char (point-max))
				  (forward-line -1)
				  (looking-at regexp3))
			   (point)))))
	(when limit
	  (goto-char (point-min))
	  (cond ((not regexp1))
		((looking-at regexp1) (goto-char (match-end 0)))
		(t (setq limit nil)))
	  (when (and limit regexp2)
	    (while (and (< (point) limit) (looking-at regexp2))
	      (goto-char (match-end 0)))
	    (unless (= (point) limit)
	      (setq limit nil)))
	  (when limit
	    (setq best-style style
		  best-weight weight))))
      (setq style-data (cdr style-data)))
    best-style))

;;; Return a regexp matching STRING without its surrounding space, maybe
;;; followed by spaces or tabs.  If STRING is nil, return the empty regexp.

(defun rebox-regexp-quote (string)
  (cond ((not string) "")
	(t (while (and (> (length string) 0)
		       (= (aref string 0) ? ))
	     (setq string (substring string 1)))
	   (concat (regexp-quote (rebox-rstrip string)) "[ \t]*"))))

;;; Return a regexp matching two or more repetitions of CHARACTER, maybe
;;; followed by spaces or tabs.  Is CHARACTER is nil, return the empty regexp.

(defun rebox-regexp-ruler (character)
  (if character
      (concat (regexp-quote (make-string 2 character)) "+[ \t]*")
    ""))

;;; Return string with trailing spaces removed.

(defun rebox-rstrip (string)
  (while (and (> (length string) 0)
	      (= (aref string (1- (length string))) ? ))
    (setq string (substring string 0 (1- (length string)))))
  string)

;; Reconstruction of boxes.

;;; Remove all comment marks, using STYLE to hint at what these are.

(defun rebox-unbuild (style)
  (let* ((data (cdr (assq style rebox-style-data)))
	 (merge-nw (aref data 4))
	 (merge-se (aref data 5))
	 (nw (aref data 6))
	 (nn (aref data 7))
	 (ne (aref data 8))
	 (ww (aref data 9))
	 (ee (aref data 10))
	 (sw (aref data 11))
	 (ss (aref data 12))
	 (se (aref data 13))
	 (nw-regexp (and nw (concat "^[ \t]*" (rebox-regexp-quote nw))))
	 (ww-regexp (and ww (concat "^[ \t]*" (rebox-regexp-quote ww))))
	 (sw-regexp (and sw (concat "^[ \t]*" (rebox-regexp-quote sw)))))
    ;; Clean up first line.
    (goto-char (point-min))
    (skip-chars-forward "\n")
    (end-of-line)
    (delete-char (- (skip-chars-backward " \t")))
    (when ne
      (let ((start (- (point) (length ne))))
	(when (and (>= start (point-min))
		   (string-equal ne (buffer-substring start (point))))
	  (delete-backward-char (length ne)))))
    (beginning-of-line)
    (if (and nw-regexp (looking-at nw-regexp))
	(replace-match (make-string (- (match-end 0) (match-beginning 0))
				    ? ))
      (skip-chars-forward " \t"))
    (when nn
      (let ((count (skip-chars-forward (char-to-string nn))))
	(delete-char (- count))
	(insert (make-string count ? ))))
    ;; Clean up last line.
    (goto-char (point-max))
    (delete-char (- (skip-chars-backward " \t\n")))
    (when se
      (let ((start (- (point) (length se))))
	(when (and (>= start (point-min))
		   (string-equal se (buffer-substring start (point))))
	  (delete-backward-char (length se)))))
    (insert "\n")
    (forward-line -1)
    (if (and sw-regexp (looking-at sw-regexp))
	(replace-match (make-string (- (match-end 0) (match-beginning 0))
				    ? ))
      (skip-chars-forward " \t"))
    (when ss
      (let ((count (skip-chars-forward (char-to-string ss))))
	(delete-char (- count))
	(insert (make-string count ? ))))
    ;; Clean up all lines.
    (goto-char (point-min))
    (while (not (eobp))
      (end-of-line)
      (delete-char (- (skip-chars-backward " \t")))
      (when ee
	(let ((start (- (point) (length ee))))
	  (when (and (>= start (point-min))
		     (string-equal ee (buffer-substring start (point))))
	    (delete-backward-char (length ee)))))
      (beginning-of-line)
      (if (and ww-regexp (looking-at ww-regexp))
	  (replace-match (make-string (- (match-end 0) (match-beginning 0))
				      ? ))
	(skip-chars-forward " \t"))
      (forward-line 1))))

;;; After refilling it if REFILL is not nil, while respecting a left MARGIN,
;;; put the narrowed buffer back into a boxed comment according to box STYLE.

(defun rebox-build (refill margin style)
  (let* ((data (cdr (assq style rebox-style-data)))
	 (merge-nw (aref data 4))
	 (merge-se (aref data 5))
	 (nw (aref data 6))
	 (nn (aref data 7))
	 (ne (aref data 8))
	 (ww (aref data 9))
	 (ee (aref data 10))
	 (sw (aref data 11))
	 (ss (aref data 12))
	 (se (aref data 13))
	 right-margin)
    ;; Merge a short end delimiter now, so it gets refilled with text.
    (when merge-se
      (goto-char (1- (point-max)))
      (cond ((memq (preceding-char) '(?  ?\t ?\n)))
	    ((memq (preceding-char) '(?. ?! ??))
	     (insert "  "))
	    (t (insert " ")))
      (insert se)
      (setq se nil))
    ;; Possibly refill, and adjust margins to account for left inserts.
    (when refill
      (let ((fill-prefix (make-string margin ? ))
	    (fill-column (- fill-column (+ (length ww) (length ee)))))
	(fill-region (point-min) (point-max))))
    (setq right-margin (+ (rebox-right-margin) (length ww)))
    ;; Construct the top line.
    (goto-char (point-min))
    (cond (merge-nw
	   (skip-chars-forward " " (+ (point) margin))
	   (insert (make-string (- margin (current-column)) ? )
		   nw)
	   (forward-line 1))
	  ((or nw nn ne)
	   (indent-to margin)
	   (when nw
	     (insert nw))
	   (if (not (or nn ne))
	       (delete-char (- (skip-chars-backward " ")))
	     (insert (make-string (- right-margin (current-column))
				  (or nn ? )))
	     (when ne
	       (insert ne)))
	   (insert "\n")))
    ;; Construct all middle lines.
    (while (not (eobp))
      (skip-chars-forward " " (+ (point) margin))
      (when (or ww ee (/= (following-char) ?\n))
	(insert (make-string (- margin (current-column)) ? ))
	(when ww
	  (insert ww))
	(when ee
	  (end-of-line)
	  (indent-to right-margin)
	  (insert ee)
	  (delete-char (- (skip-chars-backward " ")))))
      (forward-line 1))
    ;; Construct the bottom line.
    (when (or sw ss se)
      (indent-to margin)
      (when sw
	(insert sw))
      (if (not (or ss se))
	  (delete-char (- (skip-chars-backward " ")))
	(insert (make-string (- right-margin (current-column))
			     (or ss ? )))
	(when se
	  (insert se)))
      (insert "\n"))))

;;; Return the minimum value of the left margin of all lines, or -1 if
;;; all lines are empty.

(defun rebox-left-margin ()
  (let ((margin -1))
    (goto-char (point-min))
    (while (and (not (zerop margin)) (not (eobp)))
      (skip-chars-forward " \t")
      (let ((column (current-column)))
	(and (not (= (following-char) ?\n))
	     (or (< margin 0) (< column margin))
	     (setq margin column)))
      (forward-line 1))
    margin))

;;; Return the maximum value of the right margin of all lines.  Any
;;; sentence ending a line has a space guaranteed before the margin.

(defun rebox-right-margin ()
  (let ((margin 0) period)
    (goto-char (point-min))
    (while (not (eobp))
      (end-of-line)
      (if (bobp)
	  (setq period 0)
	(backward-char 1)
	(setq period (if (memq (following-char) '(?. ?? ?!)) 1 0))
	(forward-char 1))
      (setq margin (max margin (+ (current-column) period)))
      (forward-char 1))
    margin))

;;; Initialize the internal structures.

(rebox-register-all-templates)

(provide 'rebox)