;; texi-docstring-magic.el -- munge internal docstrings into texi
;;
;; Keywords: texi, docstrings
;; Author: David Aspinall <da@dcs.ed.ac.uk>
;; Copyright (C) 1998 David Aspinall
;; Maintainer:  Proof General maintainer <proofgen@dcs.ed.ac.uk>
;;
;; $Id$
;;
;; -----
;;
;; Useful binding
;;  (define-key TeXinfo-mode-map "C-cC-d" 'texi-docstring-magic-insert-magic)
;;
;; Useful enhancements to do:
;;  1. Mention default value for user options
;;  2. Use customize properties (e.g. group, simple types)
;;

(defun texi-docstring-magic-splice-sep (strings sep)
  "Return concatenation of STRINGS spliced together with separator SEP."
  (let (str)
    (while strings
      (setq str (concat str (car strings)))
      (if (cdr strings)
	  (setq str (concat str sep)))
      (setq strings (cdr strings)))
    str))

(defconst texi-docstring-magic-munge-table
  '(;; 1. Indented lines are gathered into @lisp environment.
    ;; FIXME: this isn't quite as good as it could be, we
    ;; get the last empty line included in the environment
    ;; rather than outside it.
    ("\\(^.*\\S-.*$\\)"
     t
     (let
	 ((line (match-string 0 docstring)))
       (if (eq (char-syntax (string-to-char line)) ?\ )
	   ;; whitespace
	   (if in-quoted-region
	       line
	     (setq in-quoted-region t)
	     (concat "@lisp\n" line))
	 ;; non-white space
	 (if in-quoted-region
	     (progn
	       (setq in-quoted-region nil)
	       (concat "@end lisp\n" line))
	   line))))
    ;; 2. Pieces of text `stuff' or surrounded in quotes
    ;; are marked up with @samp.  NB: Must be backquote
    ;; followed by forward quote for this to work.
    ;; Can't use two forward quotes else problems with
    ;; symbols.
    ;; Odd hack: because ' is a word constituent in text/texinfo
    ;; mode, putting this first enables the recognition of args
    ;; and symbols put inside quotes.
    ("`\\([^']+\\)'"
     t
     (concat "@samp{" (match-string 1 docstring) "}"))
    ;; 3. Upper cased words ARG corresponding to arguments become @var{arg}
    ("\\([A-Z0-9\\-]+\\)\\(\\s-\\|\\s.\\|$\\)"
     (member (downcase (match-string 1 docstring)) args)
     (concat "@var{" (downcase (match-string 1 docstring)) "}"
	     (match-string 2 docstring)))
    ;; 4. Words sym which are symbols become @code{sym}.
    ;; Must have at least one hyphen to be recognized,
    ;; terminated in whitespace, end of line, or punctuation.
    ;; (Only consider symbols made from word constituents
    ;; and hyphens).
    ("\\(\\(\\w+\\-\\(\\w\\|\\-\\)+\\)\\)\\(\\s\)\\|\\s-\\|\\s.\\|$\\)"
     (or (boundp (intern (match-string 2 docstring)))
	 (fboundp (intern (match-string 2 docstring))))
     (concat "@code{" (match-string 2 docstring) "}"
	     (match-string 4 docstring)))
    ;; 5. Words 'sym which are lisp quoted are
    ;; marked with @code.
    ("\\(\\(\\s-\\|^\\)'\\(\\(\\w\\|\\-\\)+\\)\\)\\(\\s\)\\|\\s-\\|\\s.\\|$\\)"
     t
     (concat (match-string 2 docstring)
	     "@code{" (match-string 3 docstring) "}"
	     (match-string 5 docstring))))
    "Table of regexp matches and replacements used to markup docstrings.
Format of table is a list of elements of the form
   (regexp predicate replacement-form)
If regexp matches and predicate holds, then replacement-form is
evaluated to get the replacement for the match.  
predicate and replacement-form can use variables arg,
and forms such as (match-string 1 docstring)
Match string 1 is assumed to determine the 
length of the matched item, hence where parsing restarts from.
The replacement must cover the whole match (match string 0),
including any whitespace included to delimit matches.")


(defun texi-docstring-magic-munge-docstring (docstring args)
  "Markup DOCSTRING for texi according to regexp matches."
  (let ((case-fold-search nil))
    (dolist (test texi-docstring-magic-munge-table docstring)
      (let ((regexp	(nth 0 test))
	    (predicate  (nth 1 test))
	    (replace    (nth 2 test))
	    (i		0)
	    in-quoted-region)
	
	(while (and
		(< i (length docstring))
		(string-match regexp docstring i))
	  (setq i (match-end 1))
	  (if (eval predicate)
	      (let* ((origlength  (- (match-end 0) (match-beginning 0)))
		     (replacement (eval replace))
		     (newlength   (length replacement)))
		(setq docstring
		      (replace-match replacement t t docstring))
		(setq i (+ i (- newlength origlength))))))
	(if in-quoted-region
	    (setq docstring (concat docstring "\n@end lisp")))))))

(defun texi-docstring-magic-texi (env grp name docstring args &optional endtext)
  "Make a texi def environment ENV for entity NAME with DOCSTRING."
  (concat "@def" env (if grp (concat " " grp) "") " " name
	  " "
	  (texi-docstring-magic-splice-sep args " ")
	  ;; " "
	  ;; (texi-docstring-magic-splice-sep extras " ")
	  "\n"
	  (texi-docstring-magic-munge-docstring docstring args)
	  "\n"
	  (or endtext "")
	  "@end def" env "\n"))

(defun texi-docstring-magic-format-default (default)
  "Make a default value string for the value DEFAULT.
Markup as @code{stuff} or @lisp stuff @end lisp."
  (let ((text       (format "%S" default))
	(isstringg  (stringp default)))
    (concat 
     "\nThe default value is "
     (if (string-match "\n" text)
	 ;; Carriage return will break @code, use @lisp
	 (if (stringp default)
	     (concat "the string: \n@lisp\n" default "\n@end lisp\n")
	   (concat "the value: \n@lisp\n" text "\n@end lisp\n"))
       (concat "@code{" text "}.\n")))))
 

(defun texi-docstring-magic-texi-for (symbol)
  (cond
   ;; Faces
   ((find-face symbol)
    (let*
	((face	    symbol)
	 (name      (symbol-name face))
	 (docstring (or (face-doc-string face)
			"Not documented."))
	 (useropt   (eq ?* (string-to-char docstring))))
      ;; Chop off user option setting
      (if useropt
	  (setq docstring (substring docstring 1)))
      (texi-docstring-magic-texi "fn" "Face" name docstring nil)))
   ((fboundp symbol)
    ;; Functions.
    ;; Don't handle macros,  aliases, compiled fns properly.
    (let*
	((function  symbol)
	 (name	    (symbol-name function))
	 (docstring (or (documentation function)
			"Not documented."))
	 (def	    (symbol-function function))
	 (argsyms   (cond ((eq (car-safe def) 'lambda)
			   (nth 1 def))))
	 (args	    (mapcar 'symbol-name argsyms)))
      (if (commandp function)
	  (texi-docstring-magic-texi "fn" "Command" name docstring args)
	(texi-docstring-magic-texi "un" nil name docstring args))))
   ((boundp symbol)
    ;; Variables.
    (let*
	((variable  symbol)
	 (name      (symbol-name variable))
	 (docstring (or (documentation-property variable
						'variable-documentation)
			"Not documented."))
	 (useropt   (eq ?* (string-to-char docstring)))
	 (default   (if useropt
			(texi-docstring-magic-format-default
			 (default-value symbol)))))
      ;; Chop off user option setting
      (if useropt
	  (setq docstring (substring docstring 1)))
      (texi-docstring-magic-texi
       (if useropt "opt" "var") nil name docstring nil default)))
   (t
    (error "Don't know anything about symbol %s" (symbol-name symbol)))))

(defconst texi-docstring-magic-comment
  "@c TEXI DOCSTRING MAGIC:"
  "Magic string in a texi buffer expanded into @defopt, or @deffn.")

(defun texi-docstring-magic ()
  "Update all texi docstring magic annotations in buffer."
  (interactive)
  (save-excursion
    (goto-char (point-min))
    (let ((magic (concat "^"
			 (regexp-quote texi-docstring-magic-comment)
			 "\\s-*\\(\\(\\w\\|\\-\\)+\\)$"))
	  p
	  symbol)
      (while (re-search-forward magic nil t)
	(setq symbol (intern (match-string 1)))
	(forward-line)
	(setq p (point))
	;; If comment already followed by an environment, delete it.
	(if (and
	     (looking-at "@def\\(\\w+\\)\\s-")
	     (search-forward (concat "@end def" (match-string 1)) nil t))
	    (progn
	      (forward-line)
	      (delete-region p (point))))
	(insert
	 (texi-docstring-magic-texi-for symbol))))))

(defun texi-docstring-magic-face-at-point ()
  (ignore-errors
    (let ((stab (syntax-table)))
      (unwind-protect
	  (save-excursion
	    (set-syntax-table emacs-lisp-mode-syntax-table)
	    (or (not (zerop (skip-syntax-backward "_w")))
		(eq (char-syntax (char-after (point))) ?w)
		(eq (char-syntax (char-after (point))) ?_)
		(forward-sexp -1))
	    (skip-chars-forward "'")
	    (let ((obj (read (current-buffer))))
	      (and (symbolp obj) (find-face obj) obj)))
	(set-syntax-table stab)))))

(defun texi-docstring-magic-insert-magic (symbol)
  (interactive 
   (let* ((v (or (variable-at-point)
		 (function-at-point)
		 (texi-docstring-magic-face-at-point)))
	  (val (let ((enable-recursive-minibuffers t))
                 (completing-read
		  (if v
		      (format "Magic docstring for symbol (default %s): " v)
		     "Magic docstring for symbol: ")
                   obarray '(lambda (sym)
			      (or (boundp sym)
				  (fboundp sym)
				  (find-face sym)))
		   t nil 'variable-history))))
     (list (if (equal val "") v (intern val)))))
  (insert "\n" texi-docstring-magic-comment " " (symbol-name symbol)))

	
(provide 'texi-docstring-magic)
