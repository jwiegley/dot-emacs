;; isa-thy-mode.el - Mode for Isabelle theory files.
;;
;; Author:      David Aspinall <da@dcs.ed.ac.uk>
;; Maintainer:  Isabelle maintainer <isabelle@dcs.ed.ac.uk>
;;
;; Taken from Isamode, version: 3.6 1998/09/02 11:40:45
;;
;; $Id$
;;
;; NAMESPACE management: all functions and variables declared
;; in this file begin with isa-thy-

(require 'proof-site)
(require 'isa)

;;; ========== Theory File Mode User Options ==========

(defcustom thy-heading-indent 0
  "Indentation for section headings."
  :type  'integer
  :group 'thy)

(defcustom thy-indent-level 2
  "Indentation level for Isabelle theory files."
  :type  'integer
  :group 'thy)

(defcustom thy-indent-strings t
  "If non-nil, indent inside strings.
You may wish to disable indenting inside strings if your logic uses
any of the usual bracket characters in unusual ways."
  :type 'boolean
  :group 'thy)

(defcustom thy-use-sml-mode isabelle-use-sml-mode
  "*If non-nil, invoke sml-mode inside \"ML\" section of theory files."
  :type 'boolean
  :group 'thy)


;;; ======  Theory and ML file templates =========================    

(defcustom thy-sections
  ;; NB: preceding white space in templates deleted by indentation alg.
  ;;     top must come first.
  '(("top" .     thy-insert-header)
    ("classes" . thy-insert-class)
    ("default" . thy-insert-default-sort)
    ("types"   . thy-insert-type) 
    ("arities" . thy-insert-arity)
    ;; =================================
    ;; These only make sense for HOL.
    ;; Ideally we should parameterise these parts on the theory.
    ("datatype") ("typedef")
    ("inductive") ("coninductive")
    ("intrs") ("monos")
    ("primrec") ("recdef")
    ;; ==============================
    ("consts"  . thy-insert-const)
    ("translations" . "\"\"\t==\t\"\"")
    ("axclass")
    ("syntax")
    ("instance")
    ("rules"   . thy-insert-rule)
    ("defs"    . thy-insert-rule)
    ("constdefs")
    ("oracle")
    ("local")
    ("locale")
    ("nonterminals")
    ("setup")
    ("global")
    ("end")
    ("ML"))
  "Names of theory file sections and their templates.
Template is either a string to insert or a function. Useful functions are:
  thy-insert-header, thy-insert-class, thy-insert-default-sort,
  thy-insert-const, thy-insert-rule"
  :type '(repeat
	  (cons string
	       (choice function
		       string
		       (const :tag "no template" nil))))
  :group 'thy)

(defcustom thy-id-header
  "(* 
    File:	 %f
    Theory Name: %t
    Logic Image: %l
*)\n\n"
  "*Identification header for .thy and .ML files.
Format characters: %f replaced by filename, %t by theory name,
and %l by the logic image name this file should be read in."
  :group 'thy
  :type 'string)

(defcustom thy-template
"%t  =  %p +\n
classes\n
default\n
types\n
arities\n
consts\n
translations\n
rules\n
end\n
ML\n"
"*Template for theory files.
Contains a default selection of sections in a traditional order.
You can use the following format characters:
  %t  -- replaced by theory name
  %p  -- replaced by names of parents, separated by +'s"
 :group 'thy
 :type 'string)



;;; ========== Code ==========

(defvar thy-mode-map nil)

(defvar thy-mode-syntax-table nil)		; Shared below.

(if thy-mode-syntax-table	
    nil		
  ;; This is like sml-mode, except:
  ;;   .   is a word constituent (not punctuation).  (bad for comments?)
  ;;   "   is a paired delimiter
  (setq thy-mode-syntax-table (make-syntax-table))
  (modify-syntax-entry ?\( "()1 " thy-mode-syntax-table)
  (modify-syntax-entry ?\) ")(4 " thy-mode-syntax-table)
  (modify-syntax-entry ?\\ "\\   " thy-mode-syntax-table)
  (modify-syntax-entry ?*  ". 23" thy-mode-syntax-table)
  (modify-syntax-entry ?_  "w   " thy-mode-syntax-table)
  (modify-syntax-entry ?\' "w   " thy-mode-syntax-table)
;  it's annoying to match with quotes from previous strings,
;  so this has been removed. 
;  (modify-syntax-entry ?\" "$   " thy-mode-syntax-table)
  (modify-syntax-entry ?.  "w   " thy-mode-syntax-table))

(or thy-mode-map
    (let ((map (make-sparse-keymap)))
      (define-key map [(control up)] 'thy-goto-prev-section)
      (define-key map [(control down)] 'thy-goto-next-section)
      (define-key map "\C-c\C-n" 'thy-goto-next-section)
      (define-key map "\C-c\C-p" 'thy-goto-prev-section)
      (define-key map "\C-c\C-c" 'thy-minor-sml-mode)
      (define-key map "\C-c\C-t" 'thy-insert-template)
      ;; Disabled for Proof General
      ;;(define-key map "\C-c\C-u" 'thy-use-file)
      ;;(define-key map "\C-c\C-l" 'thy-raise-windows)
      (define-key map "\C-c\C-o" 'thy-find-other-file)
      (define-key map "\C-M" 'newline-and-indent)
      (define-key map "\C-k" 'thy-kill-line)
      (setq thy-mode-map map)))

(defun thy-mode (&optional nomessage)
  "Major mode for editing Isabelle theory files.
\\<thy-mode-map>
\\[thy-goto-next-section]\t Skips to the next section.
\\[thy-goto-prev-section]\t Skips to the previous section.

\\[indent-for-tab-command]\t Indents the current line.

\\[thy-insert-template]\t Inserts a template for the file or current section.

If thy-use-sml-mode is non-nil, \\<thy-mode-map>\\[thy-minor-sml-mode] \
invokes sml-mode as a minor mode 
in the ML section.  This is done automatically by \
\\[indent-for-tab-command].

The style of indentation for theory files is controlled by these variables:
  thy-heading-indent 
  thy-indent-level
  thy-indent-strings
- see individual variable documentation for details.

Here is the full list of theory mode key bindings:
\\{thy-mode-map}"
  (interactive)
  (kill-all-local-variables)
  (setq major-mode 'thy-mode)
  (setq mode-name "Theory")
  (use-local-map thy-mode-map)
;;  (isa-menus)				                ; Add "isabelle" menu.

  (set-syntax-table thy-mode-syntax-table)
  (make-local-variable 'indent-line-function)
  (setq indent-line-function 'thy-indent-line)
  (make-local-variable 'comment-start)			; Following lines as in sml-mode
  (setq comment-start "(* ")				; .
  (make-local-variable 'comment-end)			; .
  (setq comment-end " *)")				; .
  (setq comment-start-skip "(\\*+[ \t]?")		; .
  (setq font-lock-keywords
	thy-mode-font-lock-keywords)

  ;; Toolbar: needs alteration for non-scripting mode!
  ;;  (if (featurep 'proof-toolbar)
  ;; (proof-toolbar-setup))
  ;;

  (run-hooks 'thy-mode-hook)
  (force-mode-line-update)
  (if (null nomessage)
      (message
       (substitute-command-keys 
	"Isabelle theory-file mode.   Use \\[thy-insert-template] to insert templates; \\[describe-mode] for help.")))
  )

(defun thy-mode-quiet ()
  (interactive)
  (thy-mode t))


;;; "use" and "use_thy" with theory files ========================

;;; FIXME: Isabelle has been improved, so the following code could
;;; be cleaned up.  Also set variable to allow automatic starting
;;; of process by reading logic image.

;;; NB: this is a mess at the moment because of the theory file
;;; naming conventions.  Really we need to parse the theory/ML
;;; file - yuk!!
;;; The next version of Isabelle will be more consistent.

(defun thy-use-file (&optional force-use_thy)
  "Send the file of the current buffer to an Isabelle buffer with use_thy or use."
  (interactive "P")
  (let ((fname (buffer-file-name)))
    (if fname
	(isa-query-save (current-buffer))
      (setq fname
	    (or (buffer-file-name)
		(read-file-name "Use file: " nil nil t))))
    (let*
	((has-thy-extn   (string-match "\\.thy$" fname))   ; o/w assume ML.
	 (tname          (if has-thy-extn 
			     (substring fname 0 -4); cos use_thy is daft!
			   fname))
	 (use            (if (or has-thy-extn force-use_thy)
			     "use_thy"
			   "use"))
	 (use-thy-string (concat use " \"" tname "\";"))
	 (logic (isa-guess-root)))
      (thy-send-string logic use-thy-string))))

(defun thy-use-region (beg end)
  "Send the region to an Isabelle buffer, with use"
  (interactive "r")
  (write-region beg end thy-use-tempname nil 'nomessage)
  (let* ((use-thy-string (concat "use \"" thy-use-tempname "\";"))
	 (logic (isa-guess-root)))
    (thy-send-string logic use-thy-string)))

(defun thy-copy-region (beg end &optional isa-buffer)
  "Copy the region to an Isabelle buffer."
  (interactive "r")
  (let ((text (buffer-substring beg end))
	(logic (isa-guess-root)))
    (save-excursion
      (thy-send-string logic text))))

(defun thy-use-line (&optional isabuffer)
  "Send the current interactive ML line to an Isabelle buffer.
Advance to the next line."
  (interactive)
  (isa-apply-to-interactive-line 'thy-copy-region))

(defun thy-send-string (logic text &optional hide)
  "Send TEXT to a buffer running LOGIC.
If LOGIC is nil, pick the first Isabelle buffer."
  (require 'isa-mode)
  (setq logic nil) ;;; #### HACK! This all needs changing for single-session.
  (let ((cur-frm (selected-frame)))	; Preserve selected frame.
    (if logic				; switch to Isabelle buffer, without
	(isabelle-session logic)	; raising the frame.
					; (NB: this fails if was renamed).
      (set-buffer
       (or (car-safe (isa-find-buffers-in-mode 'isa-mode))
	   (error "Can't find an Isabelle buffer"))))
    (if hide
	(isa-send-string
	 (get-buffer-process (current-buffer))
	 text)
      (isa-insert-ret text))     ; send use command
    (select-frame cur-frm)))

(defun thy-proofgeneral-send-string (logic text &optional hide)
  ;; FIXME -- new function!
  )

(defun thy-raise-windows ()
  "Raise windows/frames associated with Isabelle session."
  (interactive)
  (isa-select-buffer isa-session-buffer t)
  (let ((raise t))
    (mapcar 'isa-display-if-active   
	    isa-associated-buffers)))


(defun thy-guess-logic-in-use ()
  (if (featurep 'isa-mode)
      (let* ((buf (car-safe (isa-find-buffers-in-mode 'isa-mode)))
	     (log (and buf
		       (save-excursion
			 (set-buffer buf)
			 isa-logic-name))))
	log)
    nil))


(defvar thy-use-tempname ".region.ML"
  "*Name of temporary file to hold region dring thy-use-region.")


(defconst thy-logic-image-regexp
  "[lL][oO][gG][iI][cC] [iI][mM][aA][gG][eE]:[ \t]*\"?\\([^ \t\n\"]+\\)\"?[ \t]*$"
  "Regexp for locating name of logic image file in a .thy or .ML file.")

(defvar isa-logic-parents
  ;; I can't be bothered to write all of them in here,
  ;; and anyway they're ambiguous.  Use "Logic image:"
  ;; instead.  (Or find a way of getting emacs to track
  ;; theory structure...)
  '(("List" . "HOL") ("Prod" . "HOL") ("Nat" . "HOL")
    ("Ord" . "HOL") ("Set" ."HOL") ("Sexp" . "HOL")
    ("Univ" . "HOL") ("WF" . "HOL") ("Sum" . "HOL")
    ("IFOL" . "FOL"))
  "*An alist of parents of theories that live in logic files.")

(defun isa-guess-root ()
  "Guess the root logic of the .thy or .ML file in current buffer.
Choice based on first name found by:
  (i) special text: \"Logic Image: <name>\" toward start of file
 (ii) guess work based on parent in THY = <parent> if a .thy file."
  (save-excursion
    (goto-char (point-min))
    (cond
     ((re-search-forward thy-logic-image-regexp 500 t)
      (buffer-substring (match-beginning 1) (match-end 1)))
     ((and (string-match "\\.thy$" (or (buffer-file-name) ""))
	   (re-search-forward 
	    "\\w+[ \t\n]*=[ \t\n]*\\(\\w+\\)[ \t\n]*\\+") 500 t)
      ;; Something looks like a parent theory:
      ;; 		MyThy = HOL + ...
      (let ((child
	     (buffer-substring (match-beginning 1) (match-end 1))))
	    (or (cdr-safe (assoc child isa-logic-parents))
		child))))))

(defun isa-query-save (buffer)
  (and (buffer-modified-p buffer)
       (y-or-n-p (concat "Save file "
			 (buffer-file-name buffer)
			 "? "))
       (save-excursion (set-buffer buffer) (save-buffer))))




;;; Interfacing with sml-mode ========================

;; extending sml-mode. This only works if you visit the theory file 
;; (or start Isabelle mode) first.
;; This is probably fairly close to The Right Thing...

(defun isa-sml-hook ()
  "Hook to customize sml-mode for use with Isabelle."
  (isa-menus)				; Add Isabelle main menu
  ;; NB: these keydefs will affect other sml-mode buffers too!
  (define-key sml-mode-map "\C-c\C-o" 'thy-find-other-file)
  (define-key sml-mode-map "\C-c\C-u" 'thy-use-file)
  (define-key sml-mode-map "\C-c\C-r" 'thy-use-region)
  (define-key sml-mode-map "\C-c\C-l" 'thy-use-line)
  ;; listener minor mode removed: \C-c\C-c freed up
  (define-key sml-mode-map "\C-c\C-t" 'thy-insert-id-header))

(add-hook 'sml-mode-hook 'isa-sml-hook)

(defun isa-sml-mode ()
  "Invoke sml-mode after installing Isabelle hook."
  (interactive)
  (and (fboundp 'sml-mode) (sml-mode)))

(defcustom isa-ml-file-extension ".ML"
  "*File name extension to use for ML files."
  :type 'string
  :group 'isabelle)

(defun thy-find-other-file ()
  "Find associated .ML or .thy file."
  (interactive)
  (and 
   (buffer-file-name)
   (let* ((fname     (buffer-file-name))
	  (thyfile   (string-match "\\.thy$" fname))
	  (mlfile    (string-match
		      (concat (regexp-quote isa-ml-file-extension) "$") fname))
	  (basename  (file-name-sans-extension fname)))
     (cond (thyfile
	    (find-file-other-window (concat basename isa-ml-file-extension)))
	   (mlfile
	    (find-file-other-window (concat basename ".thy")))))))
  

;;; "minor" sml-mode inside theory files ==========

(defvar thy-minor-sml-mode-map nil)

(defun thy-install-sml-mode ()
  (progn
    (require 'sml-mode)
    (setq thy-minor-sml-mode-map (copy-keymap sml-mode-map))
    ;; Bind TAB to what it should be in sml-mode.
    (define-key thy-minor-sml-mode-map "\t" 'indent-for-tab-command)
    (define-key thy-minor-sml-mode-map "\C-c\C-c" 'thy-mode-quiet)
    (define-key thy-minor-sml-mode-map "\C-c\C-t" 'thy-insert-template)))

(defun thy-minor-sml-mode ()
  "Invoke sml-mode as if a minor mode inside a theory file.
This has no effect if thy-use-sml-mode is nil."
  (interactive)
  (if thy-use-sml-mode
      (progn
	(if (not (boundp 'sml-mode)) 
	    (thy-install-sml-mode))
	(kill-all-local-variables)
	(sml-mode)					; Switch to sml-mode
	(setq major-mode 'thy-mode)
	(setq mode-name "Theory Sml")			; looks like it's a minor-mode.
	(use-local-map thy-minor-sml-mode-map)	; special map has \C-c\C-c binding.
	(make-local-variable 'indent-line-function)
	(setq indent-line-function 'thy-do-sml-indent)
	(force-mode-line-update)
	(message "Use C-c C-c to exit SML mode."))))

(defun thy-do-sml-indent ()
  "Run sml-indent-line in an Isabelle theory file, provided inside ML section.
If not, will turn off simulated minor mode and run thy-indent-line."
  (interactive)
  (if (string= (thy-current-section) "ML")		; NB: Assumes that TAB key was 
      (sml-indent-line)					; bound to sml-indent-line.
    (thy-mode t)					; (at least, it is now!).
    (thy-indent-line)))


(defun thy-insert-name (name)
  "Insert NAME -- as a string if there are non-alphabetic characters in NAME."
  (if (string-match "[a-zA-Z]+" name)
      (insert name)
    (insert "\"" name "\"")))

(defun thy-insert-class (name supers)
  (interactive 
   (list
    (isa-read-id "Class name: ")
    (isa-read-idlist "Super classes %s: ")))
  (insert name)
  (if supers (insert "\t< " (isa-splice-separator ", " supers)))
  (indent-according-to-mode)
  (forward-line 1))

(defun thy-insert-default-sort (sort)
  (interactive
   (list
    (isa-read-id "Default sort: ")))
  (insert sort)
  (indent-according-to-mode)
  (thy-goto-next-section))

(defun thy-insert-type (name no-of-args)
  (interactive
   (list
    (isa-read-id  "Type name: ")
    (isa-read-num "Number of arguments: ")))
  ;; make type variables for arguments. Daft things for >26!
  (cond 
   ((zerop no-of-args))
   ((= 1 no-of-args)  
    (insert "'a "))
   (t 
    (insert "(")
    (let ((i 0))
      (while (< i no-of-args)
	(if (> i 0) (insert ","))
	(insert "'" (+ ?a i))
	(setq i (1+ i))))
    (insert ") ")))
  (thy-insert-name name)
  (indent-according-to-mode)
  ;; forward line, although use may wish to add infix.
  (forward-line 1))

(defun thy-insert-arity (name param-sorts result-class)
  (interactive
   (list
    (isa-read-id "Type name: ")
    (isa-read-idlist "Parameter sorts %s: ")
    (isa-read-id "Result class: ")))
  (insert name " :: ")
  (if param-sorts 
      (insert "(" (isa-splice-separator ", " param-sorts) ") "))
  (insert result-class)
  (indent-according-to-mode)
  (forward-line 1))

(defun thy-insert-const (name type)
  ;; only does a single constant, no lists.
  (interactive
   (let* ((thename  (isa-read-id "Constant name: "))
	  (thetype  (isa-read-string (format "Type of `%s' : " thename))))
     (list thename thetype)))
  (thy-insert-name name)
  (insert " ::\t \"" type "\"\t\t")
  (indent-according-to-mode)
  ;; no forward line in case user adds mixfix
  )
  
(defun thy-insert-rule (name)
  (interactive 
   (list
    (isa-read-id "Axiom name: ")))
  (end-of-line 1)
  (insert name "\t\"\"")
  (backward-char)
  (indent-according-to-mode))

(defun thy-insert-template ()
  "Insert a syntax template according to the current section"
  (interactive)
  (thy-check-mode)
  (let* ((sect (thy-current-section))
	 (tmpl (cdr-safe (assoc sect thy-sections))))
    ;; Ensure point is at start of an empty line.
    (beginning-of-line)
    (skip-chars-forward "\t ")
    (if (looking-at sect) 
	(progn 
	  (forward-line 1) 
	  (skip-chars-forward "\t ")))
    (if (looking-at "$")
	nil
      (beginning-of-line)
      (newline)
      (forward-line -1))
    (cond ((stringp tmpl)
	   (insert tmpl)
	   (indent-according-to-mode))
	  ((null tmpl))		; nil is a symbol!
	  ((symbolp tmpl)
	   (call-interactively tmpl)))))

;;; === Functions for reading from the minibuffer.
;;;

; These could be improved, e.g. to enforce syntax for identifiers.
; Also, xemacs lacks a proper read-no-blanks-input !

(defun isa-read-idlist (prompt &optional init)
  "Read a list of identifiers from the minibuffer."
  (let ((items init) item)
    (while (not (string= ""
			 (setq item (read-no-blanks-input 
				       (format prompt (or items ""))))))
      (setq items (nconc items (list item))))
    items))

(defun isa-read-id (prompt &optional init)
  "Read an identifier from the minibuffer."
  ;; don't allow empty input
  (let ((result ""))
    (while (string= result "")
      (setq result (read-no-blanks-input prompt init)))
    result))

(defun isa-read-string (prompt &optional init)
  "Read a non-empty string from the minibuffer"
  ;; don't allow empty input
  (let ((result ""))
    (while (string= result "")
      (setq result (read-string prompt init)))
    result))

(defun isa-read-num (prompt)
  "Read a number from the minibuffer."
  (read-number prompt t))

(defun thy-read-thy-name ()
  (let* ((default  (car 
		    (isa-file-name-cons-extension
		     (file-name-nondirectory 
		      (abbreviate-file-name (buffer-file-name)))))))
    default))

;(defun thy-read-thy-name ()
;  (let* ((default  (car 
;		    (isa-file-name-cons-extension
;		     (file-name-nondirectory 
;		      (abbreviate-file-name (buffer-file-name))))))
;	 (name     (read-string 
;		    (format "Name of theory [default %s]: " default))))
;    (if (string= name "") default name)))

(defun thy-read-logic-image ()
  (let*	((defimage (or (thy-guess-logic-in-use)
		       "Pure"))
	 (logic    (read-string
		    (format "Name of logic image to use [default %s]: "
			    defimage))))
    (if (string= logic "") defimage logic)))

(defun thy-insert-header (name logic parents)
  "Insert a theory file header, for LOGIC, theory NAME with PARENTS"
  (interactive 
   (list
    (thy-read-thy-name)
    (thy-read-logic-image)
    (isa-read-idlist "Parent theory %s: ")))
  (let* ((parentplus (isa-splice-separator 
		      " + " 
		      (or parents (list (or logic "Pure")))))
	 (formalist (list
		       (cons "%t" name)
		       (cons "%p" parentplus))))
    (thy-insert-id-header name logic)
    (insert (isa-format formalist thy-template)))
  (goto-char (point-min))
  (thy-goto-next-section))

(defun thy-insert-id-header (name logic)
  "Insert an identification header, for theory NAME logic image LOGIC."
  (interactive
   (list
    (thy-read-thy-name)
    (thy-read-logic-image)))
  (let* ((formalist (list
		     (cons "%f" (buffer-file-name))
		     (cons "%t" name)
		     (cons "%l" logic))))
    (insert (isa-format formalist thy-id-header))))

(defun thy-check-mode ()
  (if (not (eq major-mode 'thy-mode))
      (error "Not in Theory mode.")))
  

(defconst thy-headings-regexp
  (concat
   "^\\s-*\\("
   (substring (apply 'concat (mapcar 
			      '(lambda (pair)
				 (concat "\\|" (car pair)))
			      (cdr thy-sections))) 2)
   "\\)[ \t]*")
  "Regular expression matching headings in theory files.")

(defvar thy-mode-font-lock-keywords
  (list				
   (list thy-headings-regexp 1
	 'font-lock-keyword-face))
  "Font lock keywords for thy-mode.
Default set automatically from thy-headings-regexp.")

;;; movement between sections ===================================    

(defun thy-goto-next-section (&optional count noerror)
  "Goto the next (or COUNT'th next) section of a theory file.
Negative value for count means previous sections.
If NOERROR is non-nil, failed search will not be signalled."
  (interactive "p")
  (condition-case nil
      ;; string matching would probably be good enough
      (cond ((and count (< count 0))
	     (let ((oldp (point)))
	       (beginning-of-line)
	       (thy-goto-top-of-section)
	       ;; not quite right here - should go to top
	       ;; of file, like top of section does.
	       (if (equal (point) oldp)
		   (progn
		     (re-search-backward thy-headings-regexp 
					 nil nil (1+ (- count)))
		     (forward-line 1))))
	     t)
	    (t
	     (re-search-forward thy-headings-regexp nil nil count)
	     (forward-line 1)
	     t))
    ;; could just move to top or bottom if this happens, instead
    ;; of giving this error.
    (search-failed (if noerror nil
		     (error "No more headings")))))

(defun thy-goto-prev-section (&optional count noerror)
  "Goto the previous section (or COUNT'th previous) of a theory file.
Negative value for count means following sections.
If NOERROR is non-nil, failed search will not be signalled."
  (interactive)
  (thy-goto-next-section (if count (- count) -1) noerror))

(defun thy-goto-top-of-section ()
  "Goto the top of the current section"
  (interactive)
  (if (re-search-backward thy-headings-regexp nil t)
      (forward-line 1)
    (goto-char (point-min))))

(defun thy-current-section ()
  "Return the current section of the theory file, as a string.
\"top\" indicates no section."
  (save-excursion
    (let* ((gotsect (re-search-backward thy-headings-regexp nil t))
	   (start   (if gotsect
			(progn
			  (skip-chars-forward " \t")
			  (point)))))
      (if (not start)
	  "top"
	(skip-chars-forward "a-zA-z")
	(buffer-substring start (point))))))



;;; kill line ==================================================

(defun thy-kill-line (&optional arg)
  "As kill-line, except in a string will kill continuation backslashes also.
Coalesces multiple lined strings by leaving single spaces."
  (interactive "P")
  (let ((str           (thy-string-start))
	(kill-start    (point))
	following-slash)
    (if (not str)
	;; Usual kill line if not inside a string.
	(kill-line arg)
      (if arg
	  (forward-line (prefix-numeric-value arg))
	(if (eobp)
	    (signal 'end-of-buffer nil)))
      (setq kill-start (point))
      (if (thy-string-start str)		; if still inside a string
	  (cond 
	   ((looking-at "[ \t]*$")	; at end of line bar whitespace
	    (skip-chars-backward 
	     " \t"
	     (save-excursion (beginning-of-line) (1+ (point))))
	    (backward-char)
	    (if (looking-at "\\\\")	; preceding backslash
		(progn
		  (skip-chars-backward " \t")
		  (setq following-slash t)
		  (setq kill-start (min (point) kill-start)))
	      (goto-char kill-start))
	    (forward-line 1))
	   ((looking-at "[ \t]*\\\\[ \t]*$") ; before final backslash
	    (setq following-slash t)
	    (forward-line 1))
	   ((looking-at "\\\\[ \t]*\\\\[ \t]*$") ; an empty line!
	    (forward-line 1))
	   ((looking-at ".*\\(\\\\\\)[ \t]*$")	; want to leave backslash
	    (goto-char (match-beginning 1)))
	   ((and kill-whole-line (bolp))
	    (forward-line 1))
	   (t
	    (end-of-line))))
      (if (and following-slash 
	       (looking-at "[ \t]*\\\\"))	; delete following slash if
	  (goto-char (1+ (match-end 0)))) ; there's one
      (kill-region kill-start (point))	; do kill
      (if following-slash
	  ;; did do just-one-space, but it's not nice to delete backwards
	  ;; too
	  (delete-region (point)
			 (save-excursion
			   (skip-chars-forward " \t")
			   (point)))))))


;;; INDENTATION ==================================================
  
;;; Could do with thy-correct-string function,
;;; which does roughly the same as indent-region.
;;; Then we could have an electric " that did this!

;;; Could perhaps have used fill-prefix to deal with backslash
;;; indenting, rather than lengthy code below?

(defun thy-indent-line ()
  "Indent the current line in an Isabelle theory file.
If in the ML section, this switches into a simulated minor sml-mode."
  (let ((sect (thy-current-section)))
    (cond 
     ((and thy-use-sml-mode (string= sect "ML"))
      (progn				               ; In "ML" section,
	(thy-minor-sml-mode)	               ; switch to sml mode.
	(sml-indent-line)))

     (t   (let ((indent   (thy-calculate-indentation sect)))
	    (save-excursion
	      (beginning-of-line)
	      (let ((beg (point)))
		(skip-chars-forward "\t ")
		(delete-region beg (point)))
	      (indent-to indent))
	    (if (< (current-column) 
		   (current-indentation))	
		(skip-chars-forward "\t ")))))))

;; Better Emacs major modes achieve a kind of "transparency" to
;; the user, where special indentation,etc. happens under your feet, but
;; in a useful way that you soon get accustomed to.  Worse modes
;; cause frustration and repetitive re-editing of automatic indentation.
;; I hope I've achieved something in the first category...

(defun thy-calculate-indentation (sect)
  "Calculate the indentation for the current line.
SECT should be the string name of the current section."
  (save-excursion
    (beginning-of-line)
    (or (thy-long-comment-string-indentation)
	(if (looking-at "\\s-*$")
	    ;; Empty lines use indentation for section.
	    (thy-indentation-for sect)
	  (if (looking-at thy-headings-regexp)
	      thy-heading-indent
	    (progn
	      (skip-chars-forward "\t ")
	      (cond
	       ;; A comment?
	       ((looking-at "(\\*")         
		(thy-indentation-for sect))
	       ;; Anything else, use indentation for section
	       (t (thy-indentation-for sect)))))))))

(defun thy-long-comment-string-indentation ()
  "Calculate the indentation if inside multi-line comment or string.
Also indent string contents."
  (let* ((comstr (thy-comment-or-string-start))
	 (bolpos (save-excursion
		   (beginning-of-line)
		   (point)))
	 (multi  (and comstr 
		      (< comstr bolpos))))
    (if (not multi)
	nil		
      (save-excursion
	(beginning-of-line)
	(cond

	 ;; Inside a comment?
	 ((char-equal (char-after comstr) ?\( )
	  (forward-line -1)
	  (if (looking-at "[\t ]*(\\*")
	      (+ 3 (current-indentation))
	    (current-indentation)))
	 
	 ;; Otherwise, a string.
	 ;; Enforce correct backslashing on continuing
	 ;; line and return cons of backslash indentation
	 ;; and string contents indentation for continued
	 ;; line.
	 (t
	  (let ((quote-col (save-excursion (goto-char comstr) 
					   (current-column))))
	     (if thy-indent-strings
		(thy-string-indentation comstr)
	      ;; just to right of matching " 
	      (+ quote-col 1)))))))))

(defun thy-string-indentation (start)
  ;; Guess indentation for text inside a string
  (let* ((startcol  (save-excursion (goto-char start) (current-column)))
	 (pps-state (parse-partial-sexp (1+ start) (point)))
	 (par-depth (car pps-state)))
	 (cond (;; If not in nested expression, startcol+1
		(zerop par-depth)
		(1+ startcol))
	       (;; If in a nested expression, use position of opening bracket
		(natnump par-depth)
		(save-excursion
		  (goto-char (nth 1 pps-state))
		  (+ (current-column)
		     (cond ((looking-at "\\[|") 3)
			   (t 1)))))
	       (;; Give error for too many closing parens
		t
		(error "Mismatched parentheses")))))

(defun thy-indentation-for (sect)
  "Return the indentation for section SECT"
  (if (string-equal sect "top")
      thy-heading-indent
    thy-indent-level))

(defun thy-string-start (&optional min)
  "Return position of start of string if inside one, nil otherwise."
  (let ((comstr (thy-comment-or-string-start)))
    (if (and comstr
	     (save-excursion
	       (goto-char comstr)
	       (looking-at "\"")))
	comstr)))

;;; Is this parsing still too slow?  (better way? e.g., try setting
;;; variable "char" and examining it, rather than finding current
;;; state first - fewer branches in non-interesting cases, perhaps.
;;; NB: it won't understand escape sequences in strings, such as \"

(defun thy-comment-or-string-start (&optional min)
  "Find if point is in a comment or string, starting parse from MIN.
Returns the position of the comment or string start or nil.
If MIN is nil, starts from top of current section.

Doesn't understand nested comments."
  (or min
      (setq min
	    (save-excursion
	      (thy-goto-top-of-section) (point))))
  (if (<= (point) min)
      nil
    (let ((pos   (point))
	  (incomdepth 0)
	  incom instring)  ; char
      (goto-char min)
      (while (< (point) pos)
	;; When inside a string, only look for its end
	(if instring
	    (if (eq (char-after (point)) ?\") ; looking-at "\""
		(setq instring nil))
	  ;; If inside a comment, look for a comment end
	  (if (> 0 incomdepth)	
	      (if (and			; looking-at "\\*)"
		   (eq (char-after (point)) ?\*)
		   (eq (char-after (1+ (point))) ?\)))
		  (setq incomdepth (1- incomdepth)))
	    ;; If inside neither comment nor string, look for 
	    ;; a string start.
	    (if (eq (char-after (point)) ?\") ; looking-at "\""
		(setq instring (point))))
	  ;; Look for a comment start (unless inside a string)
	  (if (and
	       (eq (char-after (point)) ?\()
	       (eq (char-after (1+ (point))) ?\*))
	      (progn
		(if (= 0 incomdepth)	; record start of main comment
		    (setq incom (point))) ; only
		(setq incomdepth (1+ incomdepth)))))
	(forward-char))
      (if (> 0 incomdepth) incom instring))))




(provide 'thy-mode)

;;; end of thy-mode.el
