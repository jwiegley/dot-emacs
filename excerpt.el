;; excerpt.el --- extraxt text & report to main file

;; Copyright (C) 2002 Thomas Link

;; Author: Thomas Link AKA samul AT web DOT de
;; Time-stamp: <2003-03-16>
;; Keywords: editing, summaries, writing reports, text snippets

(defvar excerpt-version "0.3.1")
(defvar excerpt-homepage "http://members.a1.net/t.link/CompEmacsExcerpt.html")

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software Foundation,
;; Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA


;;; Commentary:

;; ;---(:excerpt-beg excerpt :name doc)---
;; ;---(:excerpt-source "~/Etc/TL-Wiki/CompEmacsExcerpt")---
;; 
;; ** Description
;; 
;; Extraxt text & report to main file. This is done using the following
;; commands:
;; 
;; `excerpt-insert' :: A general command for inserting excerpts. Use
;; TAB-completion to see which excerpts are available in a certain file.
;; (See also the variable `excerpt-sources'.)
;; 
;; `excerpt-insert-excerpt' ::  Insert an excerpt from a file.
;; 
;; `excerpt-insert-with-prefix' :: Insert a prefixed file excerpt.
;; 
;; `excerpt-source' :: Insert a source mark in the source file. The user
;; will be asked to enter a category name.
;; 
;; `excerpt-named-source' :: Insert a source mark in the source file. The
;; user will be asked to enter a category name and an ID.
;; 
;; `excerpt-insert-pseudo', `excerpt-insert-pseudo-with-prefix' :: Insert a
;; pseudo excerpt (a function or a variable) -- search for ":name
;; excerpt-commands" in the source code for an example.
;; 
;; 
;; Installation: Put (require 'excerpt) (excerpt-install) into your
;; startup/user init file.
;; 
;; 
;; ** In the Source File
;; 
;; In the source file these text portions are marked as
;; 
;; <example>
;; 	\<format-string NAME\>\<comment-string\>(\<start-string\> ID)
;; 	text to be reported
;; 	\<comment-string\>(\<end-string\> ID)
;; </example>
;; 
;; NAME ... a string -- may not contain ")"
;; 
;; FORMAT-STRING is mode sensitive but can be changed via buffer local
;; variables. It is possible to use tags like =LaTeX=' =\\index=.
;; 
;; START-STRING and END-STRING are global but can be changed via buffer
;; local variables.
;; 
;; 
;; ** In the Main File
;; 
;; In the main file text to be reported is marked as 
;; 
;; <example>
;; 	\<prefix\>\<comment-string\>(:excerpt NAME [:id ID])
;; 	\<prefix\><comment-string>(:excerpt-source FILE-NAME)
;; 	\<prefix\>[excerpted text]
;; 	\<prefix\>\<comment-string\>(:excerpt-end [ID])
;; </example>
;; 
;; This text is inserted with one `excerpt-insert' commands and
;; automatically updated when setting the buffer/file-local variable
;; `excerpt-update-flag' to t or when calling one of the `excerpt--update'
;; commands -- preferably via the pop-up menu.
;; 
;; A local keymap covers the excerpt. Pressing =Enter= jumps to the source
;; file; =Space= updates the excerpt if `excerpt-bind-space-to-update-flag'
;; is non-nil; pressing =Mouse-2= (or rather `excerpt-mouse-button') opens
;; a pop-up menu.
;; 
;; If no ID is given, all occurances of category NAME are being excerpted.
;; (Hm. To be honest, I'm not sure if this is true, if I planned to
;; implement such a feature, and if I've already done so.)
;; 
;; The whole excerpt will be prefixed with the first line's PREFIX. This
;; is a convenient way for inserting excerpts as comments.
;; 
;; The file/buffer local variable `excerpt-sources' defines where sources
;; are normally located. The default file for `excerpt-insert' is either
;; built on the value of this variable or the current buffer's file name.
;; 
;; 
;; ** Caveats
;; 
;; Using regular expressions for finding excerpt sources and excerpt
;; targets is of course a fragile solution. There are many ways to confuse
;; =excerpt.el=. Here are some tips.
;; 
;; 
;; *** Headless Excerpts
;; 
;; Headless excerpt won't be visible as excerpts when the file-properties file
;; is missing. Once the data of the file-properties file gets out of sync with
;; the text, it's pretty hard to restore a headless excerpt properly. You
;; can force the use of file-local variables by modifying
;; `excerpt-use-file-local-variable', though.
;; 
;; 
;; *** Copy and Paste
;; 
;; When copying an excerpt, the overlays/extents are only maintained if the
;; whole excerpt was selected. This is escpecially important with headless
;; excerpts.
;; 
;; 
;; *** COMMENT-START, COMMENT-END
;; 
;; For hiding excerpt marks to the compiler, text formatter, preprocessor,
;; or whatsoever, these marks are enclosed with =COMMENT-START= and
;; =COMMENT-END=. This means of course that these variables have to be
;; defined somewhere. Normally this is done by the major mode. If this is
;; not the case, you could use file local variables or you could use some
;; project management package that sets these variables for files in a
;; certain directory.
;; 
;; 
;; ** Customization Via Buffer Local Variables
;; 
;; The following variables overwrite global settings if defined as local
;; variables:
;; 
;; `excerpt-start-format-string', `excerpt-end-format-string' :: Define
;; source start and end marks.
;; 
;; `excerpt-start-string', `excerpt-end-string' :: These variables are
;; created by excerpt.el and define the excerpt start and end marks.
;; 
;; `excerpt-sources' :: Either a file name or a directory name where
;; excerpt sources are located.
;; 
;; `excerpt-update-flag' :: If non-nil, update all excerpts after opening.
;; 
;; For setting these variables for all files in a specific directory, use
;; some project management package. (You could also use CompEmacsFilesets,
;; defining some custom :open function.)
;; 
;; 
;; ** Types of excerpts
;; 
;; At the moment there are two "types" of excerpts:
;; 
;; excerpt :: Insert marked excerpts.
;; 
;; file :: Insert the whole file. When running the command
;; `excerpt-insert', a pseudo excerpt with the name =*FILE*= is generated.
;; 
;; In addition, there are two pseudo excerpts, which can be inserted with
;; the `excerpt-insert-pseudo' command: =*FUNCTION*= and =*VARIABLE*=.
;; Evaluation and formatting of pseudo excerpts' sources is defined by
;; three user options/variables: excerpt-allow-eval-functions,
;; excerpt-allow-eval-variables, excerpt-pseudo-excerpt-list. Evaluation of
;; functions is of course unsafe.
;; 
;; ;---(:excerpt-end excerpt :name doc)---


;;; Commands:

;; ;---(:excerpt-beg *FUNCTION* :name excerpt-commands)---
;; ;---(:excerpt-source #'(tellib-selfdocumentation "^excerpt-" #'commandp t))---
;; 
;; (excerpt-change-categories-file)
;; Change the buffer's categories file.
;; 
;; (excerpt-find-next-excerpt &optional REVERSE-DIRECTION-FLAG CAT NAME)
;; Find the *next* excerpt.
;; 
;; (excerpt-find-source BEG END)
;; Goto currently selected excerpt's source file.
;; 
;; (excerpt-find-source-at-point &optional POS)
;; Find source at point POS.
;; 
;; (excerpt-insert)
;; Insert an excerpt.
;; 
;; (excerpt-insert-excerpt &optional DEF BEG-OLD END-OLD FORCE-PREFIX
;;                        HEADLESS-FLAG)
;; Insert a excerpt mark into the main file.
;; 
;; (excerpt-insert-pseudo &optional PREFIX)
;; Insert a pseudo excerpt.
;; 
;; (excerpt-insert-pseudo-with-prefix)
;; Insert a pseudo excerpt with prefix.
;; 
;; (excerpt-insert-with-prefix)
;; Insert a prefixed excerpt.
;; 
;; (excerpt-named-source BEG END &optional NON-INTRUSIVE-FLAG)
;; Mark current region as named excerpt source.
;; 
;; (excerpt-named-source-non-intrusive BEG END)
;; Mark current region as named excerpt source.
;; 
;; (excerpt-setup-all-excerpt &optional BUFFER)
;; Set faces and text properties for all excerpts.
;; 
;; (excerpt-setup-source-marks &optional BUFFER)
;; Highlight all source marks in the current buffer.
;; 
;; (excerpt-source BEG END &optional ID NON-INTRUSIVE-FLAG)
;; Mark current region as excerpt source
;; 
;; (excerpt-update)
;; Update all excerpts.
;; 
;; (excerpt-update-current BEG END &optional FIND-DEF CAT NAME)
;; Update currently marked excerpt.
;; 
;; (excerpt-update-excerpt-at-point &optional POS)
;; Update the excerpt at point or POS.
;; 
;; (excerpt-update-next &optional REVERSE-FLAG)
;; Update the *next* excerpt.
;; 
;; (excerpt-update-region BEG END)
;; Update all excerpts in region.
;; 
;; ;---(:excerpt-end *FUNCTION* :name excerpt-commands)---


;;; Problems:

;; ;---(:excerpt-beg excerpt :name problems)---
;; ;---(:excerpt-source "~/Etc/TL-Wiki/CompEmacsExcerpt")---
;; 
;; - A pseudo excerpt is identified by the quoting style, so that the use
;; of =*FUNCTION*= and =*VARIABLE*= as category names is rather pointless.
;; 
;; ;---(:excerpt-end excerpt :name problems)---


;;; Change log:

;; ;---(:excerpt-beg excerpt :name log)---
;; ;---(:excerpt-source "~/Etc/TL-Wiki/CompEmacsExcerpt")---
;; 
;; =0.3= :: pseudo-excerpts (functions, variables), headless excerpts
;; (excerpts with no textual markers)
;; 
;; =0.2= :: non-intrusive source marks
;; 
;; =0.1= :: initial release (experimental, tested with XEmacs 21.4.8)
;; 
;; ;---(:excerpt-end excerpt :name log)---


;;; To do/ideas:

;- excerpts should have flags or options -- e.g. is this a converted or
;a literal excerpt etc.

;- Sandbox: "*FUNCTION*" pseudo-excerpts are risky

;- check names: numbered/unique excerpt names

;- link source marks to target files (i.e. jump from the source to where
;it is being cited) [should the info be stored in some central data base
;or in the source file; which solution would be less prone to outdated
;data?]

;- variables: excerpt-header, excerpt-footer (file local; e.g. for
;embedding excerpts in a LaTeX environment

;- automatically convert excerpts between file formats (emacs-wiki->text,
;emacs-wiki->latex)

;- mode for browsing excerpts

;- excerpt listings

;- excerpt-format-strings by major-mode, minor-mode, file name

;- more than one possible format for marking excerpts in the target file

;- possibility to edit excerpts and to update the source file

;- short forms for excerpts ~ dynamic fields. E.g. in LaTeX this could
;be \excerpt{CAT.NAME}{EXCERPT} The source file would be defined via a
;file local variable. The command \excerpt has to defined, of course:
;\newcommand{\excerpt}[2]{#2}. But what if the excerpt contains "}"?

;- virtual excerpts??? (not marked & automatically extracted; but don't
;we already have this feature using file-local markup/search string?)


;;; Code:

(require 'tellib)
(tellib-version-check "tellib.el" tellib-version "0.2.0")

(require 'file-properties)

(when tellib-running-xemacs
  (require 'overlay))


;; Customizations

(defgroup excerpt nil
  "Extraxt text & report to main file."
  :link `(url-link :tag "Homepage" ,excerpt-homepage)
  :link '(emacs-commentary-link :tag "Commentary" "excerpt.el")
  :prefix "excerpt-"
  :group 'data)

(defcustom excerpt-global-categories-file
  (if tellib-running-xemacs
      "~/.xemacs/excerpt-categories.txt"
    "~/.excerpt-categories.txt")
  "*Global categories file."
  :type 'file
  :group 'excerpt)

(defcustom excerpt-global-start-format-string
  "(:begin #{NAME})"
  "*Excerpt source start string."
  :type 'string
  :group 'excerpt)

(defcustom excerpt-global-end-format-string
  "(:end #{NAME})"
  "*Excerpt source end string."
  :type 'string
  :group 'excerpt)

(defcustom excerpt-id-connect
  "."
  "*String to connect excerpt category and excerpt name (visual)."
  :type '(choice :tag "Select:"
		 (const :tag "@" :value "@")
		 (const :tag "->" :value "->")
		 (const :tag "." :value ".")
		 (const :tag ":" :value ":")
		 (string :tag "String" :value ""))
  :group 'excerpt)

(defcustom excerpt-set-read-only-flag
  nil
  "*Set excerpts read-only."
  :type 'boolean
  :group 'excerpt)

(defcustom excerpt-use-file-local-variable
  `((".*" ,(if (boundp 'file-properties-list) 'file-properties 'file-local)))
  "*When storing non-intrusive/headless marks, use file local variables
instead of file-properties. If 'file-properties is used, the excerpt definitions
will be saved in a separat file -- i.e. when you move the file and the
file-properties file is not accessible, the source marks will be lost.
'file-local means, append the definitions to the local variables
section."
  :type '(repeat :tag "Definition"
		 (cons :tag "List"
		       :value (".*")
		       (regexp :tag "Filename RegExp" :value ".*")
		       (repeat :tag "Mode"
			       (choice :tag "Select"
				       (const :tag "file local"
					      :value file-local)
				       (const :tag "file-properties"
					      :value file-properties)))))
  :group 'excerpt)

(defcustom excerpt-invisible-header-flag
  nil
  "*Make excerpt definition headers invisible.
Invisible header lines are also marked read-only."
  :type 'boolean
  :group 'excerpt)

(defcustom excerpt-sources-refs-db
  nil
  "*File used to store a data base of cited excerpt sources.
Nil means, disable this feature."
  :type `(choice :label "Select"
		 (const :label "Disable" :value nil)
		 (file  :label "File"
			:value ,(if tellib-running-xemacs
				    "~/.xemacs/excerpt-refs.el"
				  "~/.excerpt-refs.el")))
  :group 'excerpt)

(defcustom excerpt-bind-space-to-update-flag t
  "*Bind space-key to `excerpt-update-current'
in the excerpt's local keypam."
  :type 'boolean
  :group 'excerpt)

(defcustom excerpt-use-relative-or-absolute-file-name
  '((same-dir t relative)
    (t t relative))
  "*Use relative file names when inserting excerpts.
Abbreviated? If non-nil, the abbreviated file name (see
`abbreviate-file-name') is matched against regexp."
  :type '(repeat :tag "List"
		 (choice :tag "Select"
			 (list :tag "Pattern"
			       :value ("^~/.*$" t relative)
			       (regexp :tag "Regexp" :value "^~/.*$")
			       (boolean :tag "Abbreviated?" :value t)
			       (choice :tag "Mode"
				       (const :tag "absolute"
					      :value absolute)
				       (const :tag "relative"
					      :value relative)))
			 (list :tag "Pair"
			       :value (("^~/.*$" "^~/.*$") t relative)
			       (list :tag "Regexps"
				     (regexp :tag "Source" :value "^~/.*$")
				     (regexp :tag "Main File" :value "^~/.*$"))
			       (boolean :tag "Abbreviated?" :value t)
			       (choice :tag "Mode"
				       (const :tag "absolute"
					      :value absolute)
				       (const :tag "relative"
					      :value relative)))
			 (list  :tag "Same directory"
				:value (same-dir t relative)
				(const :format "" :value same-dir)
				(const :format "" :value t)
				(choice :tag "Mode"
					(const :tag "absolute"
					       :value absolute)
					(const :tag "relative"
					       :value relative)))
			 (list  :tag "Else"
				:value (t t relative)
				(const :format "" :value t)
				(const :format "" :value t)
				(choice :tag "Mode"
					(const :tag "absolute"
					       :value absolute)
					(const :tag "relative"
					       :value relative)))))
  :group 'excerpt)

(defcustom excerpt-mouse-button
  (if tellib-running-xemacs [(button2)] [mouse-2])
  "*Mouse button to press for popping up the main file's excerpt menu."
  :type 'sexp
  :group 'excerpt)

(defcustom excerpt-format-strings
  '(("\\.tex$"
     "\\index{#{CATEGORY}}%%%#{START}"
     "%%% #{END}")
    (emacs-wiki-mode
     "<!-- ---(:excerpt #{CATEGORY})@#{START}--- -->"
     "<!-- ---#{END}--- -->"
     ((:no-buffer-local-vars t)))
    (""
     "#{COMMENT-START}---(:excerpt #{CATEGORY})@#{START}---#{COMMENT-END}"
     "#{COMMENT-START}---#{END}---#{COMMENT-END}"))
  "*Format strings for excerpt source marks.

An alist of the form
 '((FILE-PATTERN START-FORMAT-STRING END-FORMAT-STRING)
   ...)

FILE-PATTERN ... a regexp matching the source file name

START-FORMAT-STRING ... #{START} will be replaced by
`excerpt-global-start-format-string'

END-FORMAT-STRING ... #{END} will be replaced by
`excerpt-global-end-format-string'"
  :type '(repeat
	  (list :tag "Definiton"
		(choice :tag "Mode"
			(regexp :tag "Source file pattern")
			(symbol :tag "Symbol"))
		(string :tag "Source start string")
		(string :tag "Source end string")
		(repeat
		 (choice :tag "Props"
			 (list :tag "Don't add buffer local variables"
			       :value (:no-buffer-local-vars t)
			       (const :format "" :value :no-buffer-local-vars)
			       (boolean :tag "Boolean" :value t))))))
  :group 'excerpt)

(defcustom excerpt-allow-eval-functions
  'ask
  "*Allow the evaluation of functions in pseudo excerpts.
This option has currently been disabled -- it's value is 'ask'."
  :type '(choice :tag "Select"
		 (symbol :tag "Yes" :value yes)
		 (symbol :tag "No"  :value no)
		 (symbol :tag "Ask" :value ask))
  :group 'excerpt)
(put 'excerpt-allow-eval-functions 'risky-local-variable t)

(defcustom excerpt-allow-eval-variables
  'yes
  "*Allow the evaluation of variables in pseudo excerpts.
This option has currently been disabled -- it's value is 'ask'."
  :type '(choice :tag "Select"
		 (symbol :tag "Yes" :value yes)
		 (symbol :tag "No"  :value no)
		 (symbol :tag "Ask" :value ask))
  :group 'excerpt)
(put 'excerpt-allow-eval-variables 'risky-local-variable t)

(defcustom excerpt-converters
  '((emacs-wiki-mode
     (LaTeX-mode
      (:fn (lambda () (tellib-not-yet-implemented 'excerpt-convertor))))))
  "*A list of of convertors.
Format:  \((from-mode (to-mode (:fn function) ...) ...) )
+++Not yet implemented.
"
  :type '(repeat
	  (cons :value nil
		(symbol :tag "From Mode" :value nil)
		(repeat
		 (list :value nil
		       (symbol :tag "To Mode" :value nil)
		       (repeat
			(choice
			 (list :tag "Converter" :value (:fn)
			       (const :format "" :value :fn)
			       (function :tag "Function" :value nil))
			 ))))))
  :group 'excerpt)
(put 'excerpt-converters 'risky-local-variable t)

(defcustom excerpt-verbosity 1
  "*Verbosity of messages."
  :type 'integer
  :group 'excerpt)


;; Vars etc.

(defvar excerpt-pseudo-excerpt-list
  `(("*FUNCTION*"
     (:name function)
     (:read (read-from-minibuffer "Function: " nil nil #'intern-soft))
     (:pred (lambda (x)
	      (if (listp x)
		  (fboundp (car x))
		(fboundp x))))
     (:eval eval)
     (:allow ask)
     ;;(:allow ,excerpt-allow-eval-functions)
     (:quote "#'"))
    ("*VARIABLE*"
     (:name variable)
     (:read (read-from-minibuffer "Variable: " nil nil #'intern-soft))
     (:pred (lambda (x) (boundp x)))
     (:eval eval)
     (:allow ask)
     ;;(:allow ,excerpt-allow-eval-variables)
     (:quote "'")))
  "A alist of pseudo-excerpts.
By default the user will *always* be queried if a pseudo excerpt should
be evaluated. Use one of the following to change this:
	\(defalias 'excerpt-pseudo-eval-decide 'excerpt-pseudo-eval-query)
	\(defalias 'excerpt-pseudo-eval-decide 'excerpt-pseudo-eval-check)
	\(defalias 'excerpt-pseudo-eval-decide 'excerpt-pseudo-eval-allow)
	\(defalias 'excerpt-pseudo-eval-decide 'excerpt-pseudo-eval-deny)
")

(defvar excerpt-start-format-string nil)
(defvar excerpt-end-format-string nil)
(defvar excerpt-start-string nil)
(defvar excerpt-end-string nil)
(defvar excerpt-last-id "")
(defvar excerpt-last-id-3 nil)

(defvar excerpt-names nil)
(defvar excerpt-categories nil)
(defvar excerpt-categories-file nil)

(defvar excerpt-headless-copy-function-nested nil)

(defvar excerpt-buffer-categories-file nil)
(make-variable-buffer-local 'excerpt-buffer-categories-file)

(defvar excerpt-non-intrusive-source-marks nil)
(make-variable-buffer-local 'excerpt-non-intrusive-source-marks)

(defvar excerpt-headless-excerpts nil)
(make-variable-buffer-local 'excerpt-headless-excerpts)

(defvar excerpt-sources nil
  "Either a file name or a directory name where excerpt sources are located.")
(make-variable-buffer-local 'excerpt-sources)

(defvar excerpt-update-flag nil
  "If non-nil, update all excerpt after opening.
Of course, this means that the buffer will always modified.")
(make-variable-buffer-local 'excerpt-update-flag)

(defface excerpt-hyper-face
  '((t
     ;;(:foreground "blue" :background "yellow")
     (:background "grey85")
     ))
  "Face for marking excerpts."
  :group 'excerpt)

(defface excerpt-hyper-header-face
  '((t
     ;;(:foreground "darkblue" :background "orange")
     (:background "grey70")
     ))
  "Face for marking excerpt headers."
  :group 'excerpt)

(defface excerpt-source-face
  '((t
     ;;(:background "AntiqueWhite1")
     (:background "AntiqueWhite")
     ))
  "Face for marking source headers."
  :group 'excerpt)

(defface excerpt-source-header-face
  '((t
     ;;(:background "yellow")
     ;;(:background "grey85")
     (:background "AntiqueWhite3")
     ))
  "Face for marking source headers."
  :group 'excerpt)

(defvar excerpt-ref-local-map
  (let ((map (make-sparse-keymap)))
    (define-key map [return] 'excerpt-find-source-at-point)
    (when excerpt-bind-space-to-update-flag
      (define-key map [space] 'excerpt-update-excerpt-at-point))
    (define-key map excerpt-mouse-button 'excerpt-refmenu-at-mouse)
    map)
  "Local map referring to SOURCE-FILE.")

(defvar excerpt-src-local-map
  (let ((map (make-sparse-keymap)))
    (define-key map excerpt-mouse-button 'excerpt-srcmenu-at-mouse)
    map)
  "Local map for source marks.")


;; Utils

(defun excerpt-get-id-at-cat (cat id)
  "Return the compound name for ID and CAT."
  (concat cat excerpt-id-connect id))

(defun excerpt-find-file (filename &optional no-select-flag cat name)
  "Open an excerpt's source file."
  (catch 'exit
    (let ((buff (find-buffer-visiting filename)))
      (when (or buff
		(file-readable-p filename))
	(let ((rv (cond
		   ((and buff no-select-flag)
		    buff)
		   (buff
		    (switch-to-buffer buff)
		    buff)
		   (no-select-flag
		    (find-file-noselect filename t))
		   (t
		    (find-file filename)))))
	  (when (and cat name)
	    (beginning-of-buffer)
	    (let* ((fname buffer-file-name)
		   (def   (excerpt-get-fsdef-entry fname)))
	      (when def
		(let ((sfs (excerpt-format-format-string
			    (excerpt-get-start-format-string fname def)
			    "#{START}"
			    (excerpt-use-this-start-string)
			    cat
			    name)))
		  (tellib-re-search sfs t)))))
	  (throw 'exit rv)))
      (tellib-message 1 'excerpt "Can't goto to %s: %s"
		      (excerpt-get-id-at-cat cat name)
		      filename))))


;; Access to `excerpt-pseudo-excerpt-list'

(defun excerpt-is-valid-pseudo-name-p (name)
  "Return non-nil if NAME is a valid pseudo excerpt name."
  (assoc name excerpt-pseudo-excerpt-list))
;;test: (excerpt-is-valid-pseudo-name-p "*FUNCTION*")
;;test: (excerpt-is-valid-pseudo-name-p "*NOPE*")

(defun excerpt-pseudo-get-field (name field &optional default entry)
  "Get NAME's FIELD in `excerpt-pseudo-excerpt-list'."
  (let ((rv (tellib-alist-get (cdr (or entry
				       (assoc name excerpt-pseudo-excerpt-list)))
			      field
			      default
			      t)))
    (if rv
	rv
      (tellib-error 'error "Unknown pseudo-excerpt NAME or FIELD" name field))))
;;test: (excerpt-pseudo-get-field "*FUNCTION*" :read)
;;test: (excerpt-pseudo-get-field "*ERROR*" :read)


(defun excerpt-pseudo-eval-query (category src)
  "When evaluating a pseudo excerpt, ask user."
  (y-or-n-p (format "Excerpt: Allow eval: %S? " src)))

(defun excerpt-pseudo-eval-deny (category src)
  "When evaluating a pseudo excerpt, deny it."
  (tellib-message 1 'excerpt "Deny evaluation of: " src)
  nil)

(defun excerpt-pseudo-eval-allow (category src)
  "When evaluating a pseudo excerpt, allow it."
  (tellib-message 1 'excerpt "Allow evaluation of: " src)
  t)

(defun excerpt-pseudo-eval-check (category src)
  "When evaluating pseudo excerpts, lookup in `excerpt-pseudo-excerpt-list'."
  (case (excerpt-pseudo-get-field category :allow)
    ((ask)
     (excerpt-pseudo-eval-query category src))
    ((yes)
     (excerpt-pseudo-eval-allow category src))
    (t
     (excerpt-pseudo-eval-deny category src))))

(defalias 'excerpt-pseudo-eval-decide 'excerpt-pseudo-eval-query)
;(defalias 'excerpt-pseudo-eval-decide 'excerpt-pseudo-eval-check)
;(defalias 'excerpt-pseudo-eval-decide 'excerpt-pseudo-eval-allow)
;(defalias 'excerpt-pseudo-eval-decide 'excerpt-pseudo-eval-deny)

(defun excerpt-pseudo-eval (category src)
  "Evaluate a pseudo-excerpt's source.
TODO: Deal with security issues."
  (when (excerpt-pseudo-eval-decide category src)
    (funcall (excerpt-pseudo-get-field category :eval)
	     (eval src))))
;;test: (excerpt-pseudo-eval "*VARIABLE*" 'running-xemacs)
;;test: (excerpt-pseudo-eval "*FUNCTION*" #'(identity 1))

(defun excerpt-get-type (source)
  "Get the type for excerpt source in SOURCE."
  (cond
   ((stringp source)
    (let ((pseudo (tellib-ormap
		   (lambda (this)
		     (string-match
		      (concat "^"
			      (regexp-quote
			       (excerpt-pseudo-get-field "" :quote nil this)))
		      source))
		   excerpt-pseudo-excerpt-list)))
      (if pseudo
	  (excerpt-pseudo-get-field "" :name nil (car pseudo))
	'excerpt)))
   ((function source)
    'function)
   ((symbolp source)
    'variable)))
;;test: (excerpt-get-type "excerpt")
;;test: (excerpt-get-type "'var")
;;test: (excerpt-get-type "#'fun")
;;test: (excerpt-get-type #'funcall)
;;test: (excerpt-get-type 'fun)


;; Access to `excerpt-format-strings'

(defun excerpt-get-fsdef-entry (filename &optional def)
  "Get the `excerpt-format-strings' DEF for FILENAME."
  (or def
      (some (lambda (this)
	      (let ((mode-def (nth 0 this)))
		(when (or (and (stringp mode-def)
			       (string-match mode-def filename))
			  (and (symbolp mode-def)
			       (equal major-mode mode-def)))
		  this)))
	    excerpt-format-strings)))

(defun excerpt-get-fsdef (filename &optional def position default)
  "Get the POSITION element of `excerpt-format-strings' DEF for FILENAME."
  (let ((this (excerpt-get-fsdef-entry filename def)))
    (if this
	(or (nth position this)
	    default)
      (tellib-error 'error
		    "excerpt: " 
		    filename
		    " doesn't match any entry in `excerpt-format-strings'"))))

(defun excerpt-get-start-format-string (filename &optional def)
  "Get the start-format-string (see `excerpt-format-strings') for FILENAME."
  (excerpt-get-fsdef filename def 1))
;;test: (excerpt-get-start-format-string buffer-file-name)

(defun excerpt-get-end-format-string (filename &optional def)
  "Get the end-format-string (see `excerpt-format-strings') for FILENAME."
  (excerpt-get-fsdef filename def 2))
;;test: (excerpt-get-end-format-string buffer-file-name)

(defun excerpt-get-fsdef-props (prop filename &optional def default carp)
  "Get file-properties for FILENAME -- use DEF if provided."
  (tellib-alist-get (excerpt-get-fsdef filename def 3)
		    prop
		    default
		    carp))

(defun excerpt-use-this-start-string ()
  "Select global or local start-format-string."
  (or excerpt-start-format-string
      excerpt-global-start-format-string))

(defun excerpt-use-this-end-string ()
  "Select global or local start-format-string."
  (or excerpt-end-format-string
      excerpt-global-end-format-string))

(defun excerpt-use-this-format-start-string ()
  "Select global or local start-format-string."
  (or excerpt-start-string
      excerpt-global-start-format-string))

(defun excerpt-use-this-format-end-string ()
  "Select global or local start-format-string."
  (or excerpt-end-string
      excerpt-global-end-format-string))


;; Get marks
(defun excerpt-format-format-string (format what string
					    &optional name id non-literal-flag)
  "Helper function: format marks"
  (let ((txt format))
    (mapc #'(lambda (this)
	      (let ((fs (car this))
		    (rs (cadr this)))
		(when rs
		  (setq txt (replace-in-string txt (regexp-quote fs) rs t)))))
	  `(("#{COMMENT-START}" ,(or comment-start ""))
	    ("#{COMMENT-END}"   ,(or comment-end ""))
	    (,what              ,string)
	    ("#{NAME}"          ,id)
	    ("#{CATEGORY}"      ,name)))
    txt))
;;test: (excerpt-format-format-string "#{END}" "#{END}" "\\(.+\\)")
;;test: (excerpt-format-format-string
;;       "#{COMMENT-START}---(:excerpt #{CATEGORY})@#{START}---#{COMMENT-END}"
;;       "#{START}" "\\(.+\\)" "cat" "id")
;;test: (excerpt-format-format-string
;;       "<!-- ---(:excerpt #{CATEGORY})@(:begin #{NAME})--- -->"
;;       nil nil "\\(.+\\)" "\\(.+\\)")
;;test: (excerpt-format-format-string
;;       "#{COMMENT-START}---(:excerpt #{CATEGORY})@#{START}---#{COMMENT-END}"
;;       nil nil "\\(.+\\)" "\\(.+\\)")

(defun excerpt-auto-id ()
  "Get an automatic id based on current time."
  (let* ((id (apply 'format (cons "%x%x" (current-time)))))
    (if (string-equal id excerpt-last-id)
	(progn
	  (setq excerpt-last-id-3 (+ excerpt-last-id-3 1))
	  (apply 'format (list "%s:%x" id excerpt-last-id-3)))
      (progn
	(setq excerpt-last-id id)
	(setq excerpt-last-id-3 0)
	id))))
;;test: (excerpt-auto-id)

(defun excerpt-source-start-string (format-start id name)
  "Format excerpt source start mark"
  (if excerpt-start-string
      (excerpt-format-format-string excerpt-start-string
				    nil
				    nil
				    name id)
    (excerpt-format-format-string format-start
				  "#{START}" 
				  (excerpt-use-this-start-string)
				  name id)))

(defun excerpt-source-end-string (format-end id name)
  "Format excerpt source end mark"
  (if excerpt-end-string
      (excerpt-format-format-string excerpt-end-string
				    nil
				    nil
				    name id)
    (excerpt-format-format-string format-end
				  "#{END}"
				  (excerpt-use-this-end-string)
				  name id)))


;; Categories

(defun excerpt-read-categories-file (filename)
  (unless (tellib-lax-plist-get excerpt-categories filename)
    (setq excerpt-categories
	  (tellib-lax-plist-put 
	   excerpt-categories
	   (expand-file-name filename)
	   (mapcar (lambda (x) (list x))
		   (with-temp-buffer
		     (insert-file-contents filename)
		     (remove* "[^ \t]" (split-string (buffer-string) "\n")
			      :test-not (lambda (match txt)
					  (string-match match txt)))))))))

(defun excerpt-set-categories (&optional file-name)
  "Set categories for current buffer."
  (when (or file-name (not excerpt-buffer-categories-file ))
    (setq excerpt-buffer-categories-file
	  (expand-file-name (or file-name
				excerpt-categories-file
				excerpt-global-categories-file)))
    (excerpt-read-categories-file excerpt-buffer-categories-file)))

(defun excerpt-get-categories ()
  "Get current buffer's categories."
  (tellib-lax-plist-get excerpt-categories 
			excerpt-buffer-categories-file))

(defun excerpt-put-new-category (name)
  "Add a new category."
  (setq excerpt-categories
	(tellib-lax-plist-put 
	 excerpt-categories
	 excerpt-buffer-categories-file
	 (cons `(,name t) (excerpt-get-categories)))))
;;test: (excerpt-put-new-category "test")

(defun excerpt-change-categories-file ()
  "Change the buffer's categories file."
  (interactive)
  (let ((nf (read-file-name "Use categories from: ")))
    (when nf
      (tellib-update-local-variable-def "excerpt-categories-file" nf)
      (excerpt-set-categories nf))))


;; Names

(defun excerpt-get-names (category)
  "Get a category's names."
  (tellib-lax-plist-get excerpt-names category))
;;test: (excerpt-get-names "test")

(defun excerpt-name-is-defined-p (category name)
  "Check whether NAME is already defined for CATEGORY."
  (member name (excerpt-get-names category)))
;;test: (excerpt-name-is-defined-p "test" "a")
;;test: (excerpt-name-is-defined-p "test" "c")

(defun excerpt-add-name (category name)
  "Add a new NAME to CATEGORY."
  (let ((lst (excerpt-get-names category)))
    (unless (member name lst)
      (setq excerpt-names
	    (tellib-lax-plist-put 
	     excerpt-names
	     category
	     (cons name lst))))))
;;test: (excerpt-add-name "test" "a")
;;test: (excerpt-add-name "test" "b")


;; Source file

(defun excerpt-make-rx-from-format-string (string &optional name id)
  "Turn a format STRING into a valid regexp."
  (excerpt-format-format-string (regexp-quote string) nil nil
				(or name
				    "\\(.+\\)")
				(or id
				    "\\(.+\\)")))
;;test: (excerpt-make-rx-from-format-string
;;       "<!-- ---(:excerpt #{CATEGORY})@(:begin #{NAME})--- -->")
;;test: (excerpt-make-rx-from-format-string
;;       "#{COMMENT-START}---(:excerpt #{CATEGORY})@#{START}---#{COMMENT-END}")

(defun excerpt-filename->name (filename)
  "Turn FILENAME into a proper category name."
  (replace-in-string (file-name-sans-extension
		      (file-name-nondirectory filename))
		     "\\W"
		     "_"))

(defun excerpt-source-collect (&optional filename buffer name0 id0)
  "Return a list of regions containing source marks.
If NAME0 and ID0 are provided, only this one excerpt is being collected."
  (save-excursion
    (save-restriction
      (let* ((fname (or filename buffer-file-name))
	     (def   (excerpt-get-fsdef-entry fname)))
	(if def
	    (let ((buff (or buffer
			    (excerpt-find-file fname t))))
	      (when buff
		(set-buffer buff)
		(widen)
		(let* ((sfs (excerpt-format-format-string
			     (excerpt-get-start-format-string fname def)
			     "#{START}"
			     (excerpt-use-this-start-string)))
		       (efs (excerpt-format-format-string
			     (excerpt-get-end-format-string fname def)
			     "#{END}"
			     (excerpt-use-this-end-string)))
		       (rsfs (excerpt-make-rx-from-format-string sfs))
		       ;; (refs (excerpt-make-rx-from-format-string efs))
		       (coll (excerpt-source-collect-non-intrusive buff)))
		  (beginning-of-buffer)
		  ;;(message "DEBUG: %S %S" sfs rsfs)(sleep-for 3)
		  ;;(message "DEBUG: %S %S" (point) rsfs)(sleep-for 3)
		  (while (tellib-re-search rsfs t)
		    (let* ((beg  (match-beginning 0))
			   (begx (+ (match-end 0) 1))
			   (name (match-string 1))
			   (id   (match-string 2))
			   (refs (excerpt-make-rx-from-format-string
				  efs name id)))
		      (save-excursion
			(unless (string-equal id "#{NAME}")
			  (let* ((endx (progn
					 (tellib-re-search refs t)
					 (match-beginning 0)))
				 (end  (progn
					 (goto-char endx)
					 (point-at-bol 2))))
			    (when (or (not (and name0 id0))
				      (and (equal name0 name)
					   (equal id0 id)))
			      (setq coll
				    (append coll
					    `(,(list :category name
						     :name   id
						     :beg  beg
						     :end  end
						     :begx begx
						     :endx endx
						     :text (buffer-substring 
							     begx endx)))
					    ))))))))
		  (append coll
			  (when (or (not (and name0 id0))
				    (equal name0 "*FILE*"))
			    `(,(list :category "*FILE*"
				     :name   (excerpt-filename->name fname)
				     :beg  (point-min)
				     :end  (point-max)
				     :begx (point-min)
				     :endx (point-max)
				     :text (buffer-substring 
					     (point-min) (point-max)))))
			    )))))))))


;; Main file

(defun excerpt-get-beg-mark (mode category name source 
				  &optional prefix type process)
  "Return main file's mark header."
;	<comment-string>(:excerpt CATEGORY :name NAME \
;				[:type TYPE] [:process FN])
;	<comment-string>(:excerpt-source SOURCE)
  (let ((inserter #'(lambda (name val)
		      (cond
		       ((and val (equal mode 'insert))
			(format " %s %s" name val))
		       ((and val (equal mode 'match))
			(format " *?\\(%s %s\\)?" name val))
		       (t
			""))))
	(prefix (or prefix "")))
    (concat (if (equal mode 'insert) prefix "")
	    comment-start
	    "---("
	    (format ":excerpt-beg %s :name %s" category name)
	    ;;(funcall inserter ":type" type)
	    (funcall inserter ":type" nil)
	    (funcall inserter ":process" process)
	    ")---" comment-end "\n"
	    prefix
	    comment-start
	    (format "---(:excerpt-source %s)---"
		    (case type
		      ((excerpt)
		       (tellib-quote source))
		      (t
		       source)))
	    comment-end "\n")))

(defun excerpt-get-end-mark (category name &optional prefix)
  "Return main file's mark footer."
;	<comment-string>(:excerpt-end CATEGORY :name NAME)
  (let ((prefix (or prefix "")))
    (concat prefix
	    comment-start
	    (format "---(:excerpt-end %s :name %s)---" category name)
	    comment-end "\n")))

(defun excerpt-parse-source (string &optional type)
  "Return the proper source object from a string.
If type is 'excerpt, the string will be returned as is."
  ;;(message "DEBUG: %S" string)(sleep-for 3)
  (cond
   ((equal type 'excerpt)
    string)
   (string
    (car (read-from-string string)))
   (t
    nil)))
;;test: (excerpt-parse-source nil)
;;test: (excerpt-parse-source "'sym")
;;test: (excerpt-parse-source "#'fun")
;;test: (excerpt-parse-source "test" 'excerpt)

(defun excerpt-find-next-excerpt (&optional reverse-direction-flag cat name)
  "Find the *next* excerpt."
  (interactive "P")
  (let ((nnie
	 (let ((ols (tellib-overlay-collect* '(excerpt-ref-headless-excerpt)))
	       (pos (point))
	       nextpos
	       nextol)
	   (mapc #'(lambda (this)
		     (let ((beg (overlay-start this)))
		       (when (and (<= pos beg)
				  (or (not nextpos)
				      (< beg nextpos)))
			 (setq nextpos beg
			       nextol  this))))
		 ols)
	   (when nextol
	     (let ((src  (overlay-get nextol 'excerpt-reference))
		   (type (overlay-get nextol 'excerpt-ref-type)))
	       (list :beg      nextpos
		     :end      (overlay-end nextol)
		     :begtxt   (overlay-get nextol 'excerpt-ref-begtxt)
		     :endtxt   (overlay-get nextol 'excerpt-ref-endtxt)
		     :category (overlay-get nextol 'excerpt-ref-cat)
		     :name     (overlay-get nextol 'excerpt-ref-name)
		     :prefix   (overlay-get nextol 'excerpt-ref-prefix)
		     :headless t
		     ;;:process  (or proc 'identity)
		     :type     type
		     :rawsrc   src
		     :source   (excerpt-parse-source src type))))))
	(ne
	 (let ((bs   (excerpt-get-beg-mark 'match
					   (format "\\(%s\\)" (if cat
								  (regexp-quote cat)
								".+?"))
					   (format "\\(%s\\)" (if name
								  (regexp-quote name)
								".+?"))
					   "\\(.+\\)";; source
					   ".*";; prefix
					   ;; "\\(.+?\\)" ;; type
					   ;; "\\(.+?\\)" ;; process
					   )))
	   (when (tellib-re-search bs t reverse-direction-flag)
	     (let* ((bp    (match-beginning 0))
		    (be    (match-end 0))
		    (cat   (or cat (match-string 1)))
		    (name  (or name (match-string 2)))
		    ;; (type  (match-string 4))
		    ;; (proc  (match-string 6))
		    ;; (src   (match-string 7))
		    ;;(proc  nil)
		    (src   (match-string 3))
		    (type  (excerpt-get-type src))
		    (prfx  (save-excursion
			     (goto-char bp)
			     (buffer-substring (point-at-bol) (point))))
		    (prfxl (length prfx))
		    (es    (excerpt-get-end-mark (regexp-quote cat)
						 (regexp-quote name)))
		    (ep    (save-excursion
			     (goto-char be)
			     (tellib-re-search es t)
			     (match-beginning 0)))
		    (ee    (match-end 0)))
	       (when ee
		 (list :beg      (- bp prfxl)
		       :end      ee
		       :begtxt   be
		       :endtxt   (- ep prfxl)
		       :category cat
		       :name     name
		       :prefix   prfx
		       ;;:process  (or proc 'identity)
		       :type     type
		       :rawsrc   src  
		       :source   (excerpt-parse-source src))))))))
    (let* ((ex  (1+ (point-max)))
	   (nib (plist-get nnie :beg ex))
	   (neb (plist-get ne :beg ex))
	   (rv  (cond
		 ((<= nib neb) nnie)
		 ((> nib neb)  ne)
		 (t            nil))))
      (when rv
	(goto-char (plist-get rv :end)))
      rv)))

(defun excerpt-remove-excerpt (ol beg end)
  "Remove excerpt covered by overlay OL."
  (overlay-put ol 'read-only nil)
  (delete-region beg end))
   
(defun excerpt-source-mark-highlight (beg beg-txt end-txt end &optional
					  buffer cat name non-intrusive-flag)
  "Highlight the region BEG to END as source mark."
  (let ((marker (lambda (beg end face)
		  (when (and beg end)
		    (let ((ol (make-overlay beg end buffer)))
		      (overlay-put ol 'face face))))))
    (funcall marker beg beg-txt 'excerpt-source-header-face)
    (funcall marker beg-txt end-txt 'excerpt-source-face)
    (funcall marker end-txt end 'excerpt-source-header-face)
    (when (and name cat
	       non-intrusive-flag)
      (let ((ol (make-overlay beg-txt end-txt buffer)))
	(overlay-put ol 'local-map excerpt-src-local-map)
	(overlay-put ol 'excerpt-source-ni-flag t)
	(overlay-put ol 'excerpt-source-cat     cat)
	(overlay-put ol 'excerpt-source-name    name)
	(overlay-put ol 'excerpt-source-beg     beg)
	(overlay-put ol 'excerpt-source-end     end)
	(overlay-put ol 'excerpt-source-beg-txt beg-txt)
	(overlay-put ol 'excerpt-source-end-txt end-txt)))))

(defun excerpt-source-collect-non-intrusive (&optional buffer)
  "Return a list with non-intrusive source marks."
  (let* ((all-ol  (overlay-lists))
	 (ol-pre  (car all-ol))
	 (ol-post (cdr all-ol))
	 (ols     (append ol-pre ol-post))
	 (rv      nil))
    (mapc #'(lambda (this)
	      (let* ((cat  (overlay-get this 'excerpt-source-cat))
		     (name (overlay-get this 'excerpt-source-name))
		     ;;(beg  (overlay-get this 'excerpt-source-beg))
		     ;;(end  (overlay-get this 'excerpt-source-end))
		     ;;(begx (overlay-get this 'excerpt-source-beg-txt))
		     ;;(endx (overlay-get this 'excerpt-source-end-txt))
		     (nif  (overlay-get this 'excerpt-source-ni-flag))
		     (begx (overlay-start this))
		     (endx (overlay-end this))
		     beg end
		     )
		(when (and nif cat name)
		  (add-to-list 'rv
			       (list :category cat
				     :name   name
				     :beg  beg
				     :end  end
				     :begx begx
				     :endx endx
				     :text (buffer-substring 
					    begx endx buffer))))))
	  ols)
    rv))

(defun excerpt-use-file-local-variable-check (&optional file)
  "Determine how to store non-intrusive marks
\(see `excerpt-use-file-local-variable').
Returns a list containing one or more symbols: 'file-local and 'file-properties."
  (let ((fl (or file 
		(buffer-file-name))))
    (tellib-some (lambda (this)
		   (let ((rx  (car this))
			 (val (cdr this)))
		     (when (string-match rx fl)
		       val)))
		 excerpt-use-file-local-variable)))
;;(setq excerpt-use-file-local-variable '((".*" file-properties file-local)))
;;(setq excerpt-use-file-local-variable '((".*" file-properties)))
;;test: (excerpt-use-file-local-variable-check)

(defun excerpt-source-write-non-intrusive ()
  "Update buffer-local variables to include non-intrusive excerpts."
  (let ((mode (excerpt-use-file-local-variable-check))
	(nies    (excerpt-source-collect-non-intrusive)))
    (when (member 'file-local mode)
      (let ((counter 1)
	    (fn      (lambda (n var val)
		       (tellib-update-local-variable-def (format "%s-%s" var n)
							 val))))
	(mapc #'(lambda (this)
		  (let ((name (plist-get this :name))
			(cat  (plist-get this :category))
			(begx (plist-get this :begx))
			(endx (plist-get this :endx)))
		    (funcall fn counter "excerpt-ni-cat"  cat)
		    (funcall fn counter "excerpt-ni-name" name)
		    (funcall fn counter "excerpt-ni-begx" begx)
		    (funcall fn counter "excerpt-ni-endx" endx)
		    (setq counter (+ counter 1))))
	      nies)))
    (when (member 'file-properties mode)
      (unless (null nies)
	(file-properties-add 'excerpt-non-intrusive-source-marks)
	(setq excerpt-non-intrusive-source-marks nies)))
    nil))
;;test:: (excerpt-source-write-non-intrusive)

(defun excerpt-source-read-non-intrusive (&optional buffer)
  "Read non-intrusive excerpts definitions from buffer-local variables."
  ;;(message "DEBUG: %S" excerpt-non-intrusive-source-marks)(sleep-for 3)
  (let ((mode (excerpt-use-file-local-variable-check)))
    (when (member 'file-local mode)
      (let* ((names (tellib-scan-variables 'excerpt-ni-name nil nil buffer))
	     (cats  (tellib-scan-variables 'excerpt-ni-cat  nil nil buffer))
	     (begxs (tellib-scan-variables 'excerpt-ni-begx nil nil buffer))
	     (endxs (tellib-scan-variables 'excerpt-ni-endx nil nil buffer))
	     (excs  (tellib-zip cats names begxs endxs)))
	(mapc #'(lambda (this)
		  (excerpt-source-mark-highlight nil
						 (nth 2 this)
						 (nth 3 this)
						 nil
						 buffer
						 (nth 0 this)
						 (nth 1 this)
						 t))
	      excs)))
    (when (member 'file-properties mode)
      (dolist (this excerpt-non-intrusive-source-marks)
	;;BEG BEG-TXT END-TXT END &optional BUFFER CAT NAME NON-INTRUSIVE-FLAG
	(excerpt-source-mark-highlight nil
				       (plist-get this :begx)
				       (plist-get this :endx)
				       nil
				       buffer
				       (plist-get this :category)
				       (plist-get this :name)
				       t)
	))))
;;test:: (excerpt-source-read-non-intrusive)

(defun excerpt-overlay-copy-function (overlay beg end)
  "Return nil if the extent should not be copied."
  ;;(message "DEBUG cf: %s %s %s" beg end overlay)
  (if excerpt-headless-copy-function-nested
      t
    (let ((excerpt-headless-copy-function-nested t))
      (string= (buffer-substring beg end)
	       (buffer-substring (overlay-start overlay) (overlay-end overlay))))))

(defun excerpt-define-headless-excerpt (overlay)
  "Add a headless excerpt definition to `excerpt-headless-excerpts'."
  (file-properties-overlay-add 'excerpt-ref-headless-excerpt)
  (overlay-put overlay 'excerpt-ref-headless-excerpt t)
  (overlay-put overlay 'tellib-restore-function #'excerpt-overlay-restore-headless))

(defun excerpt-make-hyper (type source beg end begtxt endtxt cat name prefix
				&optional headless-flag overlay)
  "Mark buffer BEG to END being as a source mark referring to SOURCE."
  (let* ((ol (or overlay
		 (make-overlay beg end)))
	 (hl  (or headless-flag (overlay-get ol 'excerpt-ref-headless-excerpt)))
	 (be  (or beg (overlay-start ol)))
	 (ee  (or end (overlay-end ol)))
	 (bt  (if hl
		  be
		(or begtxt (overlay-get ol 'excerpt-ref-begtxt))))
	 (et  (if hl
		  ee
		(or endtxt (overlay-get ol 'excerpt-ref-endtxt)))))
    (overlay-put ol 'mouse-face 'highlight)
    (overlay-put ol 'evaporate t)
    (overlay-put ol 'local-map excerpt-ref-local-map)
    (overlay-put ol 'excerpt-ref-begtxt bt)
    (overlay-put ol 'excerpt-ref-endtxt et)
    (overlay-put ol 'duplicable t)
    (overlay-put ol 'copy-function #'excerpt-overlay-copy-function)
    (when type   (overlay-put ol 'excerpt-ref-type type))
    (when cat    (overlay-put ol 'excerpt-ref-cat cat))
    (when name   (overlay-put ol 'excerpt-ref-name name))
    (when prefix (overlay-put ol 'excerpt-ref-prefix prefix))
    (when source (overlay-put ol 'excerpt-reference source))
    (overlay-put ol 'face 'excerpt-hyper-face)
    (when hl
      (excerpt-define-headless-excerpt ol))
    (when excerpt-set-read-only-flag
      (overlay-put ol 'read-only t))
    ;;(let ((oli (make-overlay bt et)))
    ;;(overlay-put oli 'face 'excerpt-hyper-face)
    (let ((marker (lambda (beg end invisible-flag read-only-flag)
		    (when (/= beg end)
		      (let ((ol (make-overlay beg end)))
			(cond
			 (excerpt-invisible-header-flag
			  (when invisible-flag
			    (overlay-put ol 'invisible t))
			  (when read-only-flag
			    (overlay-put ol 'read-only t)))
			 (t
			  (overlay-put ol 'face 'excerpt-hyper-header-face))))))))
      (funcall marker be bt t t)
      (funcall marker et ee t t))))

(defun excerpt-overlay-restore-headless (overlay)
  "Turn a restored OVERLAY into a headless excerpt overlay."
  (excerpt-make-hyper nil nil nil nil
		      nil nil
		      nil nil nil
		      t overlay))

(defun excerpt-get-src-overlay-at-pos (&optional pos)
  "Get the right overlay at POS or (point) for further processing."
  (car (tellib-overlay-collect* '(excerpt-source-cat) nil
				(overlays-at (or pos (point))))))

(defun excerpt-get-ref-overlay-at-pos (&optional pos)
  "Get the right overlay at POS or (point) for further processing."
  (car (tellib-overlay-collect* '(excerpt-ref-cat) nil
				(overlays-at (or pos (point))))))

(defun excerpt-find-source-at-point (&optional pos)
  "Find source at point POS."
  (interactive)
  (let* ((ol   (excerpt-get-ref-overlay-at-pos pos))
	 (src  (overlay-get ol 'excerpt-reference))
	 (cat  (overlay-get ol 'excerpt-ref-cat))
	 (type (overlay-get ol 'excerpt-ref-type))
	 (name (overlay-get ol 'excerpt-ref-name)))
    (if src
	(case type
	  ((excerpt)
	   (excerpt-find-file src nil cat name))
	  (t
	   (tellib-error 'error "Excerpt: this is no regular excerpt")))
      (message "excerpt: Can't open file '%s'" src))))

(defun excerpt-update-excerpt-at-point (&optional pos)
  "Update the excerpt at point or POS."
  (interactive)
  (let* ((ol   (excerpt-get-ref-overlay-at-pos pos))
	 (cat  (overlay-get ol 'excerpt-ref-cat))
	 (name (overlay-get ol 'excerpt-ref-name))
	 (beg  (overlay-start ol))
	 (end  (overlay-end ol)))
    ;;(message "DEBUG: %s %s %s %s %s" pos cat name beg end)
    (excerpt-update-current beg end nil cat name)))

(defun excerpt-setup-source-marks (&optional buffer)
  "Highlight all source marks in the current buffer."
  (interactive)
  (excerpt-source-read-non-intrusive buffer)
  (save-excursion
    ;; (when buffer (set-buffer buffer))
    (beginning-of-buffer)
    (let ((marks (excerpt-source-collect (buffer-file-name) buffer)))
      (mapc #'(lambda (this)
		(let ((name (plist-get this :category))
		      (beg  (plist-get this :beg))
		      (begx (plist-get this :begx))
		      (end  (plist-get this :end))
		      (endx (plist-get this :endx)))
		  (unless (equal name "*FILE*")
		    (excerpt-source-mark-highlight beg begx endx end buffer))))
	    marks))))

(defun excerpt-setup-all-excerpt (&optional buffer)
  "Set faces and text properties for all excerpts."
  (interactive)
  (let ((buffer (or buffer (current-buffer))))
    (save-excursion
      (when buffer (set-buffer buffer))
      (excerpt-setup-source-marks buffer)
      (if excerpt-update-flag
	  (excerpt-update)
	;;(message "DEBUG: %S" buffer)(sleep-for 3)
	(beginning-of-buffer)
	(catch 'end
	  (while t
	    (let ((this (excerpt-find-next-excerpt)))
	      (if this
		  (let ((beg    (plist-get this :beg))
			(end    (plist-get this :end)))
		    (excerpt-make-hyper (plist-get this :type)
					(plist-get this :source)
					beg
					end
					(plist-get this :begtxt)
					(plist-get this :endtxt)
					(plist-get this :category)
					(plist-get this :name)
					(plist-get this :prefix))
		    (goto-char (+ end 1)))
		(throw 'end t)))))))))

(defun excerpt-add-source-ref (def beg end)
  "Add an excerpt to `excerpt-sources-refs-db'.
DEF is the source definition as returned by `excerpt-source-collect'.
BEG and END refer to the citation.

+++TBD
"
  nil)


;; Core Commands

(defun excerpt-info ()
  (interactive)
  (tellib-info "excerpt"))

(defun excerpt-update-source-marks (&optional dont-replace-flag)
  "Update local variable definitions of excerpt start and end marks
If DONT-REPLACE-FLAG is non-nil, don't replace already existing definitions."
  (interactive "P")
  (tellib-update-local-variable-def 
   "excerpt-start-string"
   (excerpt-format-format-string
    (excerpt-get-start-format-string buffer-file-name)
    "#{START}"
    (excerpt-use-this-start-string))
   :dont-replace t)
  (tellib-update-local-variable-def 
   "excerpt-end-string"
   (excerpt-format-format-string
    (excerpt-get-end-format-string buffer-file-name)
    "#{END}"
    (excerpt-use-this-end-string))
   :dont-replace t))
(put 'excerpt-update-source-marks 'tellib-unimportant t)

;;;###autoload
(defun excerpt-source (beg end &optional id non-intrusive-flag)
  "Mark current region as excerpt source"
  (interactive "r")
  (when (or buffer-file-name
	    (and (when (yes-or-no-p "File has not been saved. Save now? ")
		   (save-buffer))
		 buffer-file-name))
    (save-excursion
      (save-restriction
	(let* ((def (excerpt-get-fsdef-entry buffer-file-name))
	       (upd (not (excerpt-get-fsdef-props :no-buffer-local-vars
						  buffer-file-name
						  def
						  nil
						  t)))
	       (sfs (when def
		      (excerpt-get-start-format-string buffer-file-name def)))
	       (efs (when def
		      (excerpt-get-end-format-string buffer-file-name def))))
	  (excerpt-set-categories)
	  (if (and sfs efs)
	      (let* ((name (tellib-simplify-string
			    (let ((this (completing-read
					 "excerpt: Category: "
					 (excerpt-get-categories))))
			      (if (string-equal this "")
				  "default"
				this))
			    "[@.: ]"))
		     (id   (tellib-simplify-string
			    (or id
				(excerpt-auto-id))
			    "[@.: ]")))
		(unless (some (lambda (a) (string-equal (car a) name))
			      (excerpt-get-categories))
		  (excerpt-put-new-category name))
		(let ((bh (excerpt-source-start-string sfs id name))
		      (eh (excerpt-source-end-string efs id name))
		      beg-hdr beg-txt end-txt end-hdr)
		  (goto-char beg)
		  (unless non-intrusive-flag
		    (setq beg-hdr (point))
		    (insert bh)
		    (newline))
		  (setq beg-txt (point))
		  (goto-char (if non-intrusive-flag
				 end
			       (+ end (length bh) 1)))
		  (setq end-txt (point))
		  (unless non-intrusive-flag
		    (insert eh)
		    (newline)
		    (setq end-hdr (point)))
		  (excerpt-source-mark-highlight beg-hdr beg-txt end-txt end-hdr
						 nil name id non-intrusive-flag))
		(when upd
		  (excerpt-update-source-marks t)))
	    (tellib-error 'error "excerpt-source: sfs=" sfs "efs=" efs)))))))

;;;###autoload
(defun excerpt-named-source (beg end &optional non-intrusive-flag)
  "Mark current region as named excerpt source."
  (interactive "r")
  (let ((txt (read-from-minibuffer "Name: ")))
    (excerpt-source beg end
		    (if (string-equal txt "")
			nil
		      txt)
		    non-intrusive-flag)))

;;;###autoload
(defun excerpt-named-source-non-intrusive (beg end)
  "Mark current region as named excerpt source."
  (interactive "r")
  (excerpt-named-source beg end t))

(defun excerpt-get-source-filename (filename directory)
  "Return a filename based on `excerpt-use-relative-or-absolute-file-name'.
Any regexps will be matched against the expanded FILENAME."
  ;;(message "DEBUG: %S %S" filename directory)
  (if (and filename
	   directory)
      (catch 'exit
	(let ((lfname (expand-file-name filename))
	      (sfname (abbreviate-file-name filename t))
	      (exit (lambda (mode filename)
		      (if (equal mode 'relative)
			  (throw 'exit (file-relative-name filename directory))
			(throw 'exit filename)))))
	  (mapc #'(lambda (this)
		    (let* ((rx   (nth 0 this))
			   (abbr (nth 1 this))		  
			   (mode (nth 2 this))
			   (fname (if abbr sfname lfname)))
		      (cond
		       ((stringp rx)
			(when (string-match rx fname)
			  (funcall exit mode fname)))
		       ((listp rx)
			(let ((rxa (nth 0 rx))
			      (rxb (nth 1 rx)))
			  (when (and (string-match rxa fname)
				     (string-match rxb directory))
			    (funcall exit mode filename))))
		       ((and (equal rx 'same-dir)
			     (string= (file-name-directory lfname)
				      (expand-file-name directory)))
			(throw 'exit (file-name-nondirectory filename)))
		       ((equal rx t)
			(funcall exit mode filename)))))
		excerpt-use-relative-or-absolute-file-name)
	  filename))
    filename))

(defun excerpt-read-source-file (&optional source-file)
  "Read the source file's name from the minibuffer.
Return a list of \(full-filename directory)."
  (let* ((dir   (cond
		 ((and excerpt-sources
		       (file-directory-p excerpt-sources))
		  (file-name-as-directory excerpt-sources))
		 (excerpt-sources
		  (file-name-directory excerpt-sources))
		 (t
		  (file-name-directory (or buffer-file-name "")))))
	 (dftfl (cond
		 ((and excerpt-sources
		       (file-directory-p excerpt-sources))
		  nil)
		 (excerpt-sources
		  (file-name-nondirectory excerpt-sources))
		 (buffer-file-name
		  (file-name-nondirectory buffer-file-name))))
	 (fn    (or source-file
		    (read-file-name "Source: " dir nil t dftfl))))
    (if (or (not fn) source-file)
	fn
      (abbreviate-file-name (expand-file-name fn dir)))))
;;test: (excerpt-read-source-file)

(defun excerpt-select-excerpt (type source category name eval-flag)
  "Select an excerpt based on TYPE, SOURCE, CATEGORY, and NAME."
  (let* ((lst  (cond
		((or (equal type 'excerpt)
		     (string= type "EXCERPT"))
		 (mapcar (lambda (x)
			   (let ((id (plist-get x :name))
				 (ct (plist-get x :category)))
			     `(,(excerpt-get-id-at-cat ct id)
			       :category ,ct :name ,id :txt ,(plist-get x :text))))
			 (excerpt-source-collect source nil category name)))
		(t
		 (let ((txt (if eval-flag
				(excerpt-pseudo-eval category source)
			      "*non-evaluated*")))
		   (when txt
		     `((,(excerpt-get-id-at-cat category name)
			:category ,category :name ,name :txt ,(format "%s" txt)
			;;,(plist-get def :text)
			)))))))
	 (this  (if (and category name)
		    (excerpt-get-id-at-cat category name)
		  (completing-read "Select: " lst nil t))))
    (when this
      (cdr (assoc this lst)))))
;;test: (excerpt-select-excerpt 'pseudo #'(tellib-desc-env) "*FUNCTION*" "x" t)

;;;###autoload
(defun excerpt-insert-excerpt (&optional def beg-old end-old
					 force-prefix headless-flag)
  "Insert a excerpt mark into the main file.

Use DEF (a plist describing an excerpt) if provided. BEG-OLD and END-OLD
define the region covering the old excerpt, which should be deleted
before inserting the new one.

If HEADLESS-FLAG is non-nil, no headers will be generated. The excerpt
information will be stored as file-properties or as file local variables --
according to `excerpt-use-file-local-variable'.
"
  (interactive)
  (save-excursion
    (catch 'exit
      (let* ((bfn         buffer-file-name)
	     (currdir     (when bfn
			    (file-name-directory bfn)))
	     (rawsrc      (plist-get def :rawsrc))
	     (source      (or (plist-get def :source)
			      (excerpt-parse-source rawsrc)
			      (excerpt-read-source-file)))
	     (category    (plist-get def :category))
	     (name        (plist-get def :name))
	     (prefix      (or force-prefix
			      (plist-get def :prefix)))
	     (type        (or (plist-get def :type 'excerpt)
			      (excerpt-get-type source)))
	     ;; (process     (plist-get def :process))
	     (headless    (or headless-flag
			      (plist-get def :headless)))
	     (src
	      (cond
		((equal type 'excerpt)
		 (excerpt-get-source-filename source currdir))
		(t
		 rawsrc))))
	(when src
	  (let ((entry (excerpt-select-excerpt type source category name t)))
	    (when entry
	      (let* ((ct    (plist-get entry :category))
		     (id    (plist-get entry :name))
		     (tx    (plist-get entry :txt)))
		;;(message "DBG:%s %S %S %S %S" type src this (assoc this lst) lst)
		;;(message "DBG:%S %S %S %S %S %S" def this entry ct id tx)
		;;(sleep-for 3)
		(when (and ct id tx)
		  (when (and beg-old end-old)
		    (delete-region beg-old end-old))
		  (let* ((prefix (or prefix ""))
			 (beg    (point))
			 (end    nil)
			 (begtxt nil)
			 (endtxt nil)
			 (bmark  (excerpt-get-beg-mark 'insert ct id 
						       src prefix type))
			 (emark  (excerpt-get-end-mark ct id prefix)))
		    (unless headless
		      (insert-face bmark 'excerpt-hyper-header-face))
		    (let ((rest (tellib-split-string-by-char tx ?\n)))
		      (setq begtxt (point))
		      (while (not (null rest))
			(let ((this (car rest)))
			  (setq rest (cdr rest))
			  (if (null rest)
			      (unless (equal this "")
				(insert-face prefix 'excerpt-hyper-face)
				(insert-face this 'excerpt-hyper-face))
			    (insert-face prefix 'excerpt-hyper-face)
			    (insert-face this 'excerpt-hyper-face)
			    (newline)))))
		    (setq endtxt (point))
		    (unless headless
		      (insert-face emark 'excerpt-hyper-header-face))
		    (setq end (point))
		    (excerpt-make-hyper type src beg end begtxt endtxt 
					ct id prefix headless)
		    ;;+++ (excerpt-add-source-ref def beg end)
		    )
		  (throw 'exit t))))))
	(if (and beg-old end-old)
	    (tellib-message 1 'excerpt
			    "Can't update excerpt: %s.%s %s/%s (%s-%s)"
			    category name type source
			    beg-old end-old)
	  ;;(tellib-message 1 'excerpt "Can't insert excerpt"))))))
	  (tellib-error 'error "Excerpt: Can't insert excerpt"
			category name type source
			beg-old end-old))))))

;;;###autoload
(defun excerpt-insert-pseudo (&optional prefix)
  "Insert a pseudo excerpt."
  (interactive)
  (flet ((pseudo-read (ct)
	   (let ((rv (eval (excerpt-pseudo-get-field ct :read))))
	     (if (funcall (excerpt-pseudo-get-field ct :pred) rv)
		 rv
	       (tellib-error 'error (format "%s isn't a %s" rv ct))))))
    (let* ((ct    (completing-read "Select: " excerpt-pseudo-excerpt-list nil t))
	   (src   (pseudo-read ct))
	   (id    (read-from-minibuffer "Name: " (excerpt-auto-id))))
      (when (and ct id)
	(excerpt-insert-excerpt
	 (list :rawsrc   (format "%s%S"
				 (excerpt-pseudo-get-field ct :quote)
				 src)
	       :type     'pseudo
	       :prefix   prefix
	       :category ct
	       :name     (format "%s" id)))))))

;;;###autoload
(defun excerpt-insert-pseudo-with-prefix ()
  "Insert a pseudo excerpt with prefix."
  (interactive)
  (excerpt-insert-pseudo (read-from-minibuffer "Prefix: ")))

;;;###autoload
(defun excerpt-insert-with-prefix ()
  "Insert a prefixed excerpt."
  (interactive)
  (excerpt-insert-excerpt nil nil nil (read-from-minibuffer "Prefix: ")))

(defun excerpt-insert ()
  "Insert an excerpt."
  (interactive)
  (flet ((pseudo-read (ct)
	   (let ((rv (eval (excerpt-pseudo-get-field ct :read))))
	     (if (funcall (excerpt-pseudo-get-field ct :pred) rv)
		 rv
	       (tellib-error 'error (format "%s isn't a %s" rv ct))))))
    (let* ((type     (completing-read "Type: "
				      `(("EXCERPT") ,@excerpt-pseudo-excerpt-list)
				      nil t))
	   (prefix   (read-from-minibuffer "Prefix: "))
	   (headless (y-or-n-p "Headless? "))
	   (pseudo?  (assoc type excerpt-pseudo-excerpt-list))
	   (source   (if pseudo?
			 (pseudo-read type)
		       (excerpt-read-source-file)))
	   (cat      (when pseudo?
		       ;;(read-from-minibuffer "Category: ")
		       type
		       ))
	   (id       (when pseudo?
		       (read-from-minibuffer "Name: " (excerpt-auto-id))))
	   (excerpt  (excerpt-select-excerpt type source cat id nil)))
      (message "DEBUG %s" excerpt)
      (when source
	(excerpt-insert-excerpt
	 (list
	  :rawsrc   (when pseudo?
		      (format "%s%S" (excerpt-pseudo-get-field cat :quote) source))
	  :source   (unless pseudo? source)
	  :type     (if pseudo? 'pseudo 'excerpt)
	  :prefix   prefix
	  :headless headless
	  :category (plist-get excerpt :category)
	  :name     (format "%s" (plist-get excerpt :name))))))))

(defun excerpt-update-current (beg end &optional find-def cat name)
  "Update currently marked excerpt.
This command modifies the buffer contents. Take care."
  (interactive "r")
  (save-restriction
    (when (and beg end)
      (narrow-to-region beg end))
    (let ((def (or find-def
		   (progn
		     (goto-char (point-min))
		     (excerpt-find-next-excerpt nil cat name)))))
      (when def
	(let ((beg (plist-get def :beg))
	      (end (plist-get def :end)))
	  (narrow-to-region beg end)
	  (end-of-buffer)
	  (excerpt-insert-excerpt def beg end)
	  (end-of-buffer)
	  t)))))

(defun excerpt-update-next (&optional reverse-flag)
  "Update the *next* excerpt.
With prefix argument, update the previous excerpt.
This command modifies the buffer contents. Take care."
  (interactive "P")
  (let ((def (excerpt-find-next-excerpt reverse-flag)))
    (when def
      (excerpt-update-current (plist-get def :beg) (plist-get def :end) def))))

(defun excerpt-find-source (beg end)
  "Goto currently selected excerpt's source file."
  (interactive "r")
  (save-restriction
    (narrow-to-region beg end)
    (let ((def (excerpt-find-next-excerpt)))
      (when def
	(excerpt-find-file (plist-get def :source)
			   nil
			   (plist-get def :category)
			   (plist-get def :name))))))

;;;###autoload
(defun excerpt-update ()
  "Update all excerpts.
This command modifies the buffer contents. Take care."
  (interactive)
  (beginning-of-buffer)
  (while (excerpt-update-next) nil))

(defun excerpt-update-region (beg end)
  "Update all excerpts in region.
This command modifies the buffer contents. Take care."
  (interactive "r")
  (save-restriction
    (narrow-to-region beg end)
    (excerpt-update)))


;; Setup

(defun excerpt-kill-emacs-hook ()
  (when excerpt-categories
    (mapc #'(lambda (this)
	      (let* ((file (car this))
		     (lst  (remove* 1 (cdr this)
				    (lambda (pos a) (nth pos a)))))
		(when lst
		  (with-temp-buffer
		    (insert-file-contents file)
		    (end-of-buffer)
		    (dolist (this lst)
		      (insert (car this)) (newline))
		    (write-file file)))))
	  (plist-to-alist excerpt-categories))))
;;test: (excerpt-kill-emacs-hook)

(defun excerpt-ref-popup-menu (pos)
  (let* ((ol   (excerpt-get-ref-overlay-at-pos pos))
	 (cat  (overlay-get ol 'excerpt-ref-cat))
	 (name (overlay-get ol 'excerpt-ref-name))
	 (src  (overlay-get ol 'excerpt-reference))
	 (beg  (overlay-start ol))
	 (end  (overlay-end ol)))
    (popup-menu
     `("This is an excerpt!"
       ;;["Goto point"        (goto-char ,pos)]
       ["Find source file"  (excerpt-find-file ,src nil ,cat ,name)]
       ["Remove excerpt!"   (excerpt-remove-excerpt ,ol ,beg ,end)]
       ["Update excerpt!"   (excerpt-update-current ,beg ,end nil ,cat ,name)]
       ))))

(defun excerpt-source-popup-menu (pos)
  (let* ((ol   (excerpt-get-src-overlay-at-pos pos))
	 ;;(beg  (overlay-start ol))
	 ;;(end  (overlay-end ol))
	 )
    (popup-menu
     `("This is an excerpt source!"
       ["Remove source mark" (delete-overlay ,ol)]
       ))))

(defun excerpt-refmenu-at-mouse (event)
  "Show the excerpt popup menu."
  (interactive "e")
  (tellib-call-with-event-pos #'excerpt-ref-popup-menu event))
(put 'excerpt-refmenu-at-mouse 'tellib-unimportant t)

(defun excerpt-srcmenu-at-mouse (event)
  "Show the source popup menu."
  (interactive "e")
  (tellib-call-with-event-pos #'excerpt-source-popup-menu event))
(put 'excerpt-srcmenu-at-mouse 'tellib-unimportant t)

;;;###autoload
(defun excerpt-install (&optional top-install-flag)
  "Install excerpt-specific hooks."
  (tellib-installer '(tellib file-properties) 'excerpt top-install-flag)
  (add-hook 'find-file-hooks #'excerpt-setup-all-excerpt t)
  (add-hook 'write-file-hooks #'excerpt-source-write-non-intrusive)
  (add-hook 'kill-emacs-hook #'excerpt-kill-emacs-hook))

(defun excerpt-uninstall (&optional top-install-flag)
  "Uninstall excerpt-specific hooks."
  (tellib-uninstaller '(tellib file-properties) 'excerpt top-install-flag)
  (remove-hook 'find-file-hooks #'excerpt-setup-all-excerpt t)
  (remove-hook 'write-file-hooks #'excerpt-source-write-non-intrusive)
  (remove-hook 'kill-emacs-hook #'excerpt-kill-emacs-hook))

;;(excerpt-install)
;;(excerpt-uninstall)


(provide 'excerpt)

;;testing
;;(setq excerpt-use-file-local-variable '((".*" file-properties file-local)))

;;; excerpt.el ends here

;;; Local Variables:
;;; file-properties-flag: t
;;; excerpt-end-string:";---(:end #{NAME})---"
;;; excerpt-start-string:";---(:excerpt #{CATEGORY})@(:begin #{NAME})---"
;;; auto-recompile:1
;;; time-stamp-format:"%y-%02m-%02d"
;;; excerpt-sources: "~/Etc/TL-Wiki/CompEmacsExcerpt"
;;; End:
