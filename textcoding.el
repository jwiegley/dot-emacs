;;; textcoding.el --- Functions for coding texts, i.e. qualitative text analysis

;; Copyright (C) 2002 Thomas Link

;; Author: Thomas Link AKA samul AT web DOT de
;; Time-stamp: <2003-03-16>
;; Keywords: text codes, qualitative text analysis, interpretation, hermeneutics

(defconst textcoding-version "0.3")
(defconst textcoding-homepage
  "http://members.a1.net/t.link/CompEmacsTextcoding.html")
 
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

;; ;---(:excerpt-beg Textcoding :name desc)---
;; ;---(:excerpt-source "~/Etc/TL-Wiki/CompEmacsTextcoding")---
;; 
;; textcoding.el assists users in doing qualitative text analysis by
;; providing a mechanism to attach structured notes to a text. These
;; structured notes are grouped in categories -- i.e. text codes --, which
;; can be visualised by the use of different highlighting colours and text
;; marks. These notes are saved as
;; [[CompEmacsFileproperties][file properties]] independently from the text.
;; These notes can be summarised or exported (e.g. as tab separated file).
;; 
;; **Caveat**: textcoding.el is still experimental, i.e. it hasn't been tested
;; in a significant real world project yet. See also
;; CompEmacsFileproperties#problems.
;; 
;; 
;; *** Installation
;; 
;; Put =(require 'textcoding) (textcoding-install)= into your user init
;; file. `textcoding-install' installs all the required packages and all
;; hooks necessary. It also loads `textcoding-autoloades-file'.
;; 
;; 
;; *** Starting a new project
;; 
;; When coding a text, you should first define a project -- otherwise a
;; global project definition will be used. This is done by the
;; `textcoding-project-define' macro. An example use would be:
;; 
;; <example>
;; 	(textcoding-project-define
;; 	   textcoding-test-project
;; 	   "~/.xemacs/textcoding-testproj.el"
;; 	   (textcoding-proj-add-categories '("A" "B" "C"))
;; 	   (textcoding-proj-add-faces '(("^A" blue) ("^B" green)))
;; 	   (textcoding-proj-add-templates '((:project "Class" "Note")
;; 					    ("A" "Colour" "Note")
;; 					    ("B" "Height" "Note")))))
;; </example>
;; 
;; Put something like this into a file of its own -- say
;; "~/Etc/TC/test.el". The project data of this example is saved in
;; "~/.xemacs/textcoding-testproj.el". If you add new categories during
;; coding, these will be recorded in this data file.
;; 
;; When evaluating or compiling this macro an autoload definition will be
;; saved in `textcoding-autoloades-file'. After putting something like
;; (following this example) "mode:textcoding-test-project" into your file's
;; local variable section, the project definition in "~/Etc/TC/test.el"
;; will be automatically loaded when opening the text file.
;; 
;; Textcoded regions are implemented as [[CompEmacsRemarks][remarks]] --
;; see there for an explanation of how to edit, move, or delete them.
;; 
;; 
;; *** Important commands
;; 
;; `textcoding-code' :: Code the selected region.
;; 
;; `textcoding-summarise' :: Summarise all (or those of CATEGORIES) coded
;; passages in the current buffer -- see also
;; `textcoding-summarise-as-sexp' and
;; `textcoding-summarise-as-tab-separated'.
;; 
;; `textcoding-remake-faces' :: Remake coded text's faces according to
;; current settings.
;; 
;; 
;; *** Important functions and macros
;; 
;; `textcoding-project-define' :: Define a new textcoding project. There
;; are several functions that might be useful in this respect:
;; `textcoding-proj-add-categories', `textcoding-proj-add-faces',
;; `textcoding-proj-add-templates'.
;; 
;; 
;; *** Important variables and faces
;; 
;; `textcoding-class' :: The general textcoding project definition.
;; 
;; `textcoding-project-file' :: The general data file.
;; 
;; `textcoding-autoloades-file' :: Autoloads.
;; 
;; `textcoding-face' :: Standard textcoding face.
;; 
;; ;---(:excerpt-end Textcoding :name desc)---

;;; Known problems:

;; ;---(:excerpt-beg Textcoding :name problems)---
;; ;---(:excerpt-source "~/Etc/TL-Wiki/CompEmacsTextcoding")---
;; 
;; - See CompEmacsFileproperties#problems.
;; 
;; ;---(:excerpt-end Textcoding :name problems)---

;;; Change log:

;; ;---(:excerpt-beg Textcoding :name hist)---
;; ;---(:excerpt-source "~/Etc/TL-Wiki/CompEmacsTextcoding")---
;; 
;; v 0.2 :: Initial release (tested with XEmacs)
;; 
;; ;---(:excerpt-end Textcoding :name hist)---


;;; To do:

;- collect categories (rebuild project data from file)
;- Option: ID in summaries
;- rename -summary- to -export-

;;;later:
;- Templates in -class

;- Index files in the project definition file

;- Summary/overview of all categories in all files belonging to one
;project and/or in the current file (outl-mouse-minor-mode (vs. tree
;view) + view-mode)

;- generate *.tcd/*.tcode files/exports: (1) for all files belonging to a
;project, (2) automatically on kill-buffer

;;; Code:

(require 'tellib)
(tellib-version-check-with-name "tellib" "0.2.0")
(tellib-require 'remarks "0.2")

(require 'cl)
(require 'cus-edit)


(defgroup textcoding nil
  "Code a text, e.g. for qualitative text analysis."
  :link `(url-link :tag "Homepage" ,textcoding-homepage)
  :link '(emacs-commentary-link :tag "Commentary" "textcoding.el")
  :prefix "textcoding-"
  :group 'data)

(defcustom textcoding-project-file
  (if tellib-running-xemacs
      (concat user-init-directory "textcoding")
    "~/.textcoding")
  "*The global project file."
  :type 'file
  :group 'textcoding)

(defcustom textcoding-autoloades-file
  (if tellib-running-xemacs
      (concat user-init-directory "textcoding-auto.el")
    "~/.textcoding-auto.el")
  "*A file with autoloads, loaded when textcoding is being installed."
  :type 'file
  :group 'textcoding)

(defcustom textcoding-hierarchy-marker ?.
  "*A character denoting a subhierarchy -- e.g. 'one.two'."
  :type 'character
  :group 'textcoding)

(defcustom textcoding-shorten-marker-flag t
  "*Non-nil means, shorten markers in the text using `textcoding-get-short-marker'."
  :type 'boolean
  :group 'textcoding)

(defcustom textcoding-shorten-replacements
  '(
    ("^good$"   nil "+")
    ("^bad$"    nil "-")
    ("^better$" nil "++")
    ("^worse$"  nil "--")
    )
  "*An alist of replacements strings for use with `textcoding-get-short-marker'.
The replacement strings "
  :type '(repeat
	  (list :value ("" nil "")
		(regexp  :tag "RegExp"        :value "")
		(boolean :tag "Case sensitiv" :value nil)
		(string  :tag "Replacement"   :value "")))
  :group 'textcoding)
  
(defface textcoding-face
  '((t
     ;;(:foreground "blue" :background "yellow")
     (:background "lightsalmon")
     ))
  "Face for marking coded text."
  :group 'textcoding)

(defvar textcoding-project-modes nil
  "An alist of known project-mode functions and the corresponding files.")

(defvar textcoding-widget-children nil)
(defvar textcoding-marker nil)
(defvar textcoding-counter nil)

(defvar textcoding-buffer-project-data nil
  "The buffer's textcoding project data.")
(make-variable-buffer-local 'textcoding-buffer-project-data)

(defvar textcoding-minor-mode nil
  "Mark buffer as using textcodings.")
(make-variable-buffer-local 'textcoding-minor-mode)

(defvar textcoding-class
  `((:parent-class remarks)
    (:counter-var  textcoding-counter)
    (:write-buffer ,#'textcoding-write-buffer)
    (:read-buffer  ,#'textcoding-read-buffer)
    (:edit-mode    ,#'custom-mode)
    (:edit-map     custom-mode-map)
    (:marker-var   textcoding-marker)
    (:prettyprint  ,#'textcoding-prettyprint)
    (:face         textcoding-face)
    (:get-title    ,#'car)
    (:emptyp       ,(lambda (this)
		      (and (string= "" (car this))
			   (every (lambda (that)
				    (string= "" (plist-get that :value)))
				  (cdr this)))))
    ))



(defun textcoding-proj-load ()
  "Load the project file."
  (if (file-readable-p textcoding-project-file)
      (let ((file textcoding-project-file)
	    data)
	(with-temp-buffer
	  (insert-file-contents file)
	  (setq data (car (read-from-string (buffer-string)))))
	(setq textcoding-buffer-project-data data))
    (setq textcoding-buffer-project-data nil)))
;;test: (textcoding-proj-load)

(defun textcoding-proj-save ()
  "Save `textcoding-buffer-project-data'."
  (when textcoding-minor-mode
    (let ((data (format "%S" textcoding-buffer-project-data))
	  (file textcoding-project-file))
    (with-temp-buffer
      (insert data)
      (write-file file)))))

(defun textcoding-proj-data-set (type key val)
  "Set `textcoding-buffer-project-data' TYPE's data for KEY to VAL."
  (setq textcoding-buffer-project-data
	(plist-put textcoding-buffer-project-data type
		   (tellib-alist-set (plist-get textcoding-buffer-project-data type)
				     key val))))

(defun textcoding-proj-data-get (type &rest keys)
  "Get `textcoding-buffer-project-data' TYPE's data for KEYS or all.
KEYS ... :list list, :regexp regexp, :key key, nil (get all matches).
Return an alist of matching keys."
  (let ((data (plist-get textcoding-buffer-project-data type)))
    (if keys
	(let ((what  (car keys))
	      (match (cadr keys)))
	  (case what
	    ((:list)
	     (remove* match data :test-not (lambda (match this)
					     (member (car this) match))))
	    ((:regexp)
	     (remove* match data :test-not (lambda (match this)
					     (string-match match (car this)))))
	    ((:match)
	     (remove* match data :test-not (lambda (match this)
					     (let ((rx (car this)))
					       (when (stringp rx)
						 (string-match rx match))))))
	    ((:key)
	     (assoc match data))
	    (t
	     (tellib-error 'error "textcoding: Unknown match type" what match))))
      data)))
;;(tellib-alist-get data (car keys) nil t)))))
;;test: (plist-get textcoding-buffer-project-data :category)
;;test: (textcoding-proj-data-get :category)
;;test: (textcoding-proj-data-get :category :list '("A" "B"))
;;test: (textcoding-proj-data-get :category :key "A")
;;test: (textcoding-proj-data-get :category :regexp "^[AB]")
;;test: (textcoding-proj-data-get :face :match "A")

(defun textcoding-proj-data-key-get (type key)
  "Get KEY's value for TYPE."
  (let ((data (textcoding-proj-data-get type :key key)))
    (if data
	(cadr data)
      nil)))
;;test: (textcoding-proj-data-key-get :category "A")

(defun textcoding-proj-add-categories (categories)
  "Add CATEGORIES to `textcoding-buffer-project-data'."
  (mapc #'(lambda (this)
	    (textcoding-proj-data-set :category this 0))
	categories))

(defun textcoding-proj-add-faces (regexps-and-faces)
  "Add REGEXPS-AND-FACES to `textcoding-buffer-project-data'.
REGEXPS-AND-FACES ... a list of list \(REGEXP FACE)."
  (mapc #'(lambda (this)
	    (textcoding-proj-data-set :face (nth 0 this) (nth 1 this)))
	regexps-and-faces))

(defun textcoding-proj-add-templates (templates)
  "Add TEMPLATES to `textcoding-buffer-project-data'.
TEMPLATES ... An alist like \((CATEGORY FIELD1 ...) ...)."
  (mapc #'(lambda (this)
	    (let ((cat  (car this))
		  (flds (cdr this)))
	      (textcoding-proj-data-set
	       :template cat (mapcar (lambda (x) `(:name ,x :value "")) flds))))
	templates))
;;test: (textcoding-proj-add-templates '(("1" "x1" "xx") ("2" "x2" "xx")))
  
(defun textcoding-proj-init (&optional filename)
  "Initialise/reset `textcoding-buffer-project-data'.
Use FILENAME as `textcoding-project-file' if provided."
  (when filename
    (make-local-variable 'textcoding-project-file)
    (setq textcoding-project-file filename))
  (setq textcoding-minor-mode t)
  (textcoding-proj-load))

(defun textcoding-get-categorys-face (category)
  "Return the proper face for CATEGORY (a symbol)."
  (or (when category
	(let ((rv (textcoding-proj-data-get :face :match category)))
	  (when rv (cadar rv))))
      (textcoding-proj-data-key-get :face :project)))

(defun textcoding-write-buffer (lst)
  "Write-buffer function for `textcoding-class'."
  (make-local-variable 'textcoding-widget-children)
  (let ((tw (widget-create 'string
			     :tag "Category"
			     :value (car lst))))
    (widget-put tw :title t)
    (setq textcoding-widget-children (list tw)))
  (mapc #'(lambda (this)
	    (let ((tag (plist-get this :name))
		  (val (plist-get this :value)))
	      (setq textcoding-widget-children (cons (widget-create 'string
								    :tag tag
								    :value val)
						     textcoding-widget-children))))
	(cdr lst))
  (widget-setup))

(defun textcoding-read-buffer ()
  "Read-buffer function for `textcoding-class'."
  (let ((title "") body)
    (mapc #'(lambda (child)
	      (let ((val (widget-apply child :value-get)))
		(if (widget-get child :title)
		    (setq title val)
		  (setq body (cons (list :name (widget-get child :tag) :value val)
				   body)))))
	  textcoding-widget-children)
    (cons title body)))

(defun textcoding-get-short-marker (string)
  "Get a short marker for a hierarchical code -- separated with periods.
E.g. Something like 'Education.School.Satisfaction' becomes 'EduSchSat'."
  (let ((l 3))
    (mapconcat #'(lambda (string)
		   (let ((rs (member*
			      string textcoding-shorten-replacements
			      :test #'(lambda (x y)
					(let ((case-fold-search (not (nth 1 y))))
					  (string-match (nth 0 y) x))))))
		     (if rs
			 (nth 2 (car rs))
		       (capitalize (if (< (length string) l)
				       string
				     (subseq string 0 3))))))
	       (tellib-split-string-by-char string textcoding-hierarchy-marker)
	       "")))
;;test: (textcoding-get-short-marker "Education.School.Satisfaction")
;;test: (textcoding-get-short-marker "Education.School.Satisfaction.good")
;;test: (textcoding-get-short-marker "Education.School.Satisfaction.Bad")
;;test: (textcoding-get-short-marker "Ed.School.Satisfaction")

(defun textcoding-code (beg end &optional category)
  "Code the selected region."
  (interactive "r")
  (let* ((cats              (textcoding-proj-data-get :category))
	 (cat               (or category
				(completing-read "Category: " cats)))
	 (tmplt             (or (textcoding-proj-data-key-get :template cat)
				(textcoding-proj-data-key-get :template :project)
				'((:name "Note" :value ""))))
	 (face              (textcoding-get-categorys-face cat))
	 (textcoding-marker (format "[%s]" 
				    (if textcoding-shorten-marker-flag
					(textcoding-get-short-marker cat)
				      cat)))
	 (textcoding-counter (or (textcoding-proj-data-key-get :category cat)
				 0)))
    (textcoding-proj-data-set :category cat (1+ textcoding-counter))
    (remarks-make beg end
		  :class 'textcoding
		  :message ""
		  :use-face face
		  :text `(,cat ,@tmplt)
		  )))

(defun textcoding-prettyprint (overlays buffer &optional title)
  "Pretty print BUFFER's OVERLAYS."
  (mapc #'(lambda (ol)
	    (let* ((data (overlay-get ol 'remarks-text))
		   (beg  (overlay-start ol))
		   (end  (overlay-end ol))
		   (cat (car data))
		   (hd  (format "[Code %i:%i-%i -- %s]"
				(overlay-get ol 'remarks)
				beg
				end
				cat))
		   (wid (truncate (* (window-width) 0.8)))
		   (wi2 (- wid (length hd))))
	      (insert (if (> wi2 0) (make-string wi2 ?\-) "") hd) (newline)
	      (insert (buffer-substring beg end buffer)) (newline)
	      (insert (make-string wid ?\-)) (newline)
	      (dolist (this (cdr data))
		(let ((tag (plist-get this :name))
		      (val (plist-get this :value)))
		  (insert tag ": " val "\n")))
	      (newline)))
	overlays))

(defun textcoding-summarise (&optional categories predicate
				       buffer dont-clear-buffer)
  "Summarise all (or those of CATEGORIES) coded passages in the current buffer."
  (interactive)
  (remarks-summarise 'textcoding
		     (when categories
		       (lambda (ol)
			 (member (car (overlay-get ol 'remarks-text))  categories)))
		     predicate
		     buffer
		     dont-clear-buffer))
;;test: (textcoding-summarise)
;;test: (textcoding-summarise '("x"))
;;test: (textcoding-summarise '("y"))

(defun* textcoding-summarise-as-sexp
  (&optional categories
	     &rest args
	     &key
	     buffer
	     dont-clear-buffer
	     dont-include-category
	     dont-include-text
	     dont-include-position
	     (prolog "(")
	     (epilog    "\n)\n")
	     (new-set   "\n (")
	     (end-set   "\n )")
	     (new-field "\n  (")
	     (end-field ")")
	     (fmt-key   (lambda (this) (format "%S " this)))
	     (fmt-data  (lambda (this) (format "%S" this))))
  "Summarise all coded passages in the current buffer.
ARGS can include the following keys:
:prolog, :epilog, :new-set, :end-set, :new-field, :end-field ... A string
or a function.
:fmt-key, :fmt-data ... A function taking the key or the data a argument.
:dont-include-category, :dont-include-text, :dont-include-position ... Boolean.
:buffer ... The target buffer.
:dont-clear-buffer ... Boolean.

The data looks like this:
<prolog>
 <new-set>
  <new-field>(<fmt-key> \":category\")(<fmt-data> \"CATEGORY\")<end-field>
  <new-field>(<fmt-key> \":text\")(<fmt-data> \"TEXT\")<end-field>
  <new-field>(<fmt-key> \":begin\")(<fmt-data> \"TEXT\")<end-field>
  <new-field>(<fmt-key> \":end\")(<fmt-data> \"TEXT\")<end-field>
  <new-field>(<fmt-key> \"KEY\")(<fmt-data> \"DATA\")<end-field>
  ...
 <end-set>
<epilog>
"
  (interactive)
  (textcoding-summarise
   categories
   `(lambda (overlays buffer &optional title)
      (let ((inserter (lambda (this)
			(cond ((stringp this)
			       (insert this))
			      ((functionp this)
			       (funcall this))))))
	(funcall inserter ,prolog)
	(mapc #'(lambda (ol)
		  (let* ((data (overlay-get ol 'remarks-text))
			 (beg  (overlay-start ol))
			 (end  (overlay-end ol))
			 (cat  (car data))
			 (txt  (buffer-substring beg end buffer)))
		    (funcall inserter ,new-set)
		    (unless ,dont-include-category
		      (funcall inserter ,new-field)
		      (funcall inserter (funcall #',fmt-key ":category"))
		      (funcall inserter (funcall #',fmt-data cat))
		      (funcall inserter ,end-field))
		    (unless ,dont-include-text
		      (funcall inserter ,new-field)
		      (funcall inserter (funcall #',fmt-key ":text"))
		      (funcall inserter (funcall #',fmt-data txt))
		      (funcall inserter ,end-field))
		    (unless ,dont-include-position
		      (funcall inserter ,new-field)
		      (funcall inserter (funcall #',fmt-key ":begin"))
		      (funcall inserter (funcall #',fmt-data beg))
		      (funcall inserter ,end-field)
		      (funcall inserter ,new-field)
		      (funcall inserter (funcall #',fmt-key ":end"))
		      (funcall inserter (funcall #',fmt-data end))
		      (funcall inserter ,end-field))
		    (mapc #'(lambda (this)
			      (let ((tag (plist-get this :name))
				    (val (plist-get this :value)))
				(funcall inserter ,new-field)
				(funcall inserter (funcall #',fmt-key  tag))
				(funcall inserter (funcall #',fmt-data val))
				(funcall inserter ,end-field)))
			  (cdr data))
		    (funcall inserter ,end-set)))
	      overlays)
	(funcall inserter ,epilog)))
   buffer
   dont-clear-buffer))
;;(textcoding-summarise-as-sexp nil)
;;(textcoding-summarise-as-sexp nil :buffer (current-buffer) :dont-clear-buffer t)

(defun textcoding-summarise-as-tab-separated (&optional categories &rest args)
  "Summarise all coded passages in tab separated format.
Columns:
1 ... Category
2 ... Begin
3 ... End
other ... Data fields

Use
	\(textcoding-summarise-as-tab-separated nil :end-field \";\")
to get a semicolon separated file.
"
  (interactive)
  (apply #'textcoding-summarise-as-sexp
	 categories
	 (tellib-plist-merge
	  args
	  (list :prolog    ""
		:epilog    ""
		:new-set   ""
		:end-set   (lambda () (delete-backward-char) (insert "\n"))
		:new-field ""
		:end-field "	"
		:fmt-key   (lambda (x) "")
		))))
;;test: (textcoding-summarise-as-tab-separated)
;;test: (textcoding-summarise-as-tab-separated nil :end-field ";")

(defun textcoding-get-summary (&optional categories &rest args)
  "Get the current buffers summary as alist.
ARGS are passed on to `textcoding-summarise-as-sexp'."
  (let ((srcbuf (current-buffer)))
    (with-temp-buffer
      (let ((tgtbuf (current-buffer)))
      (save-excursion
	(set-buffer srcbuf)
	(apply #'textcoding-summarise-as-sexp categories :buffer tgtbuf args))
      (car (read-from-string (buffer-string)))))))
;;test: (textcoding-get-summary)


(defun textcoding-remake-faces ()
  "Remake coded text's faces according to current settings."
  (interactive)
  (let ((ols (tellib-overlay-collect* '(remarks-class) nil nil nil
				      #'(lambda (ol sym)
					  (equal (overlay-get ol sym)
						 'textcoding)))))
    (loop for ol in ols do
      (let* ((cat  (car (overlay-get ol 'remarks-text)))
	     (face (textcoding-get-categorys-face cat)))
	(when (and cat face)
	  (overlay-put ol 'face face))))))

(defun textcoding-remake-categories ()
  "Redefine a project categories from a given buffer."
  (interactive)
  (let ((ols (tellib-overlay-collect* '(remarks-class) nil nil nil
				      #'(lambda (ol sym)
					  (equal (overlay-get ol sym)
						 'textcoding)))))
    (loop for ol in ols do
      (let* ((cat   (car (overlay-get ol 'remarks-text)))
	     (count (or (textcoding-proj-data-key-get :category cat)
			0)))
	(textcoding-proj-data-set :category cat (1+ count))))))


(defun textcoding-menu-data ()
  "Build the menu core for the current project's categories."
  (flet ((helper (parts &optional data)
	   (let ((key (car parts)))
	     (if (= (length parts) 1)
		 (tellib-alist-set data (car parts)
				   `[,key (textcoding-code (region-beginning)
							   (region-end)
							   ,key)])
	       (tellib-alist-setcdr data key
				    (helper (cdr parts)
					    (tellib-alist-get data key))))))
	 (simplify (this &optional count)
	   (cond
	    ((vectorp this)
	     (if (and count (= count 0))
		 (progn
		   (setf (aref this 0) "[code]")
		   this)
	       this))
	    ((stringp this)
	     this)
	    ((= (length this) 2)
	     (nth 1 this))
	    (t
	     (let ((hd (car this)))
	       (cons (if (stringp hd)
			 (concat hd " ...")
		       (simplify hd))
		     (let ((dt (cdr this)))
		     (loop
		       for i from 0 to (1- (length dt))
		       for e in dt
		       collect (simplify e i)))))))))
    (let ((cats (sort (textcoding-proj-data-get :category)
		      #'(lambda (a b) (string< (car a) (car b)))))
	  data)
      (loop for cat in cats do
	(let ((parts  (tellib-split-string-by-char (car cat)
						   textcoding-hierarchy-marker)))
	  (setq data (helper parts data))))
      (simplify data))))

(defun textcoding-make-menu ()
  "Make a menu for the current project."
  (interactive)
  (add-submenu nil
	       `("Textcode"
		 ("1 Rebuild"
		  ["Categories"            (textcoding-remake-categories)]
		  ["Faces"                 (textcoding-remake-faces)]
		  ["Menu"                  (textcoding-make-menu)]
		  )
		 ("2 Summary"
		  ["Text"                  (textcoding-summarise)]
		  ["Text -- Tab Separated" (textcoding-summarise-as-tab-separated)]
		  ["Lisp Expression"       (textcoding-summarise-as-sexp)]
		  )
		 "---"
		 ,@(textcoding-menu-data)
		 )))

(defun textcoding-popup-menu (event)
  "Show a textcoding pop-up menu."
  (interactive "e")
  (tellib-call-with-event-pos
   (lambda (pos)
     (popup-menu
      `("Categories" ,@(textcoding-menu-data))))
   event))



;;;###autoload
(defun textcoding-install (&optional top-install-flag)
  "Install textcoding hooks."
  (when (file-readable-p textcoding-autoloades-file)
    (load textcoding-autoloades-file))
  (remarks-add-class 'textcoding 'textcoding-class)
  (tellib-installer '(tellib remarks) 'textcoding top-install-flag)
  (add-hook 'kill-buffer-hook #'textcoding-proj-save))

(defun textcoding-uninstall (&optional top-install-flag)
  "Deinstall textcoding hooks."
  (tellib-uninstaller '(tellib remarks) 'textcoding top-install-flag)
  (remove-hook 'kill-buffer-hook #'textcoding-proj-save))

;(textcoding-install)
;(textcoding-uninstall)




(defmacro textcoding-project-define (name project-file &rest body)
  "Set up a textcoding project.

NAME ... This macro defines the function NAME-mode, which should be put
into the buffer local variables section of project files. An autoload
definition is stored in `textcoding-autoloades-file', which will be
loaded on calling `textcoding-install'.

PROJECT-FILE ... The file where the project related information is
stored.

Example:

	\(textcoding-project-define
	   textcoding-test-project
	   \"~/.xemacs/textcoding-testproj.el\"
	   \(textcoding-proj-add-categories '\(\"A\" \"B\" \"C\"))
	   \(textcoding-proj-add-faces '\(\(\"^A\" blue) \(\"^B\" green)))
	   \(textcoding-proj-add-templates '\(\(:project \"Class\" \"Note\")
					    \(\"A\" \"Colour\" \"Note\")
					    \(\"B\" \"Height\" \"Note\")))))

Then add 'mode: textcoding-test-project' to your file's local variable
section. You can also do this by evaluating:

	\(tellib-update-local-variable-def 'mode 'textcoding-test-project :add t)
"
  (let ((fn (intern (format "%s-mode" name))))
    (unless (member fn textcoding-project-modes)
      (let ((backup-inhibited t)
	    (src  (or byte-compile-dest-file
		      (buffer-file-name))))
	(when src
	  (let ((src (file-name-sans-extension src)))
	    (add-to-list 'textcoding-project-modes (list fn src))
	    (with-temp-buffer
	      (let ((comment-start ";"))
		(insert (format "(setq textcoding-project-modes '%S)\n"
				textcoding-project-modes))
		(mapc
		 #'(lambda (this)
		     (let ((fn  (nth 0 this))
			   (src (nth 1 this)))
		       (insert (format
				"(autoload '%s %S \"*generated by textcoding*\")\n"
				fn src))))
		 textcoding-project-modes)
		(tellib-update-local-variable-def 'backup-inhibited t
						  :dont-replace t)
		(write-file textcoding-autoloades-file)))))))
    `(defun ,fn ()
       "A textcoding project mode.\n*generated by `textcoding-project-define'*"
       (interactive)
       (textcoding-proj-init ,project-file)
       (textcoding-make-menu)
       (unless textcoding-buffer-project-data
	 ,@body))))


(provide 'textcoding)

;;; textcoding.el ends here

;;; Local Variables:
;;; auto-recompile:1
;;; time-stamp-format:"%y-%02m-%02d"
;;; End:
