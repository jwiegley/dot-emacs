;;; REMARKS.EL --- text annotations

;; Copyright (C) 2001 Thomas Link

;; Author: Thomas Link <samul AT web de>
;; Time-stamp: <2003-03-16>
;; Keywords: annotations, remarks, notes

(defconst remarks-version "0.2")
(defconst remarks-homepage "http://members.a1.net/t.link/CompEmacsRemarks.html")

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; A copy of the GNU General Public License can be obtained from this
;; program's author (send electronic mail to <samul AT web de>) or
;; from the Free Software Foundation, Inc., 675 Mass Ave, Cambridge,
;; MA 02139, USA.


;;; Commentary:

;; ;---(:excerpt-beg remarks :name desc)---
;; ;---(:excerpt-source "~/Etc/TL-Wiki/CompEmacsRemarks")---
;; 
;; *** Usage
;; 
;; Installation: Put (require 'remarks) (remarks-install) into your
;; startup/user init file.
;; 
;; Select a region and execute `remarks-make'. Remarks are saved and
;; restored via =file-properties.el=.
;; 
;; - Exit the note editing buffer by pressing C-c C-c -- if you kill the
;; temporary buffer otherwise, the editing modes could get messed up.
;; 
;; - Make the first line a meaningful title.
;; 
;; - Inserting a null-text results in the deletion of the note.
;; 
;; - When notes overlap, the user will be asked to select one note by its
;; title.
;; 
;; - Usually remarks will be saved when killing the buffer. You can
;; nevertheless force saving notes by calling `file-properties-write'.
;; 
;; - When closing a buffer, opened remarks will be saved automatically.
;; 
;; 
;; *** Commands
;; 
;; `remarks-make' :: Make a note covering the region from BEG to END.
;; 
;; `remarks-edit' :: Edit the note at point.
;; 
;; `remarks-summarise' :: Summarise the current buffer's remarks.
;; 
;; `remarks-make-link' :: Mark a region as a link to another file.
;; 
;; 
;; *** Variables
;; 
;; `remarks-mouse-button' :: Pressing this mouse button over an annotated
;; region (button-3 by default) pops up a small menu.
;; 
;; `remarks-marker' :: Prefix annotated regions with this string (default:
;; "[REM%%]", %% being the note number).
;; 
;; `remarks-find-link-function' :: Function used for opening links.
;; 
;; 
;; *** Faces
;; 
;; `remarks-face' :: Face for marking excerpts.
;; 
;; `remarks-link-face' :: Face for marking excerpts.
;; 
;; 
;; *** Mouse & key bindings (local to overlay/extent)
;; 
;; `remarks-mouse-button'     | `remarks-popup-menu'
;; control return             | `remarks-edit'
;; C-c control-left           | `remarks-move-left'
;; C-c control-right          | `remarks-move-right'
;; C-c control-up             | `remarks-move-up'
;; C-c control-down           | `remarks-move-down'
;; C-c control-shift-left     | `remarks-shrink'
;; C-c control-shift-right    | `remarks-grow'
;; 
;; ;---(:excerpt-end remarks :name desc)---


;;; Change log:

;; ;---(:excerpt-beg remarks :name hist)---
;; ;---(:excerpt-source "~/Etc/TL-Wiki/CompEmacsRemarks")---
;; 
;; v0.2 :: Improvements for use with CompEmacsTextcoding
;; 
;; v0.1 :: Initial release (tested with XEmacs)
;; 
;; ;---(:excerpt-end remarks :name hist)---


;;; To do:

;; - :counter-var in :get-counter umwandeln (funktion, die counter setzt
;; und zurückgibt)

;;; Code:

(require 'tellib)
(tellib-version-check-with-name "tellib" "0.2.0")
(tellib-require 'file-properties "1.1")
(eval-and-compile (when tellib-running-xemacs (require 'overlay)))

(require 'cl)


(defgroup remarks nil
  "Non-intrusive text annotations."
  :link `(url-link :tag "Homepage" ,remarks-homepage)
  :link '(emacs-commentary-link :tag "Commentary" "remarks.el")
  :prefix "remarks-"
  :group 'convenience)

(defcustom remarks-marker "[REM%s]"
  "*Prepend a remark with a string -- %s will be replaced with the counter.
A null-string means don't add a prefix."
  :type 'string
  :group 'remarks)

(defcustom remarks-mouse-button
  (if tellib-running-xemacs [(button3)] [mouse-3])
  "*Mouse button to press for popping up the remarks menu."
  :type 'sexp
  :group 'remarks)

(defcustom remarks-links-marker "[LINK]"
  "*Prepend a link with a string -- %s will be replaced with the counter.
A null-string means don't add a prefix."
  :type 'string
  :group 'remarks)

(defcustom remarks-find-link-function
  (if (fboundp 'filesets-find-or-display-file)
      #'filesets-find-or-display-file
    #'find-file)
  "*A function used for opening links -- see `remarks-link-class'."
  :type '(choice (const :tag "filesets-find-or-display-file"
			:value filesets-find-or-display-file)
		 (const :tag "find-file"
			:value find-file)
		 (function :tag "Other" :value nil))
  :group 'remarks)

(defface remarks-face
  '((t
     ;;(:foreground "blue" :background "yellow")
     (:background "yellow")
     ))
  "Face for marking remarks."
  :group 'remarks)

(defface remarks-link-face '((t (:background "lightcyan2")))
  "Face for marking links."
  :group 'remarks)

(defvar remarks-local-map
  (let ((map (make-sparse-keymap)))
    (define-key map remarks-mouse-button    #'remarks-popup-menu)
    (define-key map [(control return)]      #'remarks-edit)
    (define-key map [(control c) (control left)]        #'remarks-move-left)
    (define-key map [(control c) (control right)]       #'remarks-move-right)
    (define-key map [(control c) (control up)]          #'remarks-move-up)
    (define-key map [(control c) (control down)]        #'remarks-move-down)
    (define-key map [(control c) (control shift left)]  #'remarks-shrink)
    (define-key map [(control c) (control shift right)] #'remarks-grow)
    map)
  "The remarks' local keymap.")

(defvar remarks-counter 0)
(make-variable-buffer-local 'remarks-counter)
;;(setq remarks-counter 0)

;(defvar remarks-changed-flag nil)
;(make-variable-buffer-local 'remarks-changed-flag)

(defvar remarks-class
  `((:counter-var  remarks-counter)
    (:marker-var   remarks-marker)
    (:face         remarks-face)
    (:edit-mode    ,#'text-mode)
    (:edit-map     nil)
    (:write-buffer ,#'insert)
    (:read-buffer  ,#'buffer-string)
    (:edit-remark  ,#'tellib-edit-in-buffer*)
    (:prettyprint  ,#'remarks-prettyprint)
    (:get-title    ,(lambda (remark)
		      (substring remark 0 (or (string-match "\n" remark)
					      (length remark)))))
    (:emptyp       ,(lambda (txt) (string= txt ""))))
  "An alist of remarks methods and variables.

:parent-class CLASS-NAME ... The name of the \"parent class\", from
which keys will be inherited -- somehow.

:write-buffer FUNCTION ... A function \(takes the text as argument) being
called for writing TEXT into the buffer -- this can be used for decoding
the remark. \(Default is `insert'.)

:read-buffer FUNCTION ... A function \(takes no arguments) being called,
when the editing buffer is killed -- this can be used for
modifying/encoding the remark. \(Default is `buffer-string'.)

:edit-remark FUNCTION ... A function (taking the same number of
arguments as `tellib-edit-in-buffer*', which will be used for editing
(or whatever) the remark.

:marker-var SYMBOL ... The variable holding the marker definition --
with one \"slot\" to be filled in. A format string like
`remarks-marker'.

:counter-var SYMBOL ... The variables holding the current count.

:face FACE ... The face to be used.

:prettyprint FUNCTION ... The function \(takes a list of overlays and the
source buffer as arguments) for prettyprinting a summary.

:emptyp PREDICATE ... The predicate used for testing if a remark is
\"empty\", i.e. to be removed.
")

(defvar remarks-link-counter 0
  "Counter for `remarks-link-class'.")

(defvar remarks-link-class
  `((:parent-class remarks)
    (:counter-var  remarks-link-counter)
    (:marker-var   remarks-links-marker)
    (:face         remarks-link-face)
    (:edit-remark  remarks-find-link))
  "A class for linking files to regions.")

(defvar remarks-classes '((remarks remarks-class)
			  (links   remarks-link-class))
  "An alist \((NAME CLASS-VAR) ...) of known remarks classes.")



(defun remarks-add-class (class-name definition-variable)
  "Add CLASS-NAME (as symbol) and DEFINITION-VARIABLE to `remarks-classes'.
CLASS-NAME ... a symbol
DEFINITION-VARIABLE ... see `remarks-class' for an example."
  (add-to-list 'remarks-classes (list class-name definition-variable) t))

(defun remarks-get-class-def (class-name)
  "Get CLASS-NAME's definition."
  (eval (tellib-alist-get remarks-classes class-name 'remarks-class t)))
;;test: (remarks-get-class-def 'remarks)

(defun remarks-class-get (class-def key &optional default)
  "Retrieve KEY's value from CLASS-DEF."
  (let ((class class-def)
	nope)
    (catch 'exit
      (while class
	(let ((rv (tellib-alist-get class key default t)))
	  (if rv
	      (throw 'exit rv)
	    (let ((parent-class (tellib-alist-get class :parent-class nil t)))
	      (if (and parent-class
		       (not (member parent-class nope)))
		  (setq nope (cons class nope)
			class (remarks-get-class-def  parent-class))
		(throw 'exit nil)))))))))

;;(defvar remarks-test-inheritance-class
;;  `((:counter-var  foo)
;;    (:marker-var   bar)
;;    (:parent-class remarks)))
;;test: (remarks-class-get remarks-test-inheritance-class :counter-var)
;;test: (remarks-class-get remarks-test-inheritance-class :face)

(defun remarks-move-up (&optional count)
  "Move the top remark at point one (or COUNT) line(s) up."
  (interactive "p")
  (tellib-overlay-move 0 (- (or count 1)) '(remarks)))

(defun remarks-move-down (&optional count)
  "Move the top remark at point one (or COUNT) line(s) down."
  (interactive "p")
  (tellib-overlay-move 0 (+ 1 (or count 1)) '(remarks)))

(defun remarks-move-left (&optional count)
  "Move the top remark at point one (or COUNT) line(s) to the left."
  (interactive "p")
  (tellib-overlay-move (- (or count 1)) 0 '(remarks)))

(defun remarks-move-right (&optional count)
  "Move the top remark at point one (or COUNT) line(s) to the right."
  (interactive "p")
  (tellib-overlay-move (+ 1 (or count 1)) 0 '(remarks)))

(defun remarks-grow (&optional count)
  "Make the top remark at point one (or COUNT) characters larger."
  (interactive "p")
  (tellib-overlay-change-size (or count 1) '(remarks)))

(defun remarks-shrink (&optional count)
  "Move the top remark at point one (or COUNT) characters smaller."
  (interactive "p")
  (tellib-overlay-change-size (- (or count 1)) '(remarks)))


(defun remarks-get-title (remark &optional class)
  "Return the title (i.e. the first line) of REMARK."
  (let* ((def (remarks-get-class-def class))
	 (gt  (remarks-class-get def :get-title)))
    (funcall gt remark)))

(defun remarks-popup-menu (event)
  "Show the remarks popup menu."
  (interactive "e")
  (tellib-call-with-event-pos
   (lambda (pos)
     (save-excursion
       (when pos
	 (goto-char pos))
       (let ((ols  (tellib-overlay-collect* '(remarks) nil (overlays-at (point))))
	     pm-edit pm-remove)
	 (mapc
	  #'(lambda (ol)
	      (let* ((txt (overlay-get ol 'remarks-text))
		     (num (overlay-get ol 'remarks))
		     (ttl (remarks-get-title txt (overlay-get ol 'remarks-class))))
		(setq pm-edit (append pm-edit
				      `([,(format "Edit #%i: %S" num ttl)
					 (remarks-edit nil ,ol)])))
		(setq pm-remove (append pm-remove
					`([,(format "Remove #%i: %S" num ttl)
					   (delete-overlay ,ol)])))))
	  ols)
	 (popup-menu `("Remarks"
		       ,@pm-edit
		       "----"
		       ,@pm-remove
		       )))))
   event))

;;;###autoload
(defun remarks-minor-mode (&optional dont-install-properties counter-var)
  "Make sure this buffer's notes are saved.
-- Exit the buffer by pressing C-c C-c -- if you kill the temporary buffer
otherwise, the editing modes easily get messed up.
-- Make the first line a meaningful title.
-- Inserting a null-text results in the deletion of the note.
-- When notes overlap, the user will be asked to select one note by its title.
-- You can force saving notes by calling `file-properties-write'.
"
  (interactive)
  (file-properties-add (or counter-var 'remarks-counter))
  (file-properties-overlay-add 'remarks))

;;;###autoload
(defun remarks-properties-restore (overlay)
  "Turn a restored OVERLAY into a proper remarks overlay."
  (overlay-put overlay 'local-map remarks-local-map))

;;;###autoload
(defun* remarks-make (beg end &rest args
			 &key
			 (class 'remarks)
			 use-counter
			 use-marker
			 use-face
			 use-mode
			 use-edit-map
			 use-write-buffer
			 use-read-buffer
			 use-emptyp
			 use-edit-function
			 (text "")
			 text!
			 (message "Make the first line a significant title.")
			 dont-edit)
  "Make a note covering the region from BEG to END \(see `remarks-minor-mode').
ARGS may include the following keyed arguments:

:text TEXT ... Use this text and edit.
:dont-edit BOOLEAN ... Don't edit text.
:text! TEXT ... Use this text as is -- same as :text and :dont-edit.
:message TEXT ... The message to display when showing the editing buffer.
:class SYMBOL ... The class this remark belongs to. \(See `remarks-classes'.)

The following keys can be used to override class methods:
:use-counter-var, :use-marker-var, :use-face, :use-edit-mode,
:use-edit-map, :use-write-buffer, :use-read-buffer, :use-emptyp,
:use-edit-function.

:use-edit-remark ... A function which takes the same arguments as
`tellib-edit-in-buffer*' (the default).
"
  (interactive "r")
  (unless (assoc class remarks-classes)
    (tellib-error "remarks: Unknown class" class))
  (when text!
    (setq text text!
	  dont-edit t))
  (let* ((def                   (remarks-get-class-def class))
	 (read-buffer-function  (or use-read-buffer
				    (remarks-class-get def :read-buffer)))
	 (write-buffer-function (or use-write-buffer
				    (remarks-class-get def :write-buffer)))
	 (mode-function         (or use-mode
				    (remarks-class-get def :mode)))
	 (mode-map              (or use-edit-map
				    (eval (remarks-class-get def :edit-map))))
	 (face                  (or use-face
				    (remarks-class-get def :face)))
	 (emptyp                (or use-emptyp
				    (remarks-class-get def :emptyp)))
	 (edit-remark           (or use-edit-function
				    (remarks-class-get def :edit-remark)
				    #'tellib-edit-in-buffer*))
	 (counter-var           (or use-counter
				    (remarks-class-get def :counter-var)))
	 (count                 (1+ (eval counter-var)))
	 (marker                (or use-marker
				    (eval (remarks-class-get def :marker-var))))
	 (set-fn
	  `(lambda (&optional text)
	     (let* ((txt (or text (,read-buffer-function))))
	       (when (not (funcall #',emptyp txt))
		 (save-excursion
		   (set-buffer ,(current-buffer))
		   (remarks-minor-mode nil ',counter-var)
		   (let ((ol  (make-overlay ,beg ,end)))
		     (overlay-put ol 'evaporate t)
		     (overlay-put ol 'duplicable t)
		     (overlay-put ol 'tellib-restore-function
				  #'remarks-properties-restore)
		     (unless (string= ,marker "")
		       (overlay-put ol 'before-string (format ,marker ,count)))
		     (when ,use-edit-function
		       (overlay-put ol 'remarks-edit-remark #',use-edit-function))
		     (overlay-put ol 'remarks ,count)
		     (overlay-put ol 'remarks-class ',class)
		     (overlay-put ol 'face ',face)
		     (overlay-put ol 'remarks-text txt)
		     (remarks-properties-restore ol)
		     )))))))
    (set counter-var count)
    (if dont-edit
	(funcall set-fn text)
      (funcall edit-remark
	       (format "*%s: Remark %i*" buffer-file-name count)
	       text
	       set-fn
	       ;;:show-other-windows t
	       :message message
	       :mode mode-function
	       :keymap mode-map
	       :write-buffer write-buffer-function
	       ))))

;;;###autoload
(defun remarks-edit (&optional use-text-edit overlay)
  "Edit the note at point (see `remarks-minor-mode').
With prefix USE-TEXT-EDIT, the remark will always be opened as a text
file -- which of course leads to problems, if the remark data is no
text. Use with care."
  (interactive "P")
  (let* ((ols    (let ((ols (if overlay
				(list overlay)
			      (overlays-at (point)))))
		   (when ols
		     (tellib-overlay-collect* '(remarks) nil ols))))
	 (ol     (cond
		  ((not ols)
		   nil)
		  ((> (length ols) 1)
		   (let* ((olls (mapcar
				 (lambda (ol)
				   (list (remarks-get-title
					  (overlay-get ol 'remarks-text)
					  (overlay-get ol 'remarks-class))
					 ol))
				 ols))
			  (this (completing-read "Select: " olls nil t)))
		     (when this
		       (cadr (assoc this olls)))))
		  (t
		   (car ols))))
	 (txt0   (overlay-get ol 'remarks-text))
	 (def    (remarks-get-class-def (overlay-get ol 'remarks-class)))
	 (rbf    (remarks-class-get def :read-buffer))
	 (wbf    (remarks-class-get def :write-buffer))
	 (mf     (remarks-class-get def :mode))
	 (mm     (eval (remarks-class-get def :edit-map)))
	 (emptyp (remarks-class-get def :emptyp))
	 (editfn (if use-text-edit
		     (remarks-class-get remarks-class :edit-remark)
		   (or (overlay-get ol 'remarks-edit-remark)
		       (remarks-class-get def :edit-remark))))
	 (set-fn `(lambda ()
		    (let ((txt1 (funcall #',rbf)))
		      (save-excursion
			(set-buffer ,(current-buffer))
			(remarks-minor-mode t))
			(cond
			 ((funcall #',emptyp txt1)
			  (delete-overlay ,ol))
			 ((not (equal (quote ,txt0) txt1))
			  (overlay-put ,ol 'remarks-text txt1)))))))
    (funcall editfn
	     (format "*%s: Remark %i*" buffer-file-name (overlay-get ol 'remarks))
	     txt0
	     set-fn
	     ;;:message "Delete text to remove the remark."
	     :dont-replace-text t
	     :mode mf
	     :keymap mm
	     :write-buffer wbf
	     ;;:show-other-windows t
	     )))

;;;###autoload
(defun remarks-find-link (title link on-exit-function &rest key-args)
  "Find a link."
  (funcall remarks-find-link-function link))

;;;###autoload
(defun remarks-make-link (beg end &rest args)
  "Mark region as link.
You can edit the link by running `remarks-edit' with a prefix -- i.e.
C-u remarks-edit."
  (interactive "r")
  (let ((dest (read-file-name "Destination: ")))
    (when dest
      (apply #'remarks-make beg end
	     (tellib-plist-merge `(:class links :text! ,dest)
				 args)))))
  
(defun remarks-prettyprint (overlays buffer &optional title)
  "Pretty-print the remarks OVERLAYS in BUFFER's."
  (interactive)
  (insert title) (newline)
  (insert (make-string (length title) ?\=)) (newline 2)
  (mapc #'(lambda (ol)
	    (let* ((beg (overlay-start ol))
		   (end (overlay-end ol))
		   (hd  (format "[Remark %i:%i-%i]"
				(overlay-get ol 'remarks)
				beg
				end))
		   (wid (truncate (* (window-width) 0.8)))
		   (wi2 (- wid (length hd))))
	      (insert (if (> wi2 0) (make-string wi2 ?\-) "") hd) (newline)
	      (insert (buffer-substring beg end buffer)) (newline)
	      (insert (make-string wid ?\-)) (newline)
	      (insert (overlay-get ol 'remarks-text))
	      (newline 3)))
	overlays))

;;;###autoload
(defun remarks-summarise (&optional class predicate prettyprint 
				    buffer dont-clear-buffer)
  "Summarise all or a specific CLASSes remarks in the current buffer.
Returns the summary buffer.

Write to BUFFER if provided.

Use PREDICATE (if provided) to test an overlay for eligibility.
PRETTYPRINT overrides the CLASS definition if provided."
  (interactive)
  (let* ((ols (tellib-overlay-collect*
	       '(remarks) nil nil nil
	       `(lambda (ol sym)
		  (and (overlay-get ol sym)
		       (if ',class
			   (equal `,class (overlay-get ol 'remarks-class))
			  t)
		       (if ',predicate
			   (funcall ,predicate ol)
			  t)
		       ))))
	 (def (remarks-get-class-def class))
	 (ppf (or prettyprint
		  (remarks-class-get def :prettyprint)))
	 (ttl (format "Remarks: %s" (buffer-name)))
	 (buf (current-buffer)))
    (if buffer
	(set-buffer buffer)
      (pop-to-buffer (concat "*" ttl "*")))
    (unless dont-clear-buffer
      (delete-region (point-min) (point-max)))
    (funcall ppf ols buf ttl)
    (mapc #'(lambda (this)
	      (delete-overlay this))
	  (tellib-overlay-collect* '(remarks)))
    (current-buffer)))


(defun remarks-install (&optional top-install-flag)
  "Install remarks hooks."
  (tellib-installer '(tellib file-properties) 'remarks top-install-flag))

(defun remarks-uninstall (&optional top-install-flag)
  "Deinstall remarks hooks."
  (tellib-uninstaller '(tellib file-properties) 'remarks top-install-flag))


(provide 'remarks)

;;; REMARKS.EL ends here

;;; Local Variables:
;;; file-properties-flag: t
;;; auto-recompile:1
;;; time-stamp-format:"%y-%02m-%02d"
;;; End:
