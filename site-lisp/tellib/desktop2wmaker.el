;;; desktop2wmaker.el --- Make a WindowMaker menu out of Redhat .desktop files

;; Copyright (C) 2003 Thomas Link

;; Author: Thomas Link AKA samul AT web DOT de
;; Time-stamp: <2003-04-18>
;; Keywords:

(defconst desktop2wmaker-version "1.0")
(defconst desktop2wmaker-homepage
  "http://members.a1.net/t.link/CompEmacsDesktopToWmaker.html")
 
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

; The elisp function `desktop2wmaker' searches the directories in
; `desktop2wmaker-dir-list' for .desktop files and builds a
; Windowmaker-menu, which is written to `desktop2wmaker-out'. 
; After writing the file, the shell-command `desktop2wmaker-postprocess'
; is run on it. Make sure that your LANG-variable and
; `desktop2wmaker-lang' are set properly. `desktop2wmaker' does not try to
; recreate the menu of the Gnome/KDE environments, but builds a menu based
; on the applications' categories.
; 
; In order to use the "Rebuild menu" entry, you have to declare
; `desktop2wmaker' as autoload and to run gnuserv (and of course (X)Emacs
; as well). Put something like this into your init file:
; 
; <example>
; 	(autoload 'desktop2wmaker "desktop2wmaker"
; 	  "Read *.desktop files and write a WindowMaker menu file." t)
; 	(unless (get-process "gnuserv")
; 	  (gnuserv-start))
; </example>
; 
; If you don't run (X)Emacs in background all the time, change the value
; of `desktop2wmaker-preferred-rebuild-method' to "emacs" or invoke the
; function as =(desktop2wmaker nil "emacs")=. From the shell, you could
; run this function as:
; 
; <example>
; 	emacs -batch -vanilla -l PATH_TO_DESKTOP2WMAKER.EL -eval '(desktop2wmaker t "emacs")'
; </example>
; 
; The `desktop2wmaker-out' menu file can be included in WMRootMenu by
; inserting something like this:
; 
; <example>
; 	(Desktop, OPEN_MENU, "~/GNUstep/Defaults/desktop-menu"),
; </example>

;;; Change log:

;;; To do:

; - Don't know what to do with some command line switches

;;; Code:

;;(require 'tellib)
(require 'cl)

(defgroup desktop2wmaker nil
  "Make a WindowMaker menu out of *.desktop files."
  :link `(url-link :tag "Homepage" ,desktop2wmaker-homepage)
  :link '(emacs-commentary-link :tag "Commentary" "desktop2wmaker.el")
  :prefix "desktop2wmaker-"
  :group 'convenience)

(defcustom desktop2wmaker-dir-list
  '(
    "/usr/share/desktop-menu-patches/"
    "/usr/share/applications/"
    ;;"/usr/share/gnome/"
    ;;"/var/lib/menu/kde/"
    "/etc/X11/applnk/"
    "~/.gnome/apps/"
    )
  "*The directory with desktop files."
  :type '(repeat (directory :value ""))
  :group 'desktop2wmaker)

(defcustom desktop2wmaker-out "~/GNUstep/Defaults/desktop-menu"
  "*The file to be written with the menu data."
  :type 'file
  :group 'desktop2wmaker)

(defcustom desktop2wmaker-query-overwrite-flag t
  "*Query user before overwriting `desktop2wmaker-out'."
  :type 'boolean
  :group 'desktop2wmaker)

(defcustom desktop2wmaker-max 35
  "*Maximal length for submenus."
  :type 'integer
  :group 'desktop2wmaker)

(defcustom desktop2wmaker-postprocess
  "which recode && recode u8 %s"
  "*The shell-command for post-processing the menu file."
  :type 'string
  :group 'desktop2wmaker)

(defcustom desktop2wmaker-lang (let ((str (getenv "LANG")))
				 (if (string-match "^\\(..\\)" str)
				     (match-string 1 str)
				   ""))
  "*Use program names of this language."
  :type 'string
  :group 'desktop2wmaker)

(defcustom desktop2wmaker-name "Desktop"
  "*The menu's name."
  :type 'string
  :group 'desktop2wmaker)

(defcustom desktop2wmaker-sound 'alarm
  "*The sound (see `sound-alist') to be played after having built the menu."
  :type 'symbol
  :group 'desktop2wmaker)

(defcustom desktop2wmaker-synonym-categories
  '(
    ("Utilities" "Utility" "UtilityApplication")
    ("Applications" "Application")
    ("Settings" "AdvancedSettings")
    ("System" "SystemSetup")
    )
  "*A list of list of synonyms."
  :type '(repeat (repeat (string :value "")))
  :group 'desktop2wmaker)

(defcustom desktop2wmaker-rightmost-cat-only-flag t
  "*Register only an application's right-most category."
  :type 'boolean
  :group 'desktop2wmaker)

(defcustom desktop2wmaker-custom-categories
  '(
    ("PDA"
     (lambda (exec name)
       (let ((case-fold-search t))
	 (string-match "\\(pilot\\|\\<pda\\>\\)" (concat exec " " name)))))
    ("RedHat"
     (lambda (exec name)
       (let ((case-fold-search t))
	 (string-match "\\<\\(redhat\\|rhn\\)-" exec))))
    )
  "*A list of custom categories.
An entry has the form '\(category predicate)."
  :type '(repeat (list :value '("" nil)
		       (string :tag "Name")
		       (function :tag "Predicate")))
  :group 'desktop2wmaker)
  
(defcustom desktop2wmaker-ignored-categories
  '("^\\W*$"
    ;;"^Application" "^Utilities" "^UtilityApplication"
    ;;"^Accessibility" "^AdvancedSettings" "^Internet" "^ProjectManagement"
    ;;"^RasterGraphics" "^Spreadsheet" "^TerminalEmulator" "^VectorGraphics"
    ;;"^WordProcessor"
    "^X-Red-Hat" "^X-KDE"
    "^Gnome$" "^KDE$"
    "^GTK$" "^QT$")
  "*A list of regexps for matching categories that should be ignored."
  :type '(repeat (regexp :value ""))
  :group 'desktop2wmaker)

(defcustom desktop2wmaker-include-uncategorized-flag t
  "*Non-nil means include uncategorized applications in the menu."
  :type 'boolean
  :group 'desktop2wmaker)

(defvar desktop2wmaker-rebuild-methods
  `(("gnuclient" "gnuclient -batch -eval '(desktop2wmaker t)'")
    ("emacs" ,(format "%s %s %S %s"
		      (if (featurep 'xemacs)
			  "xemacs"
			"emacs")
		      "-batch -vanilla -l"
		      (file-name-sans-extension (locate-library "desktop2wmaker.el"))
		      "-eval '(desktop2wmaker t \"emacs\")'")))
  "A list of possible rebuild methods.")

(defcustom desktop2wmaker-preferred-rebuild-method "gnuclient"
  "*The command to be run for rebuilding the menu."
  :type `(choice
	  ,@(mapcar (lambda (elt)
		      (let ((n (first elt)))
			`(string :tag ,n :value ,n)))
		    desktop2wmaker-rebuild-methods))
  :group 'desktop2wmaker)


(defvar desktop2wmaker-unknown "*Unknown*" "A marker for uncategorized apps.")


(defun desktop2wmaker-check-custom-cats (cats exec name)
  "Check if there is a custom category defined for EXEC and/or NAME."
  (when (and exec name)
    (catch 'exit
      (mapc (lambda (elt)
	      (let ((ccat (first elt))
		    (pred (second elt)))
		(when (funcall pred exec name)
		  (throw 'exit (nconc cats (list ccat))))))
	    desktop2wmaker-custom-categories)
      cats)))

(defun desktop2wmaker-substitute-synonymous-cats (cats)
  "Replace synonymous categories in CATS with canonic names."
  (delete-duplicates
   (loop for c in (sort cats #'string<) collect
     (let ((m (member-if (lambda (e)
			   (member c e))
			 desktop2wmaker-synonym-categories)))
       (if m
	   (first (first m))
	 c)))))

(defun desktop2wmaker-parse-file (desktop-file name-pat name-local-pat
					       exec-pat cat-pat)
  "Parse DESKTOP-FILE."
  (labels ((finder (pattern)
		   (when pattern
		     (let ((case-fold-search t))
		       (goto-char (point-min))
		       (when (re-search-forward pattern nil t)
			 (match-string 1))))))
    (with-temp-buffer
      (insert-file-contents desktop-file)
      (let* ((name       (or (finder name-local-pat)
			     (finder name-pat)))
	     (exec       (finder exec-pat))
	     (cat        (when (and name exec)
			   (let ((cat (finder cat-pat)))
			     (if (and desktop2wmaker-include-uncategorized-flag
				      (null cat))
				 (desktop2wmaker-check-custom-cats
				  (list desktop2wmaker-unknown)
				  exec name)
			       (let ((cat (when cat
					    (desktop2wmaker-check-custom-cats
					     (delete-if
					      (lambda (elt)
						(member-if
						 (lambda (pat)
						   (let ((case-fold-search t))
						     (string-match pat elt)))
						 desktop2wmaker-ignored-categories))
					      (split-string-by-char cat ?\;))
					     exec
					     name))))
				 (desktop2wmaker-substitute-synonymous-cats
				  (if desktop2wmaker-rightmost-cat-only-flag
				      (last cat)
				    cat))))))))
	(if (and name exec cat)
	    (values name exec cat)
	  (progn
	    (message
	     "desktop2wmaker: Missing info: file=%S name=%S exec=%S cat=%S"
	     desktop-file name exec cat)
	    (values nil nil nil)))))))

(defun desktop2wmaker-write-menu-file (cats data rebuild)
  "Write the menu data to `desktop2wmaker-out'."
  (let* (
	 ;;	 (menu-beg "(")
	 ;;	 (menu-end ")")
	 ;;	 (menu-hd-end "")
	 ;;	 (menu-sep ",")
	 ;;	 (entry-beg "(")
	 ;;	 (entry-end ")")
	 ;;	 (entry-sep ",")
	 (menu-beg "")
	 (menu-end "   END")
	 (menu-hd-end "   MENU")
	 (menu-sep "")
	 (entry-beg "")
	 (entry-end "")
	 (entry-sep "")
	 (catn (length cats))
	 (lev2 (make-string 2 ?\ ))
	 (lev4 (make-string 4 ?\ ))
	 (lev6 (make-string 6 ?\ ))
	 (lev8 (make-string 8 ?\ ))
	 )
    (labels ((replace-switches (string name)
			       (let ((rv string))
				 (mapc #'(lambda (this)
					   (let ((sc (nth 0 this))
						 (rs (nth 1 this)))
					     (let ((case-fold-search nil))
					       (setq rv (replace-in-string
							 rv
							 (regexp-quote sc) rs
							 t)))))
				       `(("%i" "")
					 ("%m" "")
					 ("%f" "")
					 ("%F" "")
					 ("%u" "")
					 ("%U" "")
					 ;;("%c" ,name)
					 ("-caption \"%c\"" "")
					 ("-caption %c" "")
					 ))
				 rv))
	     (concat-entries (lst level)
			     (loop for this in lst concat
			       (destructuring-bind (name exec this-cat) this
				 (format "%s\n%s%s\"%s -- %s\"%s EXEC%s %S%s" 
					 menu-sep
					 level entry-beg name
					 (file-name-nondirectory
					  (first (split-string-by-char exec ?\ )))
					 entry-sep entry-sep
					 (replace-switches exec name)
					 entry-end))))
	     (wrap-menu (apps appsn)
			(if (> appsn desktop2wmaker-max)
			    (let* ((len (/ appsn desktop2wmaker-max))
				   (data
				    (loop for n from 0 to len collect
				      (if (< n len)
					  (prog1
					      (subseq apps 0 desktop2wmaker-max)
					    (setq apps (subseq apps desktop2wmaker-max)))
					apps))))
			      (mapconcat
			       (lambda (lst)
				 (let ((name (concat
					      (destructuring-bind (name exec this-cat)
						  (first lst)
						(if (> (length name) 3)
						    (subseq name 0 3)
						  name))
					      " .. "
					      (destructuring-bind (name exec this-cat)
						  (car (last lst))
						(if (> (length name) 3)
						    (subseq name 0 3)
						  name)))))
				   (concat
				    (format "%s\n%s%s\n%s%S%s"
					    menu-sep
					    lev4 menu-beg
					    lev6 name menu-hd-end)
				    (concat-entries lst lev8)
				    (format "\n%s%S%s" lev6 name menu-end))))
			       data
			       "\n"))
			  (concat-entries apps lev6))))
    (when (or (not (file-exists-p desktop2wmaker-out))
	      (not desktop2wmaker-query-overwrite-flag)
	      (y-or-n-p (format "desktop2wmaker: File %S exists. Overwrite it? "
				(file-name-nondirectory desktop2wmaker-out))))
      (with-temp-file desktop2wmaker-out
	(insert (format "%s\n%s%S%s" menu-beg lev2 desktop2wmaker-name menu-hd-end))
	(let ((data (sort (copy-sequence data)
			  (lambda (e1 e2) (string< (first e1) (first e2))))))
	  (loop
	    for cat in (desktop2wmaker-substitute-synonymous-cats
			(copy-sequence cats))
	    for count from 1 to catn
	    do
	    (progn
	      (message "desktop2wmaker: Writing category %S (%i/%i)" cat count catn)
	      (let* ((apps (loop for this in data append
			     (let ((app-cat (third this)))
			       (when (member-if (if (string= cat
							     desktop2wmaker-unknown)
						    (lambda (c)
						      (eq c desktop2wmaker-unknown))
						  (lambda (c)
						    (string= cat c)))
						app-cat)
				 (list this)))))
		     (appsn (length apps)))
		(insert (format "%s\n%s%s\n%s%S%s"
				menu-sep
				lev2 menu-beg
				lev4 cat menu-hd-end))
		(insert (wrap-menu apps appsn))
		;;(insert (format "\n  %s" menu-end))))
		(insert (format "\n%s%S%s" lev4 cat menu-end))))))
	;;(insert (format "\n%s\n" menu-end))))))
	(insert (format "%s\n%s%s%S%s EXEC%s %S%s"
			menu-sep
			lev4 entry-beg "[[ Rebuild Menu ]]" entry-sep entry-sep
			rebuild
			entry-end))
	(insert (format "\n%S%s\n" desktop2wmaker-name menu-end)))
      (unless (string= desktop2wmaker-postprocess "")
	(shell-command
	 (format desktop2wmaker-postprocess desktop2wmaker-out)))))))

;;;###autoload
(defun desktop2wmaker (&optional batch-mode rebuild-method)
  "Read *.desktop files and write a WindowMaker menu file."
  (interactive "P")
  (let ((flst (loop for d in desktop2wmaker-dir-list append
		(let ((d (expand-file-name d)))
		  (when (file-exists-p d)
		    (message "desktop2wmaker: Scanning %S" d)
		    (split-string-by-char
		     (shell-command-to-string
		      (format "find %S -type f -name '*.desktop'" d))
		     ?\n)))))
	(desktop2wmaker-query-overwrite-flag (if batch-mode
						 nil
					       desktop2wmaker-query-overwrite-flag))
	(rebuild (second (or (assoc (or rebuild-method
					desktop2wmaker-preferred-rebuild-method)
				    desktop2wmaker-rebuild-methods)
			     (error (format "desktop2wmaker: Unknown rebuild method: %s"
					    rebuild-method)))))
	(read-execs nil)
	(read-files nil)
	(data nil)
	(cats nil)
	(name-default-pattern "^Name=\\(.*\\)$")
	(name-local-pattern (unless (string= desktop2wmaker-lang "")
			      (concat "^Name\\["
				      desktop2wmaker-lang
				      "\\]=\\(.*\\)$")))
	(cats-pattern "^Categories=\\(.*\\)$")
	(exec-pattern "^Exec=\\(.*\\)$"))
    (loop for file in flst do
      (unless (or (string= file "")
		  (member (file-name-nondirectory file) read-files))
	(multiple-value-bind
	    (name exec cat)
	    (desktop2wmaker-parse-file file
				       name-default-pattern
				       name-local-pattern
				       exec-pattern
				       cats-pattern)
	  (when (and (and name exec cat)
		     (not (member exec read-execs)))
	    (setq data (nconc data (list `(,name ,exec ,cat)))
		  read-files (adjoin file read-files)
		  read-execs (adjoin exec read-execs)
		  cats (nunion cats cat :test #'string=))))))
    (desktop2wmaker-write-menu-file cats data rebuild)
    (when desktop2wmaker-sound
      (play-sound desktop2wmaker-sound))
    (message "desktop2wmaker: Finished!")))
;;test: (desktop2wmaker)
;;test: (desktop2wmaker t)
;;test: (desktop2wmaker t "emacs")
;;test: (desktop2wmaker t "nope")
;;test: (find-file desktop2wmaker-out)


(provide 'desktop2wmaker)

;;; desktop2wmaker.el ends here

;;; Local Variables:
;;; auto-recompile:1
;;; time-stamp-format:"%y-%02m-%02d"
;;; End:
