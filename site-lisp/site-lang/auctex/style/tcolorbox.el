;;; tcolorbox.el --- AUCTeX style for `tcolorbox.sty' (v4.00)

;; Copyright (C) 2015, 2016 Free Software Foundation, Inc.

;; Author: Tassilo Horn <tsdh@gnu.org>
;; Maintainer: auctex-devel@gnu.org
;; Created: 2015-01-04
;; Keywords: tex

;; This file is part of AUCTeX.

;; AUCTeX is free software; you can redistribute it and/or modify it
;; under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; AUCTeX is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with AUCTeX; see the file COPYING.  If not, write to the Free
;; Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA
;; 02110-1301, USA.

;;; Commentary:

;; This file adds support for `tcolorbox.sty' (v4.00) from 2017/02/16.

;; This style file adds support for core macros and environments and
;; their options provided by `tcolorbox.sty'.  Macros and environments
;; provided by libraries should go in their own style files where the
;; file is prefixed with `tcolorboxlib-',
;; e.g. `tcolorboxlib-raster.el'.

;; Libraries should also append their key=val option to variable
;; `LaTeX-tcolorbox-keyval-options-full'.  This variable is called
;; with macro `\tcbset'.

;;; Code:

;; Needed for compiling `pushnew':
(eval-when-compile (require 'cl))

;; Needed for auto-parsing.
(require 'tex)

;; FIXME: Anything missing?
(defvar LaTeX-tcolorbox-keyval-options
  '(;; 4.1 Title
    ("title")
    ("notitle")
    ("adjusted title")
    ("adjust text")
    ("squeezed title")
    ("squeezed title*")
    ("detach title")
    ("attach title")
    ("attach title to upper")
    ;; 4.2 Subtitle
    ("subtitle style")
    ;; 4.3 Upper Part
    ("upperbox" ("visible" "invisible"))
    ("visible")
    ("invisible")
    ("saveto")
    ;; 4.4 Lower Part
    ("lowerbox" ("visible" "invisible" "ignored"))
    ("savelowerto")
    ("lower separated" ("true" "false"))
    ("savedelimiter")
    ;; 4.5 Colors and Fonts
    ("colframe")
    ("colback")
    ("title filled" ("true" "false"))
    ("colbacktitle")
    ("colupper")
    ("collower")
    ("coltext")
    ("coltitle")
    ("fontupper" ("\\rmfamily" "\\sffamily" "\\ttfamily" "\\mdseries" "\\bfseries"
		  "\\upshape" "\\itshape" "\\slshape" "\\scshape"
		  "\\tiny"  "\\scriptsize" "\\footnotesize"
		  "\\small" "\\normalsize" "\\large"
		  "\\Large" "\\LARGE" "\\huge" "\\Huge" "\\normalfont"))
    ("fontlower" ("\\rmfamily" "\\sffamily" "\\ttfamily" "\\mdseries" "\\bfseries"
		  "\\upshape" "\\itshape" "\\slshape" "\\scshape"
		  "\\tiny"  "\\scriptsize" "\\footnotesize"
		  "\\small" "\\normalsize" "\\large"
		  "\\Large" "\\LARGE" "\\huge" "\\Huge" "\\normalfont"))
    ("fonttitle" ("\\rmfamily" "\\sffamily" "\\ttfamily" "\\mdseries" "\\bfseries"
		  "\\upshape" "\\itshape" "\\slshape" "\\scshape"
		  "\\tiny"  "\\scriptsize" "\\footnotesize"
		  "\\small" "\\normalsize" "\\large"
		  "\\Large" "\\LARGE" "\\huge" "\\Huge" "\\normalfont"))
    ;; 4.6 Text Alignment
    ("halign" ("justify" "left" "flush left" "right"
	       "flush right" "center" "flush center"))
    ("halign lower" ("justify" "left" "flush left" "right"
		     "flush right" "center" "flush center"))
    ("halign title" ("justify" "left" "flush left" "right"
		     "flush right" "center" "flush center"))
    ("flushleft upper")
    ("center upper")
    ("flushright upper")
    ("flushleft lower")
    ("center lower")
    ("flushright lower")
    ("flushleft title")
    ("center title")
    ("flushright title")
    ("valign" ("top" "center" "bottom" "scale" "scale*"))
    ("valign upper" ("top" "center" "bottom" "scale" "scale*"))
    ("valign lower" ("top" "center" "bottom" "scale" "scale*"))
    ("valign scale limit")
    ;; 4.7 Geometry:
    ;; 4.7.1 Width
    ("width")
    ("text width")
    ("add to width")
    ;; 4.7.2 Rules
    ("toprule")
    ("bottomrule")
    ("leftrule")
    ("rightrule")
    ("titlerule")
    ("boxrule")
    ;; 4.7.3 Arcs
    ("arc")
    ("circular arc")
    ("bean arc")
    ("octogon arc")
    ("arc is angular")
    ("arc is curved")
    ("outer arc")
    ("auto outer arc")
    ;; 4.7.4 Spacing
    ("boxsep")
    ("left")
    ("left*")
    ("lefttitle")
    ("leftupper")
    ("leftlower")
    ("right")
    ("right*")
    ("righttitle")
    ("rightupper")
    ("rightlower")
    ("top")
    ("toptitle")
    ("bottom")
    ("bottomtitle")
    ("middle")
    ;; 4.7.5 Size Shortcuts
    ("size" ("normal" "title" "small" "fbox" "tight" "minimal"))
    ("oversize")
    ("toggle left and right" ("none" "forced" "evenpage"))
    ;; 4.8 Corners
    ("sharp corners" ("northwest" "northeast" "southwest" "southeast"
		      "north" "south" "east" "west" "downhill" "uphill" "all"))
    ("rounded corners" ("northwest" "northeast" "southwest" "southeast"
			"north" "south" "east" "west" "downhill" "uphill" "all"))
    ("sharpish corners")
    ;; 4.9 Transparency
    ("opacityframe")
    ("opacityback")
    ("opacitybacktitle")
    ("opacityfill")
    ("opacityupper")
    ("opacitylower")
    ("opacitytext")
    ("opacitytitle")
    ;; 4.10 Height Control
    ("natural height")
    ("height")
    ("height plus")
    ("height from")
    ("text height")
    ("add to height")
    ("add to natural height")
    ("height fill" ("true" "false" "maximum"))
    ("square")
    ("space")
    ("space to upper")
    ("space to lower")
    ("space to both")
    ("space to")
    ("split")
    ("equal height group")
    ("minimum for equal height group")
    ("minimum for current equal height group")
    ("use height from group")
    ;; 4.11 Box Content Additions
    ("before title")
    ("after title")
    ("before upper")
    ("after upper")
    ("after upper*")
    ("before lower")
    ("after lower")
    ("after lower*")
    ("text fill")
    ("tabularx")
    ("tabularx*")
    ("tikz upper")
    ("tikz lower")
    ("tikznode upper")
    ("tikznode lower")
    ("tikznode")
    ("varwidth upper")
    ;; 4.12 Overlays
    ("overlay")
    ("no overlay")
    ("overlay broken")
    ("overlay unbroken")
    ("overlay first")
    ("overlay middle")
    ("overlay last")
    ("overlay unbroken and first")
    ("overlay middle and last")
    ("overlay unbroken and last")
    ("overlay first and middle")
    ;; 4.13 Floating Objects
    ("floatplacement" ("htbp" "t" "b" "h" "p"))
    ("float" ("htbp" "t" "b" "h" "p"))
    ("float*" ("htbp" "t" "b" "h" "p"))
    ("nofloat")
    ("every float" ("\\centering" "\\raggedleft" "\\raggedright"))
    ;; 4.14 Embedding into the Surroundings
    ("before")
    ("after")
    ("parskip")
    ("noparskip")
    ("autoparskip")
    ("nobeforeafter")
    ("forces nobeforeafter")
    ("baseline")
    ("box align" ("bottom" "top" "center" "base"  ))
    ("before skip")
    ("after skip")
    ("beforeafter skip")
    ("left skip")
    ("right skip")
    ("leftright skip")
    ("ignore nobreak" ("true" "false"))
    ("before nobreak")
    ;; 4.15 Bounding Box
    ("enlarge top initially by")
    ("enlarge bottom finally by")
    ("enlarge top at break by")
    ("enlarge bottom at break by")
    ("enlarge top by")
    ("enlarge bottom by")
    ("enlarge left by")
    ("enlarge right by")
    ("enlarge by")
    ("flush left")
    ("flush right")
    ("center")
    ("grow to left by")
    ("grow to right by")
    ("toggle enlargement" ("none" "forced" "evenpage"))
    ("spread inwards")
    ("spread outwards")
    ("move upwards")
    ("move upwards*")
    ;; FIXME: This one should be added w/ `breakable' lib:
    ;; ("fill downwards")
    ("spread upwards")
    ("spread upwards*")
    ("spread sidewards")
    ("spread")
    ("spread downwards")
    ("shrink tight")
    ("extrude left by")
    ("extrude right by")
    ("extrude top by")
    ("extrude bottom by")
    ("extrude by")
    ;; 4.16 Layered Boxes and Every Box Settings
    ("every box")
    ("every box on layer 1")
    ("every box on layer 2")
    ("every box on layer 3")
    ("every box on layer 4")
    ("every box on higher layers")
    ;; 4.17 Capture Mode
    ("capture" ("minipage" "hbox" "fitbox"))
    ("hbox")
    ("minipage")
    ;; 4.18 Text Characteristics
    ("parbox" ("true" "false"))
    ("hyphenationfix" ("true" "false"))
    ;; 4.19 Files
    ("tempfile")
    ;; 4.21 Counters, Labels, and References
    ("phantom")
    ("nophantom")
    ("label")
    ("phantomlabel")
    ;; FIXME: Are these types documented somewhere in cleveref.pdf?
    ("label type")
    ("no label type")
    ("step")
    ("step and label")
    ("list entry")
    ("list text")
    ("add to list")
    ("nameref")
    ;; 4.22 Even and Odd Pages
    ("check odd page" ("true" "false"))
    ("if odd page")
    ("if odd page or oneside")
    ;; FIXME: These two should be added w/ `breakable' lib:
    ;; ("if odd page*")
    ;; ("if odd page or oneside*")
    ;; 4.24 Miscellaneous
    ("reset")
    ("only")
    ("code")
    ("void")
    ;; 6 Side by Side
    ("sidebyside" ("true" "false"))
    ("sidebyside align" ("center" "top" "bottom" "center seam"
			 "top seam" "bottom seam"))
    ("sidebyside gap")
    ("lefthand width")
    ("righthand width")
    ("lefthand ratio")
    ("righthand ratio")
    ;; 8 Recording options
    ("record")
    ("no recording"))
  "Key=value options for tcolorbox macros and environments.")

(defvar LaTeX-tcolorbox-keyval-options-local nil
   "Buffer-local key=value options for tcolorbox macros and environments.")
(make-variable-buffer-local 'LaTeX-tcolorbox-keyval-options-local)

(defvar LaTeX-tcolorbox-keyval-options-full nil
  "Key=value options of tcolorbox core and all loaded libraries.")
(make-variable-buffer-local 'LaTeX-tcolorbox-keyval-options-full)

(defvar LaTeX-tcolorbox-tcbox-options
  '(;; 4.20 \tcbox Specials
    ("tcbox raise")
    ("tcbox raise base")
    ("on line")
    ("tcbox width" ("auto" "auto limited" "forced center"
		    "forced left" "forced right" "minimum center"
		    "minimum left" "minimum right")))
  "Key=value options only for \\tcbox and \\tcboxmath from tcolorbox.sty.")

(defvar LaTeX-tcolorbox-init-options
  '(;; 5 Initialization Option Keys
    ;; 5.1 Numbered Boxes
    ("auto counter")
    ("use counter from")
    ("use counter")
    ("use counter*")
    ("no counter")
    ("number within" ("part" "chapter" "section" "subsection"))
    ("number format" ("\\arabic" "\\roman" "\\Roman" "\\Alph" "\\alph"))
    ("number freestyle")
    ("crefname")
    ("Crefname")
    ("blend into" ("figures" "tables" "listings"))
    ("blend before title" ("colon" "dash" "colon hang" "dash hang"))
    ("blend before title code")
    ;; 5.2 Lists of tcolorboxes
    ("list inside")
    ("list type"))
  "Initialization key=value options for tcolorbox macros.")

(defvar LaTeX-tcolorbox-library-list
  '("skins"
    "vignette"
    "raster"
    "listings"
    "listingsutf8"
    "minted"
    "theorems"
    "breakable"
    "magazine"
    "fitting"
    "hooks"
    "xparse"
    "external"
    "documentation"
    "many" "most" "all")
  "List with libraries provided by tcolorbox package.")

;; Setup for \newtcolorbox:
(TeX-auto-add-type "tcolorbox-newtcolorbox" "LaTeX" "tcolorbox-newtcolorboxes")

(defvar LaTeX-tcolorbox-newtcolorbox-regexp
  `(,(concat "\\\\\\(re\\)?newtcolorbox"
	     "[ \t\n\r%]*"
	     "\\(?:\\[[^][]*"
	       "\\(?:{[^}{]*"
		 "\\(?:{[^}{]*"
		   "\\(?:{[^}{]*}[^}{]*\\)*"
		 "}[^}{]*\\)*"
	       "}[^][]*\\)*"
	     "\\]\\)?"
	     "[ \t\n\r%]*"
	     "{\\([a-zA-Z0-9]+\\)}"
	     "[ \t\n\r%]*"
	     "\\(?:\\[\\([0-9]*\\)\\]\\)?"
	     "[ \t\n\r%]*"
	     "\\(\\[\\)?")
    (2 3 4 1) LaTeX-auto-tcolorbox-newtcolorbox)
  "Matches the arguments of \\newtcolorbox from tcolorbox package.")

;; Setup for \newtcbox:
(TeX-auto-add-type "tcolorbox-newtcbox" "LaTeX" "tcolorbox-newtcboxes")

(defvar LaTeX-tcolorbox-newtcbox-regexp
  `(,(concat "\\\\\\(re\\)?newtcbox"
	     "[ \t\n\r%]*"
	     "\\(?:\\[[^][]*"
	       "\\(?:{[^}{]*"
		 "\\(?:{[^}{]*"
		   "\\(?:{[^}{]*}[^}{]*\\)*"
		 "}[^}{]*\\)*"
	       "}[^][]*\\)*"
	     "\\]\\)?"
	     "[ \t\n\r%]*"
	     "{\\\\\\([a-zA-Z]+\\)}"
	     "[ \t\n\r%]*"
	     "\\(?:\\[\\([0-9]*\\)\\]\\)?"
	     "[ \t\n\r%]*"
	     "\\(\\[\\)?")
    (2 3 4 1) LaTeX-auto-tcolorbox-newtcbox)
  "Matches the arguments of \\newtcbox from tcolorbox package.")

;; Setup for \tcbuselibrary:
(TeX-auto-add-type "tcolorbox-tcbuselibrary" "LaTeX" "tcbuselibraries")

(defvar LaTeX-tcolorbox-tcbuselibrary-regexp
  '("\\\\tcbuselibrary{\\([^}]+\\)}"
    1 LaTeX-auto-tcolorbox-tcbuselibrary)
  "Matches the arguments of \\tcbuselibrary from tcolorbox package.")

(defun LaTeX-tcolorbox-load-used-libraries ()
  "Check which tcolorbox libraries are loaded and run respective style hooks.
This functions checks the arguments of \\tcbuselibrary and the
name of libraries given in the optional argument of \\usepackage
call for tcolorbox and runs the style hook for them.  The file
for style must have the prefix \"tcolorboxlib-\" in the name,
e.g. \"tcolorboxlib-raster.el\"."
  (when (LaTeX-tcolorbox-tcbuselibrary-list)
    (let (libs)
      (dolist (x (LaTeX-tcolorbox-tcbuselibrary-list))
	(push (TeX-replace-regexp-in-string "[ %\n\r\t]" "" (car x)) libs))
      (setq libs (mapconcat #'identity libs ","))
      (dolist (x (split-string libs "," t))
	(TeX-run-style-hooks (concat "tcolorboxlib-" x)))))
  (when (assoc "tcolorbox" LaTeX-provided-package-options)
    (let ((opts (cdr (assoc "tcolorbox" LaTeX-provided-package-options))))
      (dolist (x opts)
	(when (member x LaTeX-tcolorbox-library-list)
	  (TeX-run-style-hooks (concat "tcolorboxlib-" x)))))))

(defun LaTeX-tcolorbox-update-style-key ()
  "Update some key=values in `LaTeX-tcolorbox-keyval-options-local'."
  ;; Update the key=values for coloring.
  (let* ((keys '("colframe"
		 "colback"
		 "colbacktitle"
		 "colupper"
		 "collower"
		 "coltext"
		 "coltitle"))
	 (tmp (copy-alist LaTeX-tcolorbox-keyval-options-local)))
    (dolist (key keys)
      (setq tmp (assq-delete-all (car (assoc key tmp)) tmp))
      (pushnew
       (list key (mapcar #'car (LaTeX-xcolor-definecolor-list))) tmp :test #'equal))
    (setq LaTeX-tcolorbox-keyval-options-local (copy-alist tmp)))
  (setq LaTeX-tcolorbox-keyval-options-full
	(copy-alist LaTeX-tcolorbox-keyval-options-local)))

(defun LaTeX-tcolorbox-auto-prepare ()
  "Clear various LaTeX-tcolorbox-* variables before parsing."
  (setq LaTeX-auto-tcolorbox-newtcolorbox  nil
	LaTeX-auto-tcolorbox-newtcbox      nil
	LaTeX-auto-tcolorbox-tcbuselibrary nil))

(defun LaTeX-tcolorbox-auto-cleanup ()
  "Process parsed results."
  ;; Process new env's from \newtcolorbox
  (dolist (newtcbox (apply #'append LaTeX-tcolorbox-newtcolorbox-list))
    (let ((box (nth 0 newtcbox))
	  (arg (nth 1 newtcbox))
	  (opt (nth 2 newtcbox))
	  (renew (when (string= (nth 3 newtcbox) "re")
		   (nth 3 newtcbox))))
      ;; When renew'ing, delete any entry from
      ;; `LaTeX-environment-list' first:
      (when renew
	(setq LaTeX-environment-list
	      (assq-delete-all
	       (car (assoc box (LaTeX-environment-list)))
	       LaTeX-environment-list)))
      (cond (;; opt. 1st argument and mandatory argument(s)
	     (and arg (not (string= arg ""))
		  opt (not (string= opt  "")))
	     (LaTeX-add-environments
	      (list box
		    'LaTeX-env-args
		    (vector 'TeX-arg-key-val 'LaTeX-tcolorbox-keyval-options-local)
		    (1- (string-to-number arg)))))
	    (;; mandatory argument(s) only
	     (and arg (not (string= arg ""))
		  (string-equal opt ""))
	     (LaTeX-add-environments
	      (list box (string-to-number arg))))
	    (t ; No args
	     (LaTeX-add-environments (list box))))))
  ;;
  ;; Process new macros from \newtcbox
  (dolist (newtcbox (apply #'append LaTeX-tcolorbox-newtcbox-list))
    (let ((box (nth 0 newtcbox))
	  (arg (nth 1 newtcbox))
	  (opt (nth 2 newtcbox))
	  (renew (when (string= (nth 3 newtcbox) "re")
		   (nth 3 newtcbox))))
      ;; When renew'ing, delete any entry from `TeX-symbol-list'
      ;; first:
      (when renew
	(setq TeX-symbol-list
	      (assq-delete-all
	       (car (assoc box (TeX-symbol-list)))
	       TeX-symbol-list)))
      (cond (;; opt. 1st argument and mandatory argument(s)
	     (and arg (not (string= arg ""))
		  opt (not (string= opt  "")))
	     (TeX-add-symbols (list box
			       (vector 'TeX-arg-key-val 'LaTeX-tcolorbox-keyval-options-local)
			       (1- (string-to-number arg)))))
	    (;; mandatory argument(s) only
	     (and arg (not (string= arg ""))
		  (string-equal opt ""))
	     (TeX-add-symbols (list box (string-to-number arg))))
	    (t ; No args -- in pratice, this will probably never happen
	     (TeX-add-symbols (list box))))))
  ;;
  ;; Update key=vals
  (LaTeX-tcolorbox-update-style-key)
  ;;
  ;; Load style hooks for libraries, if any.
  (LaTeX-tcolorbox-load-used-libraries))

(add-hook 'TeX-auto-prepare-hook #'LaTeX-tcolorbox-auto-prepare t)
(add-hook 'TeX-auto-cleanup-hook #'LaTeX-tcolorbox-auto-cleanup t)
(add-hook 'TeX-update-style-hook #'TeX-auto-parse t)

(TeX-add-style-hook
 "tcolorbox"
 (lambda ()

   ;; Activate the buffer-local version of key-vals.
   (setq LaTeX-tcolorbox-keyval-options-local
	 (copy-alist LaTeX-tcolorbox-keyval-options))

   ;; Collect key=val's from libraries in
   ;; `LaTeX-tcolorbox-keyval-options-full'; \tcbset needs this:
   (setq LaTeX-tcolorbox-keyval-options-full
	 (copy-alist LaTeX-tcolorbox-keyval-options-local))

   ;; Add tcolorbox to the parser.
   (TeX-auto-add-regexp LaTeX-tcolorbox-newtcolorbox-regexp)
   (TeX-auto-add-regexp LaTeX-tcolorbox-newtcbox-regexp)
   (TeX-auto-add-regexp LaTeX-tcolorbox-tcbuselibrary-regexp)

   ;; We just run the style hook for `xcolor' which is loaded by pgf.sty
   (TeX-run-style-hooks "xcolor")

   ;; FIXME: Anything missing?
   (TeX-add-symbols

    ;; 1.3 Libraries
    '("tcbuselibrary"
      (TeX-arg-eval mapconcat #'identity
		    (TeX-completing-read-multiple
		     (TeX-argument-prompt optional nil "Libraries")
		     LaTeX-tcolorbox-library-list) ","))

    ;; 3 Macros for Box Creation
    '("tcblower" 0)

    '("tcbset"
      (TeX-arg-key-val LaTeX-tcolorbox-keyval-options-full))

    '("tcbsetforeverylayer"
      (TeX-arg-key-val LaTeX-tcolorbox-keyval-options-local))

    '("tcbox"
      [ TeX-arg-eval TeX-read-key-val optional
		     (append
		      LaTeX-tcolorbox-tcbox-options
		      LaTeX-tcolorbox-keyval-options-local) ]
      t)

    '("newtcolorbox"
      [ TeX-arg-key-val LaTeX-tcolorbox-init-options ]
      "Name"
      [ TeX-arg-define-macro-arguments ]
      (TeX-arg-key-val LaTeX-tcolorbox-keyval-options-local))

    '("renewtcolorbox"
      [ TeX-arg-key-val LaTeX-tcolorbox-init-options ]
      (TeX-arg-eval completing-read
		    (TeX-argument-prompt optional nil "Color box")
		    (LaTeX-tcolorbox-newtcolorbox-list))
      [ TeX-arg-define-macro-arguments ]
      (TeX-arg-key-val LaTeX-tcolorbox-keyval-options-local))

    '("newtcbox"
      [ TeX-arg-key-val LaTeX-tcolorbox-init-options ]
      TeX-arg-macro
      [ TeX-arg-define-macro-arguments ]
      (TeX-arg-key-val LaTeX-tcolorbox-keyval-options-local))

    '("renewtcbox"
      [ TeX-arg-key-val LaTeX-tcolorbox-init-options ]
      (TeX-arg-eval
       (lambda ()
	 (let ((macro (completing-read
		       (TeX-argument-prompt optional nil "Macro: \\" t)
		       (LaTeX-tcolorbox-newtcbox-list))))
	   (concat TeX-esc macro))))
      [ TeX-arg-define-macro-arguments ]
      (TeX-arg-key-val LaTeX-tcolorbox-keyval-options-local))

    '("tcolorboxenvironment"
      TeX-arg-environment
      (TeX-arg-key-val LaTeX-tcolorbox-keyval-options-local))

    ;; 4.16 Layered Boxes and Every Box Settings
    '("tcbsetmanagedlayer" "Number")

    ;; 4.22 Even and Odd Pages
    '("tcbifoddpage" 2)
    '("tcbifoddpageoroneside" 2)
    '("thetcolorboxnumber" 0)
    '("thetcolorboxpage" 0)

    ;; 5.2 Lists of tcolorboxes
    '("tcblistof"
      [ TeX-arg-eval completing-read
		     (TeX-argument-prompt optional nil "Macro")
		     (if (< (LaTeX-largest-level) 2)
			 '("\\chapter" "\\section" "\\subsection" "\\subsubsection")
		       '("\\section" "\\subsection" "\\subsubsection")) ]
      2)

    ;; 7 Saving and Loading of Verbatim Texts
    '("tcbusetemp")

    ;; 8 Recording
    '("tcbstartrecording" [ "File name" ])
    '("tcbstoprecording")
    '("tcbrecord" t)
    '("tcbinputrecords" [ TeX-arg-file ]) ) ; Terminate TeX-add-symbols

   (LaTeX-add-environments
    ;; 3 Macros for Box Creation: Main env
    '("tcolorbox" LaTeX-env-args
      [ TeX-arg-key-val LaTeX-tcolorbox-keyval-options-local ])

    ;; 7 Saving and Loading of Verbatim Texts
    '("tcbverbatimwrite" "File name")
    '("tcbwritetemp"))

   ;; Do not indent text in verbatim environments:
   (make-local-variable 'LaTeX-indent-environment-list)
   (add-to-list 'LaTeX-indent-environment-list
		'("tcbverbatimwrite" current-indentation) t)
   (add-to-list 'LaTeX-indent-environment-list
		'("tcbwritetemp" current-indentation) t)

   ;; Fontification
   (when (and (featurep 'font-latex)
	      (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("tcbuselibrary"        "{")
				("tcbset"               "{")
				("tcbsetforeverylayer"  "{")
				("tcbox"                "[{")
				("newtcolorbox"         "[{[[{")
				("renewtcolorbox"       "[{[[{")
				("newtcbox"             "[{[[{")
				("renewtcbox"           "[{[[{")
				("tcolorboxenvironment" "{{")
				("tcbsetmanagedlayer"   "{"))
			      'function)))
 LaTeX-dialect)

(defvar LaTeX-tcolorbox-package-options LaTeX-tcolorbox-library-list
  "Package options for the tcolorbox package.")

;;; tcolorbox.el ends here
