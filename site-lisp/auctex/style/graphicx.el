;;; graphicx.el --- AUCTeX style file for graphicx.sty

;; Copyright (C) 2000, 2004, 2005, 2014--2017 by Free Software Foundation, Inc.

;; Author: Ryuichi Arafune <arafune@debian.org>
;; Created: 1999/3/20
;; Keywords: tex

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This file is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin St, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;; Commentary:

;;  This package supports the includegraphcics macro in graphicx style.

;; Acknowledgements
;;  Dr. Thomas Baumann <thomas.baumann@ch.tum.de>
;;  David Kastrup <David.Kastrup@t-online.de>
;;  Masayuki Akata <ataka@milk.freemail.ne.jp>

;;; Code:

(defvar LaTeX-graphicx-key-val-options
  '(("bb")
    ("bbllx")
    ("bblly")
    ("bburx")
    ("bbury")
    ("natheight")
    ("natwidth")
    ("viewport")
    ("trim")
    ("hiresbb" ("true" "false"))
    ("angle")
    ("origin")
    ("width"           ("\\textwidth" "\\columnwidth" "\\linewidth"))
    ("height"          ("\\textheight"))
    ("totalheight"     ("\\textheight"))
    ("keepaspectratio" ("true" "false"))
    ("scale")
    ("clip"  ("true" "false"))
    ("draft" ("true" "false"))
    ("quiet")
    ("interpolate" ("true" "false")))
  "Key=value options for graphicx macros.")

(defvar LaTeX-includegraphics-dvips-extensions
  '("eps" "mps" "EPS")
  "List of extensions for image files supported by \"dvips\".")

(defvar LaTeX-includegraphics-pdftex-extensions
  '("png" "pdf" "jpe?g" "jbig2" "jb2" "mps"
    "PNG" "PDF" "JPE?G" "JBIG2" "JB2")
  "List of extensions for image files supported by \"pdftex\" and \"luatex\".")

(defvar LaTeX-includegraphics-xetex-extensions
  '("pdf" "eps" "mps" "ps" "png" "jpe?g" "jp2" "jpf"
    "PDF" "EPS" "MPS" "PS" "PNG" "JPE?G" "JP2" "JPF"
    "bmp" "pict" "psd" "mac" "tga" "gif" "tif" "tiff"
    "BMP" "PICT" "PSD" "MAC" "TGA" "GIF" "TIF" "TIFF")
  "List of extensions for image files supported by \"xetex\".")

(defun LaTeX-arg-graphicx-includegraphics-key-val (optional)
  "Insert key-val for optional argument of \\includegraphics macro.
If OPTIONAL is non-nil, insert argument in square brackets.
Temporarily remove \"space\" from `crm-local-completion-map' and
`minibuffer-local-completion-map' in order to be able to insert
spaces conveniently.

If `TeX-engine' is set to symbol 'default (while
`TeX-PDF-from-DVI' is set to nil) or 'luatex and `TeX-PDF-mode'
is non-nil, add the keys \"page\" and \"pagebox\" to list of
key-val's."
  (let ((crm-local-completion-map
	 (remove (assoc 32 crm-local-completion-map)
		 crm-local-completion-map))
	(minibuffer-local-completion-map
	 (remove (assoc 32 minibuffer-local-completion-map)
		 minibuffer-local-completion-map)))
    (TeX-argument-insert
     (TeX-read-key-val optional
		       (if (and (or (and (eq TeX-engine 'default)
					 (not (TeX-PDF-from-DVI)))
				    (eq TeX-engine 'luatex))
				TeX-PDF-mode)
			   (append '(("page")
				     ("pagebox" ("mediabox"
						 "cropbox"
						 "bleedbox"
						 "trimbox"
						 "artbox")))
				   LaTeX-graphicx-key-val-options)
			 LaTeX-graphicx-key-val-options))
     optional)))

(defun LaTeX-includegraphics-extensions (&optional list)
  "Return appropriate extensions for input files to \\includegraphics."
  (let* ((temp (copy-sequence LaTeX-includegraphics-extensions))
	 (LaTeX-includegraphics-extensions
	  (cond (;; 'default TeX-engine:
		 (if (and (eq TeX-engine 'default)
			  ;; we want to produce a pdf
			  (if TeX-PDF-mode
			      ;; Return t if default compiler produces PDF,
			      ;; nil for "Dvips" or "Dvipdfmx"
			      (not (TeX-PDF-from-DVI))
			    ;; t if pdftex is used in dvi-mode
			    TeX-DVI-via-PDFTeX))
		     ;; We're using pdflatex in pdf-mode
		     (delete-dups
		      (append LaTeX-includegraphics-pdftex-extensions
			      LaTeX-includegraphics-extensions))
		   ;; We're generating a .dvi to process with dvips or dvipdfmx
		   (progn
		     (dolist (x '("jpe?g" "pdf" "png"))
		       (setq temp (remove x temp)))
		     (delete-dups
		      (append LaTeX-includegraphics-dvips-extensions
			      temp)))))
		;; Running luatex in pdf or dvi-mode:
		((eq TeX-engine 'luatex)
		 (if TeX-PDF-mode
		     (delete-dups
		      (append LaTeX-includegraphics-pdftex-extensions
			      LaTeX-includegraphics-extensions))
		   (progn
		     (dolist (x '("jpe?g" "pdf" "png"))
		       (setq temp (remove x temp)))
		     (delete-dups
		      (append LaTeX-includegraphics-dvips-extensions
			      temp)))))
		;; Running xetex in any mode:
		((eq TeX-engine 'xetex)
		 (delete-dups (append LaTeX-includegraphics-xetex-extensions
				      LaTeX-includegraphics-extensions)))
		;; For anything else
		(t
		 LaTeX-includegraphics-extensions))))
    (concat "\\."
	    (mapconcat 'identity
		       (or list LaTeX-includegraphics-extensions)
		       "$\\|\\.")
	    "$")))

(defun LaTeX-includegraphics-read-file-TeX ()
  "Read image file for \\includegraphics.
Offers all graphic files found in the TeX search path.  See
`LaTeX-includegraphics-read-file' for more."
  (completing-read
   "Image file: "
   (TeX-delete-dups-by-car
    (mapcar 'list
	    (TeX-search-files nil LaTeX-includegraphics-extensions t t)))
   nil nil nil))

(defun LaTeX-includegraphics-read-file-relative ()
  "Read image file for \\includegraphics.

Lists all graphic files in the master directory and its
subdirectories and inserts the relative file name.  This option
doesn't works with Emacs 21.3 or XEmacs.  See
`LaTeX-includegraphics-read-file' for more."
  (file-relative-name
   (read-file-name
    "Image file: " nil nil nil nil
    ;; FIXME: Emacs 21.3 and XEmacs 21.4.15 dont have PREDICATE as the sixth
    ;; argument (Emacs 21.3: five args; XEmacs 21.4.15: sixth is HISTORY).
    (lambda (fname)
      (or (file-directory-p fname)
	  (string-match (LaTeX-includegraphics-extensions) fname))))
   (TeX-master-directory)))

(defun LaTeX-arg-includegraphics (_prefix)
  "Ask for mandantory argument for the \\includegraphics command."
  (let* ((image-file (funcall LaTeX-includegraphics-read-file)))
    (TeX-insert-braces 0)
    (insert
     (if LaTeX-includegraphics-strip-extension-flag
	 ;; We don't have `replace-regexp-in-string' in all (X)Emacs versions:
	 (with-temp-buffer
	   (insert image-file)
	   (goto-char (point-max))
	   (when (search-backward-regexp (LaTeX-includegraphics-extensions)
					 nil t 1)
	     (replace-match ""))
	   (buffer-string))
       image-file))))

(TeX-add-style-hook
 "graphicx"
 (lambda ()
   (TeX-add-symbols
    '("reflectbox" "Argument")

    '("resizebox"
      (TeX-arg-eval completing-read
		    (TeX-argument-prompt optional nil "Width")
		    (append '("\\width" "!")
			    (mapcar
			     (lambda (x) (concat TeX-esc (car x)))
			     (LaTeX-length-list))))
      (TeX-arg-eval completing-read
		    (TeX-argument-prompt optional nil "Height")
		    (append '("\\height" "\\totalheight" "\\depth" "!")
			    (mapcar
			     (lambda (x) (concat TeX-esc (car x)))
			     (LaTeX-length-list))))
      "Argument")

    '("resizebox*"
      (TeX-arg-eval completing-read
		    (TeX-argument-prompt optional nil "Width")
		    (append '("\\width" "!")
			    (mapcar
			     (lambda (x) (concat TeX-esc (car x)))
			     (LaTeX-length-list))))
      (TeX-arg-eval completing-read
		    (TeX-argument-prompt optional nil "Height")
		    (append '("\\height" "\\totalheight" "\\depth" "!")
			    (mapcar
			     (lambda (x) (concat TeX-esc (car x)))
			     (LaTeX-length-list))))
      "Argument")

    '("rotatebox" (TeX-arg-conditional (member "graphics" (TeX-style-list))
				       ()
				     ([ TeX-arg-key-val (("x") ("y") ("origin") ("units")) ]))
      "Angle" "Argument")

    '("scalebox" "Horizontal scale" [ "Vertical scale" ] "Argument")

    '("includegraphics" (TeX-arg-conditional (member "graphics" (TeX-style-list))
					     (["llx,lly"] ["urx,ury"])
					   ([ LaTeX-arg-graphicx-includegraphics-key-val ]))
      LaTeX-arg-includegraphics)

    '("includegraphics*" (TeX-arg-conditional (member "graphics" (TeX-style-list))
					      (["llx,lly"] ["urx,ury"])
					    ([ LaTeX-arg-graphicx-includegraphics-key-val ]))
      LaTeX-arg-includegraphics)

    '("graphicspath" t)

    '("DeclareGraphicsExtensions" t)

    '("DeclareGraphicsRule" 4))

   ;; Fontification
   (when (and (featurep 'font-latex)
	      (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("reflectbox" "{")
				("resizebox" "*{{{")
				("rotatebox" "[{{")
				("scalebox" "{[{"))
			      'textual)
     (font-latex-add-keywords '(("includegraphics" "*[[{"))
			      'reference)
     (font-latex-add-keywords '(("graphicspath"              "{")
				("DeclareGraphicsExtensions" "{")
				("DeclareGraphicsRule"       "{{{{"))
			      'function)))
 LaTeX-dialect)

(defvar LaTeX-graphicx-package-options
  '("draft"       "final"         "debugshow"
    "hiderotate"  "hidescale"     "hiresbb"
    "setpagesize" "nosetpagesize" "demo"
    "dvips"       "xdvi"
    "dvipdf"      "dvipdfm"       "dvipdfmx"
    "xetex"       "pdftex"        "luatex"
    "dvisvgm"     "dvipsone"      "dviwindo"
    "emtex"       "dviwin"        "oztex"
    "textures"    "pctexps"       "pctexwin"
    "pctexhp"     "pctex32"       "truetex"
    "tcidvi"      "vtex")
  "Package options for the graphicx package.")

;;; graphicx.el ends here
