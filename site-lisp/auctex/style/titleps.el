;;; titleps.el --- AUCTeX style for `titleps.sty' (v1.1.1)

;; Copyright (C) 2016 Free Software Foundation, Inc.

;; Author: Arash Esbati <arash@gnu.org>
;; Maintainer: auctex-devel@gnu.org
;; Created: 2016-06-22
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

;; This file adds support for `titleps.sty' (v1.1.1) from 2016/03/15.
;; `titleps.sty' is part of TeXLive.

;;; Code:

(defvar LaTeX-titleps-section-command-list
  '("part"
    "chapter"
    "section"
    "subsection"
    "subsubsection"
    "paragraph"
    "subparagraph")
  "List of sectioning commands available in \"titleps.sty\".")

(defun LaTeX-titleps-section-command-list ()
  "Remove \"chapter\" from variable
`LaTeX-titleps-section-command-list' and return the remainder.
Removal is based on the return value of function
`LaTeX-largest-level'."
  (if (< (LaTeX-largest-level) 2)
      (symbol-value 'LaTeX-titleps-section-command-list)
    (remove "chapter" LaTeX-titleps-section-command-list)))

(defvar LaTeX-titleps-newpagestyle-regexp
  '("\\\\newpagestyle[ \t\n\r%]*{\\([^}]+\\)}" 1 LaTeX-auto-pagestyle)
  "Match the argument of \"\\newpagestyle\" from titleps.sty.")

(add-hook 'TeX-update-style-hook #'TeX-auto-parse t)

(TeX-add-style-hook
 "titleps"
 (lambda ()

   ;; Add titleps to the parser.
   (TeX-auto-add-regexp LaTeX-titleps-newpagestyle-regexp)

   ;; Add \<section>title's
   (dolist (sec (LaTeX-titleps-section-command-list))
     (TeX-add-symbols `(,(concat sec "title") 0)))

   (TeX-add-symbols
   ;; 2. Defining Page Styles
    '("newpagestyle"
      (TeX-arg-eval
       (lambda ()
	 (let ((ps (TeX-read-string
		    (TeX-argument-prompt optional nil "Page style"))))
	   (LaTeX-add-pagestyles ps)
	   (format "%s" ps))))
      (TeX-arg-conditional (y-or-n-p "With optional global style? ")
			   ( [ t ] nil)
			 ( t )))

    '("renewpagestyle" TeX-arg-pagestyle
      (TeX-arg-conditional (y-or-n-p "With optional global style? ")
			   ( [ t ] nil)
			 ( t )))

    '("sethead"
      (TeX-arg-conditional (y-or-n-p "With optional even pages? ")
			   ( [ 3 ] nil nil nil)
			 ( 3 )))

    '("setfoot"
      (TeX-arg-conditional (y-or-n-p "With optional even pages? ")
			   ( [ 3 ] nil nil nil)
			 ( 3 )))

    '("sethead*" 3)
    '("setfoot*" 3)

    '("settitlemarks"
      (TeX-arg-eval mapconcat #'identity
		    (TeX-completing-read-multiple
		     (TeX-argument-prompt optional nil "Level names")
		     (LaTeX-titleps-section-command-list))
		    ","))

    '("settitlemarks"
      (TeX-arg-eval mapconcat #'identity
		    (TeX-completing-read-multiple
		     (TeX-argument-prompt optional nil "Level names")
		     (LaTeX-titleps-section-command-list))
		    ","))

    '("headrule" 0)
    '("setheadrule" "Thickness")

    '("footrule" 0)
    '("setfootrule" "Thickness")

    '("makeheadrule" 0)
    '("makefootrule" 0)

    ;; 3. On \markboth and \markleft
    '("setmarkboth" t)
    '("resetmarkboth" 0)

    ;; 4. Headline/footline width
    '("widenhead"
      (TeX-arg-conditional (y-or-n-p "With optional even pages? ")
			   ( [ 2 ] nil nil)
			 ( 2 )))

    '("widenhead*" 2)

    '("TitlepsPatchSection"
      (TeX-arg-eval completing-read
		    (TeX-argument-prompt optional nil "Sectioning command")
		    (LaTeX-titleps-section-command-list)))

    '("TitlepsPatchSection*"
      (TeX-arg-eval completing-read
		    (TeX-argument-prompt optional nil "Sectioning command")
		    (LaTeX-titleps-section-command-list)))

    ;; 5. Marks
    '("bottitlemarks"     0)
    '("toptitlemarks"     0)
    '("firsttitlemarks"	  0)
    '("nexttoptitlemarks" 0)
    '("outertitlemarks"   0)
    '("innertitlemarks"   0)

    '("newtitlemark" (TeX-arg-macro "Command name"))
    '("newtitlemark*" (TeX-arg-counter "Variable name"))

    '("pretitlemark"
      (TeX-arg-eval completing-read
		    (TeX-argument-prompt optional nil "Sectioning command")
		    (LaTeX-titleps-section-command-list))
      "Text")

    '("pretitlemark*"
      (TeX-arg-eval completing-read
		    (TeX-argument-prompt optional nil "Sectioning command")
		    (LaTeX-titleps-section-command-list))
      "Text")

    '("ifsamemark"
      (TeX-arg-macro "Marks group: \\")
      (TeX-arg-macro "Command: \\")
      2)

    ;; 6. Running heads with floats
    '("setfloathead"
      (TeX-arg-conditional (y-or-n-p "With optional even pages? ")
			   ( [ 3 ] nil nil nil nil [ nil ] )
			 ( 4 [ nil ] )))

    '("setfloatfoot"
      (TeX-arg-conditional (y-or-n-p "With optional even pages? ")
			   ( [ 3 ] nil nil nil nil [ nil ] )
			 ( 4 [ nil ] )))

    '("setfloathead*" 4 [ nil ] )
    '("setfloatfoot*" 4 [ nil ] )

    '("nextfloathead"
      (TeX-arg-conditional (y-or-n-p "With optional even pages? ")
			   ( [ 3 ] nil nil nil nil [ nil ] )
			 ( 4 [ nil ] )))

    '("nextfloatfoot"
      (TeX-arg-conditional (y-or-n-p "With optional even pages? ")
			   ( [ 3 ] nil nil nil nil [ nil ] )
			 ( 4 [ nil ] )))

    '("nextfloathead*" 4 [ nil ] )
    '("nextfloatfoot*" 4 [ nil ] )

    ;; 7. Extra marks: I'm not clear how the marks commands work;
    ;; until then, I ignore them
    )

   (when (and (featurep 'font-latex)
	      (eq TeX-install-font-lock 'font-latex-setup))
     (font-latex-add-keywords '(("newpagestyle"         "{[{")
				("renewpagestyle"       "{[{")
				("settitlemarks"        "*{")
				("widenhead"            "*[[{{")
				("TitlepsPatchSection"  "*{")
				("newtitlemark"         "*{")
				("pretitlemark"         "*{{")
				("nextfloathead"        "*[[[{{{{[")
				("nextfloatfoot"        "*[[[{{{{["))
			      'function)))
 LaTeX-dialect)

(defvar LaTeX-titleps-package-options
  '(;; 4. Headline/footline width
    "nopatches"

    ;; 5. Marks
    "outermarks" "innermarks" "topmarks" "botmarks"

    ;; 6. Running heads with floats
    "psfloats"

    ;; 7. Extra marks
    "extramarks")
  "Package options for the titleps package.")

;;; titleps.el ends here
