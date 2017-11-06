;;; fvextra.el --- AUCTeX style for `fvextra.sty' (v1.2.1)

;; Copyright (C) 2017 Free Software Foundation, Inc.

;; Author: Arash Esbati <arash@gnu.org>
;; Maintainer: auctex-devel@gnu.org
;; Created: 2017-03-05
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

;; This file adds support for `fvextra.sty' (v1.2.1) from 2016/09/02.
;; `fvextra.sty' is part of TeXLive.

;;; Code:

;; Needed for compiling `pushnew':
(eval-when-compile (require 'cl))

(defvar LaTeX-fvextra-key-val-options
  '(;; 3 General options
    ("curlyquotes" ("true" "false"))
    ("highlightcolor")
    ("highlightlines")
    ("linenos" ("true" "false"))
    ("mathescape" ("true" "false"))
    ("numberfirstline" ("true" "false"))
    ;; ("numbers" ("none" "left" "right" "both"))
    ("space" ("\\textvisiblespace"))
    ("spacecolor" ("none"))
    ("stepnumberfromfirst" ("true" "false"))
    ("stepnumberoffsetvalues" ("true" "false"))
    ("tab" ("\\FancyVerbTab"))
    ("tabcolor" ("none"))
    ;; 5.1 Line breaking options
    ("breakafter" ("none"))
    ("breakaftergroup" ("true" "false"))
    ("breakaftersymbolpre")
    ("breakaftersymbolpost")
    ("breakanywhere" ("true" "false"))
    ("breakanywheresymbolpre")
    ("breakanywheresymbolpost")
    ("breakautoindent" ("true" "false"))
    ("breakbefore")
    ("breakbeforegroup" ("true" "false"))
    ("breakbeforesymbolpre")
    ("breakbeforesymbolpost")
    ("breakindent")
    ("breaklines" ("true" "false"))
    ("breaksymbol")
    ("breaksymbolleft")
    ("breaksymbolright")
    ("breaksymbolindent")
    ("breaksymbolindentleft")
    ("breaksymbolindentright")
    ("breaksymbolsep")
    ("breaksymbolsepleft")
    ("breaksymbolsepright"))
  "Key=value options for fvextra macros and environments.")

(defun LaTeX-fvextra-update-key-val ()
  "Update `LaTeX-fancyvrb-key-val-options-local' with key=vals from \"fvextra.sty\"."
  ;; Delete the key "numbers" from `LaTeX-fancyvrb-key-val-options-local':
  (setq LaTeX-fancyvrb-key-val-options-local
	(assq-delete-all (car (assoc "numbers" LaTeX-fancyvrb-key-val-options-local))
			 LaTeX-fancyvrb-key-val-options-local))
  ;; Add the key with "both" value:
  (add-to-list 'LaTeX-fancyvrb-key-val-options-local
	       '("numbers" ("none" "left" "right" "both")))
  ;; Add color values to resp. keys:
  (when (or (member "xcolor" (TeX-style-list))
	    (member "color" (TeX-style-list)))
    (let* ((colorcmd (if (member "xcolor" (TeX-style-list))
			 #'LaTeX-xcolor-definecolor-list
		       #'LaTeX-color-definecolor-list))
	   (keys '("highlightcolor"
		   "rulecolor"
		   "fillcolor"
		   "tabcolor"
		   "spacecolor"))
	   (tmp (copy-alist LaTeX-fancyvrb-key-val-options-local)))
      (dolist (x keys)
	(setq tmp (assq-delete-all (car (assoc x tmp)) tmp))
	(if (string= x "highlightcolor")
	    (pushnew (list x (mapcar #'car (funcall colorcmd))) tmp :test #'equal)
	  (pushnew (list x (append '("none") (mapcar #'car (funcall colorcmd)))) tmp :test #'equal)))
      (setq LaTeX-fancyvrb-key-val-options-local
	    (copy-alist tmp)))))

(add-hook 'TeX-auto-cleanup-hook #'LaTeX-fvextra-update-key-val t)
(add-hook 'TeX-update-style-hook #'TeX-auto-parse t)

(TeX-add-style-hook
 "fvextra"
 (lambda ()

   ;; Run the style hook for "fancyvrb"
   (TeX-run-style-hooks "fancyvrb")

   ;; Append `LaTeX-fvextra-key-val' to `LaTeX-fancyvrb-key-val-options-local':
   (setq LaTeX-fancyvrb-key-val-options-local
	 (append LaTeX-fvextra-key-val-options
		 LaTeX-fancyvrb-key-val-options-local))

   (TeX-add-symbols
    ;; 4.1 Line and text formatting
    "FancyVerbFormatText"

    ;; 5.3.2 Breaks within macro arguments
    "FancyVerbBreakStart"
    "FancyVerbBreakStop"

    ;; 5.3.3 Customizing break behavior
    "FancyVerbBreakAnywhereBreak"
    "FancyVerbBreakBeforeBreak"
    "FancyVerbBreakAfterBreak"))
 LaTeX-dialect)

(defvar LaTeX-fvextra-package-options nil
  "Package options for the fvextra package.")

;;; fvextra.el ends here
