;;; diff-mode-.el --- Extensions to `diff-mode.el'.
;;
;; Filename: diff-mode-.el
;; Description: Extensions to `diff-mode.el'.
;; Author: Drew Adams
;; Maintainer: Drew Adams
;; Copyright (C) 2004-2012, Drew Adams, all rights reserved.
;; Created: Mon Nov 08 16:36:09 2004
;; Version: 21.0
;; Last-Updated: Sun Jan  1 14:26:39 2012 (-0800)
;;           By: dradams
;;     Update #: 702
;; URL: http://www.emacswiki.org/cgi-bin/wiki/diff-mode-.el
;; Keywords: data, matching, tools, unix, local, font, face
;; Compatibility: GNU Emacs: 21.x, 22.x, 23.x
;;
;; Features that might be required by this library:
;;
;;   None
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Commentary:
;;
;;    Extensions to `diff-mode.el'.
;;
;;  "*Diff*" buffer is highlighted differently.
;;
;;  NOTE: The faces defined here look best on a medium-dark
;;        background, because some are light and some are dark.
;;        Try, for example, setting the background to "LightSteelBlue"
;;        in your `~/.emacs' file: You can do this is via
;;        `special-display-buffer-names':
;;
;;         (setq special-display-buffer-names
;;               (cons '("*Diff*" (background-color . "LightSteelBlue"))
;;                     special-display-buffer-names))
;;
;;        You can alternatively change the background value of
;;        `special-display-frame-alist' and set
;;        `special-display-regexps' to something matching "*info*":
;;
;;         (setq special-display-frame-alist
;;               (cons '(background-color . "LightSteelBlue")
;;                     special-display-frame-alist))
;;         (setq special-display-regexps '("[ ]?[*][^*]+[*]"))
;;
;;
;;  New faces defined here:
;;
;;    `diff-file1-hunk-header', `diff-file2-hunk-header'.
;;
;;  New user options defined here:
;;
;;    `diff-file1-hunk-header-face', `diff-file2-hunk-header-face'.
;;
;;
;;  ***** NOTE: The following faces defined in `diff-mode.el' have
;;              been REDEFINED HERE:
;;
;;    `diff-added', `diff-changed', `diff-context',
;;    `diff-file-header', `diff-header', `diff-hunk-header',
;;    `diff-index', `diff-indicator-added', `diff-indicator-changed',
;;    `diff-indicator-removed', `diff-nonexistent', `diff-removed'.
;;
;;
;;  ***** NOTE: The following variable defined in `diff-mode.el' has
;;              been REDEFINED HERE:
;;
;;    `diff-font-lock-keywords'.
;;
;;
;;  This library should be loaded *before* library `diff-mode.el'.
;;  Put this in your initialization file, `~/.emacs':
;;    (require 'diff-mode-)
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Change Log:
;;
;; 2011/02/11 dadams
;;     Better defaults for faces on dark background.
;; 2011/01/04 dadams
;;     Added autoload cookies for defface.
;; 2008/01/01 dadams
;;     Added :group for deffaces.
;; 2006/01/04 dadams
;;     Updated to use new Emacs 22 face names for indicator faces.
;;       Thanks to Juri Linkov for the letting me know about the new faces.
;;     Updated diff-font-lock-keywords to be = Emacs 22, except for file name.
;; 2006/01/01 dadams
;;     Renamed faces, without "-face".
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth
;; Floor, Boston, MA 02110-1301, USA.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Code:

;;;;;;;;;;;;;;;;;;;;;;;;


;;; Define some additional faces.
;;;###autoload
(defface diff-file1-hunk-header
  '((((background dark))
     (:foreground "Yellow" :background "#3E3E00003E3E")) ; ~ dark magenta
    (t (:foreground "Blue" :background "DarkSeaGreen1")))
  "Face used to highlight a diff hunk for the first `diff' argument."
  :group 'diff-mode)
(defvar diff-file1-hunk-header-face 'diff-file1-hunk-header)

;;;###autoload
(defface diff-file2-hunk-header
    '((((background dark))
       (:foreground "Cyan" :background "#111117175555")) ; ~ dark blue
      (t (:foreground "Red" :background "PaleGoldenrod")))
  "Face used to highlight a diff hunk for the second `diff' argument."
  :group 'diff-mode)
(defvar diff-file2-hunk-header-face 'diff-file2-hunk-header)

;;; These faces are standard in Emacs 22, but they are new for Emacs 21.
;;;###autoload
(defface diff-indicator-changed
  '((((background dark))
       (:foreground "#111117175555" :background "Yellow")) ; ~ dark blue
    (t (:foreground "PaleGoldenrod" :background "MediumBlue")))
  "*Face used to highlight the line-start indicator of a modified line."
  :group 'diff-mode)
(defvar diff-indicator-changed-face 'diff-indicator-changed)

;;;###autoload
(defface diff-indicator-added
  '((((background dark))
       (:foreground "#111117175555" :background "#FFFF9B9BFFFF")) ; ~ dk blue, pink
    (t (:foreground "PaleGoldenrod" :background "DarkGreen")))
  "*Face used to highlight the line-start indicator of an inserted line."
  :group 'diff-mode)
(defvar diff-indicator-added-face 'diff-indicator-added)

;;;###autoload
(defface diff-indicator-removed
  '((((background dark))
       (:foreground "#111117175555" :background "#7474FFFF7474")) ; ~ dk blue,green
    (t (:foreground "PaleGoldenrod" :background "DarkMagenta")))
  "*Face used to highlight the line-start indicator of a removed line."
  :group 'diff-mode)
(defvar diff-indicator-removed-face 'diff-indicator-removed)

;;; Change existing `diff-mode' faces too.
(custom-set-faces
 '(diff-added ((((background dark)) (:foreground "#FFFF9B9BFFFF")) ; ~ pink
               (t (:foreground "DarkGreen"))) 'now)
 '(diff-changed ((((background dark)) (:foreground "Yellow"))
                 (t (:foreground "MediumBlue"))) 'now)
 '(diff-context ((((background dark)) (:foreground "White"))
                 (t (:foreground "Black"))) 'now)
 '(diff-file-header ((((background dark)) (:foreground "Cyan" :background "Black"))
                     (t (:foreground "Red" :background "White"))) 'now)
 ;; '(diff-function ((t (:foreground "Orange"))) 'now)
 '(diff-header ((((background dark)) (:foreground "Cyan"))
                (t (:foreground "Red"))) 'now)
 '(diff-index ((((background dark)) (:foreground "Magenta"))
               (t (:foreground "Green"))) 'now)
 '(diff-nonexistent ((((background dark)) (:foreground "#FFFFFFFF7474")) ; ~ yellow
                     (t (:foreground "DarkBlue"))) 'now)
 )

;;; The only real difference here now from the standard Emacs 22 version is the
;;; use of diff-file1* and diff-file2*.
(defvar diff-font-lock-keywords
  `(
    ("^\\(@@ -[0-9,]+ \\+[0-9,]+ @@\\)\\(.*\\)$" ;unified
     (1 diff-hunk-header-face) (2 diff-function-face))
    ("^\\(\\*\\{15\\}\\)\\(.*\\)$"      ;context
     (1 diff-hunk-header-face) (2 diff-function-face))
    ("^\\*\\*\\* .+ \\*\\*\\*\\*". diff-file1-hunk-header-face) ;context
    ("^--- .+ ----$" . diff-file2-hunk-header-face) ;context
    ("^[0-9,]+[acd][0-9,]+$" . diff-hunk-header-face) ; normal
    ("^---$" . diff-hunk-header-face)   ;normal
    ("^\\(---\\|\\+\\+\\+\\|\\*\\*\\*\\) \\(\\S-+\\)\\(.*[^*-]\\)?\n"
     (0 diff-header-face) (2 diff-file-header-face prepend))
    ("^\\([-<]\\)\\(.*\n\\)" (1 diff-indicator-removed-face) (2 diff-removed-face))
    ("^\\([+>]\\)\\(.*\n\\)" (1 diff-indicator-added-face) (2 diff-added-face))
    ("^\\(!\\)\\(.*\n\\)" (1 diff-indicator-changed-face) (2 diff-changed-face))
    ("^Index: \\(.+\\).*\n" (0 diff-header-face) (1 diff-index-face prepend))
    ("^Only in .*\n" . diff-nonexistent-face)
    ("^\\(#\\)\\(.*\\)"
     (1 (if (facep 'font-lock-comment-delimiter-face)
            'font-lock-comment-face))
     (2 font-lock-comment-face))
    ("^[^-=+*!<>#].*\n" (0 diff-context-face))))

;;;;;;;;;;;;;;;;;;;;;;;

(provide 'diff-mode-)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; diff-mode-.el ends here
