;;; sdic-inline-pos-tip.el -- Extension for sdic-inline-mode using pos-tip.el

;; Copyright (C) 2010 S. Irie

;; Author: S. Irie
;; Maintainer: S. Irie
;; Keywords: Tooltip, Dictionary

(defconst sdic-inline-pos-tip-version "0.0.8")

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2, or
;; (at your option) any later version.

;; It is distributed in the hope that it will be useful, but WITHOUT
;; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
;; or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public
;; License for more details.

;; You should have received a copy of the GNU General Public
;; License along with this program; if not, write to the Free
;; Software Foundation, Inc., 59 Temple Place, Suite 330, Boston,
;; MA 02111-1307 USA

;;; Commentary:

;; This program was written as a sample of pos-tip.el library, and
;; provides the tooltip showing word meanings at cursor position
;; like `rikaichan' Firefox extension, using sdic-inline.el library
;; which was written by khiker.

;; *** This program requires pos-tip.el version 0.3.0 or later ***

;;
;; Installation:
;;
;; First, save this file as pos-tip.el and byte-compile in
;; a directory that is listed in load-path.
;;
;; Put the following in your .emacs file:
;;
;;   (require 'sdic-inline-pos-tip)
;;   (setq sdic-inline-display-func 'sdic-inline-pos-tip-show)
;;   (define-key sdic-inline-map "\C-c\C-p" 'sdic-inline-pos-tip-show)
;;
;; and start emacs, then system is enabled.
;;

;;; History:
;; 2010-04-08  S. Irie
;;         * Changed to be available for non-X but graphical frames
;;              (** Require pos-tip.el ver. 0.3.0 or later **)
;;         * Version 0.0.8
;;
;; 2010-03-23  S. Irie
;;         * Changed to perform full justification
;;              (** Require pos-tip.el ver. 0.2.0 or later **)
;;         * Version 0.0.7
;;
;; 2010-03-22  S. Irie
;;         * Changed to perform word wrap or kinsoku shori
;;              (** Require pos-tip.el ver. 0.1.8 or later **)
;;         * Version 0.0.6
;;
;; 2010-03-16  S. Irie
;;         * Bug fix
;;         * Version 0.0.5
;;
;; 2010-03-11  S. Irie
;;         * Modified to simplify implementation
;;         * Fixed typo
;;         * Version 0.0.4
;;
;; 2010-03-09  S. Irie
;;         * Changed to use `pos-tip-split-string'
;;              (** Require pos-tip.el ver. 0.1.0 or later **)
;;         * Version 0.0.3
;;
;; 2010-03-08  S. Irie
;;         * Added options to use substitutive functions in non-X frame
;;         * Version 0.0.2
;;
;; 2010-03-07  S. Irie
;;         * First release
;;         * Version 0.0.1

;; ToDo:

;;; Code:

(require 'sdic-inline)
(require 'pos-tip)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Settings
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar sdic-inline-pos-tip-timeout-auto 5
  "Timeout of tooltip for automatic popup (in seconds).
See `pos-tip-show' for details.")

(defvar sdic-inline-pos-tip-timeout-man 0
  "Timeout of tooltip for manual popup (in seconds).
See `pos-tip-show' for details.")

(defvar sdic-inline-pos-tip-max-width 80
  "Maximum width of tooltip. nil means use display width.")

(defface sdic-inline-pos-tip
  '((t
     :foreground "white"
     :background "RoyalBlue4"))
  "Face for description in sdic-inline-pos-tip's tooltip.")

(defface sdic-inline-pos-tip-entry
  '((t
     :foreground "cyan"
     :bold t
     :inherit sdic-inline-pos-tip))
  "Face for entry in sdic-inline-pos-tip's tooltip.")

(defvar sdic-inline-pos-tip-subst-func-auto
  'sdic-inline-display-minibuffer
  "Function used as substitute for auto-popup in text-only frame.")

(defvar sdic-inline-pos-tip-subst-func-man
  'sdic-inline-display-popup
  "Function used as substitute for manual-popup in text-only frame.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Function
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun sdic-inline-pos-tip-show (&optional entry)
  "Show tooltip which describes the word meanings at current point."
  (interactive)
  (cond
   (window-system
    (if (interactive-p)
	(setq entry sdic-inline-last-entry))
    (when entry
      ;; Use the same font as selected frame in tooltip
      (set-face-font 'sdic-inline-pos-tip (frame-parameter nil 'font))
      ;; Main part
      (let ((width 0)
	    (height 0)
	    ;; "\n" should be propertized by the same face as the text
	    ;; because their height also affect tooltip height.
	    (nl-head (propertize "\n" 'face 'sdic-inline-pos-tip-entry))
	    (nl-desc (propertize "\n" 'face 'sdic-inline-pos-tip)))
	(pos-tip-show-no-propertize
	 ;; Arrange string
	 (mapconcat
	  (lambda (item)
	    (let* ((head (sdicf-entry-headword item))
		   ;; Split and justify the description if longer than max-width
		   (desc (pos-tip-fill-string (sdicf-entry-text item)
					      sdic-inline-pos-tip-max-width
					      1 'full))
		   (w-h (pos-tip-string-width-height desc)))
	      ;; Calculate tooltip width and height
	      (setq width (max width (string-width head) (car w-h))
		    height (+ height 1 (cdr w-h)))
	      ;; Propertize entry string by appropriate faces
	      (concat (propertize head 'face 'sdic-inline-pos-tip-entry)
		      nl-head
		      (propertize desc 'face 'sdic-inline-pos-tip))))
	  entry nl-desc)
	 ;; Face which specifies tooltip's background color
	 'sdic-inline-pos-tip
	 ;; Display current point, then omit POS and WINDOW
	 nil nil
	 ;; Timeout
	 (if (interactive-p)
	     sdic-inline-pos-tip-timeout-man
	   sdic-inline-pos-tip-timeout-auto)
	 ;; Calculate tooltip's pixel size
	 (pos-tip-tooltip-width width (frame-char-width))
	 (pos-tip-tooltip-height height (frame-char-height))))))
   ;; If text-only frame, use substitutive function
   ((interactive-p)
    (if (commandp sdic-inline-pos-tip-subst-func-man)
	(call-interactively sdic-inline-pos-tip-subst-func-man)))
   ((functionp sdic-inline-pos-tip-subst-func-auto )
    (funcall sdic-inline-pos-tip-subst-func-auto entry))))


(provide 'sdic-inline-pos-tip)

;;;
;;; sdic-inline-pos-tip.el ends here
