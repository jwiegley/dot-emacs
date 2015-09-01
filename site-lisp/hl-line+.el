;;; hl-line+.el --- Extensions to hl-line.el.
;; 
;; Filename: hl-line+.el
;; Description: Extensions to hl-line.el.
;; Author: Drew Adams
;; Maintainer: Drew Adams
;; Copyright (C) 2006-2012, Drew Adams, all rights reserved.
;; Created: Sat Aug 26 18:17:18 2006
;; Version: 22.0
;; Last-Updated: Fri May 18 07:04:49 2012 (-0700)
;;           By: dradams
;;     Update #: 465
;; URL: http://www.emacswiki.org/cgi-bin/wiki/hl-line+.el
;; Keywords: highlight, cursor, accessibility
;; Compatibility: GNU Emacs: 22.x, 23.x
;; 
;; Features that might be required by this library:
;;
;;   `hl-line'.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;;; Commentary: 
;;
;;  This library extends standard library `hl-line.el' in these ways:
;;
;;  1. As an alternative to turning on `hl-line' highlighting at all
;;     times, you can turn it on only when Emacs is idle.  To do that,
;;     use command `toggle-hl-line-when-idle' and customize
;;     `global-hl-line-mode' to nil.
;;
;;  2. As another alternative, you can turn it on for only a few
;;     seconds.  To do that, use command `flash-line-highlight' and
;;     customize `global-hl-line-mode' to nil.
;;
;;  3. It provides a face, `hl-line', that you can customize, instead
;;     of using option `hl-line-face'.  
;;
;;     I suggested #3 to the Emacs developers, and it was added to
;;     Emacs 22, but with a different default value.  If you use
;;     library `crosshairs.el', you might want to customize this to a
;;     value similar to what is used there, so that the horizontal and
;;     vertical highlights will be the same.
;;
;;  4. Option `hl-line-overlay-priority' is provided, so that you can
;;     make hl-line highlighting appear on top of other overlay
;;     highlighting that might exist.
;;
;;  To use this library, put this in your Emacs init file (~/.emacs):
;;
;;    (require 'hl-line+) ; Load this file (it will load `hl-line.el')
;;
;;  To turn on `global-hl-line-mode' only when Emacs is idle, by
;;  default, add this line also to your init file:
;;
;;    (toggle-hl-line-when-idle 1) ; Highlight only when idle
;;
;;  You can use command `toggle-hl-line-when-idle' to turn idle
;;  highlighting on and off at any time.  You can use command
;;  `hl-line-when-idle-interval' to change the number of idle seconds
;;  to wait before highlighting.
;;
;;
;;  See also these libraries:
;;
;;  * `col-highlight.el', which highlights the current column.
;;
;;  * `crosshairs.el', which highlights the current line and the
;;    current column, at the same time.  It requires libraries
;;    `col-highlight.el' and `hl-line+.el'.
;;
;;  * `hl-spotlight.el', which extends `hl-line.el' by spotlighting
;;    the lines around the cursor.
;;
;;  * `cursor-chg.el' or library `oneonone.el', to change the cursor
;;    type when Emacs is idle.
;;
;;
;;  Faces defined here:
;;
;;    `hl-line'.
;;
;;  User options defined here:
;;
;;    `hl-line-flash-show-period',
;;    `hl-line-inhibit-highlighting-for-modes',
;;    `hl-line-overlay-priority'.
;;
;;  Commands defined here:
;;
;;    `flash-line-highlight', `hl-line-flash',
;;    `hl-line-toggle-when-idle', `hl-line-when-idle-interval',
;;    `toggle-hl-line-when-idle'.
;;
;;  Non-interactive functions defined here:
;;
;;    `hl-line-highlight-now', `hl-line-unhighlight-now'.
;;
;;  Internal variables defined here:
;;
;;    `hl-line-idle-interval', `hl-line-idle-timer',
;;    `hl-line-when-idle-p'.
;;
;;
;;  ***** NOTE: The following non-interactive functions defined in
;;              `hl-line.el' have been ADVISED HERE (to respect option
;;              `hl-line-overlay-priority'):
;;
;;    `global-hl-line-highlight', `hl-line-highlight'.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;;; Change Log:
;;
;; 2012/05/18 dadams
;;     Added: hl-line-overlay-priority, defadvice for (global-)hl-line-highlight.
;; 2011/01/04 dadams
;;     Added autoload cookies for defcustom, defface and commands.
;; 2010/10/03 dadams
;;     hl-line-flash:
;;       Set ARG in interactive spec and use it.  Thx to Philip Weaver.
;; 2009/12/18 dadams
;;     Added: hl-line-inhibit-highlighting-for-modes.
;;     hl-line-highlight-now: Respect hl-line-inhibit-for-modes.  Thx to Sylecn.
;; 2009/02/16 dadams
;;     Removed spotlight stuff - moved to new library hl-spotlight.el.
;; 2009/02/15 dadams
;;     Added: hl-spotlight(-height|-old-state|widen|limits|mode),
;;            global-hl-spotlight-mode.
;; 2008/01/28 dadams
;;     Fix from Yann Yodique: Moved adding/removing hl-line-unhighlight-now as
;;     pre-command-hook from hl-line-toggle-when-idle to hl-line-(un)highlight-now.
;; 2008/01/20 dadams
;;     Renamed: line-show-period to hl-line-flash-show-period.
;; 2007/10/11 dadams
;;     Commentary typo: toggle-cursor-type-when-idle -> toggle-hl-line-when-idle.
;; 2007/01/10 dadams
;;     Update commentary to indicate that the face is now provided by default.
;; 2006/09/08 dadams
;;     Added: flash-line-highlight, hl-line-flash.
;;     Renamed: hl-line-when-idle(-off) to hl-line-(un)highlight-now.
;; 2006/09/04 dadams
;;     Added: hl-line-when-idle-p, hl-line-idle-interval, hl-line-idle-timer,
;;            hl-line-toggle-when-idle, hl-line-when-idle-interval,
;;            hl-line-when-idle(-off).
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 3, or
;; (at your option) any later version.
;; 
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.
;; 
;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth
;; Floor, Boston, MA 02110-1301, USA.
;; 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;;; Code:

(require 'hl-line)

(defvar hl-line-face)                   ; Quiet the byte-compiler.
(defvar global-hl-line-mode)            ; Quiet the byte-compiler.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This will be ignored, since this is now defined by default in Emacs 22.
;; I include it here as a different face definition that you might want to try.
;;;###autoload
(defface hl-line '((t (:background "SlateGray3"))) ; Try also (:underline "Yellow")
  "*Face to use for `hl-line-face'." :group 'hl-line)
(setq hl-line-face 'hl-line)

;;;###autoload
(defcustom hl-line-flash-show-period 1
  "*Number of seconds for `hl-line-flash' to highlight the line."
  :type 'integer :group 'cursor :group 'hl-line)

;; Possible value: `(Info-mode help-mode view-mode Man-mode)'
;;;###autoload
(defcustom hl-line-inhibit-highlighting-for-modes ()
  "*Modes where highlighting is inhibited for `hl-line-highlight-now'.
A list of `major-mode' values (symbols)."
  :type 'list :group 'hl-line)

;;;###autoload
(defcustom hl-line-overlay-priority 300
  "*Priority to use for `hl-line-overlay' and `global-hl-line-overlay'.
A higher priority can make the hl-line highlighting appear on top of
other overlays that might exist."
  :type '(choice
          (const   :tag "No priority (default priority)"  nil)
          (integer :tag "Priority"  300))
  :group 'hl-line)

(defvar hl-line-idle-interval 5
  "Number of seconds to wait before turning on `global-hl-line-mode'.
Do NOT change this yourself to change the wait period; instead, use
`\\[hl-line-when-idle-interval]'.")

(defvar hl-line-idle-timer
  (progn                                ; Cancel to prevent duplication.
    (when (boundp 'hl-line-idle-timer) (cancel-timer hl-line-idle-timer))
    (run-with-idle-timer hl-line-idle-interval t 'hl-line-highlight-now))
  "Timer used to turn on `global-hl-line-mode' whenever Emacs is idle.")

;; Turn it off, by default.  You must use `toggle-hl-line-when-idle' to turn it on.
(cancel-timer hl-line-idle-timer)

(defvar hl-line-when-idle-p nil
  "Non-nil means to turn on `global-hl-line-mode' whenever Emacs is idle.
Do NOT change this yourself; instead, use `\\[toggle-hl-line-when-idle]'.")

(defadvice hl-line-highlight (after set-priority activate)
  "Set the overlay priority to `hl-line-overlay-priority'."
  (overlay-put hl-line-overlay 'priority hl-line-overlay-priority))

(defadvice global-hl-line-highlight (after set-priority activate)
  "Set the overlay priority to `hl-line-overlay-priority'."
  (overlay-put global-hl-line-overlay 'priority hl-line-overlay-priority))

;;;###autoload
(defalias 'toggle-hl-line-when-idle 'hl-line-toggle-when-idle)
;;;###autoload
(defun hl-line-toggle-when-idle (&optional arg)
  "Turn on or off using `global-hl-line-mode' when Emacs is idle.
When on, use `global-hl-line-mode' whenever Emacs is idle.
With prefix argument, turn on if ARG > 0; else turn off."
  (interactive "P")
  (setq hl-line-when-idle-p
        (if arg (> (prefix-numeric-value arg) 0) (not hl-line-when-idle-p)))
  (cond (hl-line-when-idle-p
         (timer-activate-when-idle hl-line-idle-timer)
         (message "Turned ON using `global-hl-line-mode' when Emacs is idle."))
        (t
         (cancel-timer hl-line-idle-timer)
         (message "Turned OFF using `global-hl-line-mode' when Emacs is idle."))))

;;;###autoload
(defun hl-line-when-idle-interval (secs)
  "Set wait until using `global-hl-line-mode' when Emacs is idle.
Whenever Emacs is idle for this many seconds, `global-hl-line-mode'
will be turned on.

To turn on or off using `global-hl-line-mode' when idle,
use `\\[toggle-hl-line-when-idle]."
  (interactive "nSeconds to idle, before using `global-hl-line-mode': ")
  (timer-set-idle-time hl-line-idle-timer (setq hl-line-idle-interval secs) t))

(defun hl-line-highlight-now ()
  "Turn on `global-hl-line-mode' and highlight current line now."
  (unless (or global-hl-line-mode
              (member major-mode hl-line-inhibit-highlighting-for-modes))
    (global-hl-line-mode 1)
    (global-hl-line-highlight)
    (add-hook 'pre-command-hook 'hl-line-unhighlight-now)))
    
(defun hl-line-unhighlight-now ()
  "Turn off `global-hl-line-mode' and unhighlight current line now."
  (global-hl-line-mode -1)
  (global-hl-line-unhighlight)
  (remove-hook 'pre-command-hook 'hl-line-unhighlight-now))

;;;###autoload
(defalias 'flash-line-highlight 'hl-line-flash)
;;;###autoload
(defun hl-line-flash (&optional arg)
  "Highlight the current line for `hl-line-flash-show-period' seconds.
With a prefix argument, highlight for that many seconds."
  (interactive "P")
  (hl-line-highlight-now)
  (let ((line-period  hl-line-flash-show-period))
    (when arg (setq line-period  (prefix-numeric-value arg)))
    (run-at-time line-period nil #'hl-line-unhighlight-now)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(provide 'hl-line+)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; hl-line+.el ends here
