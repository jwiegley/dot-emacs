;;; hl-line+.el --- Extensions to hl-line.el.
;;
;; Filename: hl-line+.el
;; Description: Extensions to hl-line.el.
;; Author: Drew Adams
;; Maintainer: Drew Adams (concat "drew.adams" "@" "oracle" ".com")
;; Copyright (C) 2006-2017, Drew Adams, all rights reserved.
;; Created: Sat Aug 26 18:17:18 2006
;; Version: 0
;; Package-Requires: ()
;; Last-Updated: Wed Jun 21 07:33:43 2017 (-0700)
;;           By: dradams
;;     Update #: 555
;; URL: https://www.emacswiki.org/emacs/download/hl-line%2b.el
;; Doc URL: https://www.emacswiki.org/emacs/HighlightCurrentLine
;; Doc URL: https://www.emacswiki.org/emacs/CrosshairHighlighting
;; Keywords: highlight, cursor, accessibility
;; Compatibility: GNU Emacs: 22.x, 23.x, 24.x, 25.x
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
;;    `hl-line-flash-timer', `hl-line-idle-interval',
;;    `hl-line-idle-timer', `hl-line-when-idle-p'.
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
;; 2017/06/21 dadams
;;     hl-line-highlight-now: Inhibit highlighting if selected window is minibuffer window.
;; 2017/06/04 dadams
;;     Added: hl-line-flash-timer.
;;     hl-line-flash-show-period: Allow non-integer non-negative numbers.
;;     hl-line-(un)highlight-now: Added optional BUFFER arg.
;;                                Use hl-line-(un)highlight, not global-hl-line-mode.
;;     hl-line-highlight-now: No-op if hl-line-mode, also.
;;     hl-line-unhighlight-now: No-op if in highlighting mode.
;;     hl-line-flash: No-op if already highlighting or if highlighting inhibited.
;;                    Cancel existing flash timer.
;;     Removed vestigial settings of face hl-line and hl-line-face.
;;     Thx to Vladimir Sedach.
;; 2014/05/17 dadams
;;     hl-line-overlay-priority: Set default value to -50 (work around Emacs bug #16192 fix).
;; 2014/05/20 dadams
;;     (global-)hl-line-highlight: No-op if in the minibuffer (update for Emacs 24.4+).
;; 2013/06/08 dadams
;;     hl-line-inhibit-highlighting-for-modes: Corrected :type.
;;     global-hl-line-highlight defadvice: Respect in hl-line-inhibit-highlighting-for-modes.
;; 2013/01/17 dadams
;;     toggle-hl-line-when-idle: Added optional MSGP arg.
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

;;;###autoload
(defcustom hl-line-flash-show-period 1.0
  "*Number of seconds for `hl-line-flash' to highlight the line."
  :type '(restricted-sexp
          :match-alternatives ((lambda (x) (and (numberp x)  (>= x 0.0))))
          :value [ignore])
  :group 'cursor :group 'hl-line)

;; Possible value: `(Info-mode help-mode view-mode Man-mode)'
;;;###autoload
(defcustom hl-line-inhibit-highlighting-for-modes ()
  "*Modes where highlighting is inhibited for `hl-line-highlight-now'.
A list of `major-mode' values (symbols)."
  :type '(repeat (symbol :tag "Major mode where `hl-line' highlighting is inhibited"))
  :group 'hl-line)

;;;###autoload
(defcustom hl-line-overlay-priority -50
  "*Priority to use for `hl-line-overlay' and `global-hl-line-overlay'.
A higher priority can make the hl-line highlighting appear on top of
other overlays that might exist."
  :type '(choice
          (const   :tag "No priority (default priority)"  nil)
          (integer :tag "Priority"  -50))
  :group 'hl-line)

(defvar hl-line-flash-timer nil "Timer for `hl-line-flash'.")
(make-variable-buffer-local 'hl-line-flash-timer)

(defvar hl-line-idle-interval 5
  "Number of seconds to wait before highlighting current line.
Do NOT change this yourself to change the wait period; instead, use
`\\[hl-line-when-idle-interval]'.")

(defvar hl-line-idle-timer
  (let ((timer  (run-with-idle-timer hl-line-idle-interval t 'hl-line-highlight-now)))
    (cancel-timer timer)
    timer)
  "Timer used to highlight current line whenever Emacs is idle.
Use `toggle-hl-line-when-idle' to turn it on.")

(defvar hl-line-when-idle-p nil
  "Non-nil means highlight current line whenever Emacs is idle.
Do NOT change this yourself; instead, use `\\[toggle-hl-line-when-idle]'.")

(defadvice hl-line-highlight (after set-priority activate)
  "Set the overlay priority to `hl-line-overlay-priority'."
  (unless (window-minibuffer-p)
    (overlay-put hl-line-overlay 'priority hl-line-overlay-priority)))

(defadvice global-hl-line-highlight (around set-priority-+respect-mode-inhibit activate)
  "Set hl-line overlay priority and inhibit for specific modes.
Set the overlay to `hl-line-overlay-priority'.
Respect option `hl-line-inhibit-highlighting-for-modes'."
  (unless (or (window-minibuffer-p)
              (member major-mode hl-line-inhibit-highlighting-for-modes))
    ad-do-it
    (overlay-put global-hl-line-overlay 'priority hl-line-overlay-priority)))

;;;###autoload
(defalias 'toggle-hl-line-when-idle 'hl-line-toggle-when-idle)
;;;###autoload
(defun hl-line-toggle-when-idle (&optional arg msgp)
  "Toggle highlighting the current line when Emacs is idle.
With prefix argument, turn on if ARG > 0; else turn off.

In Lisp code, non-nil optional second arg MSGP means display a message
showing the new value."
  (interactive "P\np")
  (setq hl-line-when-idle-p
        (if arg (> (prefix-numeric-value arg) 0) (not hl-line-when-idle-p)))
  (cond (hl-line-when-idle-p
         (timer-activate-when-idle hl-line-idle-timer)
         (when msgp (message "Idle highlighting of current line is now ON")))
        (t
         (cancel-timer hl-line-idle-timer)
         (when msgp (message "Idle highlighting of current line is now OFF")))))

;;;###autoload
(defun hl-line-when-idle-interval (secs)
  "Set the idle wait for highlighting of current line.
Whenever Emacs is idle for this many seconds, `hl-line-highlight' is
called to highlight the current line.

Use `\\[toggle-hl-line-when-idle] to toggle this idle highlighting."
  (interactive "nIdle seconds to wait, before highlighting current line: ")
  (timer-set-idle-time hl-line-idle-timer (setq hl-line-idle-interval secs) t))

(defun hl-line-highlight-now (&optional buffer)
  "Highlight the current line in BUFFER.
BUFFER defaults to the current buffer."
  (with-current-buffer (or buffer  (current-buffer))
    (unless (or hl-line-mode
                global-hl-line-mode
                (window-minibuffer-p)
                (member major-mode hl-line-inhibit-highlighting-for-modes))
      (let ((hl-line-mode  t)) (hl-line-highlight))
      (add-hook 'pre-command-hook 'hl-line-unhighlight-now))))

(defun hl-line-unhighlight-now (&optional buffer)
  "Unhighlight the current line in BUFFER.
BUFFER defaults to the current buffer."
  (with-current-buffer (or buffer  (current-buffer))
    (unless (or hl-line-mode  global-hl-line-mode) (hl-line-unhighlight))
    (remove-hook 'pre-command-hook 'hl-line-unhighlight-now)))

;;;###autoload
(defalias 'flash-line-highlight 'hl-line-flash)
;;;###autoload
(defun hl-line-flash (&optional seconds)
  "Flash highlighting of current line for `hl-line-flash-show-period' sec.
With a prefix argument, flash for that many seconds."
  (interactive (and current-prefix-arg  (prefix-numeric-value current-prefix-arg)))
  (unless (or hl-line-mode  global-hl-line-mode
              (member major-mode hl-line-inhibit-highlighting-for-modes))
    (unless seconds (setq seconds  hl-line-flash-show-period))
    (if (not hl-line-flash-timer)
        (setq hl-line-flash-timer  (run-at-time seconds nil #'hl-line-unhighlight-now
                                                (current-buffer)))
      (cancel-timer hl-line-flash-timer)
      (timer-set-time hl-line-flash-timer (timer-relative-time (current-time) seconds))
      (timer-activate hl-line-flash-timer))
    (hl-line-highlight-now)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(provide 'hl-line+)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; hl-line+.el ends here
