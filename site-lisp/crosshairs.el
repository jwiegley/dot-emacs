;;; crosshairs.el --- Highlight the current line and column.
;;
;; Filename: crosshairs.el
;; Description: Highlight the current line and column.
;; Author: Drew Adams
;; Maintainer: Drew Adams (concat "drew.adams" "@" "oracle" ".com")
;; Copyright (C) 2006-2017, Drew Adams, all rights reserved.
;; Created: Fri Sep 08 13:09:19 2006
;; Version: 0
;; Package-Requires: ((hl-line+ "0") (col-highlight "0") (vline "0"))
;; Last-Updated: Mon Jun 26 15:48:30 2017 (-0700)
;;           By: dradams
;;     Update #: 511
;; URL: http://www.emacswiki.org/emacs/download/crosshairs.el
;; Doc URL: http://www.emacswiki.org/CrosshairHighlighting
;; Keywords: faces, frames, emulation, highlight, cursor, accessibility
;; Compatibility: GNU Emacs: 22.x, 23.x, 24.x, 25.x
;;
;; Features that might be required by this library:
;;
;;   `col-highlight', `hl-line', `hl-line+', `vline'.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Commentary:
;;
;;  This library highlights the current line and the current column.
;;  It combines the features of libraries `hl-line.el', `hl-line+.el',
;;  and `col-highlight.el', which let you highlight the line or column
;;  individually.  See those libraries for more information, in
;;  particular for user options that affect the behavior.
;;
;;  If you want the horizontal and vertical highlighting to look the
;;  same, then:
;;
;;  1. Set option `col-highlight-vline-face-flag' to non-nil.
;;  2. Customize faces `col-highlight' and `hl-line' to look the same.
;;
;;  Command `crosshairs-mode' toggles this highlighting on and off.
;;  You can do this twice in succession to flash the crosshairs to
;;  show you where the cursor is.  An alternative way to
;;  flash-highlight is to use command `flash-crosshairs' (once).
;;
;;  Command `crosshairs-highlight' shows crosshairs highlighting until
;;  your next action (next command, technically).  Command
;;  `crosshairs-unhighlight' turns off crosshairs highlighting due to
;;  `crosshairs-highlight'.
;;
;;  With no prefix arg, command `crosshairs' is
;;  `crosshairs-highlight'.  With a prefix arg, it is
;;  `crosshairs-mode'.
;;
;;  You can also have crosshairs highlighting come on automatically,
;;  when Emacs is idle.  Command `toggle-crosshairs-when-idle' toggles
;;  this mode.
;;
;;  You can use command `flash-crosshairs' to do what its name says
;;  when you switch buffers or windows.  Here is how one user did it
;;  (rejoin the split URL):
;;  http://unix.stackexchange.com/questions/83167/emacs-finding-the-
;;  cursor-in-multiple-windows
;;
;;
;;  See also:
;;
;;  * Library `hl-line+.el', which highlights the current line.
;;
;;  * Library `col-highlight.el', which highlights the current column.
;;
;;  * Library `cursor-chg.el' or library `oneonone.el', to change the
;;    cursor type when Emacs is idle.
;;
;;
;;  User options defined here:
;;
;;    `crosshairs-mode'.
;;
;;  Commands defined here:
;;
;;    `crosshairs', `crosshairs-flash', `crosshairs-highlight',
;;    `crosshairs-mode', `crosshairs-toggle-when-idle',
;;    `crosshairs-unhighlight', `flash-crosshairs',
;;    `toggle-crosshairs-when-idle'.
;;
;;  Internal variables defined here:
;;
;;    `crosshairs-flash-col-timer', `crosshairs-flash-line-timer',
;;    `crosshairs-highlight-when-idle-p'.
;;
;;  Suggested alternative key bindings:
;;
;;      (global-set-key [(control ?+)] 'crosshairs)
;;   or (global-set-key [(control ?+)] 'crosshairs-mode)
;;   or (global-set-key [(control ?+)] 'crosshairs-flash)
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Change Log:
;;
;; 2017/06/26 dadams
;;     crosshairs-flash:
;;       Use hl-line-unhighlight-now, not global-hl-line-unhighlight, for
;;       crosshairs-flash-line-timer.  Thx to Dan Harms.
;; 2014/11/28 dadams
;;     crosshairs-mode: Call global-hl-line-unhighlight-all (Emacs 24.4+).
;;     crosshairs-highlight:
;;       Push global-hl-line-overlay to global-hl-line-overlays (Emacs 24.4+).
;;     crosshairs-unhighlight: Call global-hl-line-unhighlight-all (Emacs 24.4+).
;; 2014/07/22 dadams
;;     Removed extra, vestigial package-requires.
;; 2012/12/25 dadams
;;     Added Package-Requires.
;; 2012/05/18 dadams
;;     Removed: crosshairs-overlay-priority.  Instead, use vline-overlay-priority
;;              and col-highlight-overlay-priority.
;;     crosshairs-mode, crosshairs-(un)highlight:
;;       Do not set the overlay priority - done using defadvice in hl-line+.el and
;;       col-highlight.el.
;; 2012/05/17 dadams
;;     crosshairs-mode: Made it respect crosshairs-overlay-priority.
;;     Removed: crosshairs-vline-same-face-flag.
;; 2011/01/03 dadams
;;     Added autoload cookies for defgroup, defcustoms, commands.
;; 2010/06/29 dadams
;;     Added: crosshairs-overlay-priority.
;;     crosshairs-(un)highlight: Set/remove priority if crosshairs-overlay-priority.
;; 2008/09/03 dadams
;;     crosshairs-mode: Don't set previous state if explicit ARG.
;;                      Added message indicating position.
;;     Added: crosshairs, crosshairs-(un)highlight.
;; 2008/08/31 dadams
;;     crosshairs-flash: Cancel timers at the outset.
;;                       Remove hl-line-unhighlight-now from pre-command-hook.
;; 2008/08/08 dadams
;;     Added: crosshairs-flash-col-timer, crosshairs-flash-line-timer.
;;     crosshairs-flash:
;;       Call col-highlight-(un)highlight with arg t.
;;       Save unhighlighting timers in crosshairs-flash-(col|line)-timer.
;;       First, cancel unhighlighting timers.
;; 2008/01/21 dadams
;;     Use vline.el now, instead of column-marker.el.
;;     Added group crosshairs, option crosshairs-vline-same-face-flag.
;;     crosshairs-mode, crosshairs-toggle-when-idle:
;;       If both are already on or off, reflect that as the crosshair state.
;;     crosshairs-toggle-when-idle:
;;       crosshairs-highlight-when-idle-p, not col-highlight-when-idle-p.
;;     crosshairs-flash:
;;       Save/restore global-hl-line-mode.
;;       Clear and rehighlight column initially.  Maybe highlight twice (bug).
;;       Don't use highlight modes to unhighlight - just unhighlight.
;;       Renamed: line-show-period to hl-line-flash-show-period.
;;     Removed semi-support for Emacs 20.
;; 2006/09/08 dadams
;;     Created.
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

(require 'hl-line+) ;; Requires `hl-line.el'.
(require 'col-highlight) ;; Requires `vline.el'.

(defvar global-hl-line-overlays)        ; In `hl-line.el' (Emacs 24.4+)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;###autoload
(defgroup crosshairs nil
  "Highlight the current line and column."
  :prefix "crosshairs-"
  :group 'editing :group 'cursor :group 'hl-line :group 'frames
  :link `(url-link :tag "Send Bug Report"
                   ,(concat "mailto:" "drew.adams" "@" "oracle" ".com?subject=\
crosshairs.el bug: \
&body=Describe bug here, starting with `emacs -q'.  \
Don't forget to mention your Emacs and library versions."))
  :link '(url-link :tag "Other Libraries by Drew"
          "http://www.emacswiki.org/DrewsElispLibraries")
  :link '(url-link :tag "Download"
          "http://www.emacswiki.org/crosshairs.el"))

(defvar crosshairs-highlight-when-idle-p nil
  "Non-nil means highlight current line and column when Emacs is idle.
Do NOT change this yourself; instead, use
`\\[toggle-crosshairs-when-idle]'.")

(defvar crosshairs-flash-line-timer (timer-create)
  "Timer used to unhighlight current line for `crosshairs-flash'.")

(defvar crosshairs-flash-col-timer (timer-create)
  "Timer used to unhighlight current column for `crosshairs-flash'.")

;;;###autoload
(define-minor-mode crosshairs-mode
    "Toggle highlighting the current line and column.
With ARG, turn highlighting on if and only if ARG is positive."
  :init-value nil :global t :group 'crosshairs
  :link `(url-link :tag "Send Bug Report"
                   ,(concat "mailto:" "drew.adams" "@" "oracle" ".com?subject=\
crosshairs.el bug: \
&body=Describe bug here, starting with `emacs -q'.  \
Don't forget to mention your Emacs and library versions."))
  :link '(url-link :tag "Other Libraries by Drew"
          "http://www.emacswiki.org/DrewsElispLibraries")
  :link '(url-link :tag "Download"
          "http://www.emacswiki.org/crosshairs.el")
  :link '(url-link :tag "Description"
          "http://www.emacswiki.org/ChangingCursorDynamically")
  :link '(emacs-commentary-link :tag "Commentary" "crosshairs")
  ;; If both were already on or off, reflect that as the previous crosshairs state.
  (unless arg
    (cond ((and global-hl-line-mode column-highlight-mode)
           (setq crosshairs-mode nil))
          ((and (not global-hl-line-mode) (not column-highlight-mode))
           (setq crosshairs-mode t))))
  (cond (crosshairs-mode
         (unless global-hl-line-mode
           (global-hl-line-mode 1)
           (global-hl-line-highlight))
         (column-highlight-mode 1)
         (message "Point: %d - Crosshairs mode enabled" (point)))
        (t
         (global-hl-line-mode -1)
         (global-hl-line-unhighlight)
         (when (fboundp 'global-hl-line-unhighlight-all) ; Emacs 24.4+
           (global-hl-line-unhighlight-all))
         (column-highlight-mode -1)
         (message "Point: %d - Crosshairs mode disabled" (point)))))

;;;###autoload
(defalias 'toggle-crosshairs-when-idle 'crosshairs-toggle-when-idle)
;;;###autoload
(defun crosshairs-toggle-when-idle (&optional arg)
  "Toggle highlighting the current line and column when Emacs is idle.
With prefix argument, turn on if ARG > 0; else turn off.
You can use commands `col-highlight-set-interval' and
`hl-line-when-idle-interval' to change the idle times."
  (interactive "P")
  ;; First, if both are already on or off, reflect that as the crosshair state.
  (when (or (and hl-line-when-idle-p col-highlight-when-idle-p)
            (and (not hl-line-when-idle-p) (not col-highlight-when-idle-p)))
    (setq crosshairs-highlight-when-idle-p hl-line-when-idle-p))
  (setq crosshairs-highlight-when-idle-p (if arg
                                             (> (prefix-numeric-value arg) 0)
                                           (not crosshairs-highlight-when-idle-p)))
  (setq hl-line-when-idle-p        crosshairs-highlight-when-idle-p
        col-highlight-when-idle-p  crosshairs-highlight-when-idle-p)
  (cond (crosshairs-highlight-when-idle-p
         (timer-activate-when-idle col-highlight-idle-timer)
         (timer-activate-when-idle hl-line-idle-timer)
         (add-hook 'pre-command-hook #'col-highlight-unhighlight)
         (add-hook 'pre-command-hook #'hl-line-unhighlight-now)
         (message "Turned ON highlighting line and column when Emacs is idle."))
        (t
         (cancel-timer col-highlight-idle-timer)
         (cancel-timer hl-line-idle-timer)
         (remove-hook 'pre-command-hook #'col-highlight-unhighlight)
         (remove-hook 'pre-command-hook #'hl-line-unhighlight-now)
         (message "Turned OFF highlighting line and column when Emacs is idle."))))

;;;###autoload
(defalias 'flash-crosshairs 'crosshairs-flash)
;;;###autoload
(defun crosshairs-flash (&optional seconds)
  "Highlight the current line and column temporarily.
Highlight the line for `hl-line-flash-show-period' and the column for
`column-show-period' seconds.  With prefix argument SECONDS, highlight
both for SECONDS seconds."
  (interactive "P")
  (cancel-timer crosshairs-flash-line-timer) ; Cancel to prevent duplication.
  (cancel-timer crosshairs-flash-col-timer)
  (let ((global-hl-line-mode  global-hl-line-mode))
    (col-highlight-unhighlight t)
    (col-highlight-highlight t)
    (when column-highlight-mode (col-highlight-highlight t)) ; Extra - a vline bug.
    (hl-line-highlight-now)
    (remove-hook 'pre-command-hook 'hl-line-unhighlight-now)
    (let ((line-period    hl-line-flash-show-period) ; Defined in `hl-line+.el'.
          (column-period  col-highlight-period)) ; Defined in `col-highlight.el'.
      (when seconds
        (setq line-period    (prefix-numeric-value seconds)
              column-period  line-period))
      ;; $$$$$$ Do we need to worry about `global-hl-line-unhighlight-all' here?
      (setq crosshairs-flash-line-timer (run-at-time
                                         line-period nil
                                         #'hl-line-unhighlight-now)
            crosshairs-flash-col-timer  (run-at-time
                                         column-period nil
                                         #'col-highlight-unhighlight t)))))

;;;###autoload
(defun crosshairs (&optional modalp)
  "Highlight current position with crosshairs.
With no prefix arg, highlighting turns off at the next command.
With a prefix arg, highlighting stays on until you toggle it off using
`crosshairs-mode'."
  (interactive "P")
  (if modalp (crosshairs-mode 1) (crosshairs-highlight)))

;;;###autoload
(defun crosshairs-highlight (&optional mode nomsg)
  "Echo current position and highlight it with crosshairs.
If optional arg MODE is `line-only', then highlight only the line.
If optional arg MODE is `col-only', then highlight only the column.
 Interactively:
  A non-negative prefix argument uses MODE `line-only'.
  A negative prefix argument uses MODE `col-only'.

Optional arg NOMSG non-nil means show no message.

If the current buffer is not the same as the value of `orig-buff',
then indicate the buffer, as well as the position.  Variable
`orig-buff' is not bound here; if you want to take advantage of this
feature in your code, then bind it.

Return current position as a marker."
  (interactive (list (and current-prefix-arg
                          (if (wholenump (prefix-numeric-value current-prefix-arg))
                              'line-only
                            'col-only))))
  (when crosshairs-mode (crosshairs-mode -1))
  (prog1 (point-marker)
    (unless (eq mode 'line-only) (require 'col-highlight nil t))
    (unless (eq mode 'col-only) (require 'hl-line nil t))
    (setq mark-active  nil)
    (crosshairs-unhighlight 'even-if-frame-switch)
    (when (and (boundp 'global-hl-line-overlay) (not (eq mode 'col-only)))
      (unless global-hl-line-overlay
        (setq global-hl-line-overlay (make-overlay 1 1)) ; to be moved
        (overlay-put global-hl-line-overlay 'face hl-line-face))
      (when (and (boundp 'global-hl-line-overlays)
                 (not (member global-hl-line-overlay global-hl-line-overlays)))
	(push global-hl-line-overlay global-hl-line-overlays))
      (overlay-put global-hl-line-overlay 'window (selected-window))
      (hl-line-move global-hl-line-overlay))
    (when (and (fboundp 'col-highlight-highlight) (not (eq mode 'line-only)))
      (redisplay t) ; Force a redisplay, or else it doesn't always show up.
      (col-highlight-highlight))
    (when (or (boundp 'global-hl-line-overlay) (fboundp 'col-highlight-highlight))
      (add-hook 'pre-command-hook 'crosshairs-unhighlight))
    (unless nomsg
      (if (and (boundp 'orig-buff) (eq (current-buffer) orig-buff))
          (message "Point: %d" (point))
        (message "Buffer: `%s', Point: %d" (current-buffer) (point))))))

;;;###autoload
(defun crosshairs-unhighlight (&optional arg)
  "Turn off crosshairs highlighting of current position.
Optional arg nil means do nothing if this event is a frame switch."
  (interactive)
  (when (or arg (not (and (consp last-input-event)
                          (eq (car last-input-event) 'switch-frame))))
    (when (fboundp 'col-highlight-unhighlight) (col-highlight-unhighlight t))
    (when (and (boundp 'global-hl-line-overlay) global-hl-line-overlay)
;;       (when crosshairs-overlay-priority
;;         (overlay-put global-hl-line-overlay 'priority nil))
      (delete-overlay global-hl-line-overlay))
    (when (fboundp 'global-hl-line-unhighlight-all) ; Emacs 24.4+
      (global-hl-line-unhighlight-all))
    (remove-hook 'pre-command-hook 'crosshairs-unhighlight)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(provide 'crosshairs)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; crosshairs.el ends here
