;;; reveal-next.el --- Progressively reveal text after the cursor.
;;
;; Filename: reveal-next.el
;; Description: Progressively reveal text after the cursor.
;; Author: Drew Adams
;; Maintainer: Drew Adams
;; Copyright (C) 2014-2015, Drew Adams, all rights reserved.
;; Created: Fri May 16 07:28:05 2014 (-0700)
;; Version: 0
;; Package-Requires: ()
;; Last-Updated: Thu Jan  1 11:11:24 2015 (-0800)
;;           By: dradams
;;     Update #: 27
;; URL: http://www.emacswiki.org/reveal-next.el
;; Doc URL: http://www.emacswiki.org/RevealNextTextMode
;; Keywords: hide show invisible learning
;; Compatibility: GNU Emacs: 22.x, 23.x, 24.x, 25.x
;;
;; Features that might be required by this library:
;;
;;   None
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Commentary:
;;
;;    Progressively reveal text after the cursor as you move it.
;;
;; You can use this during a presentation, such as in a class, to
;; progressively show more of the text in a buffer.  As you move the
;; cursor in any way, more text is revealed (or hidden, if moving
;; backward).
;;
;; There are two levels: show at least a line at a time or show at
;; least a char at a time.  User option `reveal-next-char-level' sets
;; the level, but you can also switch levels using command
;; `reveal-next-char/line' or `reveal-next-cycle'.  The latter command
;; cycles among line-level, char-level, and off.
;;
;;
;; User options defined here:
;;
;;    `reveal-next-char-level'.
;;
;; Commands defined here:
;;
;;    `reveal-next-char/line', `reveal-next-cycle',
;;    `reveal-next-mode'.
;;
;; Non-interactive functions defined here:
;;
;;    `reveal-next-update'.
;;
;; Internal variables defined here:
;;
;;    `reveal-next-overlay'.
;;
;;
;; This library was inspired by this Stack Overflow question:
;; http://stackoverflow.com/q/23677844/729907
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Change Log:
;;
;; 2014/05/16 dadams
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

(defcustom reveal-next-char-level nil
  "`t' means `reveal-next-mode' can reveal a character at a time.
`nil' means it reveals at least a line at a time."
  :type 'boolean :group 'editing)

(defvar reveal-next-overlay nil "Overlay that `reveal-next-mode' uses to hide text.")

;;;###autoload
(define-minor-mode reveal-next-mode
    "Toggle whether moving the cursor progressively reveals/hides text after it."
  :init-value nil :group 'editing :lighter " Reveal"
  (if reveal-next-mode
      (add-hook 'post-command-hook 'reveal-next-update)
    (delete-overlay reveal-next-overlay)
    (remove-hook 'post-command-hook 'reveal-next-update))
  (when (if (> emacs-major-version 22)
            (called-interactively-p 'interactive)
          (called-interactively-p))
    (message "%seveal mode is now %s in buffer `%s'"
             (if reveal-next-mode (if reveal-next-char-level "CHAR-level r" "LINE-level r") "R")
             (if reveal-next-mode "ON" "OFF") (buffer-name))))

(defun reveal-next-update ()
  "In `reveal-next-mode', update hidden portion of buffer.
Option `reveal-next-char-level' determines where hiding starts: next char
or beginning of next line."
  (when reveal-next-mode
    (when (and (= (point) (point-max))  (overlayp reveal-next-overlay))
      (delete-overlay reveal-next-overlay))
    (let ((start  (if reveal-next-char-level
                      (point)
                    (save-excursion
                      (forward-paragraph 1)
                      (point)))))
      (cond ((eobp))                    ; No-op at eob.
            ((overlayp reveal-next-overlay) (move-overlay reveal-next-overlay start (point-max)))
            (t
             (setq reveal-next-overlay  (make-overlay start (point-max)))
             ;; It would be better to just use property `invisible', but `next-line' hardcodes
             ;; skipping over invisible text (actually, it is `line-move-1' that does this).
             (overlay-put reveal-next-overlay
                          'face (list :foreground (frame-parameter nil 'background-color))))))))

;;;###autoload
(defun reveal-next-char/line (&optional msgp)
  "Toggle whether `reveal-next-mode' hides text at char level or line level."
  (interactive "p")
  (setq reveal-next-char-level  (not reveal-next-char-level))
  (reveal-next-mode 'toggle) (reveal-next-mode 'toggle)
  (when msgp (message "Reveal mode is now at %s level" (if reveal-next-char-level "CHAR" "LINE"))))

;;;###autoload
(defun reveal-next-cycle ()
  "Cycle `reveal-next-mode': line-level > char-level > off ..."
  (interactive)
  (cond ((and reveal-next-mode  reveal-next-char-level) (call-interactively #'reveal-next-mode))
        (reveal-next-mode (call-interactively #'reveal-next-char/line))
        (t (setq reveal-next-char-level  nil) (call-interactively #'reveal-next-mode))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(provide 'reveal-next)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; reveal-next.el ends here
