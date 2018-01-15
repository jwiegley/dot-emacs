;;; package --- summary
;;; feebleline.el

;; Copyright 2018 Benjamin Lindqvist

;; Author: Benjamin Lindqvist <benjamin.lindqvist@gmail.com>
;; Maintainer: Benjamin Lindqvist <benjamin.lindqvist@gmail.com>
;; URL: https://github.com/tautologyclub/feeblel
;; Package-Version:
;; Version: 1.0

;; This file is not part of GNU Emacs.

;; This program is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; For hardline Luddite editing!

;; Feebleline removes the modeline and replaces it with a slimmer proxy
;; version, which displays some basic information in the echo area
;; instead.  This information is only displayed if the echo area is not used
;; for anything else (but if you switch frame/window, it will replace whatever
;; message is currently displayed).

;; NOTE:
;; feebleline.el will look considerably better with the following
;; settings:

;;   (window-divider-mode t)
;;   (setq window-divider-default-bottom-width 1)
;;   (setq window-divider-default-places (quote bottom-only))

;; But this mode does not work for all EMACS versions and may not work with
;; terminal EMACS (but I haven't checked).  If you're on GUI EMACS and your
;; version supports it, just place the following in your init file:

;;   (feebleline-default-settings)

;; Otherwise, do (feebleline-mode t) instead, but be warned that I'm not sure
;; if it will look good.

;;; Code:

(require 'advice)
(defvar feebleline/mode-line-format-default)
(defvar feebleline/timer)
(defvar feebleline/default-log-max)

(defun feebleline-default-settings ()
  "Some default settings that works well with feebleline."
  (custom-set-variables
   '(window-divider-default-bottom-width 1)
   '(window-divider-default-places (quote bottom-only)))
  (window-divider-mode t)
  (feebleline-mode t))

(define-minor-mode feebleline-mode
  "Replace modeline with a slimmer proxy."
  :global t
  (if feebleline-mode
      (progn
        (setq feebleline/mode-line-format-default mode-line-format)
        (setq feebleline/timer (run-with-timer 0 0.1 'mode-line-proxy-fn))
        (custom-set-variables '(mode-line-format nil))
        (ad-activate 'handle-switch-frame)
        (add-hook 'focus-in-hook 'mode-line-proxy-fn))
    (custom-set-variables
     '(mode-line-format feebleline/mode-line-format-default))
    (cancel-timer feebleline/timer)
    (ad-deactivate 'handle-switch-frame)
    (remove-hook 'focus-in-hook 'mode-line-proxy-fn)))

;; (defvar msg-string)
;; (defun mode-line-proxy-string-fn () (interactive)
;;   "Hej."
;;   (setq msg-string (concat "a" "b"))
;;   (message "%s" msg-string))

(defun message-buffer-file-name-or-nothing ()
  "Replace echo-area message with mode-line proxy."
  (setq feebleline/default-log-max message-log-max)
  (unwind-protect
      (progn
        (setq message-log-max nil)
        (if buffer-file-name
            (message "[%s] %s/%s @ %s"
                     (format-time-string "%H:%M:%S")
                     (string-to-number (format-mode-line "%l"))
                     (current-column)
                     (buffer-file-name))))
    (setq message-log-max feebleline/default-log-max)))

(defun mode-line-proxy-fn ()
  "Put a mode-line proxy in the echo area *if* echo area is empty."
  (if (not (current-message))
      (message-buffer-file-name-or-nothing)))

(defadvice handle-switch-frame (after switch-frame-message-name)
  "Get the modeline proxy to work with i3 switch focus."
  (message-buffer-file-name-or-nothing)
  ad-do-it
  (message-buffer-file-name-or-nothing))

(provide 'feebleline)

;;; feebleline.el ends here
