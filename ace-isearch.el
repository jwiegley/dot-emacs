;;; ace-isearch.el --- A seamless bridge between isearch and ace-jump-mode -*- coding: utf-8; lexical-binding: t -*-

;; Copyright (C) 2014 by Akira TAMAMORI

;; Author: Akira Tamamori
;; URL: https://github.com/tam17aki/ace-isearch
;; Version: 0.1.1
;; Created: Sep 25 2014
;; Package-Requires: ((ace-jump-mode "2.0") (helm-swoop "1.4") (emacs "24"))

;; This program is free software; you can redistribute it and/or modify it under
;; the terms of the GNU General Public License as published by the Free Software
;; Foundation, either version 3 of the License, or (at your option) any later
;; version.

;; This program is distributed in the hope that it will be useful, but WITHOUT
;; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
;; FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
;; details.

;; You should have received a copy of the GNU General Public License along with
;; this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:
;;
;; `ace-isearch.el' provides a minor mode which combines `isearch' and
;; `ace-jump-mode'.
;;
;; The "default" behavior can be summrized as:
;;
;; L = 1     : `ace-jump-mode'
;; 1 < L < 6 : `isearch'
;; L >= 6    : `helm-swoop-from-isearch'
;;
;; where L is the input string length during `isearch'.  When L is 1, after a
;; few seconds specified by `ace-isearch-input-idle-delay', `ace-jump-mode' will
;; be invoked. Of course you can customize the above behaviour.

;;; Installation:
;;
;; To use this package, add following code to your init file.
;;
;;   (require 'ace-isearch)
;;   (global-ace-isearch-mode +1)

;;; Code:

(eval-when-compile (defvar helm-swoop-last-prefix-number 0))

(require 'helm-swoop)
(require 'ace-jump-mode)

(defgroup ace-isearch nil
  "Group of ace-isearch."
  :group 'ace-jump)

(defcustom ace-isearch-lighter " AceI"
  "Lighter of ace-isearch-mode."
  :type 'string
  :group 'ace-isearch)

(defcustom ace-isearch-input-idle-delay 0.4
  "Delay seconds for invoking `ace-jump-mode' and `ace-isearch-function-from-isearch'
during isearch."
  :type 'number
  :group 'ace-isearch)

(defcustom ace-isearch-input-length 6
  "Length of inpunt string required for invoking `ace-isearch-function-from-isearch'
during isearch."
  :type 'integer
  :group 'ace-isearch)

(defcustom ace-isearch-submode 'ace-jump-word-mode
  "Sub-mode for ace-jump-mode."
  :type '(choice (const :tag "Use ace-jump-word-mode." ace-jump-word-mode)
                 (const :tag "Use ace-jump-char-mode." ace-jump-char-mode))
  :group 'ace-isearch)

(defcustom ace-isearch-use-ace-jump t
  "If `nil', `ace-jump-mode' is never invoked.

If `t', it is always invoked if the length of `isearch-string' is
equal to 1.

If `printing-char', it is invoked only if you hit a printing
character to search for as a first input.  This prevents it from
being invoked when repeating a one character search, yanking a
character or calling `isearch-delete-char' leaving only one
character."
  :type '(choice (const :tag "Always" t)
                 (const :tag "Only after a printing character is input" printing-char)
                 (const :tag "Never" nil))
  :group 'ace-isearch)

(defcustom ace-isearch-funtion-from-isearch 'helm-swoop-from-isearch
  "Symbol name of function which is invoked when the length of `isearch-string'
is longer than or equal to `ace-isearch-input-length'."
  :type 'symbol
  :group 'ace-isearch)

(defcustom ace-isearch-use-function-from-isearch t
  "When non-nil, invoke `ace-isearch-funtion-from-isearch' if the length
of `isearch-string' is longer than or equal to `ace-isearch-input-length'."
  :type 'boolean
  :group 'ace-isearch)

(defcustom ace-isearch-fallback-function 'helm-swoop-from-isearch
  "Symbol name of function which is invoked when isearch fails and
`ace-isearch-use-fallback-function' is non-nil."
  :type 'symbol
  :group 'ace-isearch)

(defcustom ace-isearch-use-fallback-function nil
  "When non-nil, invoke `ace-isearch-fallback-function' when isearch fails."
  :type 'boolean
  :group 'ace-isearch)

(defvar ace-isearch--submode-list
  (list "ace-jump-word-mode" "ace-jump-char-mode")
  "List of jump type for ace-jump-mode.")

(defun ace-isearch-switch-submode ()
  (interactive)
  (let ((submode (completing-read
                  (format "Sub-mode (current is %s): " ace-isearch-submode)
                  ace-isearch--submode-list nil t "ace-jump-")))
    (setq ace-isearch-submode (intern-soft submode))
    (message "Sub-mode of ace-isearch is set to %s." submode)))

(defun ace-isearch--fboundp (func flag)
  (when flag
    (when (eq func nil)
      (error "function name must be specified!"))
    (unless (fboundp func)
      (error (format "function %s is not bounded!" func)))
    t))

(defun ace-isearch--pop-mark ()
  (if (= (length isearch-string) 1) (progn (pop-mark))))

(defun ace-isearch--jumper-function ()
  (cond ((and (= (length isearch-string) 1)
              (not (or isearch-regexp
                       isearch-word))
              (ace-isearch--fboundp ace-isearch-submode
                                    (or (eq ace-isearch-use-ace-jump t)
                                        (and (eq ace-isearch-use-ace-jump 'printing-char)
                                             (eq this-command 'isearch-printing-char))))
              (sit-for ace-isearch-input-idle-delay))
         (isearch-exit)
         (funcall ace-isearch-submode (string-to-char isearch-string)))

        ((and (> (length isearch-string) 1)
              (< (length isearch-string) ace-isearch-input-length)
              (not isearch-success)
              (sit-for ace-isearch-input-idle-delay))
         (if (ace-isearch--fboundp
              ace-isearch-fallback-function ace-isearch-use-fallback-function)
             (funcall ace-isearch-fallback-function)))

        ((and (>= (length isearch-string) ace-isearch-input-length)
              (not isearch-regexp)
              (ace-isearch--fboundp
               ace-isearch-funtion-from-isearch ace-isearch-use-function-from-isearch)
              (sit-for ace-isearch-input-idle-delay))
         (isearch-exit)
         (funcall ace-isearch-funtion-from-isearch))))

;;;###autoload
(define-minor-mode ace-isearch-mode
  "Minor-mode which combines isearch and ace-jump-mode seamlessly."
  :group      'ace-isearch
  :init-value nil
  :global     nil
  :lighter    ace-isearch-mode-lighter
  (if ace-isearch-mode
      (progn
        (add-hook 'isearch-update-post-hook 'ace-isearch--jumper-function nil t)
        (add-hook 'ace-jump-mode-end-hook 'ace-isearch--pop-mark nil t))
    (remove-hook 'isearch-update-post-hook 'ace-isearch--jumper-function t)
    (remove-hook 'ace-jump-mode-end-hook 'ace-isearch--pop-mark t)))

(defun ace-isearch--turn-on ()
  (unless (minibufferp)
    (ace-isearch-mode +1)))

;;;###autoload
(define-globalized-minor-mode global-ace-isearch-mode
  ace-isearch-mode ace-isearch--turn-on
  :group 'ace-isearch)

;; misc
(defvar ace-isearch--active-when-isearch-exit-p nil)

(defadvice isearch-exit (after do-ace-isearch-jump disable)
  (if (and ace-isearch--active-when-isearch-exit-p
           (> (length isearch-string) 1)
           (< (length isearch-string) ace-isearch-input-length))
      (let ((ace-jump-mode-scope 'window))
        (ace-jump-do (regexp-quote isearch-string)))))

(defun ace-isearch-set-ace-jump-after-isearch-exit (activate)
  "Set invoking ace-jump-mode automatically when `isearch-exit' has done."
  (if activate
      (ad-enable-advice 'isearch-exit 'after 'do-ace-isearch-jump)
    (ad-disable-advice 'isearch-exit 'after 'do-ace-isearch-jump))
  (ad-activate 'isearch-exit)
  (setq ace-isearch--active-when-isearch-exit-p activate))

(provide 'ace-isearch)
;;; ace-isearch.el ends here
