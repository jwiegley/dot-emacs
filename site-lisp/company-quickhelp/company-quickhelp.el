;;; company-quickhelp.el --- Popup documentation for completion candidates

;; Copyright (C) 2015, Lars Andersen

;; Author: Lars Andersen <expez@expez.com>
;; URL: https://www.github.com/expez/company-quickhelp
;; Keywords: company popup documentation quickhelp
;; Version: 0.1
;; Package-Requires: ((emacs "24.4") (company "0.8.9") (pos-tip "0.4.6"))

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

;; When idling on a completion candidate the documentation for the
;; candidate will pop up after `company-quickhelp-idle-delay' seconds.

;;; Usage:
;;  put (company-quickhelp-mode 1) in you init.el to activate
;;  `company-quickhelp-mode'.

;; You can adjust the time it takes for the documentation to pop up by
;; changing `company-quickhelp-delay'

;;; Code:
(require 'company)
(require 'pos-tip)

(defgroup company-quickhelp nil
  "Documentation popups for `company-mode'"
  :group 'company)

(defcustom company-quickhelp-delay 0.5
  "Delay, in seconds, before the quickhelp popup appears."
  :type 'number
  :group 'company-quickhelp)

(defcustom company-quickhelp-max-lines nil
  "When not NIL, limits the number of lines in the popup."
  :type '(choice (integer :tag "Max lines to show in popup")
                 (const :tag "Don't limit the number of lines shown" nil))
  :group 'company-quickhelp)

(defvar company-quickhelp--timer nil
  "Quickhelp idle timer.")

(defvar company-quickhelp--original-tooltip-width nil
  "The documentation popup breaks inexplicably when we transition
  from a large pseudo-tooltip to a small one.  We solve this by
  overriding `company-tooltip-minimum-width' and save the
  original value here so we can restore it.")

(defun company-quickhelp-frontend (command)
  "`company-mode' front-end showing documentation in a `pos-tip' popup."
  (pcase command
    (`post-command (company-quickhelp--set-timer))
    (`hide
     (company-quickhelp--cancel-timer)
     (pos-tip-hide))))

(defun company-quickhelp--doc-and-meta (doc-buffer)
  (with-current-buffer doc-buffer
    (let ((truncated t))
      (goto-char (point-min))
      (if company-quickhelp-max-lines
          (forward-line company-quickhelp-max-lines)
        (goto-char (point-max))
        (beginning-of-line))
      (when (= (line-number-at-pos)
               (save-excursion (goto-char (point-max)) (line-number-at-pos)))
        (setq truncated nil))
      ;; [back] appears at the end of the help buffer
      (while (and (not (= (line-number-at-pos) 1))
                  (or (looking-at "\\[back\\]")
                      (looking-at "^\\s-*$")))
        (forward-line -1))
      (list :doc (buffer-substring-no-properties (point-min) (point-at-eol))
            :truncated truncated))))

(defun company-quickhelp--doc (selected)
  (let* ((doc-buffer (company-call-backend 'doc-buffer selected))
         (doc-and-meta (when doc-buffer
                         (company-quickhelp--doc-and-meta doc-buffer)))
         (truncated (plist-get doc-and-meta :truncated))
         (doc (plist-get doc-and-meta :doc)))
    (unless (string= doc "")
      (if truncated
          (concat doc "\n\n[...]")
        doc))))

(defun company-quickhelp--show ()
  (company-quickhelp--cancel-timer)
  (let* ((selected (nth company-selection company-candidates))
         (doc (company-quickhelp--doc selected))
         (ovl company-pseudo-tooltip-overlay)
         (x-gtk-use-system-tooltips nil))
    (when (and ovl doc)
      (with-no-warnings
        (pos-tip-show doc nil (overlay-start ovl) nil 300 80 nil nil 1)))))

(defun company-quickhelp--set-timer ()
  (when (null company-quickhelp--timer)
    (setq company-quickhelp--timer
          (run-with-idle-timer company-quickhelp-delay nil
                               'company-quickhelp--show))))

(defun company-quickhelp--cancel-timer ()
  (when (timerp company-quickhelp--timer)
    (cancel-timer company-quickhelp--timer)
    (setq company-quickhelp--timer nil)))

(defun company-quickhelp-hide ()
  (company-cancel))

(defun company-quickhelp--enable ()
  (add-hook 'focus-out-hook #'company-quickhelp-hide)
  (setq company-quickhelp--original-tooltip-width company-tooltip-minimum-width
        company-tooltip-minimum-width (max company-tooltip-minimum-width 40))
  (add-to-list 'company-frontends 'company-quickhelp-frontend :append))

(defun company-quickhelp--disable ()
  (remove-hook 'focus-out-hook #'company-quickhelp-hide)
  (company-quickhelp--cancel-timer)
  (setq company-tooltip-minimum-width company-quickhelp--original-tooltip-width
        company-frontends
        (delq 'company-quickhelp-frontend company-frontends)))

;;;###autoload
(define-minor-mode company-quickhelp-mode
  "Provides documentation popups for `company-mode' using `pos-tip'."
  :global t
  (if company-quickhelp-mode
      (company-quickhelp--enable)
    (company-quickhelp--disable)))

(provide 'company-quickhelp)

;;; company-quickhelp.el ends here
