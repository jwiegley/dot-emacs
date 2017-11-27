;;; phi-replace.el --- another incremental search & replace, compatible with "multiple-cursors"

;; Copyright (C) 2013- zk_phi

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2 of the License, or
;; (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program; if not, write to the Free Software
;; Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA

;; Author: zk_phi
;; URL: http://hins11.yu-yake.com/
;; Version: 2.3.1

;;; Commentary:

;; Add following expression in your init file :
;;
;;   (require 'phi-replace)
;;
;; and bind command "phi-replace" or "phi-replace-query"
;;
;;   (global-set-key (kbd "M-%") 'phi-replace)

;; For more details, see "Readme".

;;; Change Log:

;; 1.0.0 first released
;; 1.0.1 added weight for phi-replace
;; 1.0.2 use "sublimity" not "nurumacs"
;; 1.0.3 better integration with sublimity
;; 1.0.4 added a hook
;; 1.0.5 added some commands
;; 1.0.6 better handling of narrowed buffer
;; 1.0.7 fixed bug on completing replace without matches
;; 1.0.8 use "remap" for default keybindings
;; 2.0.0 follow "phi-search" update
;;       changed the default value of phi-replace-weight
;; 2.0.1 added phi-replace-init-hook
;; 2.0.2 compatible with phi-search-core v1.2.0
;; 2.1.0 provide '!' for phi-replace-query
;; 2.2.0 compatibility with phi-search-core v2.0.0
;; 2.3.0 add interactive preview feature
;; 2.3.1 call phi-replace even in popup window

;;; Code:

(require 'phi-search-core)

;; + constant

(defconst phi-replace-version "2.3.1")

;; + suppress byte-compiler

(declare-function sublimity--pre-command "sublimity")
(declare-function sublimity--post-command "sublimity")

;; + customs

(defcustom phi-replace-weight nil
  "weight for \"phi-replace\""
  :group 'phi-search
  :type 'number)

(defcustom phi-replace-init-hook nil
  "hook run after initialization of phi-replace"
  :group 'phi-search
  :type 'hook)

(defcustom phi-replace-additional-keybinds
  '(([remap phi-search-complete] . 'phi-replace-again-or-complete))
  "additional bindings used in phi-replace"
  :group 'phi-search
  :type 'list)

(defcustom phi-replace-enable-preview t
  "wnen non-nil, show interactive preview of replace."
  :group 'phi-search
  :type 'boolean)

;; + faces

(defface phi-replace-preview-face
  '((t (:inherit 'highlight)))
  "Face used to show interactive preview."
  :group 'phi-search)

;; + variables

(defvar phi-replace--original-restriction nil)
(make-variable-buffer-local 'phi-replace--original-restriction)

(defvar phi-replace--query-mode nil)
(make-variable-buffer-local 'phi-replace--query-mode)

;; + start/end phi-replace

(defvar phi-replace--mode-line-format
  '(" *phi-replace*" (:eval (format " [ %d ]" (length phi-search--overlays)))))

(defun phi-replace--update-visual-preview (query replac)
  (save-excursion
    (dolist (ov phi-search--overlays)
      (goto-char (overlay-start ov))
      (looking-at query)
      (overlay-put
       ov 'after-string
       (ignore-errors
         (propertize
          (concat "=>" (match-substitute-replacement replac))
          'face 'phi-replace-preview-face))))))

(defun phi-replace--complete-function ()
  (phi-search--with-target-buffer
   (when phi-search--overlays
     (let* ((orig-cursor (make-overlay phi-search--original-position
                                       phi-search--original-position))
            (enable-recursive-minibuffers t)
            (str (minibuffer-with-setup-hook
                     (lambda ()
                       (when phi-replace-enable-preview
                         (add-hook 'after-change-functions
                                   (lambda (&rest _)
                                     (let ((str (minibuffer-contents)))
                                       (with-current-buffer (cdr target)
                                         (phi-replace--update-visual-preview query str))))
                                   nil t))
                       (with-current-buffer (cdr target)
                         (phi-replace--update-visual-preview query "")))
                   (read-from-minibuffer "replace with ? "))))
       (dotimes (n (length phi-search--overlays))
         (if phi-replace--query-mode
             (phi-search--with-sublimity (phi-search--select n))
           (phi-search--select n))
         (let* ((ov (nth n phi-search--overlays))
                (match-data (progn (goto-char (overlay-start ov))
                                   (looking-at query)
                                   (match-data))))
           (if (and phi-replace--query-mode
                    (let ((ch (read-char-choice
                               (format "replace with %s (y, n or !) ? "
                                       (match-substitute-replacement str))
                               '(?y ?n ?!))))
                      (if (= ch ?!)
                          (setq phi-replace--query-mode nil)
                        (= ch ?n))))
               (overlay-put ov 'face 'defualt)
             (set-match-data match-data)
             (replace-match str))
           (overlay-put ov 'after-string nil))
         (when (and (not phi-replace--query-mode) phi-replace-weight)
           (sit-for phi-replace-weight)))
       (goto-char (overlay-start orig-cursor))))
   (when phi-replace--original-restriction
     (let ((beg (car phi-replace--original-restriction))
           (end (cdr phi-replace--original-restriction)))
       (narrow-to-region (overlay-start beg) (overlay-start end))
       (delete-overlay beg)
       (delete-overlay end)))
   (setq phi-replace--original-restriction nil
         phi-replace--query-mode           nil)))

(defun phi-replace--initialize (&optional query)
  (setq phi-replace--query-mode query)
  ;; narrow to region
  (when (use-region-p)
    (setq phi-replace--original-restriction
          (cons
           (make-overlay (point-min) (point-min))
           (make-overlay (point-max) (point-max))))
    (narrow-to-region (region-beginning) (region-end))
    (deactivate-mark))
  (phi-search--initialize
   phi-replace--mode-line-format phi-replace-additional-keybinds nil nil
   'phi-replace--complete-function
   nil (lambda () (run-hooks 'phi-replace-init-hook)) "phi-replace: "))

;; + commands

;;;###autoload
(defun phi-replace ()
  "replace command using phi-search"
  (interactive)
  (phi-replace--initialize nil))

;;;###autoload
(defun phi-replace-query ()
  "replace command using phi-search"
  (interactive)
  (phi-replace--initialize t))

(defun phi-replace-again-or-complete ()
  "execute phi-replace. if the query is empty, use the last
  query."
  (interactive)
  (let ((str (phi-search--with-target-buffer
              phi-search--last-executed)))
    (when (and (string= (minibuffer-contents) "") str)
      (insert str)))
  (phi-search-complete))

;; + provide

(provide 'phi-replace)

;;; phi-replace.el ends here
