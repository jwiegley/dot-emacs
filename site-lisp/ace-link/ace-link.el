;;; ace-link.el --- Quickly follow links using `ace-jump-mode'

;; Copyright (C) 2014 Oleh Krehel

;; Author: Oleh Krehel <ohwoeowho@gmail.com>
;; URL: https://github.com/abo-abo/ace-link
;; Version: 0.3.0
;; Package-Requires: ((ace-jump-mode "2.0"))
;; Keywords: convenience, links

;; This file is not part of GNU Emacs

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; For a full copy of the GNU General Public License
;; see <http://www.gnu.org/licenses/>.

;;; Commentary:
;;
;; This package offers an alternative to tabbing through links in
;; buffers, for instance, in an Info buffer.  `ace-jump-mode' is used
;; to turn opening a link from an O(N) operation into an O(1).
;;
;; Use `ace-link-setup-default' to set up the default bindings, which currently
;; bind e.g. `ace-link-info' to "o", which was previously unbound and is
;; close to "l" (which by default goes back).
;;
;; Supported modes: `Info-mode', `help-mode', `org-mode', `eww-mode'.

;;; Code:

(require 'ace-jump-mode)

;; ——— Macros ——————————————————————————————————————————————————————————————————
(defmacro ali-flet (binding &rest body)
  "Temporarily override BINDING and execute BODY."
  (declare (indent 1))
  (let* ((name (car binding))
         (old (cl-gensym (symbol-name name))))
    `(let ((,old (symbol-function ',name)))
       (unwind-protect
            (progn
              (fset ',name (lambda ,@(cdr binding)))
              ,@body)
         (fset ',name ,old)))))

(defmacro ali-generic (candidates &rest follower)
  "Ace jump to CANDIDATES using FOLLOWER."
  (declare (indent 1))
  `(ali-flet (ace-jump-search-candidate
              (str va-list)
              (mapcar (lambda (x)
                        (make-aj-position
                         :offset (1- x)
                         :visual-area (car va-list)))
                      ,candidates))
     (setq ace-jump-mode-end-hook
           (list (lambda ()
                   (setq ace-jump-mode-end-hook)
                   ,@follower)))
     (let ((ace-jump-mode-scope 'window))
       (ace-jump-do ""))))

;; ——— Interactive —————————————————————————————————————————————————————————————
;;;###autoload
(defun ace-link-info ()
  "Ace jump to links in `Info-mode' buffers."
  (interactive)
  (ali-generic
      (ali--info-collect-references)
    (let ((end (window-end)))
      (while (not (ignore-errors
                    (Info-follow-nearest-node)))
        (forward-char 1)
        (when (> (point) end)
          (error "Could not follow link"))))))

;;;###autoload
(defun ace-link-help ()
  "Ace jump to links in `help-mode' buffers."
  (interactive)
  (ali-generic
      (ali--help-collect-references)
    (forward-char 1)
    (push-button)))

;;;###autoload
(defun ace-link-eww ()
  "Ace jump to links in `eww-mode' buffers."
  (interactive)
  (ali-generic
      (ali--eww-collect-references)
    (forward-char 1)
    (eww-follow-link)))

;;;###autoload
(defun ace-link-org ()
  "Ace jump to links in `org-mode' buffers."
  (interactive)
  (ali-generic
      (ali--org-collect-references)
    (org-open-at-point)))

;; ——— Utility —————————————————————————————————————————————————————————————————
(defun ali--info-collect-references ()
  "Collect the positions of visible links in the current `Info-mode' buffer."
  (let ((end (window-end))
        points)
    (save-excursion
      (goto-char (window-start))
      (when (ignore-errors (Info-next-reference) t)
        (push (point) points)
        (Info-next-reference)
        (while (and (< (point) end)
                    (> (point) (car points)))
          (push (point) points)
          (Info-next-reference))
        (nreverse points)))))

(defun ali--help-collect-references ()
  "Collect the positions of visible links in the current `help-mode' buffer."
  (let ((skip (text-property-any (point-min) (point-max)
                                 'button nil))
        candidates)
    (save-excursion
      (while (setq skip (text-property-not-all skip (point-max)
                                               'button nil))
        (goto-char skip)
        (push skip candidates)
        (setq skip (text-property-any (point) (point-max)
                                      'button nil))))
    (nreverse candidates)))

(defun ali--eww-collect-references ()
  "Collect the positions of visible links in the current `eww' buffer."
  (save-excursion
    (save-restriction
      (narrow-to-region
       (window-start)
       (window-end))
      (goto-char (point-min))
      (let ((skip (text-property-any (point) (point-max)
                                     'help-echo nil))
            candidates)
        (while (setq skip (text-property-not-all
                           skip (point-max) 'help-echo nil))
          (goto-char skip)
          (push skip candidates)
          (setq skip (text-property-any (point) (point-max)
                                        'help-echo nil)))
        (nreverse candidates)))))

(defun ali--org-collect-references ()
  (let ((end (window-end))
        points)
    (save-excursion
      (goto-char (window-start))
      (while (re-search-forward org-any-link-re end t)
        ;; Check that the link is visible. Look at the last character
        ;; position in the link ("...X]]") to cover links with and
        ;; without a description.
        (when (not (outline-invisible-p (- (match-end 0) 3)))
          (push (+ (match-beginning 0) 1) points)))
      (nreverse points))))

;;;###autoload
(defun ace-link-setup-default ()
  "Setup the defualt shortcuts."
  (eval-after-load "info"
    '(define-key Info-mode-map "o" 'ace-link-info))
  (eval-after-load "help-mode"
    '(define-key help-mode-map "o" 'ace-link-help))
  (eval-after-load "eww"
    '(progn
      (define-key eww-link-keymap "o" 'ace-link-eww)
      (define-key eww-mode-map "o" 'ace-link-eww))))

(provide 'ace-link)

;;; ace-link.el ends here
