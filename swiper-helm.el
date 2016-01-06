;;; swiper-helm.el --- Helm version of Swiper. -*- lexical-binding: t -*-

;; Copyright (C) 2015 Oleh Krehel

;; Author: Oleh Krehel <ohwoeowho@gmail.com>
;; URL: https://github.com/abo-abo/swiper-helm
;; Version: 0.1.0
;; Package-Requires: ((emacs "24.1") (swiper "0.1.0") (helm "1.5.3"))
;; Keywords: matching

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
;; This package gives an overview of the current regex search
;; candidates.  The search regex can be split into groups with a
;; space.  Each group is highlighted with a different face.
;;
;; The overview back end is `helm'.
;;
;; It can double as a quick `regex-builder', although only single
;; lines will be matched.

;;; Code:

(require 'swiper)
(require 'helm)

(defgroup swiper-helm nil
  "`isearch' with an overview using `helm'."
  :group 'matching
  :prefix "swiper-helm-")

(defvar swiper-helm-keymap
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "C-s") 'helm-next-line)
    (define-key map (kbd "C-r") 'helm-previous-line)
    map)
  "Allows you to go to next and previous hit isearch-style.")

(defun swiper-helm-default-display-buffer (buf)
  "Display BUF buffer."
  (when (one-window-p)
    (split-window-vertically))
  (other-window 1)
  (switch-to-buffer buf))

(defcustom swiper-helm-display-function 'swiper-helm-default-display-buffer
  "The function that switches to the window where helm should be."
  :type 'function)

(defvar swiper--anchor nil
  "A line number to which the search should be anchored.")

(defvar swiper--len 0
  "The last length of input for which an anchoring was made.")

(defun swiper--helm-init ()
  "Perform initialization common to both completion methods."
  (setq swiper--opoint (point))
  (setq swiper--len 0)
  (setq swiper--anchor (line-number-at-pos))
  (when (bound-and-true-p evil-jumper-mode)
    (evil-jumper--set-jump)))

;;;###autoload
(defun swiper-helm (&optional initial-input)
  "`isearch' with an overview using `helm'.
When non-nil, INITIAL-INPUT is the initial search pattern."
  (interactive)
  (require 'helm)
  (require 'helm-multi-match)
  (swiper--helm-init)
  (setq ivy-last
        (make-ivy-state
         :window (selected-window)))
  (unwind-protect
       (let ((helm-display-function swiper-helm-display-function)
             helm-candidate-number-limit)
         (helm :sources
               `((name . ,(buffer-name))
                 (init . (lambda ()
                           (add-hook 'helm-move-selection-after-hook
                                     #'swiper--update-sel)
                           (add-hook 'helm-update-hook
                                     #'swiper--update-input-helm)
                           (add-hook 'helm-after-update-hook
                                     #'swiper--reanchor)))
                 (match-strict . (lambda (x)
                                   (ignore-errors
                                     (string-match (ivy--regex helm-input) x))))
                 (candidates . ,(swiper--helm-candidates))
                 (filtered-candidate-transformer
                  helm-fuzzy-highlight-matches)
                 (action . swiper--action-helm))
               :keymap (make-composed-keymap
                        swiper-helm-keymap
                        helm-map)
               :input initial-input
               :preselect
               (format "^%d " swiper--anchor)
               :buffer "*swiper*"))
    ;; cleanup
    (remove-hook 'helm-move-selection-after-hook #'swiper--update-sel)
    (remove-hook 'helm-update-hook #'swiper--update-input-helm)
    (remove-hook 'helm-after-update-hook #'swiper--reanchor)
    (swiper--cleanup)))

(defun swiper--update-input-helm ()
  "Update selection."
  (swiper--cleanup)
  (let ((swiper--window (ivy-state-window ivy-last)))
    (with-selected-window swiper--window
      (swiper--add-overlays
       (ivy--regex helm-input)
       (window-start swiper--window)
       (window-end swiper--window t)))
    (when (/= (length helm-input) swiper--len)
      (setq swiper--len (length helm-input))
      (swiper--reanchor))))

(defun swiper--binary (beg end)
  "Find anchor between BEG and END."
  (if (<= (- end beg) 10)
      (let ((min 1000)
            n
            ln
            d)
        (goto-char (point-min))
        (forward-line (1- beg))
        (while (< beg end)
          (beginning-of-line)
          (setq n (read (current-buffer)))
          (when (< (setq d (abs (- n swiper--anchor))) min)
            (setq min d)
            (setq ln beg))
          (cl-incf beg)
          (forward-line 1))
        (goto-char (point-min))
        (when ln
          (forward-line (1- ln))))
    (let ((mid (+ beg (/ (- end beg) 2))))
      (goto-char (point-min))
      (forward-line mid)
      (beginning-of-line)
      (let ((n (read (current-buffer))))
        (if (> n swiper--anchor)
            (swiper--binary beg mid)
          (swiper--binary mid end))))))

(defun swiper--update-sel ()
  "Update selection."
  (let* ((re (ivy--regex helm-input))
         (str (buffer-substring-no-properties
               (line-beginning-position)
               (line-end-position)))
         (num (if (string-match "^[0-9]+" str)
                  (string-to-number (match-string 0 str))
                0))
         pt)
    (with-ivy-window
      (when (> (length re) 0)
        (goto-char (point-min))
        (forward-line (1- num))
        (when (re-search-forward re (point-max) t)
          (setq pt (match-beginning 0)))
        (when pt
          (helm-persistent-action-display-window)
          (goto-char pt)
          (recenter)
          (swiper--update-input-helm)))
      (let ((ov (make-overlay
                 (line-beginning-position)
                 (1+ (line-end-position)))))
        (overlay-put ov 'face 'swiper-line-face)
        (push ov swiper--overlays)))))

(defun swiper--reanchor ()
  "Move to a valid match closest to `swiper--anchor'."
  (with-selected-window (helm-window)
    (goto-char (point-min))
    (if (re-search-forward (format "^%d " swiper--anchor) nil t)
        nil
      (forward-line 1)
      (swiper--binary 2 (1+ (count-lines (point) (point-max)))))
    (when (> (count-lines (point-min) (point-max)) 1)
      (forward-line -1)
      (helm-next-line 1))))

(defun swiper--action-helm (x)
  "Goto line X."
  (if (null x)
      (user-error "No candidates")
    (goto-char (point-min))
    (forward-line (1- (read x)))
    (re-search-forward
     (ivy--regex helm-input)
     (line-end-position)
     t)
    (swiper--ensure-visible)
    (when (/= (point) swiper--opoint)
      (unless (and transient-mark-mode
                   mark-active)
        (push-mark swiper--opoint t)
        (message
         "Mark saved where search started"))))
  (recenter))

(defun swiper-helm-from-isearch ()
  "Invoke `swiper-helm' from isearch."
  (interactive)
  (let ((query (if isearch-regexp
                   isearch-string
                 (regexp-quote isearch-string))))
    (isearch-exit)
    (swiper-helm query)))

(defun swiper--helm-candidates ()
  "Return a list of this buffer lines."
  (let ((n-lines (count-lines (point-min) (point-max))))
    (unless (zerop n-lines)
      (setq swiper--width (1+ (floor (log n-lines 10))))
      (setq swiper--format-spec
            (format "%%-%dd %%s" swiper--width))
      (let ((line-number 0)
            candidates)
        (save-excursion
          (goto-char (point-min))
          (swiper-font-lock-ensure)
          (while (< (point) (point-max))
            (push (format swiper--format-spec
                          (cl-incf line-number)
                          (buffer-substring
                           (line-beginning-position)
                           (line-end-position)))
                  candidates)
            (forward-line 1))
          (nreverse candidates))))))

(provide 'swiper-helm)

;;; swiper-helm.el ends here
