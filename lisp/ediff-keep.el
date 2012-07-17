;;; ediff-keep --- Commands to help manipulate diff3 regions

;; Copyright (C) 2012 John Wiegley

;; Author: John Wiegley <jwiegley@gmail.com>
;; Created: 28 Jun 2012
;; Version: 1.0
;; Keywords: ediff diff
;; X-URL: https://github.com/jwiegley/ediff-keep

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2, or (at
;; your option) any later version.

;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;; The module changes Ediff conflicts regions to match the appearance and
;; meaning of diff3, plus adds an "x" key prefix in the Ediff Control Panel
;; for picking two or three out of the displayed regions.
;;
;; For example:
;;
;;   a       Select region A
;;   b       Select region B
;;   x a     Exclude region A (keep ancestor and B)
;;   x b     Exclude region B (keep ancestor and A)
;;   x c     Exclude ancestor (keep A and B)
;;
;; I recommend using Smerge mode for direct editing of diff3 output files:
;;
;;   (add-hook 'diff-mode-hook 'smerge-mode)
;;
;; Also, to remain sane, change Ediff's merge display to be the same as diff3:
;;
;;   (setq ediff-combination-pattern
;;         '("<<<<<<< A: HEAD" A "||||||| Ancestor" Ancestor
;;           "=======" B ">>>>>>> B: Incoming"))

(require 'bind-key)

(defgroup ediff-keep nil
  "Commands to help manipulate diff3 regions"
  :group 'ediff-merge)

(defun ediff-keep-identify-conflicts ()
  (interactive)
  (with-current-buffer (or ediff-buffer-C
                           (current-buffer))
    (let ((result (list (cons t t)
                        (cons t t)
                        (cons t t)
                        (cons t t))))
      (beginning-of-line)
      (when (or (looking-at "<<<<<<")
                (re-search-backward "^<<<<<<" nil t)
                (re-search-forward "^<<<<<<" nil t))
        (beginning-of-line)
        (setcar (nth 0 result) (point-marker))
        (forward-line)
        (setcdr (nth 0 result) (point-marker))

        (re-search-forward "^|||||||")
        (beginning-of-line)
        (setcar (nth 1 result) (point-marker))
        (forward-line)
        (setcdr (nth 1 result) (point-marker))

        (re-search-forward "^=======")
        (beginning-of-line)
        (setcar (nth 2 result) (point-marker))
        (forward-line)
        (setcdr (nth 2 result) (point-marker))

        (re-search-forward "^>>>>>>>")
        (beginning-of-line)
        (setcar (nth 3 result) (point-marker))
        (forward-line)
        (setcdr (nth 3 result) (point-marker))

        result))))

;; These three functions duplicate part of what smerge-mode does.  They are
;; here for completeness' sake.
(defun ediff-keep-head ()
  (interactive)
  (let ((marks (ediff-keep-identify-conflicts)))
    (delete-region (car (nth 1 marks)) (cdr (nth 3 marks)))
    (delete-region (car (nth 0 marks)) (cdr (nth 0 marks)))))

(defun ediff-keep-ancestor ()
  (interactive)
  (let ((marks (ediff-keep-identify-conflicts)))
    (delete-region (car (nth 2 marks)) (cdr (nth 3 marks)))
    (delete-region (car (nth 0 marks)) (cdr (nth 1 marks)))))

(defun ediff-keep-incoming ()
  (interactive)
  (let ((marks (ediff-keep-identify-conflicts)))
    (delete-region (car (nth 3 marks)) (cdr (nth 3 marks)))
    (delete-region (car (nth 0 marks)) (cdr (nth 2 marks)))))

(defun ediff-keep-head-and-ancestor ()
  (interactive)
  (let ((marks (ediff-keep-identify-conflicts)))
    (delete-region (car (nth 2 marks)) (cdr (nth 3 marks)))
    (delete-region (car (nth 1 marks)) (cdr (nth 1 marks)))
    (delete-region (car (nth 0 marks)) (cdr (nth 0 marks)))))

(defun ediff-keep-head-and-incoming ()
  (interactive)
  (let ((marks (ediff-keep-identify-conflicts)))
    (delete-region (car (nth 3 marks)) (cdr (nth 3 marks)))
    (delete-region (car (nth 1 marks)) (cdr (nth 2 marks)))
    (delete-region (car (nth 0 marks)) (cdr (nth 0 marks)))))

(defun ediff-keep-ancestor-and-incoming ()
  (interactive)
  (let ((marks (ediff-keep-identify-conflicts)))
    (delete-region (car (nth 3 marks)) (cdr (nth 3 marks)))
    (delete-region (car (nth 2 marks)) (cdr (nth 2 marks)))
    (delete-region (car (nth 0 marks)) (cdr (nth 1 marks)))))

(defun ediff-keep-combine-all ()
  (interactive)
  (let ((marks (ediff-keep-identify-conflicts)))
    (delete-region (car (nth 3 marks)) (cdr (nth 3 marks)))
    (delete-region (car (nth 2 marks)) (cdr (nth 3 marks)))
    (delete-region (car (nth 1 marks)) (cdr (nth 1 marks)))
    (delete-region (car (nth 0 marks)) (cdr (nth 0 marks)))))

(add-hook 'ediff-keymap-setup-hook
          #'(lambda ()
              (bind-key "x" nil ediff-mode-map)
              (bind-key "x h" 'ediff-keep-ancestor-and-incoming ediff-mode-map)
              (bind-key "x a" 'ediff-keep-head-and-incoming ediff-mode-map)
              (bind-key "x i" 'ediff-keep-head-and-ancestor ediff-mode-map)
              (bind-key "x c" 'ediff-keep-combine-all ediff-mode-map)))

(provide 'ediff-keep)

;;; ediff-keep.el ends here
