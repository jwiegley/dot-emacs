;;; ee-outline.el --- manipulate outlines collected from outline-mode

;; Copyright (C) 2002, 2003, 2004, 2010  Juri Linkov <juri@jurta.org>

;; Author: Juri Linkov <juri@jurta.org>
;; Keywords: ee, outlines

;; This file is [not yet] part of GNU Emacs.

;; This package is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This package is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this package; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;; See the file README and documentation for more information.

;; HINT: good hack is to invoke ee-outline on ee-buffers (or ee-dired)
;; with directory tree where (setq outline-regexp " *[+-]") is set

;; TODO: use standard Emacs faces outline-1, outline-2, ..., outline-8

;;; Code:

(require 'ee)

(eval-when-compile
  (require 'outline))

;;; Constants

(defconst ee-outline-mode-name "ee-outline")

;;; Customizable Variables

(defgroup ee-outline nil
  "Manipulate outlines collected from outline-mode."
  :prefix "ee-outline-"
  :group 'ee)

;;; Data Description

(defvar ee-outline-data
  '[(meta
     (format-version . "0.0.1")
     (view-data-file . "view/outline.ee")
     (collector . ee-outline-data-collect)
     (fields level heading b e ())
     (key-fields heading))])

;;; Data Extraction

(defun ee-outline-data-collect (data)
  (let ((new-data
         (ee-data-convert-lists-to-vectors
          (with-current-buffer ee-parent-buffer
            (ee-outline-data-collect-conv
             (ee-data-field-names data))))))
    (aset new-data 0 (aref data 0))
    new-data))

(defun ee-outline-data-collect-conv (field-names)
  (mapcar
   (lambda (e)
     (mapcar
      (lambda (field-name)
        (cond
         ((eq field-name 'level) (nth 0 e))
         ((eq field-name 'heading)
          (buffer-substring;;-no-properties ;; use original outline properties
           (nth 1 e) ;;BAD:? (+ (nth 0 e) (nth 1 e))
           (nth 2 e)))
         ((eq field-name 'b) (nth 1 e))
         ((eq field-name 'e) (nth 3 e))))
      field-names))
   (ee-outline-data-collect-list)))

(defun ee-outline-data-collect-list ()
  (save-excursion
    (let ((prev-point 1)
          (prev-level 0)
          ;; fix Emacs21 flaw with fake level 1000 in (lisp-outline-level):
          ;; change level 1000 to previous_level + 1
          (prev-level-not-1000 0)
          (prev-heading-point 1)
          (next-point 1)
          res)
      (goto-char (point-min))
      (if (outline-on-heading-p)
          (setq prev-point (point)
                prev-level (funcall outline-level)
                prev-heading-point (progn (outline-end-of-heading) (point))))
      (while (setq next-point (outline-next-heading))
        (if (< prev-level 1000)
            (setq prev-level-not-1000 prev-level))
        (setq res (cons (list (if (< prev-level 1000) prev-level (1+ prev-level-not-1000))
                              prev-point prev-heading-point next-point) res)
              prev-point next-point
              prev-level (funcall outline-level)
              prev-heading-point (progn (outline-end-of-heading) (point))))
      (if (/= (point) prev-point)
          (setq res (cons (list prev-level prev-point prev-heading-point (point)) res)))
      (nreverse res))))

;; this is the same as ee-menubar-c-tree-builder - TODO: make generic function
(defun ee-outline-c-tree-builder (&optional record-index)
  ;; input:  [[level1 "name1" apos1 bpos1] [level2 "name2" apos2 bpos2] ...]
  ;; output: (1 (2 ...) ...)
  ;; with assumption that order of input vector elements corresponds to tree pre-order
  (let ((data ee-data)
        (level -1))
    (with-temp-buffer
 ;; (with-current-buffer (get-buffer-create "*TEST*")
      (insert (format "(%s" ee-mark-record-tree))
      (ee-data-records-do
       data
       (lambda (r ri)
         (let* ((elt-level (ee-field 'level r))
                (diff (- elt-level level)))
           (if (> diff 0)
               (dotimes (i (- diff 1)) (insert "(nil "))
             (dotimes (i (+ (abs diff) 1)) (insert ")")))
           (insert "(")
           (insert (format "%s" ri))
           (setq level elt-level))))
      (dotimes (i (+ level 1)) (insert ")"))
      (insert ")")
      (goto-char (point-min))
      (read (current-buffer)))))

;;; Actions

(defun ee-outline-switch-to-buffer (&optional arg other-window)
  (interactive)
  (let ((b (ee-field 'b))
        (parent-buffer ee-parent-buffer))
    (when (and b parent-buffer)
      (when other-window
        ;; TODO: improve next bad hack
        (if (one-window-p) (split-window-horizontally 33))
        (select-window (next-window)))
      (switch-to-buffer parent-buffer)
      (goto-char b)
      (set-window-start nil b)
      (if (eq other-window 'display)
          (select-window (next-window))))))

(defun ee-outline-switch-to-buffer-other-window (&optional arg)
  (interactive)
  (ee-outline-switch-to-buffer arg t))

(defun ee-outline-display-buffer (&optional arg)
  (interactive)
  ;; TODO: qv occur-mode-display-occurrence
  ;; TODO: qv ibuffer-occur-display-occurence
  (ee-outline-switch-to-buffer arg 'display))

;; TODO: use arg other-window and bind to some key ("r"?)
(defun ee-outline-switch-to-buffer-narrow-to-region (&optional other-window)
  (interactive)
  (let* ((r (ee-view-record-get))
         (b (ee-field 'b r))
         (e (ee-field 'e r)))
    (when (and b e ee-parent-buffer)
      (with-current-buffer ee-parent-buffer
        (narrow-to-region b e)
        (goto-char b))
      (set-window-start (display-buffer ee-parent-buffer) b))))

;; TODO: use arg other-window and bind to some key (C-???)
(defun ee-outline-switch-to-buffer-mark-region (&optional other-window)
  (interactive)
  (let* ((r (ee-view-record-get))
         (b (ee-field 'b r))
         (e (ee-field 'e r)))
    (when (and r ee-parent-buffer)
      (switch-to-buffer ee-parent-buffer)
      (goto-char b)
      (push-mark (save-excursion (goto-char e) (point)) nil t))))

;;; Key Bindings

(defvar ee-outline-keymap nil
  "Local keymap for ee-outline-mode buffers.")

(defun ee-outline-keymap-make-default ()
  "Defines default key bindings for `ee-outline-keymap'.
It inherits key bindings from `ee-mode-map'."
  (or ee-mode-map
      (ee-mode-map-make-default))
  (let ((map (copy-keymap ee-mode-map)))
    (define-key map "o" 'ee-outline-switch-to-buffer-other-window)
    (define-key map "\C-o" 'ee-outline-display-buffer)
    (setq ee-outline-keymap map)))

(or ee-outline-keymap
    (ee-outline-keymap-make-default))

;;; Top-Level Functions

;;;###autoload
(defun ee-outline (&optional arg)
  "Manipulate outlines collected from outline-mode."
  (interactive "P")
  (require 'outline)
  (ee-view-buffer-create
   (format "*%s*/%s" ee-outline-mode-name (buffer-name))
   ee-outline-mode-name
   ee-outline-keymap
   ee-outline-data))

(provide 'ee-outline)

;;; ee-outline.el ends here
