;;; ov.el --- Overlay library for Emacs Lisp -*- coding: utf-8; lexical-binding: t -*-

;; Copyright (C) 2014 by Shingo Fukuyama

;; Version: 1.0.6
;; Author: Shingo Fukuyama - http://fukuyama.co
;; URL: https://github.com/ShingoFukuyama/ov.el
;; Created: Mar 20 2014
;; Keywords: overlay
;; Package-Requires: ((emacs "24.3"))

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2 of
;; the License, or (at your option) any later version.

;; This program is distributed in the hope that it will be
;; useful, but WITHOUT ANY WARRANTY; without even the implied
;; warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR
;; PURPOSE.  See the GNU General Public License for more details.

;;; Commentary:

;; Simple way to manipulate overlay for Emacs.
;; More information is in README.md or https://github.com/ShingoFukuyama/ov.el

;;; Code:

(require 'cl-lib)

(defgroup ov nil
  "Group for ov.el"
  :prefix "ov-" :group 'development)

(defvar ov-sticky-front nil)
(defvar ov-sticky-rear nil)

;; http://www.gnu.org/software/emacs/manual/html_node/elisp/Overlay-Properties.html
(defvar ov-prop-list '(priority
                       window
                       category
                       face
                       mouse-face
                       display
                       help-echo
                       field
                       modification-hooks
                       insert-in-front-hooks
                       insert-behind-hooks
                       invisible
                       intangible
                       isearch-open-invisible
                       isearch-open-invisible-temporary
                       before-string
                       after-string
                       line-prefix
                       wrap-prefix
                       evaporate
                       local-map
                       keymap))

;; Make overlay / Set properties -----------------------------------------------
;; Just make an overlay from `beg' and `end'.
;; Alias                             ;; Argument
(defalias 'ov-create  'make-overlay) ;; (beg end)
(defalias 'ov-make    'make-overlay) ;; (beg end)

(defun ov (beg end &rest properties)
  "Make an overlay from BEG to END.

If PROPERTIES are specified, set them for the created overlay."
  (if properties
      (progn
        ;; To pass properties to `ov-set'
        (when (listp (car-safe properties))
          (setq properties (car properties)))
        (let ((o (ov-make beg end nil (not ov-sticky-front) ov-sticky-rear)))
          (ov-set o properties)
          o))
    (ov-make beg end nil (not ov-sticky-front) ov-sticky-rear)))

(defun ov-line (&optional point)
  "Make an overlay from the beginning of the line to the beginning of the next line, which include POINT."
  (let (o)
    (save-excursion
      (goto-char (or point (point)))
      (setq o (ov-make (point-at-bol) (min (1+ (point-at-eol)) (point-max))
                       nil (not ov-sticky-front) ov-sticky-rear)))
    o))

(defun ov-match (string &optional beg end)
  "Make overlays spanning the regions that match STRING.

If BEG and END are numbers, they specify the bounds of the search."
  (save-excursion
    (goto-char (or beg (point-min)))
    (let (ov-or-ovs)
      (ov-recenter (point-max))
      (while (search-forward string end t)
        (setq ov-or-ovs (cons (ov-make (match-beginning 0)
                                       (match-end 0)
                                       nil (not ov-sticky-front) ov-sticky-rear)
                              ov-or-ovs)))
      ov-or-ovs)))

(defun ov-regexp (regexp &optional beg end)
  "Make overlays spanning the regions that match REGEXP.

If BEG and END are numbers, they specify the bounds of the search."
  (save-excursion
    (goto-char (or beg (point-min)))
    (let (ov-or-ovs finish)
      (ov-recenter (point-max))
      (while (and (not finish) (re-search-forward regexp end t))
        (setq ov-or-ovs (cons (ov-make (match-beginning 0)
                                       (match-end 0)
                                       nil (not ov-sticky-front) ov-sticky-rear)
                              ov-or-ovs))
        (when (= (match-beginning 0) (match-end 0))
          (if (eobp)
              (setq finish t)
            (forward-char 1))))
      ov-or-ovs)))

(defun ov-region ()
  "Make an overlay from a region if region is active."
  (if (use-region-p)
      (let ((o (ov-make (region-beginning) (region-end)
                        nil (not ov-sticky-front) ov-sticky-rear)))
        (deactivate-mark t)
        o)
    (error "Need to make region")))

(defun ov-set (ov-or-ovs-or-regexp &rest properties)
  "Set overlay properties and values.
OV-OR-OVS-OR-REGEXP can be an overlay, overlays or a regexp.

If an overlay or list of overlays, PROPERTIES are set for these.

If a regexp, first overlays are created on the matching
regions (see `ov-regexp'), then the properties are set."
  (when ov-or-ovs-or-regexp
    (unless (and ov-or-ovs-or-regexp properties)
      (error "Arguments are OV and PROPERTIES"))
    (when (listp (car-safe properties))
      (setq properties (car properties)))
    (let ((len (length properties))
          (i 0)
          return-value return-type)
      (cond ((stringp ov-or-ovs-or-regexp)
             (setq ov-or-ovs-or-regexp (ov-regexp ov-or-ovs-or-regexp))
             (setq return-type 'ov-list))
            ((ov-p ov-or-ovs-or-regexp)
             (setq ov-or-ovs-or-regexp (cons ov-or-ovs-or-regexp nil))
             (setq return-type 'ov))
            ((listp ov-or-ovs-or-regexp)
             (setq return-type 'ov-list)))
      (unless (eq (logand len 1) 0)
        (error "Invalid properties pairs"))
      (setq return-value
            (mapc (lambda (ov)
                    (while (< i len)
                      (overlay-put
                       ov
                       (nth i properties) (nth (setq i (1+ i)) properties))
                      (setq i (1+ i)))
                    (setq i 0))
                  ov-or-ovs-or-regexp))
      (if (eq 'ov return-type)
          (car return-value)
        return-value))))
(defalias 'ov-put 'ov-set)

(defun ov-insert (any)
  "Insert ANY (string, number, list, etc) covered with an empty overlay."
  (or (stringp any) (setq any (format "%s" any)))
  (let* ((beg (point))
         (len (length any))
         (end (+ beg len)))
    (insert any)
    (ov-make beg end nil (not ov-sticky-front) ov-sticky-rear)))


;; Delete overlay --------------------------------------------------------------
;;;###autoload
(cl-defun ov-clear (&optional prop-or-beg (val-or-end 'any) beg end)
  "Clear overlays satisfying a condition.

If PROP-OR-BEG is a symbol, clear overlays with this property set to non-nil.

If VAL-OR-END is non-nil, the specified property's value should
`equal' to this value.

If both of these are numbers, clear the overlays between these points.

If BEG and END are numbers, clear the overlays with specified
property and value between these points.

With no arguments, clear all overlays in the buffer."
  (interactive)
  (cl-labels ((clear
               (con beg end)
               (ov-recenter (or end (point-max)))
               (mapc (lambda (ov)
                       (when (and (memq prop-or-beg (ov-prop ov))
                                  (if con
                                      t (equal val-or-end (ov-val ov prop-or-beg))))
                         (delete-overlay ov)))
                     (overlays-in beg end))))
    (cond
     ;; (ov-clear)
     ((and (not prop-or-beg) (eq 'any val-or-end) (not beg) (not end))
      (ov-recenter (point-max))
      (remove-overlays (point-min) (point-max)))
     ;; (ov-clear 10 500)
     ((and (numberp prop-or-beg) (numberp val-or-end))
      (ov-recenter val-or-end)
      (remove-overlays prop-or-beg val-or-end))
     ;; (ov-clear 'face 'warning)
     ((and (symbolp prop-or-beg) (not (eq 'any val-or-end)) (not beg) (not end))
      (clear nil (point-min) (point-max)))
     ;; (ov-clear 'face) or (ov-clear 'face 'any)
     ((and (symbolp prop-or-beg) (eq 'any val-or-end) (not beg) (not end))
      (clear t (point-min) (point-max)))
     ;; (ov-clear 'face 'worning 10 500)
     ((and (symbolp prop-or-beg) (not (eq 'any val-or-end)) (numberp beg) (numberp end))
      (clear nil beg end))
     ;; (ov-clear 'face 'any 10 500)
     ((and (symbolp prop-or-beg) (eq 'any val-or-end) (numberp beg) (numberp end))
      (clear t beg end))
     (t nil)))
  nil)

(defmacro ov-reset (ov-or-ovs-variable)
  "Clear overlays in OV-OR-OVS-VARIABLE.

OV-OR-OVS-VARIABLE should be a symbol whose value is an overlay
or a list of overlays.

Finally, the variable is set to nil."
  `(progn
     (mapc (lambda (ov)
             (delete-overlay ov))
           (if (listp ,ov-or-ovs-variable)
               ,ov-or-ovs-variable
             (cons ,ov-or-ovs-variable nil)))
     (setq ,ov-or-ovs-variable nil)))


;; Look up overlay parameters, etc ---------------------------------------------
;; Alias                                ;; Argument
;; Check whether `ov' is overlay or not.
(defalias 'ov-p    'overlayp)           ;; (ov)
(defalias 'ov?     'overlayp)           ;; (ov)
(defalias 'ov-val  'overlay-get)        ;; (ov property)
;; Get the boundary position of an overlay.
(defalias 'ov-beg  'overlay-start)      ;; (ov)
(defalias 'ov-end  'overlay-end)        ;; (ov)
;; Get the buffer object of an overlay.
(defalias 'ov-buf  'overlay-buffer)     ;; (ov)
;; Get the properties from an overlay.
(defalias 'ov-prop 'overlay-properties) ;; (ov)

(defun ov-length (overlay)
  "Return the length of the region spanned by OVERLAY."
  (- (ov-end overlay) (ov-beg overlay)))

(defun ov-spec (ov-or-ovs)
  "Make an overlay specification list.
This is of the form:

  (beginnig end buffer &rest properties).

OV-OR-OVS should be an overlay or a list of overlays."
  (or (listp ov-or-ovs) (setq ov-or-ovs (cons ov-or-ovs nil)))
  (mapcar (lambda (ov)
            (list (ov-beg ov) (ov-end ov)
                  (ov-buf ov) (overlay-properties ov)))
          ov-or-ovs))


;; Get present overlay object --------------------------------------------------
(defun ov-at (&optional point)
  "Get an overlay at POINT.
POINT defaults to the current `point'."
  (or point (setq point (point)))
  (car (overlays-at point)))

;; Get overlays between `beg' and `end'.
(cl-defun ov-in (&optional prop-or-beg (val-or-end 'any) beg end)
  "Get overlays satisfying a condition.

If PROP-OR-BEG is a symbol, get overlays with this property set to non-nil.

If VAL-OR-END is non-nil, the specified property's value should
`equal' to this value.

If both of these are numbers, get the overlays between these points.

If BEG and END are numbers, get the overlays with specified
property and value between these points.

With no arguments, get all overlays in the buffer."
  (cl-labels ((in (con beg end)
                  (delq nil
                        (mapcar
                         (lambda ($ov)
                           (when (and (memq prop-or-beg (ov-prop $ov))
                                      (if con
                                          t (equal val-or-end (ov-val $ov prop-or-beg))))
                             $ov))
                         (overlays-in beg end)))))
    (cond
     ;; (ov-in)
     ((and (not prop-or-beg) (eq 'any val-or-end) (not beg) (not end))
      (overlays-in (point-min) (point-max)))
     ;; (ov-in 10 500)
     ((and (numberp prop-or-beg) (numberp val-or-end))
      (overlays-in prop-or-beg val-or-end))
     ;; (ov-in 'face 'warning)
     ((and (symbolp prop-or-beg) (not (eq 'any val-or-end)) (not beg) (not end))
      (in nil (point-min) (point-max)))
     ;; (ov-in 'face) or (ov-in 'face 'any)
     ((and (symbolp prop-or-beg) (eq 'any val-or-end) (not beg) (not end))
      (in t (point-min) (point-max)))
     ;; (ov-in 'face 'worning 10 500)
     ((and (symbolp prop-or-beg) (not (eq 'any val-or-end)) (numberp beg) (numberp end))
      (in nil beg end))
     ;; (ov-in 'face 'any 10 500)
     ((and (symbolp prop-or-beg) (eq 'any val-or-end) (numberp beg) (numberp end))
      (in t beg end))
     (t nil))))

(defun ov-all ()
  "Get all the overlays in the entire buffer."
  (overlays-in (point-min) (point-max)))

(defun ov-backwards (&optional point)
  "Get all the overlays from the beginning of the buffer to POINT."
  (ov-in (point-min) (or point (point))))

(defun ov-forwards (&optional point)
  "Get all the overlays from POINT to the end of the buffer."
  (ov-in (or point (point)) (point-max)))


;; Overlay manipulation --------------------------------------------------------
;; Alias                                  ;; Argument
(defalias 'ov-recenter 'overlay-recenter) ;; (point)
;; Move an existing overlay position to another position.
(defalias 'ov-move     'move-overlay)     ;; (ov beg end &optional buffer)

(defmacro ov-timeout (time func func-after)
  "Execute FUNC-AFTER after TIME seconds passed since FUNC finished."
  (declare (indent 1))
  (if (symbolp func-after)
      (run-with-timer time nil `(lambda () (funcall ',func-after)))
    (run-with-timer time nil `(lambda () ,(funcall `(lambda () ,func-after)))))
  (if (symbolp func)
      (funcall func)
    (funcall (lambda () (eval func)))))

(cl-defun ov-next (&optional point-or-prop prop-or-val (val 'any))
  "Get the next overlay satisfying a condition.

If POINT-OR-PROP is a symbol, get the next overlay with this
property being non-nil.

If PROP-OR-VAL is non-nil, the property should have this value.

If POINT-OR-PROP is a number, get the next overlay after this
point.

If PROP-OR-VAL and VAL are also specified, get the next overlay
after POINT-OR-PROP having property PROP-OR-VAL set to VAL (with
VAL unspecified, only the presence of property is tested)."
  (cl-labels ((next
               (po pr va)
               (save-excursion
                 (goto-char (next-overlay-change po))
                 (let (ov)
                   (while (and (not (if (setq ov (ov-at (point)))
                                        (and (memq pr (ov-prop ov))
                                             (if (eq 'any va)
                                                 t (equal va (ov-val ov pr))))))
                               (not (if (eobp) (progn (setq ov nil) t))))
                     (goto-char (next-overlay-change (point))))
                   ov))))
    (cond
     ;; (ov-next) or (ov-next 300)
     ((and (or (numberp point-or-prop) (not point-or-prop))
           (not prop-or-val) (eq 'any val))
      (let* ((po (next-overlay-change (or point-or-prop (point))))
             (ov (ov-at po)))
        (if (ov? ov)
            ov
          (ov-at (next-overlay-change po)))))
     ;; (ov-next 'face)
     ((and point-or-prop (symbolp point-or-prop) (not prop-or-val) (eq 'any val))
      (next (point) point-or-prop 'any))
     ;; (ov-next 'face 'warning)
     ((and point-or-prop (symbolp point-or-prop) prop-or-val (eq 'any val))
      (next (point) point-or-prop prop-or-val))
     ;; (ov-next 300 'face 'warning)
     ((and (or (not point-or-prop) (numberp point-or-prop))
           (symbolp prop-or-val) (not (eq 'any val)))
      (next (or point-or-prop (point)) prop-or-val val))
     ;; (ov-next 300 'face)
     ((and (or (numberp point-or-prop) (not point-or-prop)) (symbolp prop-or-val))
      (next (or point-or-prop (point)) prop-or-val val))
     (t nil))))

(cl-defun ov-prev (&optional point-or-prop prop-or-val (val 'any))
  "Get the previous overlay satisfying a condition.

If POINT-OR-PROP is a symbol, get the previous overlay with this
property being non-nil.

If PROP-OR-VAL is non-nil, the property should have this value.

If POINT-OR-PROP is a number, get the previous overlay after this
point.

If PROP-OR-VAL and VAL are also specified, get the previous
overlay after POINT-OR-PROP having property PROP-OR-VAL set to
VAL (with VAL unspecified, only the presence of property is
tested)."
  (cl-labels ((prev
               (po pr va)
               (save-excursion
                 (goto-char (previous-overlay-change po))
                 (let (ov)
                   (while (and (not (if (setq ov (ov-at (1- (point))))
                                        (and (memq pr (ov-prop ov))
                                             (if (eq 'any va)
                                                 t (equal va (ov-val ov pr))))))
                               (not (if (bobp) (progn (setq ov nil) t))))
                     (goto-char (previous-overlay-change (point))))
                   ov))))
    (cond
     ((and (or (numberp point-or-prop) (not point-or-prop))
           (not prop-or-val) (eq 'any val))
      (let* ((po1 (previous-overlay-change (point)))
             (po2 (previous-overlay-change po1))
             (ov (or (ov-at po2) (ov-at (1- po2)))))
        (if (ov? ov) ov)))
     ;; (ov-prev 'face)
     ((and point-or-prop (symbolp point-or-prop) (not prop-or-val) (eq 'any val))
      (prev (point) point-or-prop 'any))
     ;; (ov-prev 'face 'warning)
     ((and point-or-prop (symbolp point-or-prop) prop-or-val (eq 'any val))
      (prev (point) point-or-prop prop-or-val))
     ;; (ov-prev 300 'face 'warning)
     ((and (or (not point-or-prop) (numberp point-or-prop))
           (symbolp prop-or-val) (not (eq 'any val)))
      (prev (or point-or-prop (point)) prop-or-val val))
     ;; (ov-prev 300 'face)
     ((and (or (numberp point-or-prop) (not point-or-prop)) (symbolp prop-or-val))
      (prev (or point-or-prop (point)) prop-or-val val))
     (t nil))))

(cl-defun ov-goto-next (&optional point-or-prop prop-or-val (val 'any))
  "Move cursor to the end of the next overlay.
The arguments are the same as for `ov-next'."
  (interactive)
  (let ((o (ov-next point-or-prop prop-or-val val)))
    (if o (goto-char (ov-end o)))))

(cl-defun ov-goto-prev (&optional point-or-prop prop-or-val (val 'any))
  "Move cursor to the beginning of previous overlay.
The arguments are the same as for `ov-prev'."
  (interactive)
  (let ((o (ov-prev point-or-prop prop-or-val val)))
    (if o (goto-char (ov-beg o)))))

(defun ov-keymap (ov-or-ovs-or-id &rest keybinds)
  "Set KEYBINDS to an overlay or a list of overlays.

If OV-OR-OVS-OR-ID is a symbol, the KEYBINDS will be enabled for
the entire buffer and the property represented by the symbol to
`t'.

The overlay is expanded if new inputs are inserted at the
beginning or end of the buffer."
  (let ((map (make-sparse-keymap)))
    (when (cl-evenp (length keybinds))
      (while keybinds
        (let* ((key (pop keybinds))
               (fn  (pop keybinds))
               (command (cl-typecase fn
                          (command fn)
                          (cons `(lambda () (interactive) ,fn))
                          (t (error "Invalid function")))))
          (cl-typecase key
            (vector (define-key map key command))
            (string (define-key map (kbd key) command))
            (list   (mapc (lambda (k)
                            (define-key map (cl-typecase k
                                              (vector k)
                                              (string (kbd k))) command))
                          key))
            (t (error "Invalid key"))))))
    (if (symbolp ov-or-ovs-or-id)
        (let ((ov-sticky-front t)
              (ov-sticky-rear  t))
          (ov (point-min) (point-max) 'keymap map ov-or-ovs-or-id t))
      (ov-set ov-or-ovs-or-id 'keymap map))))


;; Impliment pseudo read-only overlay function ---------------------------------
(defun ov-read-only (ov-or-ovs &optional insert-in-front insert-behind)
  "Implement a read-only like feature for an overlay or a list of overlays.

If INSERT-IN-FRONT is non-nil, inserting in front of each overlay is prevented.

If INSERT-BEHIND is non-nil, inserting behind of each overlay is prevented.

Note that it allows modifications from out of range of a read-only overlay."
  (cond ((not (and insert-in-front insert-behind))
         (ov-set ov-or-ovs
                 'modification-hooks '(ov--read-only)))
        ((and insert-in-front insert-behind)
         (ov-set ov-or-ovs
                 'modification-hooks '(ov--read-only)
                 'insert-in-front-hooks '(ov--read-only)
                 'insert-behind-hooks '(ov--read-only)))
        (insert-in-front
         (ov-set ov-or-ovs
                 'modification-hooks '(ov--read-only)
                 'insert-in-front-hooks '(ov--read-only)))
        (t ;; Should be insert-behind
         (ov-set ov-or-ovs
                 'modification-hooks '(ov--read-only)
                 'insert-behind-hooks '(ov--read-only)))))

(defun ov--read-only (ov after beg end &optional _length)
  (when (and (not (or after
                      undo-in-progress
                      (eq this-command 'undo)
                      (eq this-command 'redo)))
             ;; Modification within range of a text
             (or (< (ov-beg ov) beg)
                 (> (ov-end ov) end)))
    (error "Text is read-only")))


;; Special overlay -------------------------------------------------------------
(defun ov-placeholder (ov-or-ovs)
  "Set a placeholder feature for an overlay or a list of overlays.

Each overlay deletes its string and overlay, when it is modified."
  (ov-set ov-or-ovs
          'evaporate t
          'modification-hooks '(ov--placeholder)
          'insert-in-front-hooks '(ov--placeholder)
          'insert-behind-hooks '(ov--placeholder)))

(defun ov--placeholder (ov after beg end &optional length)
  (let ((inhibit-modification-hooks t))
    (when (not (or undo-in-progress
                   (eq this-command 'undo)
                   (eq this-command 'redo)))
      (cond ((and (not after) (eq beg end))
             (delete-region (ov-beg ov) (ov-end ov)))
            ((and after (> length 0))
             (if (ov-beg ov)
                 (delete-region (ov-beg ov) (ov-end ov))))))))


;; Smear background ------------------------------------------------------------
(defun ov--parse-hex-color (hex)
  "Convert a hex color code to a RGB list.
i.e.
#99ccff => (153 204 255)
#33a    => (51 51 170)"
  (let (result)

    (when (string-match
           "^\\s-*\\#\\([0-9a-fA-F]\\)\\([0-9a-fA-F]\\)\\([0-9a-fA-F]\\)\\s-*$"
           hex)
      (let ((m1 (match-string 1 hex))
            (m2 (match-string 2 hex))
            (m3 (match-string 3 hex)))
        (setq result (list (read (format "#x%s%s" m1 m1))
                           (read (format "#x%s%s" m2 m2))
                           (read (format "#x%s%s" m3 m3))))))
    (when (string-match
           "^\\s-*\\#\\([0-9a-fA-F]\\{2\\}\\)\\([0-9a-fA-F]\\{2\\}\\)\\([0-9a-fA-F]\\{2\\}\\)\\s-*$"
           hex)
      (setq result (list (read (format "#x%s" (match-string 1 hex)))
                         (read (format "#x%s" (match-string 2 hex)))
                         (read (format "#x%s" (match-string 3 hex))))))
    result))

(defun ov--random-color (&optional base-color range)
  "Generate random color based on BASE-COLOR and RANGE.
Default background color is used when BASE-COLOR is nil."
  (or range (setq range 50))
  (let ((default-background-color (ignore-errors (face-attribute 'default :background))))
    (or base-color
        (setq base-color
              (cond ((eq 'unspecified default-background-color)
                     "#fff")
                    ((string-match "^#[0-9a-fA-F]\\{3,6\\}" default-background-color)
                     default-background-color)
                    ((color-name-to-rgb default-background-color) ;; yellow, LightBlue, etc...
                     default-background-color)
                    (t "#fff")))))
  (if (color-name-to-rgb base-color)
      (let ((rgb) (hex "#"))
        (mapc (lambda (x)
                (setq rgb (cons (round (* x 255)) rgb)))
              (color-name-to-rgb base-color))
        (setq rgb (nreverse rgb))
        (mapc (lambda (x)
                (setq hex (concat hex (format "%02x" x))))
              rgb)
        (setq base-color hex)))
  (let* ((rgb (ov--parse-hex-color base-color))
         (half-range (/ range 2))
         (fn (lambda (n)
               (let* ((base (nth n rgb))
                      (min half-range)
                      (max (- 255 half-range))
                      result)
                 (if (< base min) (setq base min))
                 (if (> base max) (setq base max))
                 (setq result (+ (- (cl-random range) half-range) base))
                 (if (< result 0) (setq result 0))
                 (if (> result 255) (setq result 255))
                 result)))
         (r (funcall fn 0))
         (g (funcall fn 1))
         (b (funcall fn 2)))
    (format "#%02x%02x%02x" r g b)))

(defun ov-smear (regexp-or-list &optional match-end base-color color-range)
  "Set background color overlays to the current buffer.
Each background color is randomly determined based on BASE-COLOR
or  the default background color.

If REGEXP-OR-LIST is regexp
   Set overlays between matches of a regexp.
If REGEXP-OR-LIST is list
   Set overlays between point pairs in a list.
   i.e. (ov-smear '((1 . 30) (30 . 90))) "
  (interactive "sSplitter: ")
  (ov-clear 'ov-smear)
  (let (points area length (counter 0) ov-list)
    (cl-typecase regexp-or-list
      (string (save-excursion
                (goto-char (point-min))
                (while (re-search-forward regexp-or-list nil t)
                  (setq points (cons
                                (if match-end
                                    (match-end 0)
                                  (match-beginning 0))
                                points))))
              (setq points (nreverse points))
              (setq length (length points))
              (while (< counter (1- length))
                (setq area (cons
                            (cons
                             (nth counter points)
                             (nth (1+ counter) points))
                            area))
                (setq counter (1+ counter))))
      (list (setq area regexp-or-list)))
    (mapc (lambda (a)
            (let ((ov (ov (car a) (cdr a))))
              (ov-set ov
                      'face `(:background ,(ov--random-color base-color color-range))
                      'ov-smear t)
              (setq ov-list (cons ov ov-list))))
          area)
    ov-list))




(provide 'ov)
;;; ov.el ends here
