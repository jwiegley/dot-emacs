;;; ee-menubar.el --- categorized access to Emacs menu-bar

;; Copyright (C) 2002, 2003, 2004, 2010  Juri Linkov <juri@jurta.org>

;; Author: Juri Linkov <juri@jurta.org>
;; Keywords: ee, tools

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

;;; Suggested keybindings:

;; (define-key global-map "\M-`" 'ee-menubar)
;; (define-key global-map [f10] 'ee-menubar)

;;; Code:

(require 'ee)

(eval-when-compile
  (require 'tmm nil t))

;;; Constants

(defconst ee-menubar-mode-name "ee-menubar")

;;; Customizable Variables

(defgroup ee-menubar nil
  "Categorized access to Emacs menu-bar."
  :prefix "ee-menubar-"
  :group 'ee)

(defcustom ee-menubar-record-flag nil
  "Put the called command in the command-history."
  :type 'boolean
  :group 'ee-menubar)

;;; Data Description

(defvar ee-menubar-data
  '[(meta
     (format-version . "0.0.1")
     (database-version . "0.0.1")
     (view-data-file . "view/menubar.ee")
     (collector . ee-menubar-data-collect)
     (fields category name title level command help event binding ())
     (key-fields name category))])

;;; Data Extraction

(defun ee-menubar-data-collect (data)
  (let ((old-data (if ee-data
                      (mapcar (lambda (r)
                                (ee-field 'name r))
                              (ee-data-records-find ee-data '(read . t)))))
        (new-data
         (ee-data-convert-lists-to-vectors
          (ee-menubar-data-collect-items
           (ee-data-field-names data)
           (tmm-get-keybind [menu-bar])
           0))))
    (aset new-data 0 (aref data 0))
    (if old-data
        (ee-data-records-do
         new-data
         (lambda (r ri)
           (if (member (ee-field 'name r) old-data)
               (ee-field-set 'read t r (ee-data-meta-setters-get-set new-data))))))
    new-data))

(defun ee-menubar-data-collect-items (field-names menu level)
  (if (keymapp menu)
      (mapcan
       (lambda (item)
         (if (consp item)
             (let* ((name (car-safe item))
                    (title (if (eq (car-safe (cdr-safe item)) 'menu-item)
                               (car (cdr-safe (cdr-safe item)))
                             (car-safe (cdr-safe item))))
                    (keymap (cond ((keymapp (cdr-safe (cdr-safe item)))
                                   (indirect-function (cdr (cdr item))))
                                  ((keymapp (car-safe (cdr-safe (cdr-safe (cdr-safe item)))))
                                   (indirect-function (car (cdr (cdr (cdr item))))))))
                    (command (or keymap
                                 (car-safe (cdr-safe (cdr-safe (cdr-safe item)))))))
               (append
                (if (and name title)
                    (list (mapcar (lambda (field-name)
                                    (cond
                                     ((eq field-name 'name) name)
                                     ((eq field-name 'title) title)
                                     ((eq field-name 'level) level)
                                     ((eq field-name 'command) command)))
                                  field-names)))
                (if keymap
                    (ee-menubar-data-collect-items
                     field-names keymap (1+ level)))))))
       (reverse (cdr menu)))))

;; this is the same as ee-outline-c-tree-builder - TODO: make generic function
(defun ee-menubar-c-tree-builder (&optional record-index)
  ;; input:  [[level1 "name1" apos1 bpos1] [level2 "name2" apos2 bpos2] ...]
  ;; output: (1 (2 ...) ...)
  ;; with assumption that order of input vector elements corresponds to tree pre-order
  (let ((data ee-data)
        (level -1))
    (with-temp-buffer
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

(defun ee-menubar-select (&optional arg)
  (interactive)
  (if (ee-view-on-expansion-line-p)
      (ee-view-expansion-show-or-hide)
    (let ((command (ee-field 'command))
          (parent-buffer ee-parent-buffer))
      (ee-field-set 'read t)
      (ee-view-update '(read)) ;; (ee-view-record-update)
      (when (and command parent-buffer)
        (switch-to-buffer parent-buffer)
        (call-interactively command ee-menubar-record-flag)))))

(defun ee-menubar-execute (r marks)
  (interactive))

;;; Key Bindings

(defvar ee-menubar-keymap nil
  "Local keymap for ee-menubar mode.")

(defun ee-menubar-keymap-make-default ()
  "Defines default key bindings for `ee-menubar-keymap'.
It inherits key bindings from `ee-mode-map'."
  (or ee-mode-map
      (ee-mode-map-make-default))
  (let ((map (copy-keymap ee-mode-map)))
    ;; (define-key map "o" 'ee-menubar-select)
    (setq ee-menubar-keymap map)))

(or ee-menubar-keymap
    (ee-menubar-keymap-make-default))

;;; Top-Level Functions

;;;###autoload
(defun ee-menubar (&optional arg)
  "Categorized access to Emacs menu-bar."
  (interactive "P")
  (require 'tmm)
  ;; TODO: remove next two lines, when submenus will be implemented
  ;; as categories (not records) in the ee-menubar-c-tree-builder,
  ;; so ee-hidden-expansions could be used to retain opened menus
  (if (get-buffer (format "*%s*" ee-menubar-mode-name))
      (switch-to-buffer (format "*%s*" ee-menubar-mode-name))
    (ee-view-buffer-create
     (format "*%s*" ee-menubar-mode-name)
     ee-menubar-mode-name
     ee-menubar-keymap
     ee-menubar-data)))

;;;###autoload (defalias 'ee-tmm 'ee-menubar)

(provide 'ee-menubar)

;;; ee-menubar.el ends here
