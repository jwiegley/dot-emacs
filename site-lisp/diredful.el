;;; diredful.el --- colorful file names in dired buffers

;; Author: Thamer Mahmoud <thamer.mahmoud@gmail.com>
;; Version: 1.2
;; Time-stamp: <2011-04-11 14:36:44 thamer>
;; URL: http://www.emacswiki.org/emacs/download/diredful.el
;; Keywords: dired, colors, extension, widget
;; Compatibility: Tested on GNU Emacs 23.2
;; Copyright (C) 2011 Thamer Mahmoud, all rights reserved.

;; This file is NOT part of GNU Emacs.

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 3, or (at
;; your option) any later version.

;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING. If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth
;; Floor, Boston, MA 02110-1301, USA.

;;; Commentary:
;;
;; This package provides a simple way to customize dired mode to
;; display files in different faces and colors. Faces are chosen based
;; on file extension, file name, or a regexp that matches the whole
;; file line.
;;
;;; Install:
;;
;; Put this file in your Emacs-Lisp load path, and add the following
;; into your $HOME/.emacs startup file.
;;
;;     (require 'diredful)
;;
;;; Usage:
;;
;; Do:
;;
;;     M-x diredful-add
;;
;; This will ask you to define a new name for a file type, like
;; "images". You can then specify a list of extensions and file names
;; that belong to this type, and customize the face that will be
;; used to display them. A new face will be automatically generated
;; and updated for each type.
;;
;; Note: changes will only be applied to newly created dired
;; buffers.
;;
;; File Types can be added, edited, and deleted using any of the
;; following three commands:
;;
;;     M-x diredful-add
;;     M-x diredful-delete
;;     M-x diredful-edit
;;
;; These settings will be saved to the location of
;; `diredful-init-file' (the default location is
;; "~/.emacs.d/diredful-conf.el"). You may choose a different location
;; by doing:
;;
;;     M-x customize-variable diredful-init-file
;;
;; Tip: File type names are sorted alphabetically before being
;; applied. If two file types matched the same file, the
;; file type that comes last in an alphabetically-sorted list will
;; take precedence (e.g., a type named "zworldwritable" will take
;; priority over other file types).
;;

;;; Code:
(require 'dired)
(require 'dired-x)
;;; wid-edit and cus-edit are required below

(defgroup diredful nil "diredful group"
  :group 'convenience
  :group 'dired)

(defcustom diredful-init-file
  (convert-standard-filename "~/.emacs.d/diredful-conf.el")
  "Name of file used to save diredful settings."
  :type 'file
  :group 'diredful)

(defvar diredful-names nil
  "List holding the names of patterns as strings.")

(defvar diredful-alist nil
  "An alist of lists with each element representing a file type that
will be matched when running and displaying files in dired
buffers. Each type has the following structure:
 NAME ;; Name for a file type, used as a key.
 FACE ;; Face as a symbol that will be used to display the files.
 PATTERN ;; String holding one or more regexp patterns.
 PATTERN-TYPE ;; Set the pattern-type for pattern
      nil: List of file extensions (default)
      t: List of file or directory names
      1: Regexp applied to the whole line shown by dired.
 WHOLELINE ;; if non-nil, apply face to the whole line \
 not just the file name.
 WITHDIR ;; if non-nil, include directories when applying pattern.
 WITHOUTLINK ;; if non-nil, exclude symbolic links when applying.
 pattern")

(defun diredful-settings-save ()
  (let ((file (expand-file-name diredful-init-file)))
    (save-excursion
      (with-temp-buffer
        (print diredful-names (current-buffer))
        (print diredful-alist (current-buffer))
        (write-file file nil)
        (message "diredful: Settings saved")))))

(defun diredful-settings-load ()
  (let ((file (expand-file-name diredful-init-file)))
    (save-excursion
      (with-temp-buffer
        (if (not (file-exists-p file))
            (message "diredful: No diredful configuration \
file found. Run diredful-add.")
          (insert-file-contents file)
          (goto-char (point-min))
          (condition-case eof
              (setq diredful-names (read (current-buffer)))
            (end-of-file (message "diredful: Failed to load. \
            File exists but empty or corrupt.")))
          (condition-case eof
              (setq diredful-alist (read (current-buffer)))
            (end-of-file (message "diredful: Failed to load. \
            File exists but empty or corrupt.")))
          (setq diredful-custom-loaded t))))))

(defun diredful-filter (condp ls)
  (delq nil (mapcar (lambda (x) (and (funcall condp x) x)) ls)))

(defun diredful-get-face-part (l)
  "Deal with the structure of dired-font-lock-keywords so that
only the faces that we've added can be returned."
  (if (and  (stringp (car l))
            (> (length l) 0)
            (= (length (cadr l)) 4))
      (car (cdr (car (last (cadr l)))))
    nil))

(defun diredful-apply (regexp face whole enable)
  "Add face to file type name based on the given regexp. The
regexp is applied to the whole line."
  (let* ((face-part (list 0 face))
         (face-list
          (list ".+"
                (if whole
                    '(move-beginning-of-line nil)
                  '(dired-move-to-filename))
                nil face-part)))
    (if (eq enable 0)
        ;; Delete only the faces that we've added
        (setq dired-font-lock-keywords
              (diredful-filter
               '(lambda (x)
                  (if (equal face
                             (diredful-get-face-part x))
                      nil
                    t)) dired-font-lock-keywords))
      (add-to-list 'dired-font-lock-keywords
                   (list regexp face-list)))))

(defun diredful-ext-regexp (extensions withdir withoutlink)
  "Given a list of extensions, return a regexp usable to
dired-font-lock-keywords."
  (concat
   "^. [0-9\\s ]*"
   (diredful-dirlink-regexp withdir withoutlink)
   ".*\\("
   (mapconcat
    (lambda (str) (format "\\.%s[*]?$\\|\\.%s[*]?" str (upcase str)))
    extensions "\\|")
   "\\)$"))

(defun diredful-filename-regexp (regx withdir withoutlink)
  "Return a regexp usable to apply on a file name."
  (concat
   "^. [0-9\\s ]*"
   (diredful-dirlink-regexp withdir withoutlink)
   ".*\\("
   (mapconcat
    (lambda (str) (format " %s[*]?$" str))
    regx "\\|")
   "\\)$"))

(defun diredful-whole-line-regexp (regx withdir withoutlink)
  "Return a regexp usable to apply on a whole line."
  (concat
   "^. [0-9\\s ]*"
   (diredful-dirlink-regexp withdir withoutlink)
   "\\("
   (format ".*%s.*[*]?" (car regx))
   "\\)$"))

(defun diredful-dirlink-regexp (dir link)
  (if (or (not dir) link)
      (concat "[^" (unless dir "d")
              (when link "l")
              "]")))

(defun diredful-make-face (name face-list)
  "Create and return a new face."
  (let* ((face-name (concat "diredful-face-" name))
         (face (make-face (intern face-name))))
    ;; Reset face by setting the default properties
    (diredful-set-attributes-from-alist
     face (face-all-attributes 'default))
    ;; Set new properties
    (diredful-set-attributes face face-list)
    (symbol-name face)))

(defun diredful-set-attributes (face attr)
  "Apply a list of attributes in the form (:PROP VALUE) to face."
  (while (string= (substring (symbol-name (car attr)) 0 1) ":")
    (set-face-attribute face nil (car attr) (cadr attr))
    (setq attr (cddr attr))))

(defun diredful-set-attributes-from-alist (face attr)
  "Apply an alist of attributes in the form ((:PROP . VALUE)) to
face."
  (while (car attr)
    (set-face-attribute face nil (caar attr) (cdar attr))
    (setq attr (cdr attr))))

(defun diredful-add-name (name doc-string alist)
  "Add name to an alist, but check if a name already exists and
trigger an error."
  (cond
   ((equal name "")
    (error (format "%s name cannot be empty" doc-string)))
   ((assoc name alist)
    (error (format "%s exists. Name must be unique. Choose \
another name" doc-string)))) name)

(defun diredful-add (name)
  "Add a file type used for choosing colors to file names in
dired buffers"
  (interactive
   (append
    (let* ((name (read-string (format "New name for file type: "))))
      (list name))))
  (diredful-add-name name "File type" diredful-alist)
  (add-to-list 'diredful-alist `(,name . (,'default "" nil nil)))
  (add-to-list 'diredful-names name)
  (diredful-settings-save)
  (diredful-edit name))

(defun diredful-delete (name)
  "Delete a file type used for choosing colors to file names in
dired buffers"
  (interactive
   (list
    (completing-read
     "Choose a file type to delete: " diredful-names nil t)))
  "Deletes a file type and all its parameters."
  (when (equal name "")
    (error "File type cannot be empty"))
  ;; Reset all colors from dired font-lock so that any deleted types
  ;; wouldn't remain active
  (diredful 0)
  ;; No assoc-delete-all?
  (setq diredful-alist
        (remove (assoc name diredful-alist) diredful-alist))
  (setq diredful-names (remove name diredful-names))
  (diredful-settings-save)
  ;; Re-Enable colors
  (diredful 1))

(defvar diredful-widgets nil
  "List holding widget information.")

(defun diredful-edit (name)
  "Edit a file type used for choosing colors to file names in
dired buffers"
  (interactive
   (list (completing-read "Edit Dired Color: "
                          diredful-names nil t)))
  (when (equal name "")
    (error "File type cannot be empty"))
  (switch-to-buffer
   (concat "*Customize diredful type `" name "'*"))
  (let* ((inhibit-read-only t)
         (map (make-sparse-keymap))
         (current (assoc name diredful-alist))
         ;; Numbers here should reflect the order of the widget.el
         ;; buffer
         (face-str (nth 1 current))
         (pattern-str (nth 2 current))
         (pattern-type (nth 3 current))
         (whole (nth 4 current))
         (withdir (nth 5 current))
         (withoutlink (nth 6 current)))
    (kill-all-local-variables)
    (make-local-variable 'diredful-widgets)
    (erase-buffer)
    (remove-overlays)
    ;; (unless (facep face-str)
    ;;   (setq face-str 'default))
    (require 'widget)
    ;; FIXIT: Loading this alone might break customize colors?
    (require 'cus-edit) ;; for custom-face-edit
    (widget-insert "Type `C-c C-c' or press [Save] after you have \
finished editing.\n\n" )
    (setq diredful-widgets
          (list
           ;; This widget also includes the current name of the type
           ;; being edited.
           (let ((wid (widget-create
                       'editable-field :value name
                       :format "Type Name: %v" "")))
             (widget-put wid :being-edited name)
             wid)
           (ignore (widget-insert "\n"))
           (widget-create
            'editable-field :value pattern-str
            :format "Pattern: %v" "")
           (ignore (widget-insert "\nPattern Type:\n"))
           (widget-create
            'radio-button-choice
            :value pattern-type
            '(item :format "A list of space-separated extension \
regexps. Ex. jpe?g gif png (case-insensitive)\n"
                   nil)
            '(item :format "A list of space-separated regexps \
applied to file names. Ex. README [Rr]eadme.\n"
                   t)
            '(item :format "Regexp on whole line (starting from \
the first permission column), and including file name.\n"
                   1))
           (ignore (widget-insert "\n "))
           ;; Check Boxes
           (widget-create 'checkbox withdir)
           (ignore (widget-insert
                    " Apply to directories.\n "))
           (widget-create 'checkbox withoutlink)
           (ignore (widget-insert
                    " Ignore symbolic links.\n "))
           (widget-create 'checkbox whole)
           (ignore (widget-insert
                    " Apply face to the whole line (not just \
file name).\n"))
           (ignore (widget-insert "\n"))
           ;; Face Attributes
           (ignore (widget-insert "Face to use:\n\n"))
           ;; FIXIT: Use a better equivalent to custom-face-edit if
           ;; there is one
           (widget-create 'custom-face-edit :value face-str)))
    ;; Delete empty widget-insert
    (delq nil diredful-widgets)
    (widget-insert "\n")
    ;; Buttons
    (widget-create
     'push-button
     :button-face 'custom-button
     :notify (lambda (&rest ignore)
               (diredful-save diredful-widgets)
               (kill-buffer)) "Save")
    (widget-insert " ")
    (widget-create 'push-button
                   :button-face 'custom-button
                   :notify (lambda (&rest ignore)
                             (kill-buffer))
                   "Cancel")
    (widget-insert "\n\n")
    ;; This is needed to get rid of cus-edit bindings.
    ;; Keymaps
    (widget-put (get 'editable-field 'widget-type) :keymap nil)
    (set-keymap-parent map widget-keymap)
    (define-key map (kbd "C-c C-c")
      '(lambda () (interactive)
         (diredful-save diredful-widgets)
         (kill-buffer)))
    (use-local-map map)
    (widget-setup))
  (goto-char (point-min))
  (widget-forward 1))

(defun diredful-save (widget-list)
  "Adds values of widget to type lists, saves them to file and
update."
  (let* ((old-name (widget-get (nth 0 widget-list) :being-edited))
         (current (assoc old-name diredful-alist))
         (name (widget-value (nth 0 widget-list)))
         (withdir (widget-value (nth 3 widget-list)))
         (withoutlink (widget-value (nth 4 widget-list)))
         (whole (widget-value (nth 5 widget-list)))
         (pattern-type (widget-value (nth 2 widget-list)))
         (face (widget-value (nth 6 widget-list)))
         (pattern (widget-value (nth 1 widget-list))))
    ;; Replace old type with new type
    (setq diredful-alist
          (remove (assoc old-name diredful-alist)
                  diredful-alist))
    (setq diredful-names (remove old-name diredful-names))
    ;; Delete the old name in case of a rename
    (setq dired-font-lock-keywords
          (diredful-filter
           '(lambda (x)
              (if (equal (concat "diredful-face-" old-name)
                         (diredful-get-face-part x))
                  nil
                t)) dired-font-lock-keywords))
    ;; Update variables
    (add-to-list 'diredful-alist
                 (list name face pattern pattern-type whole withdir
                       withoutlink))
    (add-to-list 'diredful-names name)
    (diredful-settings-save)
    (diredful 0)
    (diredful 1)))

(defun diredful (enable)
  (if (not (length diredful-names))
      (message "diredful: No file types have been \
defined. Define a new file type using diredful-add.")
    (let (sorted name)
      ;; Make a copy of list
      (setq sorted (append diredful-names nil))
      ;; Sort it
      (setq sorted (sort sorted 'string<))
      ;; Loop over each pattern and collect all settings
      (while sorted
        (let* ((ft-list (assoc (car sorted) diredful-alist))
               (ft-name (nth 0 ft-list))
               (ft-face (nth 1 ft-list))
               (ft-pattern (nth 2 ft-list))
               (ft-type (nth 3 ft-list))
               (ft-whole (nth 4 ft-list))
               (ft-withdir (nth 5 ft-list))
               (ft-withoutlink (nth 6 ft-list))
               conc-commands)
          (unless (eq ft-face 'default)
            (cond
             ;; Type is a list of extensions
             ((eq ft-type nil)
              (progn
                (diredful-apply
                 (diredful-ext-regexp
                  (split-string ft-pattern) ft-withdir ft-withoutlink)
                 (if (facep ft-face)
                     (symbol-name ft-face)
                  (diredful-make-face (car sorted) ft-face)) ft-whole
                   enable)))
             ;; Type is a file name
             ((eq ft-type t)
              (progn
                (diredful-apply
                 (diredful-filename-regexp
                  (split-string ft-pattern) ft-withdir ft-withoutlink)
                 (if (facep ft-face)
                     (symbol-name ft-face)
                   (diredful-make-face (car sorted) ft-face)) ft-whole
                   enable)))
             ;; Type is a whole line
             ((eq ft-type 1)
              (progn
                (diredful-apply
                 (diredful-whole-line-regexp
                  (split-string ft-pattern) ft-withdir ft-withoutlink)
                 (if (facep ft-face)
                     (symbol-name ft-face)
                   (diredful-make-face (car sorted) ft-face)) ft-whole
                   enable))))))
        (setq sorted (cdr sorted)))
      ;; Add last after processing list
      (diredful-apply "^[D]" "dired-flagged" nil enable)
      (diredful-apply "^[*]" "dired-marked" nil enable))))

(diredful-settings-load)
(diredful 0)
(diredful 1)
(provide 'diredful)
;;; diredful.el ends here.
