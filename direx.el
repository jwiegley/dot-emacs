;;; direx.el --- Simple Directory Explorer

;; Copyright (C) 2011-2015  Tomohiro Matsuyama

;; Author: Tomohiro Matsuyama <m2ym.pub@gmail.com>
;; Keywords: convenience
;; Version: 1.0.0

;; This program is free software; you can redistribute it and/or modify
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

;; 

;;; Code:

(require 'cl-lib)
(eval-when-compile (require 'cl))
(require 'eieio)
(require 'dired)
(require 'regexp-opt)

(defconst direx:version "1.0.0")

(defgroup direx nil
  "Directory Explorer."
  :group 'convenience
  :prefix "direx:")

(defcustom direx:leaf-icon "   "
  ""
  :type 'string
  :group 'direx)
  
(defcustom direx:open-icon "[-]"
  ""
  :type 'string
  :group 'direx)

(defcustom direx:closed-icon "[+]"
  ""
  :type 'string
  :group 'direx)

(defcustom direx:ignored-files-regexp
  (concat "\\(?:" (regexp-opt completion-ignored-extensions) "\\|#\\)$")
  ""
  :type 'string
  :group 'direx)



;;; Utilities

(defmacro direx:aif (test then &rest else)
  (declare (indent 2))
  `(let ((it ,test)) (if it ,then ,@else)))

(defmacro direx:awhen (test &rest body)
  (declare (indent 1))
  `(let ((it ,test)) (when it ,@body)))

(defun direx:apply-partially (fun &rest args)
  (if (fboundp 'apply-partially)
      (apply 'apply-partially fun args)
    (require 'cl)
    (lexical-let ((fun fun) (args args))
      (lambda (&rest restargs)
	(apply fun (append args restargs))))))

(defun direx:starts-with (x y)
  (and (<= (length y) (length x))
       (equal (substring x 0 (length y)) y)))

(defun direx:walk-tree (fun object)
  (if (atom object)
      (funcall fun object)
    (direx:walk-tree fun (car object))
    (direx:walk-tree fun (cdr object))))

(defun direx:canonical-filename (filename)
  (expand-file-name filename))

(defun direx:canonical-dirname (dirname)
  (file-name-as-directory (expand-file-name dirname)))

(defun direx:directory-basename (dirname)
  (file-name-nondirectory
   (directory-file-name
    (direx:canonical-dirname dirname))))

(defun direx:directory-dirname (dirname)
  (file-name-directory
   (directory-file-name
    (direx:canonical-dirname dirname))))

(defun direx:directory-parents (filename)
  (cl-loop for current-dirname = (direx:canonical-filename filename) then parent-dirname
           for parent-dirname = (direx:directory-dirname current-dirname)
           while (and parent-dirname (< (length parent-dirname) (length current-dirname)))
           collect parent-dirname))

(defmacro direx:save-excursion-from-error (&rest body)
  (let ((point (cl-gensym "point"))
        (error (cl-gensym "error")))
    `(let ((,point (point)))
       (condition-case ,error
           (progn ,@body)
         (error
          (goto-char ,point)
          (signal (car ,error) (cdr ,error)))))))



;;; Trees

(defclass direx:tree ()
  ((name :initarg :name
         :accessor direx:tree-name)))

(defgeneric direx:tree-equals (x y)
  "Returns t if X is equal to Y.")

(defmethod direx:tree-equals (x y)
  (eq x y))

(defgeneric direx:tree-status (tree)
  "Returns a status of TREE in string.")

(defmethod direx:tree-status (tree)
  "")

(defclass direx:node (direx:tree)
  ())

(defgeneric direx:node-children (node)
  "Returns the children of the NODE.")

(defmethod direx:node-children (node)
  nil)

(defgeneric direx:node-contains (node descendant)
  "Returns t if the NODE has the DESCENDANT. The default
implementation of this generic function uses
`direx:node-children' to expand the descendants of the NODE
recursively and check if the DESCENDANT is a member of the
descendants. You may add a heuristic method for speed.")

(defmethod direx:node-contains (node descendant)
  (cl-loop for child in (direx:node-children node) thereis
           (or (direx:tree-equals child descendant)
               (and (cl-typep child 'direx:node)
                    (direx:node-contains child descendant)))))

(defclass direx:leaf (direx:tree)
  ())



;;; Tree Widgets

(defclass direx:item ()
  ((tree :initarg :tree
         :accessor direx:item-tree)
   (parent :initarg :parent
           :accessor direx:item-parent)
   (children :accessor direx:item-children)
   (face :initarg :face
         :accessor direx:item-face)
   (keymap :initarg :keymap
           :accessor direx:item-keymap)
   (overlay :accessor direx:item-overlay)
   (open :accessor direx:item-open)))

(defgeneric direx:generic-find-item (item not-this-window))

(defgeneric direx:generic-view-item (item not-this-window))

(defgeneric direx:generic-display-item (item))

(defgeneric direx:make-item (tree parent)
  "Returns a item of the TREE.")

(defmethod direx:make-item (tree parent)
  (make-instance 'direx:item :tree tree :parent parent))

(defun direx:make-item-children (item)
  (cl-loop for child-tree in (direx:node-children (direx:item-tree item))
           collect (direx:make-item child-tree item)))

(defun direx:item-equals (x y)
  (direx:tree-equals (direx:item-tree x) (direx:item-tree y)))

(defun direx:item-name (item)
  (direx:tree-name (direx:item-tree item)))

(defun direx:item-leaf-p (item)
  (cl-typep (direx:item-tree item) 'direx:leaf))

(defun direx:item-node-p (item)
  (cl-typep (direx:item-tree item) 'direx:node))

(defun direx:item-depth (item)
  (direx:aif (direx:item-parent item)
      (1+ (direx:item-depth it))
    0))

(defun direx:item-start (item)
  (overlay-start (direx:item-overlay item)))

(defun direx:item-end (item)
  (let ((children (direx:item-children item)))
    (if children
        (direx:item-end (car (last children)))
      (overlay-end (direx:item-overlay item)))))

(defun direx:item-root (item)
  (direx:aif (direx:item-parent item)
      (direx:item-root it)
    item))

(defun direx:item-buffer (item)
  (overlay-buffer (direx:item-overlay item)))

;; Rendering

(defun direx:item-icon-part-offset (item)
  (* (direx:item-depth item) (length direx:open-icon)))

(defun direx:item-name-part-offset (item)
  (+ (direx:item-icon-part-offset item) (length direx:open-icon)))

(defun direx:item-render-indent-part (item)
  (make-string (direx:item-icon-part-offset item) ? ))

(defun direx:item-render-icon-part (item)
  (if (direx:item-leaf-p item)
      direx:leaf-icon
    direx:closed-icon))

(defun direx:item-render-name-part (item)
  (propertize (direx:item-name item)
              'face (direx:item-face item)
              'mouse-face 'hightlight
              'help-echo "mouse-1: toggle or find this node
mouse-2: find this node in other window"))

(defun direx:item-render (item)
  (concat (direx:item-render-indent-part item)
          (direx:item-render-icon-part item)
          (direx:item-render-name-part item)
          "\n"))

(defun direx:item-make-overlay (item start end)
  (let ((overlay (make-overlay start end nil t nil)))
    (overlay-put overlay 'direx:item item)
    (overlay-put overlay 'keymap (direx:item-keymap item))
    (setf (direx:item-overlay item) overlay)
    overlay))

(defun direx:item-insert (item)
  (let ((start (point))
        (buffer-read-only nil))
    (insert (direx:item-render item))
    (direx:item-make-overlay item start (point))
    item))

(defun direx:item-insert-children (item)
  (let ((children (direx:make-item-children item)))
    (setf (direx:item-children item) children)
    (save-excursion
      (goto-char (overlay-end (direx:item-overlay item)))
      (dolist (child children)
        (direx:item-insert child)))))

(defun direx:item-ensure-children (item)
  (unless (direx:item-children item)
    (direx:item-insert-children item)))

(cl-defun direx:item-delete (item)
  (let* ((overlay (direx:item-overlay item))
         (start (overlay-start overlay))
         (end (overlay-end overlay))
         (buffer-read-only nil))
    (delete-region start end)
    (delete-overlay overlay)))

(defun direx:item-delete-recursively (item)
  (direx:item-delete item)
  (unless (direx:item-leaf-p item)
    (dolist (child (direx:item-children item))
      (direx:item-delete-recursively child))))

(defun direx:item-change-icon (item new-icon)
  (let ((buffer-read-only nil))
    (save-excursion
      ;; Insert the icon carefully with consideration of the
      ;; front-advance overlay.
      (goto-char (+ (direx:item-start item)
                    (direx:item-name-part-offset item)))
      (insert new-icon)
      ;; Then delete the icon.
      (goto-char (+ (line-beginning-position)
                    (direx:item-icon-part-offset item)))
      (delete-char (length new-icon)))))

(defun direx:item-visible-p (item)
  (not (overlay-get (direx:item-overlay item) 'invisible)))

(defun direx:item-show (item)
  (overlay-put (direx:item-overlay item) 'invisible nil))

(defun direx:item-hide (item)
  (overlay-put (direx:item-overlay item) 'invisible t))

(defun direx:item-show-children (item)
  (when (and (not (direx:item-leaf-p item))
             (direx:item-open item))
    (dolist (child (direx:item-children item))
      (direx:item-show child)
      (direx:item-show-children child))))

(defun direx:item-hide-children (item)
  (unless (direx:item-leaf-p item)
    (dolist (child (direx:item-children item))
      (direx:item-hide child)
      (direx:item-hide-children child))))

(defun direx:item-expand (item)
  (unless (direx:item-leaf-p item)
    (setf (direx:item-open item) t)
    (direx:item-ensure-children item)
    (direx:item-show-children item)
    (direx:item-change-icon item direx:open-icon)))

(defun direx:item-ensure-open (item)
  (unless (direx:item-open item)
    (direx:item-expand item)))

(defun direx:item-expand-recursively (item)
  (direx:item-expand item)
  (dolist (child (direx:item-children item))
    (direx:item-expand-recursively child)))

(defun direx:item-collapse (item)
  (unless (direx:item-leaf-p item)
    (setf (direx:item-open item) nil)
    (direx:item-hide-children item)
    (direx:item-change-icon item direx:closed-icon)))

(defun direx:item-ensure-closed (item)
  (when (direx:item-open item)
    (direx:item-collapse item)))

(defun direx:item-toggle (item)
  (if (direx:item-open item)
      (direx:item-collapse item)
    (direx:item-expand item)))

(defmethod direx:item-refresh ((item direx:item))
  (when (and (not (direx:item-leaf-p item))
             (direx:item-children item))
    (cl-loop with point = (overlay-end (direx:item-overlay item))
             with old-children = (direx:item-children item)
             for new-child in (direx:make-item-children item)
             for old-child = (cl-find-if (direx:apply-partially
                                          'direx:item-equals new-child)
                                         old-children)
             if old-child
             do (setq new-child old-child
                      old-children (delq old-child old-children))
             else
             do (save-excursion
                  (goto-char point)
                  (direx:item-insert new-child))
             do (setq point (direx:item-end new-child))
             collect new-child into new-children
             finally
             (dolist (old-child old-children)
               (direx:item-delete-recursively old-child))
             (setf (direx:item-children item) new-children))))

(defun direx:item-refresh-recursively (item)
  (direx:item-refresh item)
  (dolist (child (direx:item-children item))
    (direx:item-refresh-recursively child)))

(cl-defun direx:item-refresh-parent (item &key recursive)
  (direx:awhen (direx:item-parent item)
    (direx:item-refresh-recursively it)))



;;; File System

;; Trees

(defclass direx:file (direx:tree)
  ((full-name :initarg :full-name
              :accessor direx:file-full-name)))

(defmethod direx:tree-equals ((x direx:file) y)
  (or (eq x y)
      (and (cl-typep y 'direx:file)
           (equal (direx:file-full-name x) (direx:file-full-name y)))))

(defmethod direx:tree-status ((file direx:file))
  (let* ((filename (direx:file-full-name file))
         (dired-actual-switches "-la")
         (file-list (list (if (direx:regular-file-item-p file)
                              (file-name-nondirectory filename)
                            (direx:directory-basename filename))))
         (default-directory (direx:directory-dirname filename)))
    (with-temp-buffer
      (dired-insert-directory default-directory
                              dired-actual-switches
                              file-list)
      (goto-char (point-min))
      (buffer-substring-no-properties (point) (line-end-position)))))

(defclass direx:regular-file (direx:file direx:leaf)
  ())

(defun direx:make-regular-file (filename)
  (make-instance 'direx:regular-file
                 :name (file-name-nondirectory filename)
                 :full-name (direx:canonical-filename filename)))

(defclass direx:directory (direx:file direx:node)
  ())

(defun direx:make-directory (dirname)
  (let* ((dirname (direx:canonical-dirname dirname))
         (basename (direx:directory-basename dirname))
         (name (if (zerop (length basename)) dirname basename)))
    (make-instance 'direx:directory
                   :name name
                   :full-name dirname)))

(defmethod direx:node-children ((dir direx:directory))
  (cl-loop with dirname = (direx:file-full-name dir)
           for filename in (directory-files dirname t)
           for basename = (file-name-nondirectory filename)
           unless (string-match dired-trivial-filenames basename)
           if (file-directory-p filename)
           collect (direx:make-directory filename)
           else
           collect (direx:make-regular-file filename)))

(defmethod direx:node-contains ((dir direx:directory) file)
  (and (cl-typep file 'direx:file)
       (direx:starts-with (direx:file-full-name file)
                          (direx:file-full-name dir))))

;; Tree Items

(defclass direx:file-item (direx:item)
  ())

(defvar direx:file-keymap
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "R") 'direx:do-rename-file)
    (define-key map (kbd "C") 'direx:do-copy-files)
    (define-key map (kbd "D") 'direx:do-delete-files)
    (define-key map (kbd "+") 'direx:create-directory)
    (define-key map (kbd "M") 'direx:do-chmod-file)
    (define-key map (kbd "L") 'direx:do-load-file)
    (define-key map (kbd "B") 'direx:do-byte-compile-file)
    (define-key map (kbd "G") 'direx:do-chgrp)
    (define-key map (kbd "O") 'direx:do-chown)
    (define-key map (kbd "T") 'direx:do-touch)
    map))

(defun direx:do-rename-file ()
  (interactive)
  (let* ((item (direx:item-at-point!))
         (file (direx:item-tree item))
         (file-full-name (direx:file-full-name file))
         (dir-name (file-name-directory file-full-name))
         (file-name (file-name-nondirectory file-full-name))
         (to (read-file-name (format "Rename %s to " file-name) dir-name file-name)))
    (dired-rename-file file-full-name to nil)
    (direx:item-refresh-parent item)
    (direx:move-to-item-name-part item)))

(defun direx:do-copy-files ()
  (interactive)
  (let* ((item (direx:item-at-point!))
         (file (direx:item-tree item))
         (file-full-name (direx:file-full-name file))
         (dir-name (file-name-directory file-full-name))
         (file-name (file-name-nondirectory file-full-name))
         (to (read-directory-name (format "Copy %s to " file-name) dir-name file-name)))
    (dired-copy-file file-full-name to nil)
    (direx:item-refresh-parent item)
    (direx:move-to-item-name-part item)))

(defun direx:do-delete-files ()
  (interactive)
  (let* ((item (direx:item-at-point!))
         (file (direx:item-tree item))
         (file-full-name (direx:file-full-name file)))
    (when (yes-or-no-p (format "Delete %s" (direx:tree-name file)))
      (dired-delete-file file-full-name dired-recursive-deletes t)
      (direx:item-refresh-parent item)
      (direx:move-to-item-name-part item)
      (dired-clean-up-after-deletion file-full-name))))

(defun direx:create-directory ()
  (interactive)
  (let* ((item (direx:item-at-point!))
         (file (direx:item-tree item))
         (parent-dir
          (if (cl-typep file 'direx:directory)
              (direx:file-full-name file)
            (direx:directory-dirname
             (direx:file-full-name file))))
         (dir (read-directory-name "Create directory: " parent-dir)))
    (when (file-exists-p dir)
      (error "Can't create directory %s: file exists" dir))
    (make-directory dir t)
    (direx:item-refresh-parent item)
    (direx:move-to-item-name-part item)))

(defun direx:do-chmod-file ()
  (interactive)
  (let* ((item (direx:item-at-point!))
         (file (direx:item-tree item))
         (filename (file-name-nondirectory (direx:file-full-name file)))
         (orig-modes (file-modes filename))
         (modes (read-string (format "Change mode of %s to: " filename)))
         (new-modes (if (string-match "^[0-7]+" modes)
                        (string-to-number modes 8)
                      (file-modes-symbolic-to-number modes orig-modes))))
    (set-file-modes filename new-modes)))

(defun direx:do-load-file ()
  (interactive)
  (let* ((item (direx:item-at-point!))
         (file (direx:item-tree item))
         (filename (direx:file-full-name file))
         (failure nil))
    (when (y-or-n-p (format "Load %s?" (file-name-nondirectory filename)))
      (condition-case err
          (load filename nil nil t)
        (error (setq failure err)))
      (when failure
        (message "Load error for %s:\n%s\n" file failure)))))

(defun direx:do-byte-compile-file ()
  (interactive)
  (let* ((item (direx:item-at-point!))
         (file (direx:item-tree item))
         (filename (direx:file-full-name file))
         (dest-file (byte-compile-dest-file filename))
         (failure nil))
    (when (y-or-n-p (format "Byte-Compile %s?" (file-name-nondirectory filename)))
      (condition-case err
          (save-excursion (byte-compile-file filename))
        (error (setq failure err)))
      (or (file-exists-p dest-file)
          (setq failure t))
      (if failure
          (error "Byte compile error for %s\n%s\n" filename failure)
        (progn
          (direx:item-refresh-parent item)
          (direx:next-item))))))

(defun direx:exec-command (program args)
  (unless (executable-find program)
    (error "Command '%s' not found" program))
  (with-temp-buffer
    (unless (zerop (apply 'call-process program nil t nil args))
      (message "%s" (replace-regexp-in-string "[\r\n]+\\'" ""
                                              (buffer-string))))))

(defun direx:do-chxxx (program attr filename)
  (let* ((prompt (format "Change %s of %s to: "
                         attr (file-name-nondirectory filename)))
         (new-attr (read-string prompt))
         (args (list new-attr filename)))
    (direx:exec-command program args)))

(defun direx:do-chgrp ()
  (interactive)
  (let* ((item (direx:item-at-point!))
         (file (direx:item-tree item))
         (filename (direx:file-full-name file)))
    (direx:do-chxxx "chgrp" "Group" filename)))

(defun direx:do-chown ()
  (interactive)
  (let* ((item (direx:item-at-point!))
         (file (direx:item-tree item))
         (filename (direx:file-full-name file)))
    (direx:do-chxxx "chown" "Owner" filename)))

(defun direx:do-touch ()
  (interactive)
  (let* ((item (direx:item-at-point!))
         (file (direx:item-tree item))
         (filename (direx:file-full-name file))
         (default (format-time-string "%Y%m%d%H%M.%S"
                                      (nth 5 (file-attributes filename))))
         (prompt (format "Change Timestamp of %s to (default now): "
                         (file-name-nondirectory filename)))
         (new-time (read-string prompt))
         (args (if (string= new-time "")
                   (list filename)
                 (list "-t" new-time filename))))
    (direx:exec-command "touch" args)))

(defclass direx:regular-file-item (direx:file-item)
  ())

(defmethod direx:generic-find-item ((item direx:regular-file-item) not-this-window)
  (let ((filename (direx:file-full-name (direx:item-tree item))))
    (if not-this-window
        (find-file-other-window filename)
      (find-file filename))))

(defmethod direx:generic-view-item ((item direx:regular-file-item) not-this-window)
  (let ((filename (direx:file-full-name (direx:item-tree item))))
    (if not-this-window
        (view-file-other-window filename)
      (view-file filename))))

(defmethod direx:generic-display-item ((item direx:regular-file-item))
  (let ((filename (direx:file-full-name (direx:item-tree item))))
    (display-buffer (find-file-noselect filename))))

(defmethod direx:make-item ((file direx:regular-file) parent)
  (let* ((filename (direx:file-full-name file))
         (face (when (string-match direx:ignored-files-regexp filename)
                 'dired-ignored)))
    (make-instance 'direx:regular-file-item
                   :tree file
                   :parent parent
                   :face face
                   :keymap direx:file-keymap)))

(defclass direx:directory-item (direx:file-item)
  ())

(defmethod direx:generic-find-item ((item direx:directory-item) not-this-window)
  (let ((dirname (direx:file-full-name (direx:item-tree item))))
    (if not-this-window
        (dired-other-window dirname)
      (dired dirname))))

(defmethod direx:generic-display-item ((item direx:directory-item))
  (let ((dirname (direx:file-full-name (direx:item-tree item))))
    (display-buffer (dired-noselect dirname))))

(defmethod direx:make-item ((dir direx:directory) parent)
  (make-instance 'direx:directory-item
                 :tree dir
                 :parent parent
                 :face 'dired-directory
                 :keymap direx:file-keymap))



;;; Tree Buffers

(defvar direx:root-item nil)

(defun direx:item-at-point (&optional point)
  (get-char-property (or point (point)) 'direx:item))

(defun direx:item-at-point! (&optional point)
  (or (direx:item-at-point point)
      (error "No item at point")))

(defun direx:item-at-event (event)
  (direx:awhen (posn-window (event-end event))
    (with-selected-window it
      (direx:item-at-point (posn-point (event-end event))))))

(defun direx:find-root-item-if (predicate)
  (cl-find-if predicate
              (mapcar (direx:apply-partially 'buffer-local-value 'direx:root-item)
                      (direx:buffer-list))))

(defun direx:find-root-item-for-root (root)
  (direx:find-root-item-if
   (lambda (item) (direx:tree-equals root (direx:item-tree item)))))

(defun direx:buffer-live-p (buffer)
  (and (buffer-live-p buffer)
       (eq (buffer-local-value 'major-mode buffer) 'direx:direx-mode)))

(defun direx:buffer-list ()
  (cl-remove-if-not 'direx:buffer-live-p (buffer-list)))

(defgeneric direx:make-buffer (root))

(defmethod direx:make-buffer ((root direx:tree))
  (let ((buffer (generate-new-buffer (direx:tree-name root))))
    (with-current-buffer buffer
      (direx:direx-mode)
      (setq default-directory (direx:file-full-name root))
      (setq-local revert-buffer-function 'direx:revert-buffer))
    buffer))

(defmethod direx:make-buffer ((dir direx:directory))
  (with-current-buffer (call-next-method)
    (set (make-local-variable 'dired-directory)
         (direx:file-full-name dir))
    (current-buffer)))

(defun direx:revert-buffer (ignore-auto noconfirm)
  (direx:refresh-whole-tree))

(defun direx:make-buffer-for-root (root)
  (let ((buffer (direx:make-buffer root)))
    (direx:add-root-into-buffer root buffer)
    buffer))

(defun direx:ensure-buffer-for-root (root)
  (or (direx:find-buffer-for-root root)
      (direx:make-buffer-for-root root)))

(defun direx:find-buffer-for-root (root)
  (direx:awhen (direx:find-root-item-for-root root)
    (direx:item-buffer it)))

(defun direx:add-root-into-buffer (root buffer &optional noexpand)
  (with-current-buffer buffer
    (let ((root-item (direx:make-item root nil))
          (buffer-read-only nil))
      (goto-char (point-max))
      (direx:item-insert root-item)
      (setq direx:root-item root-item)
      (unless noexpand
        (direx:item-expand root-item)
        (direx:move-to-item-name-part root-item)))))

(defun direx:goto-item-for-tree-1 (tree)
  (goto-char (point-min))
  (cl-loop for item = (direx:item-at-point)
           for item-tree = (and item (direx:item-tree item))
           while item-tree
           if (direx:tree-equals item-tree tree)
           return (direx:move-to-item-name-part item)
           else if (and (cl-typep item-tree 'direx:node)
                        (direx:node-contains item-tree tree))
           do (direx:down-item)
           else
           do (direx:next-sibling-item)
           finally (error "Item not found")))

(defun direx:goto-item-for-tree (tree)
  (ignore-errors
    (direx:save-excursion-from-error
     (direx:goto-item-for-tree-1 tree))))



;;; Major Mode

(defun direx:ensure-item-visible (item))

(defun direx:move-to-item-name-part (&optional item)
  (unless item
    (setq item (direx:item-at-point)))
  (when (and item (direx:item-start item))
    (goto-char (+ (direx:item-start item)
                  (direx:item-name-part-offset item)))
    (direx:ensure-item-visible item)))

(defun direx:next-item (&optional arg)
  (interactive "p")
  (cl-loop unless (zerop (forward-line arg))
           do (error (if (cl-plusp arg) "End of buffer" "Beginning of buffer"))
           for item = (direx:item-at-point!)
           when (direx:item-visible-p item)
           return (direx:move-to-item-name-part item)))

(defun direx:previous-item (&optional arg)
  (interactive "p")
  (direx:next-item (if (null arg) -1 (- arg))))

(defun direx:up-item-1 (item)
  (cl-loop with parent = (direx:item-parent item)
           while (and (zerop (forward-line -1))
                      (not (eq (direx:item-at-point) parent)))
           finally (direx:move-to-item-name-part)))

(defun direx:up-item ()
  (interactive)
  (direx:aif (direx:item-at-point)
      (direx:up-item-1 it)
    (goto-char (point-min))))

(defun direx:down-item ()
  (interactive)
  (direx:awhen (direx:item-at-point)
    (unless (direx:item-node-p it) (error "No children"))
    (direx:item-ensure-open it)
    (unless (direx:item-children it) (error "No children")))
  (direx:next-item))

(defun direx:next-sibling-item-1 (item arg)
  (cl-loop with parent = (direx:item-parent item)
           with siblings = (when parent (direx:item-children parent))
           with ordered-siblings = (if (cl-plusp arg) siblings (reverse siblings))
           with sibling = (cadr (memq item ordered-siblings))
           with point = (point)
           with item
           while (and sibling
                      (zerop (forward-line arg))
                      (setq item (direx:item-at-point)))
           if (eq item sibling)
           return (direx:move-to-item-name-part item)
           finally
           (goto-char point)
           (error "No sibling")))

(defun direx:next-sibling-item (&optional arg)
  (interactive "p")
  (setq arg (if (or (null arg) (> arg 0)) 1 -1))
  (direx:aif (direx:item-at-point)
      (direx:next-sibling-item-1 it arg)
    (direx:next-item arg)))

(defun direx:previous-sibling-item (&optional arg)
  (interactive "p")
  (direx:next-sibling-item (if (or (null arg) (> arg 0)) -1 1)))

(defun direx:refresh-whole-tree (&optional item)
  (interactive)
  (setq item (or item (direx:item-at-point) direx:root-item))
  (direx:item-refresh-recursively (direx:item-root item))
  (direx:move-to-item-name-part item))

(defun direx:echo-item ()
  (interactive)
  (message "%s" (direx:tree-status (direx:item-tree (direx:item-at-point)))))

(defun direx:find-item (&optional item)
  (interactive)
  (setq item (or item (direx:item-at-point!)))
  (direx:generic-find-item item nil))

(defun direx:find-item-other-window (&optional item)
  (interactive)
  (setq item (or item (direx:item-at-point!)))
  (direx:generic-find-item item t))

(defun direx:view-item (&optional item)
  (interactive)
  (setq item (or item (direx:item-at-point!)))
  (direx:generic-view-item item nil))

(defun direx:view-item-other-window (&optional item)
  (interactive)
  (setq item (or item (direx:item-at-point!)))
  (direx:generic-view-item item t))

(defun direx:display-item (&optional item)
  "Open ITEM at point without changing focus."
  (interactive)
  (setq item (or item (direx:item-at-point!)))
  (direx:generic-display-item item))

(defun direx:maybe-find-item (&optional item)
  (interactive)
  (setq item (or item (direx:item-at-point!)))
  (if (direx:item-leaf-p item)
      (direx:find-item item)
    (direx:toggle-item item)))

(defun direx:expand-item (&optional item)
  (interactive)
  (setq item (or item (direx:item-at-point!)))
  (direx:item-expand item)
  (let ((children (direx:item-children item)))
    (when (and (= (length children) 1)
               (direx:item-node-p (car children)))
      ;; Also expands the sub directory
      (direx:expand-item (car children))))
  (direx:move-to-item-name-part item))

(defun direx:expand-item-recursively (&optional item)
  (interactive)
  (setq item (or item (direx:item-at-point!)))
  (direx:item-expand-recursively item)
  (direx:move-to-item-name-part item))

(defun direx:collapse-item (&optional item)
  (interactive)
  (setq item (or item (direx:item-at-point!)))
  (direx:item-collapse item)
  (direx:move-to-item-name-part item))

(defun direx:toggle-item (&optional item)
  (interactive)
  (setq item (or item (direx:item-at-point!)))
  (if (direx:item-open item)
      (direx:collapse-item item)
    (direx:expand-item item))
  (direx:move-to-item-name-part item))

(defun direx:mouse-1 (event)
  (interactive "e")
  (direx:awhen (direx:item-at-event event)
    (direx:maybe-find-item it)))

(defun direx:mouse-2 (event)
  (interactive "e")
  (direx:awhen (direx:item-at-event event)
    (direx:find-item-other-window it)))

(defvar direx:direx-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "n")           'direx:next-item)
    (define-key map (kbd "C-n")         'direx:next-item)
    (define-key map (kbd "<down>")      'direx:next-item)
    (define-key map (kbd "p")           'direx:previous-item)
    (define-key map (kbd "C-p")         'direx:previous-item)
    (define-key map (kbd "<up>")        'direx:previous-item)
    (define-key map (kbd "C-M-n")       'direx:next-sibling-item)
    (define-key map (kbd "C-M-<down>")  'direx:next-sibling-item)
    (define-key map (kbd "C-M-p")       'direx:previous-sibling-item)
    (define-key map (kbd "C-M-<up>")    'direx:previous-sibling-item)
    (define-key map (kbd "^")           'direx:up-item)
    (define-key map (kbd "C-M-u")       'direx:up-item)
    (define-key map (kbd "C-M-<left>")  'direx:up-item)
    (define-key map (kbd "C-M-d")       'direx:down-item)
    (define-key map (kbd "C-M-<right>") 'direx:up-item)
    (define-key map (kbd "e")           'direx:echo-item)
    (define-key map (kbd "f")           'direx:find-item)
    (define-key map (kbd "o")           'direx:find-item-other-window)
    (define-key map (kbd "v")           'direx:view-item)
    (define-key map (kbd "V")           'direx:view-item-other-window)
    (define-key map (kbd "C-o")         'direx:display-item)
    (define-key map (kbd "RET")         'direx:maybe-find-item)
    (define-key map (kbd "TAB")         'direx:toggle-item)
    (define-key map (kbd "i")           'direx:toggle-item)
    (define-key map (kbd "E")           'direx:expand-item-recursively)
    (define-key map (kbd "g")           'direx:refresh-whole-tree)
    (define-key map [mouse-1]           'direx:mouse-1)
    (define-key map [mouse-2]           'direx:mouse-2)
    map))

(define-derived-mode direx:direx-mode special-mode "Direx"
  ""
  (set (make-local-variable 'direx:root-item) nil)
  (setq buffer-read-only t
        truncate-lines t)
  (use-local-map direx:direx-mode-map))



;;; Directory

(defun direx:find-directory-noselect (dirname)
  (interactive "DDirex (directory): ")
  (direx:ensure-buffer-for-root (direx:make-directory dirname)))

(defun direx:find-directory (dirname)
  (interactive "DDirex (directory): ")
  (switch-to-buffer (direx:find-directory-noselect dirname)))

(defun direx:find-directory-other-window (dirname)
  (interactive "DDirex (directory): ")
  (switch-to-buffer-other-window (direx:find-directory-noselect dirname)))

(defun direx:find-directory-reuse-noselect (dirname)
  (interactive "DDirex (directory): ")
  (cl-loop for current-dirname = dirname then parent-dirname
           for parent-dirname in (direx:directory-parents dirname)
           for dir = (direx:make-directory current-dirname)
           for buffer = (direx:find-buffer-for-root dir)
           if buffer return buffer
           finally return (direx:find-directory-noselect dirname)))

(defun direx:find-directory-reuse (dirname)
  (interactive "DDirex (directory): ")
  (switch-to-buffer (direx:find-directory-reuse-noselect dirname)))

(defun direx:find-directory-reuse-other-window (dirname)
  (interactive "DDirex (directory): ")
  (switch-to-buffer-other-window (direx:find-directory-reuse-noselect dirname)))

(defun direx:maybe-goto-current-buffer-item (buffer)
  (let ((filename buffer-file-name)
        (dirname default-directory))
    (with-current-buffer buffer
      (cond (filename
             (direx:goto-item-for-tree (direx:make-regular-file filename)))
            (dirname
             (direx:goto-item-for-tree (direx:make-directory dirname)))))))

(defun direx:jump-to-directory-noselect ()
  (interactive)
  (let ((buffer (direx:find-directory-reuse-noselect default-directory)))
    (direx:maybe-goto-current-buffer-item buffer)
    buffer))

;;;###autoload
(defun direx:jump-to-directory ()
  (interactive)
  (switch-to-buffer (direx:jump-to-directory-noselect)))

;;;###autoload
(defun direx:jump-to-directory-other-window ()
  (interactive)
  (switch-to-buffer-other-window (direx:jump-to-directory-noselect)))

(provide 'direx)
;;; direx.el ends here
