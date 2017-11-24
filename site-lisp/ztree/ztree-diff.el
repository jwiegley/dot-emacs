;;; ztree-diff.el --- Text mode diff for directory trees -*- lexical-binding: t; -*-

;; Copyright (C) 2013-2016  Free Software Foundation, Inc.
;;
;; Author: Alexey Veretennikov <alexey.veretennikov@gmail.com>
;;
;; Created: 2013-11-11
;;
;; Keywords: files tools
;; URL: https://github.com/fourier/ztree
;; Compatibility: GNU Emacs 24.x
;;
;; This file is part of GNU Emacs.
;;
;; GNU Emacs is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.
;;
;; GNU Emacs is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.
;;
;;; Commentary:

;;; Code:
(require 'ztree-view)
(require 'ztree-diff-model)

(defconst ztree-diff-hidden-files-regexp "^\\."
  "Hidden files regexp.
By default all filest starting with dot `.', including . and ..")

(defface ztreep-diff-header-face
  '((((type tty pc) (class color)) :foreground "lightblue" :weight bold)
    (((background dark)) (:height 1.2 :foreground "lightblue" :weight bold))
    (t :height 1.2 :foreground "darkblue" :weight bold))
  "*Face used for the header in Ztree Diff buffer."
  :group 'Ztree-diff :group 'font-lock-highlighting-faces)
(defvar ztreep-diff-header-face 'ztreep-diff-header-face)

(defface ztreep-diff-header-small-face
  '((((type tty pc) (class color)) :foreground "lightblue" :weight bold)
    (((background dark)) (:foreground "lightblue" :weight bold))
    (t :weight bold :foreground "darkblue"))
  "*Face used for the header in Ztree Diff buffer."
  :group 'Ztree-diff :group 'font-lock-highlighting-faces)
(defvar ztreep-diff-header-small-face 'ztreep-diff-header-small-face)

(defface ztreep-diff-model-diff-face
  '((t                   (:foreground "red")))
  "*Face used for different files in Ztree-diff."
  :group 'Ztree-diff :group 'font-lock-highlighting-faces)
(defvar ztreep-diff-model-diff-face 'ztreep-diff-model-diff-face)

(defface ztreep-diff-model-add-face
  '((t                   (:foreground "blue")))
  "*Face used for added files in Ztree-diff."
  :group 'Ztree-diff :group 'font-lock-highlighting-faces)
(defvar ztreep-diff-model-add-face 'ztreep-diff-model-add-face)

(defface ztreep-diff-model-ignored-face
  '((((type tty pc) (class color) (min-colors 256)) :foreground "#2f2f2f")
    (((type tty pc) (class color) (min-colors 8))   :foreground "white")
    (t                   (:foreground "#7f7f7f" :strike-through t)))
  "*Face used for non-modified files in Ztree-diff."
  :group 'Ztree-diff :group 'font-lock-highlighting-faces)
(defvar ztreep-diff-model-ignored-face 'ztreep-diff-model-ignored-face)

(defface ztreep-diff-model-normal-face
  '((((type tty pc) (class color) (min-colors 8)) :foreground "white")
    (t                   (:foreground "#7f7f7f")))
  "*Face used for non-modified files in Ztree-diff."
  :group 'Ztree-diff :group 'font-lock-highlighting-faces)
(defvar ztreep-diff-model-normal-face 'ztreep-diff-model-normal-face)


(defvar-local ztree-diff-filter-list (list ztree-diff-hidden-files-regexp)
  "List of regexp file names to filter out.
By default paths starting with dot (like .git) are ignored")

(defvar-local ztree-diff-dirs-pair nil
  "Pair of the directories stored.  Used to perform the full rescan.")

(defvar-local ztree-diff-show-equal-files t
  "Show or not equal files/directories on both sides.")

(defvar-local ztree-diff-show-filtered-files nil
  "Show or not files from the filtered list.")

(defvar-local ztree-diff-show-right-orphan-files t
  "Show or not orphan files/directories on right side.")

(defvar-local ztree-diff-show-left-orphan-files t
  "Show or not orphan files/directories on left side.")

(defvar-local ztree-diff-wait-message nil
  "Message showing while constructing the diff tree.")

(defvar-local ztree-diff-ediff-previous-window-configuration nil
  "Window configuration prior to calling `ediff'.")

;;;###autoload
(define-minor-mode ztreediff-mode
  "A minor mode for displaying the difference of the directory trees in text mode."
  ;; initial value
  nil
  ;; modeline name
  " Diff"
  ;; The minor mode keymap
  `(
    (,(kbd "C") . ztree-diff-copy)
    (,(kbd "h") . ztree-diff-toggle-show-equal-files)
    (,(kbd "H") . ztree-diff-toggle-show-filtered-files)
    (,(kbd "D") . ztree-diff-delete-file)
    (,(kbd "v") . ztree-diff-view-file)
    (,(kbd "d") . ztree-diff-simple-diff-files)
    (,(kbd "r") . ztree-diff-partial-rescan)
    (,(kbd "R") . ztree-diff-full-rescan)
    ([f5] . ztree-diff-full-rescan)))


(defun ztree-diff-node-face (node)
  "Return the face for the NODE depending on diff status."
  (let ((diff (ztree-diff-node-different node)))
    (cond ((eq diff 'ignore) ztreep-diff-model-ignored-face)
          ((eq diff 'diff) ztreep-diff-model-diff-face)
          ((eq diff 'new)  ztreep-diff-model-add-face)
          ((eq diff 'same) ztreep-diff-model-normal-face))))

(defun ztree-diff-insert-buffer-header ()
  "Insert the header to the ztree buffer."
  (ztree-insert-with-face "Differences tree" ztreep-diff-header-face)
  (insert "\n")
  (when ztree-diff-dirs-pair
    (ztree-insert-with-face (concat "Left:  " (car ztree-diff-dirs-pair))
                            ztreep-diff-header-small-face)
    (insert "\n")
    (ztree-insert-with-face (concat "Right: " (cdr ztree-diff-dirs-pair))
                            ztreep-diff-header-small-face)
    (insert "\n"))
  (ztree-insert-with-face "Legend:" ztreep-diff-header-small-face)
  (insert "\n")
  (ztree-insert-with-face " Normal file " ztreep-diff-model-normal-face)
  (ztree-insert-with-face "- same on both sides" ztreep-diff-header-small-face)
  (insert "\n")
  (ztree-insert-with-face " Orphan file " ztreep-diff-model-add-face)
  (ztree-insert-with-face "- does not exist on other side" ztreep-diff-header-small-face)
  (insert "\n")
  (ztree-insert-with-face " Mismatch file " ztreep-diff-model-diff-face)
  (ztree-insert-with-face "- different from other side" ztreep-diff-header-small-face)
  (insert "\n ")
  (ztree-insert-with-face "Ignored file" ztreep-diff-model-ignored-face)
  (ztree-insert-with-face " - ignored from comparison" ztreep-diff-header-small-face)
  (insert "\n")

  (ztree-insert-with-face "==============" ztreep-diff-header-face)
  (insert "\n"))

(defun ztree-diff-full-rescan ()
  "Force full rescan of the directory trees."
  (interactive)
  (when (and ztree-diff-dirs-pair
             (yes-or-no-p (format "Force full rescan?")))
    (ztree-diff (car ztree-diff-dirs-pair) (cdr ztree-diff-dirs-pair))))



(defun ztree-diff-existing-common (node)
  "Return the NODE if both left and right sides exist."
  (let ((left (ztree-diff-node-left-path node))
        (right (ztree-diff-node-right-path node)))
    (if (and left right
             (file-exists-p left)
             (file-exists-p right))
        node
      nil)))

(defun ztree-diff-existing-common-parent (node)
  "Return the first node in up in hierarchy of the NODE which has both sides."
  (let ((common (ztree-diff-existing-common node)))
    (if common
        common
      (ztree-diff-existing-common-parent (ztree-diff-node-parent node)))))

(defun ztree-diff-do-partial-rescan (node)
  "Partly rescan the NODE."
  (let* ((common (ztree-diff-existing-common-parent node))
         (parent (ztree-diff-node-parent common)))
    (if (not parent)
        (when ztree-diff-dirs-pair
          (ztree-diff (car ztree-diff-dirs-pair) (cdr ztree-diff-dirs-pair)))
      (ztree-diff-update-wait-message
           (concat "Updating " (ztree-diff-node-short-name common) " ..."))
      (ztree-diff-model-partial-rescan common)
      (message "Done")
      (ztree-refresh-buffer (line-number-at-pos)))))


(defun ztree-diff-partial-rescan ()
  "Perform partial rescan on the current node."
  (interactive)
  (let ((found (ztree-find-node-at-point)))
    (when found
      (ztree-diff-do-partial-rescan (car found)))))


(defun ztree-diff-simple-diff (node)
  "Create a simple diff buffer for files from left and right panels.
Argument NODE node containing paths to files to call a diff on."
  (let* ((node-left (ztree-diff-node-left-path node))
         (node-right (ztree-diff-node-right-path node)))
    (when (and
           node-left
           node-right
           (not (file-directory-p node-left)))
      ;; show the diff window on the bottom
      ;; to not to crush tree appearance
      (let ((split-width-threshold nil))
        (diff node-left node-right)))))


(defun ztree-diff-simple-diff-files ()
  "Create a simple diff buffer for files from left and right panels."
  (interactive)
  (let ((found (ztree-find-node-at-point)))
    (when found
      (let ((node (car found)))
        (ztree-diff-simple-diff node)))))

(defun ztree-diff-ediff-before-setup-hook-function ()
  "Hook function for `ediff-before-setup-hook'.

See the Info node `(ediff) hooks'.

This hook function removes itself."
  (setq ztree-diff--ediff-previous-window-configuration (current-window-configuration))
  (remove-hook 'ediff-before-setup-hook #'ztree-diff-ediff-before-setup-hook-function))

(defun ztree-diff-ediff-quit-hook-function ()
  "Hook function for `ediff-quit-hook'.

See the Info node `(ediff) hooks'.

This hook function removes itself."
  (set-window-configuration ztree-diff--ediff-previous-window-configuration)
  (remove-hook 'ediff-quit-hook #'ztree-diff-ediff-quit-hook-function))

(defun ztree-diff-ediff (file-a file-b &optional startup-hooks)
  "Ediff that cleans up after itself.

Ediff-related buffers are killed and the pre-Ediff window
configuration is restored."
  (add-hook 'ediff-before-setup-hook #'ztree-diff-ediff-before-setup-hook-function)
  (add-hook 'ediff-quit-hook #'ztree-diff-ediff-quit-hook-function t)
  (ediff file-a file-b startup-hooks))

(defun ztree-diff-node-action (node hard)
  "Perform action on NODE:
1 if both left and right sides present:
   1.1 if they are differend
      1.1.1 if HARD ediff
      1.1.2 simple diff otherwiste
   1.2 if they are the same - view left
2 if left or right present - view left or rigth"
  (let ((left (ztree-diff-node-left-path node))
        (right (ztree-diff-node-right-path node))
        ;; FIXME: The GNU convention is to only use "path" for lists of
        ;; directories as in load-path.
        (open-f #'(lambda (path) (if hard (find-file path)
                                  (let ((split-width-threshold nil))
                                    (view-file-other-window path))))))
    (cond ((and left right)
           (if (eql (ztree-diff-node-different node) 'same)
               (funcall open-f left)
             (if hard
                 (ztree-diff-ediff left right)
               (ztree-diff-simple-diff node))))
          (left (funcall open-f left))
          (right (funcall open-f right))
          (t nil))))



(defun ztree-diff-copy-file (node source-path destination-path copy-to-right)
  "Update the NODE status and copy the file.
File copied from SOURCE-PATH to DESTINATION-PATH.
COPY-TO-RIGHT specifies which side of the NODE to update."
  (let ((target-path (concat
                      (file-name-as-directory destination-path)
                      (file-name-nondirectory
                       (directory-file-name source-path)))))
    (let ((err (condition-case error-trap
                   (progn
                     ;; don't ask for overwrite
                     ;; keep time stamp
                     (copy-file source-path target-path t t)
                     nil)
                 (error error-trap))))
      ;; error message if failed
      (if err (message (concat "Error: " (nth 2 err)))
        ;; otherwise:
        ;; assuming all went ok when left and right nodes are the same
        ;; set both as not different if they were not ignored
        (unless (eq (ztree-diff-node-different node) 'ignore)
          (setf (ztree-diff-node-different node) 'same))
        ;; update left/right paths
        (if copy-to-right
            (setf (ztree-diff-node-right-path node) target-path)
          (setf (ztree-diff-node-left-path node) target-path))
        (ztree-diff-node-update-all-parents-diff node)
        (ztree-refresh-buffer (line-number-at-pos))))))


(defun ztree-diff-copy-dir (node source-path destination-path copy-to-right)
  "Update the NODE status and copy the directory.
Directory copied from SOURCE-PATH to DESTINATION-PATH.
COPY-TO-RIGHT specifies which side of the NODE to update."
  (let* ((src-path (file-name-as-directory source-path))
         (target-path (file-name-as-directory destination-path))
         (target-full-path (concat
                            target-path
                            (file-name-nondirectory
                             (directory-file-name source-path)))))
    (let ((err (condition-case error-trap
                   (progn
                     ;; keep time stamp
                     ;; ask for overwrite
                     (copy-directory src-path target-path t t)
                     nil)
                 (error error-trap))))
      ;; error message if failed
      (if err
          (progn
            (message (concat "Error: " (nth 1 err)))
            ;; and do rescan of the node
            (ztree-diff-do-partial-rescan node))
        ;; if everything is ok, update statuses
        (message target-full-path)
        (if copy-to-right
            (setf (ztree-diff-node-right-path node) target-full-path)
          (setf (ztree-diff-node-left-path node) target-full-path))
        (ztree-diff-update-wait-message
         (concat "Updating " (ztree-diff-node-short-name node) " ..."))
        ;; TODO: do not rescan the node. Use some logic like in delete
        (ztree-diff-model-update-node node)
        (message "Done.")
        (ztree-diff-node-update-all-parents-diff node)
        (ztree-refresh-buffer (line-number-at-pos))))))


(defun ztree-diff-copy ()
  "Copy the file under the cursor to other side."
  (interactive)
  (let ((found (ztree-find-node-at-point)))
    (when found
      (let* ((node (car found))
             (side (cdr found))
             (node-side (ztree-diff-node-side node))
             (copy-to-right t)           ; copy from left to right
             (node-left (ztree-diff-node-left-path node))
             (node-right (ztree-diff-node-right-path node))
             (source-path nil)
             (destination-path nil)
             (parent (ztree-diff-node-parent node)))
        (when parent                ; do not copy the root node
          ;; determine a side to copy from/to
          ;; algorithm:
          ;; 1) if both side are present, use the side
          ;;    variable
          (setq copy-to-right (if (eq node-side 'both)
                                  (eq side 'left)
                                ;; 2) if one of sides is absent, copy from
                                ;;    the side where the file is present
                                (eq node-side 'left)))
          ;; 3) in both cases determine if the destination
          ;;    directory is in place
          (setq source-path (if copy-to-right node-left node-right)
                destination-path (if copy-to-right
                                     (ztree-diff-node-right-path parent)
                                   (ztree-diff-node-left-path parent)))
          (when (and source-path destination-path
                     (yes-or-no-p (format "Copy [%s]%s to [%s]%s/ ?"
                                          (if copy-to-right "LEFT" "RIGHT")
                                          (ztree-diff-node-short-name node)
                                          (if copy-to-right "RIGHT" "LEFT")
                                          destination-path)))
            (if (file-directory-p source-path)
                (ztree-diff-copy-dir node
                                     source-path
                                     destination-path
                                     copy-to-right)
              (ztree-diff-copy-file node
                                    source-path
                                    destination-path
                                    copy-to-right))))))))

(defun ztree-diff-view-file ()
  "View file at point, depending on side."
  (interactive)
  (let ((found (ztree-find-node-at-point)))
    (when found
      (let* ((node (car found))
             (side (cdr found))
             (node-side (ztree-diff-node-side node))
             (node-left (ztree-diff-node-left-path node))
             (node-right (ztree-diff-node-right-path node)))
        (when (or (eq node-side 'both)
                  (eq side node-side))
          (cond ((and (eq side 'left)
                      node-left)
                 (view-file node-left))
                ((and (eq side 'right)
                      node-right)
                 (view-file node-right))))))))


(defun ztree-diff-delete-file ()
  "Delete the file under the cursor."
  (interactive)
  (let ((found (ztree-find-node-at-point)))
    (when found
      (let* ((node (car found))
             (side (cdr found))
             (node-side (ztree-diff-node-side node))
             (parent (ztree-diff-node-parent node))
             ;; algorithm for determining what to delete similar to copy:
             ;; 1. if the file is present on both sides, delete
             ;;    from the side currently selected
             ;; 2. if one of sides is absent, delete
             ;;    from the side where the file is present
             (delete-from-left
              (or (eql node-side 'left)
                  (and (eql node-side 'both)
                       (eql side 'left))))
             (remove-path (if delete-from-left
                              (ztree-diff-node-left-path node)
                            (ztree-diff-node-right-path node))))
        (when (and parent                    ; do not delete the root node
                   (yes-or-no-p (format "Delete the file [%s]%s ?"
                                        (if delete-from-left "LEFT" "RIGHT")
                                        remove-path)))
          (let* ((delete-command
                  (if (file-directory-p remove-path)
                      #'delete-directory
                    #'delete-file))
                 (children (ztree-diff-node-children parent))
                 (err
                  (condition-case error-trap
                      (progn
                        (funcall delete-command remove-path t)
                        nil)
                    (error error-trap))))
            (if err
                (progn
                  (message (concat "Error: " (nth 2 err)))
                  ;; when error happened while deleting the
                  ;; directory, rescan the node
                  ;; and update the parents with a new status
                  ;; of this node
                  (when (file-directory-p remove-path)
                    (ztree-diff-model-partial-rescan node)))
              ;; if everything ok
              ;; if was only on one side
              ;; remove the node from children
              (if (or (and (eql node-side 'left)
                           delete-from-left)
                      (and (eql node-side 'right)
                           (not delete-from-left)))
                  (setf (ztree-diff-node-children parent)
                        (ztree-filter
                         (lambda (x) (not (ztree-diff-node-equal x node)))
                         children))
                ;; otherwise update only one side
                (mapc (if delete-from-left
                          (lambda (x) (setf (ztree-diff-node-left-path x) nil))
                        (lambda (x) (setf (ztree-diff-node-right-path x) nil)))
                      (cons node (ztree-diff-node-children node)))
                ;; and update diff status
                ;; if was ignored keep the old status
                (unless (eql (ztree-diff-node-different node) 'ignore)
                  (setf (ztree-diff-node-different node) 'new))
                ;; finally update all children statuses
                (ztree-diff-node-update-diff-from-parent node)))
            (ztree-diff-node-update-all-parents-diff node)
            (ztree-refresh-buffer (line-number-at-pos))))))))



(defun ztree-diff-node-ignore-p (node)
  "Determine if the NODE is in filter list.
If the node is in the filter list it shall not be visible,
unless it is a parent node."
  (let ((name (ztree-diff-node-short-name node)))
    ;; ignore then
    ;; not a root and is in filter list
    (and (ztree-diff-node-parent node)
         (ztree-find ztree-diff-filter-list #'(lambda (rx) (string-match rx name))))))


(defun ztree-node-is-visible (node)
  "Determine if the NODE should be visible."
  (let ((diff (ztree-diff-node-different node)))
    ;; visible then
    ;; either it is a root. root have no parent
    (or (not (ztree-diff-node-parent node))    ; parent is always visible
        ;; or the files are different
        (eql diff 'diff)
        ;; or it is orphaned, but show orphaned files for now
        (and (eql diff 'new)
             (if (ztree-diff-node-left-path node)
                 ztree-diff-show-left-orphan-files
               ztree-diff-show-right-orphan-files))
        ;; or it is ignored but we show ignored for now
        (and (eql diff 'ignore)
             ztree-diff-show-filtered-files)
        ;; or they are same but we show same for now
        (and (eql diff 'same)
             ztree-diff-show-equal-files))))

(defmacro ztree-diff-define-toggle-show (what)
  (let ((funcsymbol (intern (concat "ztree-diff-toggle-show-" what "-files")))
        (variable (intern (concat "ztree-diff-show-" what "-files")))
        (fundesc (concat "Toggle visibility of the " what " files/directories")))
    `(defun ,funcsymbol ()
       ,fundesc
       (interactive)
       (setq ,variable (not ,variable))
       (message (concat (if ,variable "Show " "Hide ") ,what " files"))
       (ztree-refresh-buffer))))

(ztree-diff-define-toggle-show "equal")
(ztree-diff-define-toggle-show "filtered")
(ztree-diff-define-toggle-show "left-orphan")
(ztree-diff-define-toggle-show "right-orphan")

(defun ztree-diff-toggle-show-orphan-files ()
  "Toggle visibility of left and right orphan files."
  (interactive)
  (let ((show (not ztree-diff-show-left-orphan-files)))
    (setq ztree-diff-show-left-orphan-files show)
    (setq ztree-diff-show-right-orphan-files show)
    (message (concat (if show "Show" "Hide") " orphan files"))
    (ztree-refresh-buffer)))

(defun ztree-diff-update-wait-message (&optional msg)
  "Update the wait message MSG with one more `.' progress indication."
  (if msg
      (setq ztree-diff-wait-message msg)
    (when ztree-diff-wait-message
      (setq ztree-diff-wait-message (concat ztree-diff-wait-message "."))))
  (message ztree-diff-wait-message))

;;;###autoload
(defun ztree-diff (dir1 dir2)
  "Create an interactive buffer with the directory tree of the path given.
Argument DIR1 left directory.
Argument DIR2 right directory."
  (interactive "DLeft directory \nDRight directory ")
  (unless (and dir1 (file-directory-p dir1))
    (error "Path %s is not a directory" dir1))
  (unless (file-exists-p dir1)
    (error "Path %s does not exist" dir1))
  (unless (and dir2 (file-directory-p dir2))
    (error "Path %s is not a directory" dir2))
  (unless (file-exists-p dir2)
    (error "Path %s does not exist" dir2))
  (unless (ztree-same-host-p dir1 dir2)
    (error "Compared directories are not on the same host"))
  (let* ((model
          (ztree-diff-node-create nil dir1 dir2 nil))
         (buf-name (concat "*"
                           (ztree-diff-node-short-name model)
                           " <--> "
                           (ztree-diff-node-right-short-name model)
                           "*")))
    ;; after this command we are in a new buffer,
    ;; so all buffer-local vars are valid
    (ztree-view buf-name
                model
                'ztree-node-is-visible
                'ztree-diff-insert-buffer-header
                'ztree-diff-node-short-name-wrapper
                'ztree-diff-node-is-directory
                'ztree-diff-node-equal
                'ztree-diff-node-children
                'ztree-diff-node-face
                'ztree-diff-node-action
                'ztree-diff-node-side)
    (ztreediff-mode)
    (ztree-diff-model-set-ignore-fun #'ztree-diff-node-ignore-p)
    (ztree-diff-model-set-progress-fun #'ztree-diff-update-wait-message)
    (setq ztree-diff-dirs-pair (cons dir1 dir2))
    (ztree-diff-update-wait-message (concat "Comparing " dir1 " and " dir2 " ..."))
    (ztree-diff-node-recreate model)
    (message "Done.")

    (ztree-refresh-buffer)))






(provide 'ztree-diff)
;;; ztree-diff.el ends here
