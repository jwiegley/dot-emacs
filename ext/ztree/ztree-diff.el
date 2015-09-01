;;; ztree-diff.el --- Text mode diff for directory trees

;; Copyright (C) 2013 Alexey Veretennikov
;;
;; Author: Alexey Veretennikov <alexey dot veretennikov at gmail dot com>
;; Created: 2013-11-1l
;; Version: 1.0.0
;; Keywords: files
;; URL: https://github.com/fourier/ztree
;; Compatibility: GNU Emacs GNU Emacs 24.x
;;
;; This file is NOT part of GNU Emacs.
;;
;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License
;; as published by the Free Software Foundation; either version 2
;; of the License, or (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.
;;
;;; Commentary:

;;; Code:
(require 'ztree-view)
(require 'ztree-diff-model)

(defconst ztree-diff-hidden-files-regexp "^\\."
  "Hidden files regexp. By default all filest starting with dot '.',
including . and ..")

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

(defface ztreep-diff-model-normal-face
  '((t                   (:foreground "#7f7f7f")))
  "*Face used for non-modified files in Ztree-diff."
  :group 'Ztree-diff :group 'font-lock-highlighting-faces)
(defvar ztreep-diff-model-normal-face 'ztreep-diff-model-normal-face)


(defvar ztree-diff-filter-list (list ztree-diff-hidden-files-regexp)
  "List of regexp file names to filter out. By default paths starting with
dot (like .git) are ignored")
(make-variable-buffer-local 'ztree-diff-filter-list)

(defvar ztree-diff-dirs-pair nil
  "Pair of the directories stored. Used to perform the full rescan")
(make-variable-buffer-local 'ztree-diff-dirs-pair)

(defvar ztree-diff-show-equal-files t
  "Show or not equal files/directories on both sides")
(make-variable-buffer-local 'ztree-diff-show-equal-files)

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
    (,(kbd "D") . ztree-diff-delete-file)
    (,(kbd "v") . ztree-diff-view-file)
    (,(kbd "d") . ztree-diff-simple-diff-files)
    (,(kbd "r") . ztree-diff-partial-rescan)
    ([f5] . ztree-diff-full-rescan)))


(defun ztree-diff-node-face (node)
  (let ((diff (ztree-diff-node-different node)))
    (cond ((eq diff 'diff) ztreep-diff-model-diff-face)
          ((eq diff 'new)  ztreep-diff-model-add-face)
          (t ztreep-diff-model-normal-face))))  

(defun ztree-diff-insert-buffer-header ()
  (insert-with-face "Differences tree" ztreep-diff-header-face)
  (newline-and-begin)
  (when ztree-diff-dirs-pair
    (insert-with-face (concat "Left:  " (car ztree-diff-dirs-pair))
                      ztreep-diff-header-small-face)
    (newline-and-begin)
    (insert-with-face (concat "Right: " (cdr ztree-diff-dirs-pair))
                      ztreep-diff-header-small-face)
    (newline-and-begin))
  (insert-with-face "Legend:" ztreep-diff-header-small-face)
  (newline-and-begin)
  (insert-with-face " Normal file " ztreep-diff-model-normal-face)
  (insert-with-face "- same on both sides" ztreep-diff-header-small-face)
  (newline-and-begin)
  (insert-with-face " Orphan file " ztreep-diff-model-add-face)
  (insert-with-face "- does not exist on other side" ztreep-diff-header-small-face)
  (newline-and-begin)
  (insert-with-face " Mismatch file " ztreep-diff-model-diff-face)
  (insert-with-face "- different from other side" ztreep-diff-header-small-face)
  (newline-and-begin)
  (insert-with-face "==============" ztreep-diff-header-face)
  (newline-and-begin))

(defun ztree-diff-full-rescan ()
  "Forces full rescan of the directory trees"
  (interactive)
  (when (and ztree-diff-dirs-pair
             (yes-or-no-p (format "Force full rescan?")))
    (ztree-diff (car ztree-diff-dirs-pair) (cdr ztree-diff-dirs-pair))))



(defun ztree-diff-existing-common (node)
  (let ((left (ztree-diff-node-left-path node))
        (right (ztree-diff-node-right-path node)))
    (if (and left right
             (file-exists-p left)
             (file-exists-p right))
        node
      nil)))
      
(defun ztree-diff-existing-common-parent (node)
  (let ((common (ztree-diff-existing-common node)))
    (if common
        common
      (ztree-diff-existing-common-parent (ztree-diff-node-parent node)))))

(defun ztree-diff-do-partial-rescan (node)
  (let* ((common (ztree-diff-existing-common-parent node))
         (parent (ztree-diff-node-parent common)))
    (if (not parent)
        (when ztree-diff-dirs-pair
          (ztree-diff (car ztree-diff-dirs-pair) (cdr ztree-diff-dirs-pair)))
      (progn
        (ztree-diff-model-partial-rescan common)
        (ztree-diff-node-update-all-parents-diff node)
        (ztree-refresh-buffer (line-number-at-pos))))))
  

(defun ztree-diff-partial-rescan ()
  "Performs partial rescan on the current node"
  (interactive)
  (let ((found (ztree-find-node-at-point)))
    (when found
      (ztree-diff-do-partial-rescan (car found)))))
  

(defun ztree-diff-simple-diff (node)
  "Create a simple diff buffer for files from left and right panels"
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
  "Create a simple diff buffer for files from left and right panels"
  (interactive)
  (let ((found (ztree-find-node-at-point)))
    (when found
      (let ((node (car found)))
        (ztree-diff-simple-diff node)))))

(defun ztree-diff-node-action (node hard)
  "Perform action on node:
1 if both left and right sides present:
   1.1 if they are differend
      1.1.1 if hard ediff
      1.1.2 simple diff otherwiste
   1.2 if they are the same - view left
2 if left or right present - view left or rigth"
  (let ((left (ztree-diff-node-left-path node))
        (right (ztree-diff-node-right-path node))
        (open-f '(lambda (path) (if hard (find-file path)
                                  (let ((split-width-threshold nil))
                                    (view-file-other-window path))))))
    (cond ((and left right)
           (if (not (ztree-diff-node-different node))
               (funcall open-f left)
             (if hard
                 (ediff left right)
               (ztree-diff-simple-diff node))))
          (left (funcall open-f left))
          (right (funcall open-f right))
          (t nil))))
           


(defun ztree-diff-copy-file (node source-path destination-path copy-to-right)
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
        (progn              ; otherwise:
          ;; assuming all went ok when left and right nodes are the same
          ;; set both as not different
          (ztree-diff-node-set-different node nil)
          ;; update left/right paths
          (if copy-to-right
              (ztree-diff-node-set-right-path node target-path)
            (ztree-diff-node-set-left-path node target-path))
          (ztree-diff-node-update-all-parents-diff node)
          (ztree-refresh-buffer (line-number-at-pos)))))))


(defun ztree-diff-copy-dir (node source-path destination-path copy-to-right)
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
      (if err (message (concat "Error: " (nth 1 err)))
        (progn
          (message target-full-path)
          (if copy-to-right
              (ztree-diff-node-set-right-path node
                                              target-full-path)
            (ztree-diff-node-set-left-path node
                                           target-full-path))
          (ztree-diff-model-update-node node)
          (ztree-diff-node-update-all-parents-diff node)
          (ztree-refresh-buffer (line-number-at-pos)))))))


(defun ztree-diff-copy ()
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
  "View file at point, depending on side"
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
  (interactive)
  (let ((found (ztree-find-node-at-point)))
    (when found
      (let* ((node (car found))
             (side (cdr found))
             (node-side (ztree-diff-node-side node))
             (delete-from-left t)
             (remove-path nil)
             (parent (ztree-diff-node-parent node)))
        (when parent                    ; do not delete the root node
          ;; algorithm for determining what to delete similar to copy:
          ;; 1. if the file is present on both sides, delete
          ;;    from the side currently selected
          (setq delete-from-left (if (eq node-side 'both)
                                     (eq side 'left)
                                   ;; 2) if one of sides is absent, delete
                                   ;; from the side where the file is present
                                   (eq node-side 'left)))
          (setq remove-path (if delete-from-left
                                (ztree-diff-node-left-path node)
                              (ztree-diff-node-right-path node)))
          (when (yes-or-no-p (format "Delete the file [%s]%s ?"
                                     (if delete-from-left "LEFT" "RIGHT")
                                     remove-path))
            (let* ((delete-command 
                    (if (file-directory-p remove-path)
                        '(delete-directory remove-path t)
                      '(delete-file remove-path t)))
                   (children (ztree-diff-node-children parent))
                   (err 
                    (condition-case error-trap
                        (progn
                          (eval delete-command)
                          nil)
                      (error error-trap))))
              (if err (message (concat "Error: " (nth 2 err)))
                (progn 
                  (setq children (ztree-filter
                                  #'(lambda (x) (not (ztree-diff-node-equal x node)))
                                  children))
                  (ztree-diff-node-set-children parent children))
                (ztree-diff-node-update-all-parents-diff node)
                (ztree-refresh-buffer (line-number-at-pos))))))))))



(defun ztree-node-is-in-filter-list (node)
  "Determine if the node is in filter list (and therefore
apparently shall not be visible"
  (ztree-find ztree-diff-filter-list #'(lambda (rx) (string-match rx node))))


(defun ztree-node-is-visible (node)
  (and (ztree-diff-node-parent node)    ; parent is always visible
       (not (ztree-node-is-in-filter-list (ztree-diff-node-short-name node)))
       (or ztree-diff-show-equal-files
           (ztree-diff-node-different node))))

(defun ztree-diff-toggle-show-equal-files ()
  (interactive)
  (setq ztree-diff-show-equal-files (not ztree-diff-show-equal-files))
  (ztree-refresh-buffer))

;;;###autoload
(defun ztree-diff (dir1 dir2)
  "Creates an interactive buffer with the directory tree of the path given"
  (interactive "DLeft directory \nDRight directory ")
  (let* ((difference (ztree-diff-model-create dir1 dir2))
         (buf-name (concat "*"
                           (ztree-diff-node-short-name difference)
                           " <--> "
                           (ztree-diff-node-right-short-name difference)
                           "*")))
    (ztree-view buf-name
                difference
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
    (setq ztree-diff-dirs-pair (cons dir1 dir2))
    (ztree-refresh-buffer)))
          



(provide 'ztree-diff)
;;; ztree-diff.el ends here
