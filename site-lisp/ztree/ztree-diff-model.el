;;; ztree-diff-model.el --- diff model for directory trees

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

;; Diff model

;;; Code:
(require 'ztree-util)

(defvar ztree-diff-model-wait-message nil
  "Message showing while constructing the diff tree")
(make-variable-buffer-local 'ztree-diff-model-wait-message)


(defun ztree-diff-model-update-wait-message ()
  (when ztree-diff-model-wait-message
    (setq ztree-diff-model-wait-message (concat ztree-diff-model-wait-message "."))
    (message ztree-diff-model-wait-message)))



;; Create a record ztree-diff-node with defined fielsd and getters/setters
;; here:
;; parent - parent node
;; left-path is the full path on the left side of the diff window,
;; right-path is the full path of the right side,
;; short-name - is the file or directory name
;; children - list of nodes - files or directories if the node is a directory
;; different = {nil, 'new, 'diff} - means comparison status
(defrecord ztree-diff-node (parent left-path right-path short-name right-short-name children different))

(defun ztree-diff-node-to-string (node)
  (let* ((string-or-nil #'(lambda (x) (if x
                                          (cond ((stringp x) x)
                                                ((eq x 'new) "new")
                                                ((eq x 'diff) "different")
                                                (t (ztree-diff-node-short-name x)))
                                        "(empty)")))
         (children (ztree-diff-node-children node))
         (ch-str ""))
    (dolist (x children)
      (setq ch-str (concat ch-str "\n   * " (ztree-diff-node-short-name x))))
    (concat "Node: " (ztree-diff-node-short-name node)
            "\n"
            ;; " * Parent: " (let ((parent (ztree-diff-node-parent node)))
            ;;                 (if parent (ztree-diff-node-short-name parent) "nil"))
            " * Parent: " (funcall string-or-nil (ztree-diff-node-parent node))
            "\n"
            " * Left path: " (funcall string-or-nil (ztree-diff-node-left-path node))
            "\n"
            " * Right path: " (funcall string-or-nil (ztree-diff-node-right-path node))
            "\n"
            " * Children: " ch-str
            "\n")))
                          

(defun ztree-diff-node-short-name-wrapper (node &optional right-side)
  (if (not right-side)
      (ztree-diff-node-short-name node)
    (ztree-diff-node-right-short-name node)))


(defun ztree-diff-node-is-directory (node)
  (let ((left (ztree-diff-node-left-path node))
        (right (ztree-diff-node-right-path node)))
    (if left
        (file-directory-p left)
      (file-directory-p right))))

(defun ztree-diff-node-side (node)
  (let ((left (ztree-diff-node-left-path node))
        (right (ztree-diff-node-right-path node)))
    (if (and left right) 'both
      (if left 'left 'right))))

(defun ztree-diff-node-equal (node1 node2)
  (and (string-equal (ztree-diff-node-short-name node1)
                     (ztree-diff-node-short-name node2))
       (string-equal (ztree-diff-node-left-path node1)
                     (ztree-diff-node-left-path node2))
       (string-equal (ztree-diff-node-right-path node1)
                     (ztree-diff-node-right-path node1))))

(defun ztree-diff-untrampify-filename (file)
  "Returns `file' as the local file name."
  (require 'tramp)
  (if (not (tramp-tramp-file-p file))
      file
    (tramp-file-name-localname (tramp-dissect-file-name file))))

(defun ztree-diff-modef-quotify-string (x)
  (concat "\"" x "\""))

(defun ztree-diff-model-files-equal (file1 file2)
  "Compare files using external diff. Returns t if equal"
  (let* ((file1-untrampified (ztree-diff-untrampify-filename (ztree-diff-modef-quotify-string file1)))
         (file2-untrampified (ztree-diff-untrampify-filename (ztree-diff-modef-quotify-string file2)))
         (diff-command (concat "diff -q" " " file1-untrampified " " file2-untrampified))
         (diff-output (shell-command-to-string diff-command)))
    (not (> (length diff-output) 2))))

(defun ztree-directory-files (dir)
  "Returns the list of full paths of files in a directory, filtering out . and .."
  (ztree-filter #'(lambda (file) (let ((simple-name (file-short-name file)))
                                   (not (or (string-equal simple-name ".")
                                            (string-equal simple-name "..")))))
                (directory-files dir 'full)))

(defun ztree-diff-model-partial-rescan (node)
  ;; assuming what parent is always exists
  ;; otherwise the UI shall force the full rescan
  (let ((parent (ztree-diff-node-parent node))
        (isdir (ztree-diff-node-is-directory node))
        (left (ztree-diff-node-left-path node))
        (right (ztree-diff-node-right-path node)))
    ;; if node is a directory - traverse
    (when (and left right
               (file-exists-p left)
               (file-exists-p right))
      (if isdir 
        (let ((traverse (ztree-diff-node-traverse
                         node
                         left
                         right)))
          (ztree-diff-node-set-different node (car traverse))
          (ztree-diff-node-set-children node (cdr traverse)))
        ;; node is a file
        (ztree-diff-node-set-different
         node
         (if (ztree-diff-model-files-equal left right)
             nil
           'diff))))))

(defun ztree-diff-model-subtree (parent path side)
  "Creates a subtree for the given path for either 'left or 'right sides"
  (let ((files (ztree-directory-files path))
        (result nil))
    (dolist (file files)
      (if (file-directory-p file)
          (let* ((node (ztree-diff-node-create
                        parent
                        (when (eq side 'left) file)
                        (when (eq side 'right) file)
                        (file-short-name file)
                        (file-short-name file)
                        nil
                        'new))
                 (children (ztree-diff-model-subtree node file side)))
            (ztree-diff-node-set-children node children)
            (push node result))
        (push (ztree-diff-node-create
               parent
               (when (eq side 'left) file)
               (when (eq side 'right) file)
               (file-short-name file)
               (file-short-name file)
               nil
               'new)
              result)))
    result))

(defun ztree-diff-node-update-diff-from-children (node)
  (let ((children (ztree-diff-node-children node))
        (diff nil))
    (dolist (child children)
      (setq diff
            (ztree-diff-model-update-diff
             diff
             (ztree-diff-node-different child))))
    (ztree-diff-node-set-different node diff)))

(defun ztree-diff-node-update-all-parents-diff (node)
  (let ((parent node))
    (while (setq parent (ztree-diff-node-parent parent))
      (ztree-diff-node-update-diff-from-children parent))))


(defun ztree-diff-model-update-diff (old new)
  (if new
      (if (or (not old)
              (eq old 'new))
          new
        old)
    old))

(defun ztree-diff-node-traverse (parent path1 path2)
  "Function traversing 2 paths returning the list where the
first element is the difference status (nil, 'diff, 'new') and
the rest is the combined list of nodes"
  (let ((list1 (ztree-directory-files path1))
        (list2 (ztree-directory-files path2))
        (different-dir nil)
        (result nil))
    (ztree-diff-model-update-wait-message)
    ;; first - adding all entries from left directory
    (dolist (file1 list1)
      ;; for every entry in the first directory 
      ;; we are creating the node
      (let* ((simple-name (file-short-name file1))
             (isdir (file-directory-p file1))
             (children nil)
             (different nil)
             ;; create the current node to be set as parent to
             ;; subdirectories
             (node (ztree-diff-node-create parent file1 nil simple-name simple-name nil nil))
             ;; 1. find if the file is in the second directory and the type
             ;;    is the same - i.e. both are directories or both are files
             (file2 (ztree-find list2
                                #'(lambda (x) (and (string-equal (file-short-name x)
                                                                 simple-name)
                                                   (eq isdir (file-directory-p x)))))))
        ;; 2. if it is not in the second directory, add it as a node
        (if (not file2)
            (progn
              ;; 2.1 if it is a directory, add the whole subtree
              (when (file-directory-p file1)
                (setq children (ztree-diff-model-subtree node file1 'left)))
              ;; 2.2 update the difference status for this entry
              (setq different 'new))
          ;; 3. if it is found in second directory and of the same type
          ;; 3.1 if it is a file
          (if (not (file-directory-p file1))
              ;; 3.1.1 set difference status to this entry
              (setq different (if (ztree-diff-model-files-equal file1 file2) nil 'diff))
            ;; 3.2 if it is the directory
            ;; 3.2.1 get the result of the directories comparison together with status
            (let ((traverse (ztree-diff-node-traverse node file1 file2)))
              ;; 3.2.2 update the difference status for whole comparison from
              ;;       difference result from the 2 subdirectories comparison
              (setq different (car traverse))
              ;; 3.2.3 set the children list from the 2 subdirectories comparison
              (setq children (cdr traverse)))))
        ;; 2.3 update difference status for the whole comparison
        (setq different-dir (ztree-diff-model-update-diff different-dir different))
        ;; update calculated parameters of the node
        (ztree-diff-node-set-right-path node file2)
        (ztree-diff-node-set-children node children)
        (ztree-diff-node-set-different node different)
        ;; push the created node to the result list
        (push node result)))
    ;; second - adding entries from the right directory which are not present
    ;; in the left directory
    (dolist (file2 list2)
      ;; for every entry in the second directory 
      ;; we are creating the node
      (let* ((simple-name (file-short-name file2))
             (isdir (file-directory-p file2))
             (children nil)
             ;; create the node to be added to the results list
             (node (ztree-diff-node-create parent nil file2 simple-name simple-name nil 'new))
             ;; 1. find if the file is in the first directory and the type
             ;;    is the same - i.e. both are directories or both are files
             (file1 (ztree-find list1
                                #'(lambda (x) (and (string-equal (file-short-name x)
                                                                 simple-name)
                                                   (eq isdir (file-directory-p x)))))))
        ;; if it is not in the first directory, add it as a node
        (when (not file1)
          ;; if it is a directory, set the whole subtree to children
          (when (file-directory-p file2)
            (setq children (ztree-diff-model-subtree node file2 'right)))
          ;; update the different status for the whole comparison
          (setq different-dir (ztree-diff-model-update-diff different-dir 'new))
          ;; set calculated children to the node
          (ztree-diff-node-set-children node children)
          ;; push the created node to the result list
          (push node result))))
    ;; result is a pair: difference status and nodes list
    (cons different-dir result)))

(defun ztree-diff-model-create (dir1 dir2)
  (when (not (file-directory-p dir1))
    (error "Path %s is not a directory" dir1))
  (when (not (file-directory-p dir2))
    (error "Path %s is not a directory" dir2))
  (setq ztree-diff-model-wait-message (concat "Comparing " dir1 " and " dir2 " ..."))
  (let* ((model 
          (ztree-diff-node-create nil dir1 dir2
                                  (file-short-name dir1)
                                  (file-short-name dir2)
                                  nil
                                  nil))
         (traverse (ztree-diff-node-traverse model dir1 dir2)))
    (ztree-diff-node-set-children model (cdr traverse))
    (ztree-diff-node-set-different model (car traverse))
    (message "Done.")
    model))

(defun ztree-diff-model-update-node (node)
  (setq ztree-diff-model-wait-message
        (concat "Updating " (ztree-diff-node-short-name node) " ..."))
  (let ((traverse (ztree-diff-node-traverse node
                                            (ztree-diff-node-left-path node)
                                            (ztree-diff-node-right-path node))))
    (ztree-diff-node-set-children node (cdr traverse))
    (ztree-diff-node-set-different node (car traverse))
    (message "Done.")))
    


(provide 'ztree-diff-model)

;;; ztree-diff-model.el ends here
