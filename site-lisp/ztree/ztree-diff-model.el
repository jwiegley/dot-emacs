;;; ztree-diff-model.el --- diff model for directory trees -*- lexical-binding: t; -*-

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

;; Diff model

;;; Code:
(require 'ztree-util)
(eval-when-compile (require 'cl-lib))

(defvar-local ztree-diff-model-ignore-fun nil
  "Function which determines if the node should be excluded from comparison.")

(defvar-local ztree-diff-model-progress-fun nil
  "Function which should be called whenever the progress indications is updated.")


(defun ztree-diff-model-update-progress ()
  "Update the progress."
  (when ztree-diff-model-progress-fun
    (funcall ztree-diff-model-progress-fun)))

;; Create a record ztree-diff-node with defined fields and getters/setters
;; here:
;; parent - parent node
;; left-path is the full path on the left side of the diff window,
;; right-path is the full path of the right side,
;; short-name - is the file or directory name
;; children - list of nodes - files or directories if the node is a directory
;; different = {nil, 'same, 'new, 'diff, 'ignore} - means comparison status
(cl-defstruct (ztree-diff-node
               (:constructor)
               (:constructor ztree-diff-node-create
                (parent left-path right-path
                        different
                        &aux
                        (short-name (ztree-file-short-name
                                     (or left-path right-path)))
                        (right-short-name
                         (if (and left-path right-path)
                             (ztree-file-short-name right-path)
                           short-name)))))
  parent left-path right-path short-name right-short-name children different)

(defun ztree-diff-model-ignore-p (node)
  "Determine if the NODE should be excluded from comparison results."
  (when ztree-diff-model-ignore-fun
    (funcall ztree-diff-model-ignore-fun node)))

(defun ztree-diff-node-to-string (node)
  "Construct the string with contents of the NODE given."
  (let ((string-or-nil #'(lambda (x) (if x
                                         (cond ((stringp x) x)
                                               ((eq x 'new) "new")
                                               ((eq x 'diff) "different")
                                               ((eq x 'ignore) "ignored")
                                               ((eq x 'same) "same")
                                               (t (ztree-diff-node-short-name x)))
                                       "(empty)")))
        (children (ztree-diff-node-children node))
        (ch-str ""))
    (dolist (x children)
      (setq ch-str (concat ch-str "\n   * " (ztree-diff-node-short-name x)
                           ": "
                           (funcall string-or-nil (ztree-diff-node-different x)))))
    (concat "Node: " (ztree-diff-node-short-name node)
            "\n"
            " * Parent: " (funcall string-or-nil (ztree-diff-node-parent node))
            "\n"
            " * Status: " (funcall string-or-nil (ztree-diff-node-different node))
            "\n"
            " * Left path: " (funcall string-or-nil (ztree-diff-node-left-path node))
            "\n"
            " * Right path: " (funcall string-or-nil (ztree-diff-node-right-path node))
            "\n"
            " * Children: " ch-str
            "\n")))


(defun ztree-diff-node-short-name-wrapper (node &optional right-side)
  "Return the short name of the NODE given.
If the RIGHT-SIDE is true, take the right leaf"
  (if (not right-side)
      (ztree-diff-node-short-name node)
    (ztree-diff-node-right-short-name node)))


(defun ztree-diff-node-is-directory (node)
  "Determines if the NODE is a directory."
  (let ((left (ztree-diff-node-left-path node))
        (right (ztree-diff-node-right-path node)))
    (if left
        (file-directory-p left)
      (file-directory-p right))))

(defun ztree-diff-node-side (node)
  "Determine the side there the file is present for NODE.
Return BOTH if the file present on both sides;
LEFT if only on the left side and
RIGHT if only on the right side."
  (let ((left (ztree-diff-node-left-path node))
        (right (ztree-diff-node-right-path node)))
    (if (and left right) 'both
      (if left 'left 'right))))


(defun ztree-diff-node-equal (node1 node2)
  "Determines if NODE1 and NODE2 are equal."
  (and (string-equal (ztree-diff-node-short-name node1)
                     (ztree-diff-node-short-name node2))
       (string-equal (ztree-diff-node-left-path node1)
                     (ztree-diff-node-left-path node2))
       (string-equal (ztree-diff-node-right-path node1)
                     (ztree-diff-node-right-path node1))))

(defun ztree-diff-model-files-equal (file1 file2)
  "Compare files FILE1 and FILE2 using external diff.
Returns t if equal."
  (unless (ztree-same-host-p file1 file2)
    (error "Compared files are not on the same host"))
  (let* ((file1-untrampified (ztree-untrampify-filename file1))
         (file2-untrampified (ztree-untrampify-filename file2)))
    (if (or
         (/= (nth 7 (file-attributes file1))
            (nth 7 (file-attributes file2)))
         (/= 0 (process-file diff-command nil nil nil "-q"
                           file1-untrampified
                           file2-untrampified)))
        'diff
      'same)))

(defun ztree-directory-files (dir)
  "Return the list of full paths of files in a directory DIR.
Filters out . and .."
  (ztree-filter #'(lambda (file) (let ((simple-name (ztree-file-short-name file)))
                                   (not (or (string-equal simple-name ".")
                                            (string-equal simple-name "..")))))
                (directory-files dir 'full)))

(defun ztree-diff-model-partial-rescan (node)
  "Rescan the NODE.
The node is a either a file or directory with both
left and right parts existing."
  ;; if a directory - recreate
  (if (ztree-diff-node-is-directory node)
      (ztree-diff-node-recreate node)
    ;; if a file, change a status
    (setf (ztree-diff-node-different node)
          (if (or (ztree-diff-model-ignore-p node) ; if should be ignored
                  (eql (ztree-diff-node-different node) 'ignore) ; was ignored
                  (eql (ztree-diff-node-different ; or parent was ignored
                        (ztree-diff-node-parent node))
                       'ignore))
              'ignore
            (ztree-diff-model-files-equal (ztree-diff-node-left-path node)
                                          (ztree-diff-node-right-path node)))))
  ;; update all parents statuses
  (ztree-diff-node-update-all-parents-diff node))

(defun ztree-diff-model-subtree (parent path side diff)
  "Create a subtree with given PARENT for the given PATH.
Argument SIDE either `left' or `right' side.
Argument DIFF different status to be assigned to all created nodes."
  (let ((files (ztree-directory-files path))
        (result nil))
    (dolist (file files)
      (if (file-directory-p file)
          (let* ((node (ztree-diff-node-create
                        parent
                        (when (eq side 'left) file)
                        (when (eq side 'right) file)
                        diff))
                 (children (ztree-diff-model-subtree node file side diff)))
            (setf (ztree-diff-node-children node) children)
            (push node result))
        (push (ztree-diff-node-create
               parent
               (when (eq side 'left) file)
               (when (eq side 'right) file)
               diff)
              result)))
    result))

(defun ztree-diff-node-update-diff-from-children (node)
  "Set the diff status for the NODE based on its children."
  (unless (eql (ztree-diff-node-different node) 'ignore)
    (let ((diff (cl-reduce #'ztree-diff-model-update-diff
                           (ztree-diff-node-children node)
                           :initial-value 'same
                           :key 'ztree-diff-node-different)))
      (setf (ztree-diff-node-different node) diff))))

(defun ztree-diff-node-update-all-parents-diff (node)
  "Recursively update all parents diff status for the NODE."
  (let ((parent node))
    (while (setq parent (ztree-diff-node-parent parent))
      (ztree-diff-node-update-diff-from-children parent))))


(defun ztree-diff-model-update-diff (old new)
  "Get the diff status depending if OLD or NEW is not nil.
If the OLD is `ignore', do not change anything"
  ;; if the old whole directory is ignored, ignore children's status
  (cond ((eql old 'ignore) 'ignore)
        ;; if the new status is ignored, use old
        ((eql new 'ignore) old)
        ;; if the old or new status is different, return different
        ((or (eql old 'diff)
             (eql new 'diff)) 'diff)
        ;; if new is 'new, return new
        ((eql new 'new) 'new)
        ;; all other cases return old
        (t old)))

(defun ztree-diff-node-update-diff-from-parent (node)
  "Recursively update diff status of all children of NODE.
This function will traverse through all children recursively
setting status from the NODE, unless they have an ignore status"
  (let ((status (ztree-diff-node-different node))
        (children (ztree-diff-node-children node)))
    ;; if the parent has ignore status, force all kids this status
    ;; otherwise only update status when the child status is not ignore
    (mapc (lambda (child)
            (when (or (eql status 'ignore)
                      (not
                       (or (eql status 'ignore)
                           (eql (ztree-diff-node-different child) 'ignore))))
              (setf (ztree-diff-node-different child) status)
              (ztree-diff-node-update-diff-from-parent child)))
            children)))



(defun ztree-diff-model-find-in-files (list shortname is-dir)
  "Find in LIST of files the file with name SHORTNAME.
If IS-DIR searching for directories; assume files otherwise"
  (ztree-find list
              (lambda (x) (and (string-equal (ztree-file-short-name x)
                                             shortname)
                               (eq is-dir (file-directory-p x))))))


(defun ztree-diff-model-should-ignore (node)
  "Determine if the NODE and its children should be ignored.
If no parent - never ignore;
if in ignore list - ignore
if parent has ignored status - ignore"
  (let ((parent (ztree-diff-node-parent node)))
    (and parent
         (or (eql (ztree-diff-node-different parent) 'ignore)
             (ztree-diff-model-ignore-p node)))))


(defun ztree-diff-node-recreate (node)
  "Traverse 2 paths defined in the NODE updating its children and status."
  (let* ((list1 (ztree-directory-files (ztree-diff-node-left-path node))) ;; left list of liles
         (list2 (ztree-directory-files (ztree-diff-node-right-path node))) ;; right list of files
         (should-ignore (ztree-diff-model-should-ignore node))
         ;; status automatically assigned to children of the node
         (children-status (if should-ignore 'ignore 'new))
         (children nil))    ;; list of children
    ;; update waiting status
    (ztree-diff-model-update-progress)
    ;; update node status ignore status either inhereted from the
    ;; parent or the own
    (when should-ignore
      (setf (ztree-diff-node-different node) 'ignore))
    ;; first - adding all entries from left directory
    (dolist (file1 list1)
      ;; for every entry in the first directory
      ;; we are creating the node
      (let* ((simple-name (ztree-file-short-name file1))
             (isdir (file-directory-p file1))
             ;; find if the file is in the second directory and the type
             ;; is the same - i.e. both are directories or both are files
             (file2 (ztree-diff-model-find-in-files list2 simple-name isdir))
             ;; create a child. The current node is a parent
             ;; new by default - will be overriden below if necessary
             (child
              (ztree-diff-node-create node file1 file2 children-status)))
        ;; update child own ignore status
        (when (ztree-diff-model-should-ignore child)
          (setf (ztree-diff-node-different child) 'ignore))
        ;; if exists on a right side with the same type,
        ;; remove from the list of files on the right side
        (when file2
          (setf list2 (cl-delete file2 list2 :test #'string-equal)))
        (cond
         ;; when exist just on a left side and is a directory, add all
         ((and isdir (not file2))
          (setf (ztree-diff-node-children child)
                (ztree-diff-model-subtree child
                                          file1
                                          'left
                                          (ztree-diff-node-different child))))
         ;; if 1) exists on both sides and 2) it is a file
         ;; and 3) not ignored file
         ((and file2 (not isdir) (not (eql (ztree-diff-node-different child) 'ignore)))
          (setf (ztree-diff-node-different child)
                (ztree-diff-model-files-equal file1 file2)))
         ;; if exists on both sides and it is a directory, traverse further
         ((and file2 isdir)
          (ztree-diff-node-recreate child)))
        ;; push the created node to the children list
        (push child children)))
    ;; second - adding entries from the right directory which are not present
    ;; in the left directory
    (dolist (file2 list2)
      ;; for every entry in the second directory
      ;; we are creating the node
      (let* ((isdir (file-directory-p file2))
             ;; create the child to be added to the results list
             (child
              (ztree-diff-node-create node nil file2 children-status)))
        ;; update ignore status of the child
        (when (ztree-diff-model-should-ignore child)
          (setf (ztree-diff-node-different child) 'ignore))
          ;; if it is a directory, set the whole subtree to children
        (when isdir
          (setf (ztree-diff-node-children child)
                (ztree-diff-model-subtree child
                                          file2
                                          'right
                                          (ztree-diff-node-different child))))
        ;; push the created node to the result list
        (push child children)))
    ;; finally set different status based on all children
    ;; depending if the node should participate in overall result
    (unless should-ignore
      (setf (ztree-diff-node-different node)
            (cl-reduce #'ztree-diff-model-update-diff
                       children
                       :initial-value 'same
                       :key 'ztree-diff-node-different)))
    ;; and set children
    (setf (ztree-diff-node-children node) children)))


(defun ztree-diff-model-update-node (node)
  "Refresh the NODE."
  (ztree-diff-node-recreate node))



(defun ztree-diff-model-set-ignore-fun (ignore-p)
  "Set the buffer-local ignore function to IGNORE-P.
Ignore function is a function of one argument (ztree-diff-node)
which returns t if the node should be ignored (like files starting
with dot etc)."
  (setf ztree-diff-model-ignore-fun ignore-p))


(defun ztree-diff-model-set-progress-fun (progress-fun)
  "Setter for the buffer-local PROGRESS-FUN callback.
This callback is called to indicate the ongoing activity.
Callback is a function without arguments."
  (setf ztree-diff-model-progress-fun progress-fun))

(provide 'ztree-diff-model)

;;; ztree-diff-model.el ends here
