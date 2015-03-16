;;; ztree-view.el --- Text mode tree view (buffer)

;; Copyright (C) 2013 Alexey Veretennikov
;;
;; Author: Alexey Veretennikov <alexey dot veretennikov at gmail dot com>
;; Created: 2013-11-1l
;; Version: 1.0.1
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
;;
;; Add the following to your .emacs file:
;;
;; (push (substitute-in-file-name "path-to-ztree-directory") load-path)
;; (require 'ztree-view)
;;
;; Call the ztree interactive function:
;; Use the following function: ztree-view
;;
;;; Issues:
;;
;;; TODO:
;;
;;
;;; Change Log:
;;
;; 2013-11-10 (1.0.0)
;;    Initial Release.
;;
;;; Code:

(require 'ztree-util)

;;
;; Globals
;;

(defvar ztree-expanded-nodes-list nil
  "A list of Expanded nodes (i.e. directories) entries.")
(make-variable-buffer-local 'ztree-expanded-nodes-list)

(defvar ztree-start-node nil
  "Start node(i.e. directory) for the window.")
(make-variable-buffer-local 'ztree-start-node)

(defvar ztree-line-to-node-table nil
  "List of tuples with full node(i.e. file/directory name
 and the line.")
(make-variable-buffer-local 'ztree-line-to-node-table)

(defvar ztree-start-line nil
  "Index of the start line - the root")
(make-variable-buffer-local 'ztree-start-line)

(defvar ztree-parent-lines-array nil
  "Array of parent lines, there the ith value of the array
is the parent line for line i. If ith value is i - it is the root
line")
(make-variable-buffer-local 'ztree-parent-lines-array)

(defvar ztree-count-subsequent-bs nil
  "Counter for the subsequest BS keys (to identify double BS). Used
in order to not to use cl package and lexical-let")
(make-variable-buffer-local 'ztree-count-subsequent-bs)

(defvar ztree-line-tree-properties nil
  "Hash with key - line number, value - property ('left, 'right, 'both).
Used for 2-side trees, to determine if the node exists on left or right
or both sides")
(make-variable-buffer-local 'ztree-line-tree-properties)

(defun ztree-tree-header-fun nil
  "Function inserting the header into the tree buffer.
MUST inster newline at the end!")
(make-variable-buffer-local 'ztree-tree-header-fun)

(defvar ztree-node-short-name-fun nil
  "Function which creates a pretty-printable short string from
the node")
(make-variable-buffer-local 'ztree-node-short-name-fun)

(defun ztree-node-is-expandable-fun nil
  "Function which determines if the node is expandable,
for example if the node is a directory")
(make-variable-buffer-local 'ztree-node-is-expandable-fun)

(defun ztree-node-equal-fun nil
  "Function which determines if the 2 nodes are equal")
(make-variable-buffer-local 'ztree-node-equal-fun)

(defun ztree-node-contents-fun nil
  "Function returning list of node contents")
(make-variable-buffer-local 'ztree-node-contents-fun)

(defun ztree-node-side-fun nil
  "Function returning position of the node: 'left, 'right or 'both.
If not defined(by default) - using single screen tree, otherwise
the buffer is split to 2 trees")
(make-variable-buffer-local 'ztree-node-side-fun)

(defun ztree-node-face-fun nil
  "Function returning face for the node")
(make-variable-buffer-local 'ztree-node-face-fun)

(defun ztree-node-action-fun nil
  "Function called when Enter/Space pressed on the node")
(make-variable-buffer-local 'ztree-node-action-fun)

(defvar ztree-node-showp-fun nil
  "Function called to decide if the node should be visible")
(make-variable-buffer-local 'ztree-node-showp-fun)


;;
;; Major mode definitions
;;

(defvar ztree-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "\r") 'ztree-perform-action)
    (define-key map (kbd "SPC") 'ztree-perform-soft-action)
    (define-key map [double-mouse-1] 'ztree-perform-action)
    (define-key map (kbd "TAB") 'ztree-jump-side)
    (define-key map (kbd "g") 'ztree-refresh-buffer)
    (define-key map (kbd "x") 'ztree-toggle-expand-subtree)
    (if window-system
        (define-key map (kbd "<backspace>") 'ztree-move-up-in-tree)
      (define-key map "\177" 'ztree-move-up-in-tree))
    map)
  "Keymap for `ztree-mode'.")


(defface ztreep-node-face
  '((((background dark)) (:foreground "#ffffff"))
    (((type nil))        (:inherit 'font-lock-function-name-face))
    (t                   (:foreground "Blue")))
  "*Face used for expandable entries(directories etc) in Ztree buffer."
  :group 'Ztree :group 'font-lock-highlighting-faces)
(defvar ztreep-node-face 'ztreep-node-face)

(defface ztreep-leaf-face
  '((((background dark)) (:foreground "cyan1"))
    (((type nil))        (:inherit 'font-lock-variable-name-face))
    (t                   (:foreground "darkblue")))
  "*Face used for not expandable nodes(leafs, i.e. files) in Ztree buffer."
  :group 'Ztree :group 'font-lock-highlighting-faces)
(defvar ztreep-leaf-face 'ztreep-leaf-face)

(defface ztreep-arrow-face
  '((((background dark)) (:foreground "#7f7f7f"))
    (t                   (:foreground "#8d8d8d")))
  "*Face used for arrows in Ztree buffer."
  :group 'Ztree :group 'font-lock-highlighting-faces)
(defvar ztreep-arrow-face 'ztreep-arrow-face)

(defface ztreep-expand-sign-face
  '((((background dark)) (:foreground "#7f7fff"))
    (t                   (:foreground "#8d8d8d")))
  "*Face used for expand sign [+] in Ztree buffer."
  :group 'Ztree :group 'font-lock-highlighting-faces)
(defvar ztreep-expand-sign-face 'ztreep-expand-sign-face)


;;;###autoload
(define-derived-mode ztree-mode special-mode "Ztree"
  "A major mode for displaying the directory tree in text mode."
  ;; only spaces
  (setq indent-tabs-mode nil)
  ;; fix for electric-indent-mode
  ;; for emacs 24.4
  (if (fboundp 'electric-indent-local-mode)
      (electric-indent-local-mode -1)
    ;; for emacs 24.3 or less
    (add-hook 'electric-indent-functions
              (lambda (arg) 'no-indent) nil 'local)))


(defun ztree-find-node-in-line (line)
  "Search through the array of node-line pairs and return the
node for the line specified"
  (gethash line ztree-line-to-node-table))

(defun ztree-find-node-at-point ()
  "Returns cons pair (node, side) for the current point or nil
if there is no node"
  (let ((center (/ (window-width) 2))
        (node (ztree-find-node-in-line (line-number-at-pos))))
    (when node
      (cons node (if (> (current-column) center) 'right 'left)))))
  

(defun ztree-is-expanded-node (node)
  "Find if the node is in the list of expanded nodes"
  (ztree-find ztree-expanded-nodes-list
              #'(lambda (x) (funcall ztree-node-equal-fun x node))))


(defun ztree-set-parent-for-line (line parent)
  (aset ztree-parent-lines-array (- line ztree-start-line) parent))

(defun ztree-get-parent-for-line (line)
  (when (and (>= line ztree-start-line)
             (< line (+ (length ztree-parent-lines-array) ztree-start-line)))
    (aref ztree-parent-lines-array (- line ztree-start-line))))

(defun scroll-to-line (line)
  "Recommended way to set the cursor to specified line"
  (goto-char (point-min))
  (forward-line (1- line)))


(defun ztree-do-toggle-expand-subtree-iter (node state)
  (when (funcall ztree-node-is-expandable-fun node)
    (let ((children (funcall ztree-node-contents-fun node)))
      (ztree-do-toggle-expand-state node state)
      (dolist (child children)
        (ztree-do-toggle-expand-subtree-iter child state)))))

     
(defun ztree-do-toggle-expand-subtree ()
  (let* ((line (line-number-at-pos))
         (node (ztree-find-node-in-line line))
         ;; save the current window start position
         (current-pos (window-start)))
    ;; only for expandable nodes
    (when (funcall ztree-node-is-expandable-fun node)
      ;; get the current expand state and invert it 
      (let ((do-expand (not (ztree-is-expanded-node node))))
        (ztree-do-toggle-expand-subtree-iter node do-expand))
      ;; refresh buffer and scroll back to the saved line
      (ztree-refresh-buffer line)
      ;; restore window start position
      (set-window-start (selected-window) current-pos))))
          

(defun ztree-do-perform-action (hard)
  (let* ((line (line-number-at-pos))
         (node (ztree-find-node-in-line line)))
    (when node
      (if (funcall ztree-node-is-expandable-fun node)
          ;; only for expandable nodes
          (ztree-toggle-expand-state node)
        ;; perform action
        (when ztree-node-action-fun
          (funcall ztree-node-action-fun node hard)))
      ;; save the current window start position
      (let ((current-pos (window-start)))
        ;; refresh buffer and scroll back to the saved line
        (ztree-refresh-buffer line)
        ;; restore window start position
        (set-window-start (selected-window) current-pos))))) 
  

(defun ztree-perform-action ()
  "Toggle expand/collapsed state for nodes or perform hard action,
binded on RET, on node"
  (interactive)
  (ztree-do-perform-action t))

(defun ztree-perform-soft-action ()
  "Toggle expand/collapsed state for nodes or perform soft action,
binded on Space, on node"
  (interactive)
  (ztree-do-perform-action nil))


(defun ztree-toggle-expand-subtree()
  "Toggle Expanded/Collapsed state on all nodes of the subtree"
  (interactive)
  (ztree-do-toggle-expand-subtree))

(defun ztree-do-toggle-expand-state (node do-expand)
  "Set the expanded state of the node to do-expand"
  (if (not do-expand)
      (setq ztree-expanded-nodes-list
            (ztree-filter
             #'(lambda (x) (not (funcall ztree-node-equal-fun node x)))
             ztree-expanded-nodes-list))
    (push node ztree-expanded-nodes-list)))

   
(defun ztree-toggle-expand-state (node)
  "Toggle expanded/collapsed state for nodes"
  (ztree-do-toggle-expand-state node (not (ztree-is-expanded-node node))))


(defun ztree-move-up-in-tree ()
  "Action on Backspace key: to jump to the line of a parent node or
if previous key was Backspace - close the node"
  (interactive)
  (when ztree-parent-lines-array
    (let* ((line (line-number-at-pos (point)))
           (parent (ztree-get-parent-for-line line)))
      (when parent
        (if (and (equal last-command 'ztree-move-up-in-tree)
                 (not ztree-count-subsequent-bs))
            (let ((node (ztree-find-node-in-line line)))
              (when (ztree-is-expanded-node node)
                (ztree-toggle-expand-state node))
              (setq ztree-count-subsequent-bs t)
              (ztree-refresh-buffer line))
          (progn (setq ztree-count-subsequent-bs nil)
                 (scroll-to-line parent)))))))


(defun ztree-get-splitted-node-contens (node)
  "Returns pair of 2 elements: list of expandable nodes and
list of leafs"
  (let ((nodes (funcall ztree-node-contents-fun node))
        (comp  #'(lambda (x y)
                 (string< (funcall ztree-node-short-name-fun x)
                          (funcall ztree-node-short-name-fun y)))))
    (cons (sort (ztree-filter
                 #'(lambda (f) (funcall ztree-node-is-expandable-fun f))
                 nodes) comp)
          (sort (ztree-filter
                 #'(lambda (f) (not (funcall ztree-node-is-expandable-fun f)))
                 nodes) comp))))
                

(defun ztree-draw-char (c x y &optional face)
  "Draw char c at the position (1-based) (x y)"
  (save-excursion
    (scroll-to-line y)
    (beginning-of-line)
    (goto-char (+ x (-(point) 1)))
    (delete-char 1)
    (insert-char c 1)
    (put-text-property (1- (point)) (point) 'face (if face face 'ztreep-arrow-face))))

(defun ztree-draw-vertical-line (y1 y2 x &optional face)
  "Draw a vertical line of '|' characters"
  (let ((count (abs (- y1 y2)))) 
    (if (> y1 y2)
        (progn
          (dotimes (y count)
            (ztree-draw-char ?\| x (+ y2 y) face))
          (ztree-draw-char ?\| x (+ y2 count) face))
      (progn
        (dotimes (y count)
          (ztree-draw-char ?\| x (+ y1 y) face))
        (ztree-draw-char ?\| x (+ y1 count) face)))))        

(defun ztree-draw-vertical-rounded-line (y1 y2 x &optional face)
  "Draw a vertical line of '|' characters finishing with '`' character"
  (let ((count (abs (- y1 y2)))) 
    (if (> y1 y2)
        (progn
          (dotimes (y count)
            (ztree-draw-char ?\| x (+ y2 y) face))
          (ztree-draw-char ?\` x (+ y2 count) face))
      (progn
        (dotimes (y count)
          (ztree-draw-char ?\| x (+ y1 y) face))
        (ztree-draw-char ?\` x (+ y1 count) face)))))        


(defun ztree-draw-horizontal-line (x1 x2 y)
  (if (> x1 x2)
      (dotimes (x (1+ (- x1 x2)))
        (ztree-draw-char ?\- (+ x2 x) y))
    (dotimes (x (1+ (- x2 x1)))
      (ztree-draw-char ?\- (+ x1 x) y))))


(defun ztree-draw-tree (tree depth start-offset)
  "Draw the tree of lines with parents"
  (if (atom tree)
      nil
    (let* ((root (car tree))
           (children (cdr tree))
           (offset (+ start-offset (* depth 4)))
           (line-start (+ 3 offset))
           (line-end-leaf (+ 7 offset))
           (line-end-node (+ 4 offset))
           ;; determine if the line is visible. It is always the case
           ;; for 1-sided trees; however for 2 sided trees
           ;; it depends on which side is the actual element
           ;; and which tree (left with offset 0 or right with offset > 0
           ;; we are drawing
           (visible #'(lambda (line) ()
                        (if (not ztree-node-side-fun) t
                          (let ((side
                                 (gethash line ztree-line-tree-properties)))
                            (cond ((eq side 'left) (= start-offset 0))
                                  ((eq side 'right) (> start-offset 0))
                                  (t t)))))))
      (when children
        ;; draw the line to the last child
        ;; since we push'd children to the list, it's the first visible line
        ;; from the children list
        (let ((last-child (ztree-find children
                                      #'(lambda (x)
                                          (funcall visible (car-atom x)))))
              (x-offset (+ 2 offset)))
          (when last-child
            (ztree-draw-vertical-rounded-line (1+ root)
                                              (car-atom last-child)
                                              x-offset)))
        ;; draw recursively
        (dolist (child children)
          (ztree-draw-tree child (1+ depth) start-offset)
          (let ((end (if (listp child) line-end-node line-end-leaf)))
            (when (funcall visible (car-atom child))
              (ztree-draw-horizontal-line line-start
                                          end
                                          (car-atom child)))))))))

(defun ztree-fill-parent-array (tree)
  ;; set the root line
  (let ((root (car tree))
        (children (cdr tree)))
    (dolist (child children)
      (ztree-set-parent-for-line (car-atom child) root)
      (when (listp child)
        (ztree-fill-parent-array child)))))


(defun ztree-insert-node-contents (path)
  ;; insert node contents with initial depth 0
  ;; ztree-insert-node-contents-1 return the tree of line
  ;; numbers to determine who is parent line of the
  ;; particular line. This tree is used to draw the
  ;; graph
  (let ((tree (ztree-insert-node-contents-1 path 0))
        ;; number of 'rows' in tree is last line minus start line
        (num-of-items (- (line-number-at-pos (point)) ztree-start-line)))
    ;; create a parents array to store parents of lines
    ;; parents array used for navigation with the BS 
    (setq ztree-parent-lines-array (make-vector num-of-items 0))
    ;; set the root node in lines parents array
    (ztree-set-parent-for-line ztree-start-line ztree-start-line)
    ;; fill the parent arrray from the tree
    (ztree-fill-parent-array tree)
    ;; draw the tree starting with depth 0 and offset 0
    (ztree-draw-tree tree 0 0)
    ;; for the 2-sided tree we need to draw the vertical line
    ;; and an additional tree
    (if ztree-node-side-fun             ; 2-sided tree
        (let ((width (window-width)))
          ;; draw the vertical line in the middle of the window
          (ztree-draw-vertical-line ztree-start-line
                                    (1- (+ num-of-items ztree-start-line))
                                    (/ width 2)
                                    'vertical-border)
          (ztree-draw-tree tree 0 (1+ (/ width 2)))))))


(defun ztree-insert-node-contents-1 (node depth)
  (let* ((expanded (ztree-is-expanded-node node))
         ;; insert node entry with defined depth
         (root-line (ztree-insert-entry node depth expanded))
         ;; children list is the list of lines which are children
         ;; of the root line
         (children nil))
    (when expanded ;; if expanded we need to add all subnodes
      (let* ((contents (ztree-get-splitted-node-contens node))
             ;; contents is the list of 2 elements:
             (nodes (car contents))     ; expandable entries - nodes
             (leafs (cdr contents)))    ; leafs - which doesn't have subleafs
        ;; iterate through all expandable entries to insert them first
        (dolist (node nodes)            
          ;; if it is not in the filter list
          (when (funcall ztree-node-showp-fun node)
            ;; insert node on the next depth level
            ;; and push the returning result (in form (root children))
            ;; to the children list
            (push (ztree-insert-node-contents-1 node (1+ depth))
                  children)))
        ;; now iterate through all the leafs
        (dolist (leaf leafs)
          ;; if not in filter list
          (when (funcall ztree-node-showp-fun leaf)
            ;; insert the leaf and add it to children
            (push (ztree-insert-entry leaf (1+ depth) nil)
                    children)))))
    ;; result value is the list - head is the root line,
    ;; rest are children 
    (cons root-line children)))

(defun ztree-insert-entry (node depth expanded)
  (let ((line (line-number-at-pos))
        (expandable (funcall ztree-node-is-expandable-fun node))
        (short-name (funcall ztree-node-short-name-fun node)))
    (if ztree-node-side-fun           ; 2-sided tree
        (let ((right-short-name (funcall ztree-node-short-name-fun node t))
              (side (funcall ztree-node-side-fun node))
              (width (window-width)))
          (when (eq side 'left)  (setq right-short-name ""))
          (when (eq side 'right) (setq short-name ""))
          (ztree-insert-single-entry short-name depth
                                     expandable expanded 0
                                     (when ztree-node-face-fun
                                       (funcall ztree-node-face-fun node)))
          (ztree-insert-single-entry right-short-name depth
                                     expandable expanded (1+ (/ width 2))
                                     (when ztree-node-face-fun
                                       (funcall ztree-node-face-fun node)))
          (puthash line side ztree-line-tree-properties))
      (ztree-insert-single-entry short-name depth expandable expanded 0))
    (puthash line node ztree-line-to-node-table)    
    (newline-and-begin)
    line))

(defun ztree-insert-single-entry (short-name depth
                                             expandable expanded
                                             offset
                                             &optional face)
  (let ((node-sign #'(lambda (exp)    
                       (insert "[" (if exp "-" "+") "]")
                       (set-text-properties (- (point) 3)
                                            (point)
                                            '(face ztreep-expand-sign-face)))))
    (move-to-column offset t)
    (delete-region (point) (line-end-position))
    (when (> depth 0)
      (dotimes (i depth)
        (insert " ")
        (insert-char ?\s 3)))           ; insert 3 spaces
    (when (> (length short-name) 0)
      (if expandable
          (progn                          
            (funcall node-sign expanded)   ; for expandable nodes insert "[+/-]"
            (insert " ")
            (put-text-property 0 (length short-name)
                               'face (if face face 'ztreep-node-face) short-name)
            (insert short-name))
        (progn
          (insert "    ")
          (put-text-property 0 (length short-name)
                             'face (if face face 'ztreep-leaf-face) short-name)
          (insert short-name))))))

(defun ztree-jump-side ()
  (interactive)
  (when ztree-node-side-fun             ; 2-sided tree
    (let ((center (/ (window-width) 2)))
      (cond ((< (current-column) center) 
             (move-to-column (1+ center)))
            ((> (current-column) center) 
             (move-to-column 1))
            (t nil)))))



(defun ztree-refresh-buffer (&optional line)
  (interactive)
  (when (and (equal major-mode 'ztree-mode)
             (boundp 'ztree-start-node))
    (setq ztree-line-to-node-table (make-hash-table))
    ;; create a hash table of node properties for line
    ;; used in 2-side tree mode
    (when ztree-node-side-fun
      (setq ztree-line-tree-properties (make-hash-table)))
    (toggle-read-only)
    (erase-buffer)
    (funcall ztree-tree-header-fun)
    (setq ztree-start-line (line-number-at-pos (point)))
    (ztree-insert-node-contents ztree-start-node)
    (scroll-to-line (if line line ztree-start-line))
    (toggle-read-only)))


(defun ztree-view (
                   buffer-name
                   start-node
                   filter-fun
                   header-fun
                   short-name-fun
                   expandable-p
                   equal-fun
                   children-fun
                   face-fun
                   action-fun
                   &optional node-side-fun
                   )
  (let ((buf (get-buffer-create buffer-name)))
    (switch-to-buffer buf)
    (ztree-mode)
    ;; configure ztree-view
    (setq ztree-start-node start-node)
    (setq ztree-expanded-nodes-list (list ztree-start-node))
    (setq ztree-node-showp-fun filter-fun)
    (setq ztree-tree-header-fun header-fun)
    (setq ztree-node-short-name-fun short-name-fun)
    (setq ztree-node-is-expandable-fun expandable-p)
    (setq ztree-node-equal-fun equal-fun)
    (setq ztree-node-contents-fun children-fun)
    (setq ztree-node-face-fun face-fun)
    (setq ztree-node-action-fun action-fun)
    (setq ztree-node-side-fun node-side-fun)
    (ztree-refresh-buffer)))


(provide 'ztree-view)
;;; ztree-view.el ends here
