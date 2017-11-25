;;; jump-tree-visualizer.el --- Treat position history as a tree  -*- lexical-binding: t; -*-

;; Copyright (C) 2017  Free Software Foundation, Inc

;; Author: Wen Yang <yangwen0228@foxmail.com>
;; Maintainer: Wen Yang <yangwen0228@foxmail.com>
;; Package-Version: 20170803.1
;; URL: https://github.com/yangwen0228/jump-tree
;; Keywords: convenience, position, jump, tree

;; This file is NOT part of GNU Emacs.

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
;; This file serves as the visualizer of the jump-tree.

;;; Code:

(eval-when-compile (require 'cl))
(require 'jump-tree-pos)


;;; =====================================================================
;;;              Compatibility hacks for older Emacsen

;; `characterp' isn't defined in Emacs versions < 23
(unless (fboundp 'characterp)
  (defalias 'characterp 'char-valid-p))

(unless (fboundp 'registerv-data)
  (defmacro registerv-data (data) data))


;;; =====================================================================
;;;              Global variables and customization options
(defcustom jump-tree-visualizer-relative-timestamps t
  "When non-nil, display times relative to current time.

When displaying time stamps in visualizer.  Otherwise, display absolute times."
  :group 'jump-tree
  :type 'boolean)

(defcustom jump-tree-visualizer-timestamps nil
  "When non-nil, display time-stamps by default in jump-tree visualizer.

\\<jump-tree-visualizer-mode-map>You can always toggle time-stamps on and off \
using \\[jump-tree-visualizer-toggle-timestamps], regardless of the
setting of this variable."
  :group 'jump-tree
  :type 'boolean)

(defcustom jump-tree-visualizer-lazy-drawing 100
  "When non-nil, use lazy jump-tree drawing in visualizer.

Setting this to a number causes the visualizer to switch to lazy
drawing when the number of nodes in the tree is larger than this
value.

Lazy drawing means that only the visible portion of the tree will
be drawn initially, and the tree will be extended later as
needed.  For the most part, the only visible effect of this is to
significantly speed up displaying the visualizer for very large
trees.

There is one potential negative effect of lazy drawing.  Other
branches of the tree will only be drawn once the node from which
they branch off becomes visible.  So it can happen that certain
portions of the tree that would be shown with lazy drawing
disabled, will not be drawn immediately when it is
enabled.  However, this effect is quite rare in practice."
  :group 'jump-tree
  :type '(choice (const :tag "never" nil)
                 (const :tag "always" t)
                 (integer :tag "> count")))

(defface jump-tree-visualizer-default-face
  '((((class color)) :foreground "gray"))
  "Face used to draw jump-tree in visualizer."
  :group 'jump-tree)

(defface jump-tree-visualizer-current-face
  '((((class color)) :foreground "red"))
  "Face used to highlight current jump-tree node in visualizer."
  :group 'jump-tree)

(defface jump-tree-visualizer-active-branch-face
  '((((class color) (background dark))
     (:foreground "white" :weight bold))
    (((class color) (background light))
     (:foreground "black" :weight bold)))
  "Face used to highlight active jump-tree branch in visualizer."
  :group 'jump-tree)

(defface jump-tree-visualizer-register-face
  '((((class color)) :foreground "yellow"))
  "Face used to highlight jump-tree nodes saved to a register
in visualizer."
  :group 'jump-tree)

(defvar jump-tree-visualizer-parent-buffer nil
  "Parent buffer in visualizer.")

(defvar jump-tree-visualizer-parent-mtime nil
  "Store modification time of parent buffer's file, if any.")

(defvar jump-tree-visualizer-spacing nil
  "Store current horizontal spacing needed for drawing jump-tree.")

(defsubst jump-tree-visualizer-calculate-spacing ()
  "Calculate horizontal spacing required for drawing tree with current settings."
  (if jump-tree-visualizer-timestamps
      (if jump-tree-visualizer-relative-timestamps 9 13)
    3))

;; holds node that was current when visualizer was invoked
(defvar jump-tree-visualizer-initial-node nil)

;; holds currently selected node in visualizer selection mode
(defvar jump-tree-visualizer-selected-node nil)

;; used to store nodes at edge of currently drawn portion of tree
(defvar jump-tree-visualizer-needs-extending-down nil)
(defvar jump-tree-visualizer-needs-extending-up nil)

;; dynamically bound to t when jump-preving from visualizer, to inhibit
;; `jump-tree-kill-visualizer' hook function in parent buffer
(defvar jump-tree-inhibit-kill-visualizer nil)

;; can be let-bound to a face name, used in drawing functions
(defvar jump-tree-insert-face nil)

;; visualizer buffer names
(defconst jump-tree-visualizer-buffer-name " *jump-tree*")


;;; =================================================================
;;;                          Default keymaps

(defvar jump-tree-visualizer-mode-map nil
  "Keymap used in jump-tree visualizer.")

(unless jump-tree-visualizer-mode-map
  (let ((map (make-sparse-keymap)))
    ;; vertical motion keys jump-prev/jump-next
    (define-key map [remap previous-line] 'jump-tree-visualize-jump-prev)
    (define-key map [remap next-line] 'jump-tree-visualize-jump-next)
    (define-key map [up] 'jump-tree-visualize-jump-prev)
    (define-key map "p" 'jump-tree-visualize-jump-prev)
    (define-key map "\C-p" 'jump-tree-visualize-jump-prev)
    (define-key map [down] 'jump-tree-visualize-jump-next)
    (define-key map "n" 'jump-tree-visualize-jump-next)
    (define-key map "\C-n" 'jump-tree-visualize-jump-next)
    ;; horizontal motion keys switch branch
    (define-key map [remap forward-char]
      'jump-tree-visualize-switch-branch-right)
    (define-key map [remap backward-char]
      'jump-tree-visualize-switch-branch-left)
    (define-key map [right] 'jump-tree-visualize-switch-branch-right)
    (define-key map "f" 'jump-tree-visualize-switch-branch-right)
    (define-key map "\C-f" 'jump-tree-visualize-switch-branch-right)
    (define-key map [left] 'jump-tree-visualize-switch-branch-left)
    (define-key map "b" 'jump-tree-visualize-switch-branch-left)
    (define-key map "\C-b" 'jump-tree-visualize-switch-branch-left)
    ;; paragraph motion keys jump-prev/jump-next to significant points in tree
    (define-key map [remap backward-paragraph] 'jump-tree-visualize-jump-prev-to-x)
    (define-key map "\M-{" 'jump-tree-visualize-jump-prev-to-x)
    (define-key map [C-up] 'jump-tree-visualize-jump-prev-to-x)
    ;; mouse sets buffer state to node at click
    (define-key map [mouse-1] 'jump-tree-visualizer-mouse-set)
    ;; toggle selection mode
    (define-key map "s" 'jump-tree-visualizer-selection-mode)
    ;; horizontal scrolling may be needed if the tree is very wide
    (define-key map "," 'jump-tree-visualizer-scroll-left)
    (define-key map "." 'jump-tree-visualizer-scroll-right)
    (define-key map "<" 'jump-tree-visualizer-scroll-left)
    (define-key map ">" 'jump-tree-visualizer-scroll-right)
    ;; vertical scrolling may be needed if the tree is very tall
    (define-key map [next] 'jump-tree-visualizer-scroll-up)
    (define-key map [prior] 'jump-tree-visualizer-scroll-down)
    ;; toggle timestamp
    (define-key map "t" 'jump-tree-visualizer-toggle-timestamps)
    ;; quit/abort visualizer
    (define-key map "q" 'jump-tree-visualizer-quit)
    (define-key map "\C-q" 'jump-tree-visualizer-abort)
    ;; set keymap
    (setq jump-tree-visualizer-mode-map map)))

(defvar jump-tree-visualizer-selection-mode-map nil
  "Keymap used in jump-tree visualizer selection mode.")

(unless jump-tree-visualizer-selection-mode-map
  (let ((map (make-sparse-keymap)))
    ;; vertical motion keys move up and down tree
    (define-key map [remap previous-line]
      'jump-tree-visualizer-select-previous)
    (define-key map [remap next-line]
      'jump-tree-visualizer-select-next)
    (define-key map [up] 'jump-tree-visualizer-select-previous)
    (define-key map "p" 'jump-tree-visualizer-select-previous)
    (define-key map "\C-p" 'jump-tree-visualizer-select-previous)
    (define-key map [down] 'jump-tree-visualizer-select-next)
    (define-key map "n" 'jump-tree-visualizer-select-next)
    (define-key map "\C-n" 'jump-tree-visualizer-select-next)
    ;; vertical scroll keys move up and down quickly
    (define-key map [next]
      (lambda () (interactive) (jump-tree-visualizer-select-next 10)))
    (define-key map [prior]
      (lambda () (interactive) (jump-tree-visualizer-select-previous 10)))
    ;; horizontal motion keys move to left and right siblings
    (define-key map [remap forward-char] 'jump-tree-visualizer-select-right)
    (define-key map [remap backward-char] 'jump-tree-visualizer-select-left)
    (define-key map [right] 'jump-tree-visualizer-select-right)
    (define-key map "f" 'jump-tree-visualizer-select-right)
    (define-key map "\C-f" 'jump-tree-visualizer-select-right)
    (define-key map [left] 'jump-tree-visualizer-select-left)
    (define-key map "b" 'jump-tree-visualizer-select-left)
    (define-key map "\C-b" 'jump-tree-visualizer-select-left)
    ;; horizontal scroll keys move left or right quickly
    (define-key map ","
      (lambda () (interactive) (jump-tree-visualizer-select-left 10)))
    (define-key map "."
      (lambda () (interactive) (jump-tree-visualizer-select-right 10)))
    (define-key map "<"
      (lambda () (interactive) (jump-tree-visualizer-select-left 10)))
    (define-key map ">"
      (lambda () (interactive) (jump-tree-visualizer-select-right 10)))
    ;; <enter> sets buffer state to node at point
    (define-key map "\r" 'jump-tree-visualizer-set)
    ;; mouse selects node at click
    (define-key map [mouse-1] 'jump-tree-visualizer-mouse-select)
    ;; toggle timestamp
    (define-key map "t" 'jump-tree-visualizer-toggle-timestamps)
    ;; set keymap
    (setq jump-tree-visualizer-selection-mode-map map)))


;;; =====================================================================
;;;                     jump-tree data structure
(defstruct
    (jump-tree-visualizer-data
     (:type vector)   ; create unnamed struct
     (:constructor nil)
     (:constructor jump-tree-make-visualizer-data
                   (&optional lwidth cwidth rwidth marker))
     (:copier nil))
  lwidth cwidth rwidth marker)

(defmacro jump-tree-visualizer-data-p (v)
  "Check V is whether a `jump-tree-make-visualizer-data'."
  (let ((len (length (jump-tree-make-visualizer-data))))
    `(and (vectorp ,v) (= (length ,v) ,len))))

(defun jump-tree-node-clear-visualizer-data (node)
  "Clear the data in NODE's :visualizer field."
  (let ((plist (jump-tree-node-meta-data node)))
    (if (eq (car plist) :visualizer)
        (setf (jump-tree-node-meta-data node) (nthcdr 2 plist))
      (while (and plist (not (eq (cadr plist) :visualizer)))
        (setq plist (cdr plist)))
      (if plist (setcdr plist (nthcdr 3 plist))))))

(defmacro jump-tree-node-lwidth (node)
  "Fetch LWIDTH data from NODE's meta-data field :visualizer."
  `(let ((v (plist-get (jump-tree-node-meta-data ,node) :visualizer)))
     (when (jump-tree-visualizer-data-p v)
       (jump-tree-visualizer-data-lwidth v))))

(defmacro jump-tree-node-cwidth (node)
  "Fetch CWIDTH data from NODE's meta-data field :visualizer."
  `(let ((v (plist-get (jump-tree-node-meta-data ,node) :visualizer)))
     (when (jump-tree-visualizer-data-p v)
       (jump-tree-visualizer-data-cwidth v))))

(defmacro jump-tree-node-rwidth (node)
  "Fetch RWIDTH data from NODE's meta-data field :visualizer."
  `(let ((v (plist-get (jump-tree-node-meta-data ,node) :visualizer)))
     (when (jump-tree-visualizer-data-p v)
       (jump-tree-visualizer-data-rwidth v))))

(defmacro jump-tree-node-marker (node)
  "Fetch MARKER data from NODE's meta-data field :visualizer."
  `(let ((v (plist-get (jump-tree-node-meta-data ,node) :visualizer)))
     (when (jump-tree-visualizer-data-p v)
       (jump-tree-visualizer-data-marker v))))

(defsetf jump-tree-node-lwidth (node) (val)
  `(let ((v (plist-get (jump-tree-node-meta-data ,node) :visualizer)))
     (unless (jump-tree-visualizer-data-p v)
       (setf (jump-tree-node-meta-data ,node)
             (plist-put (jump-tree-node-meta-data ,node) :visualizer
                        (setq v (jump-tree-make-visualizer-data)))))
     (setf (jump-tree-visualizer-data-lwidth v) ,val)))

(defsetf jump-tree-node-cwidth (node) (val)
  `(let ((v (plist-get (jump-tree-node-meta-data ,node) :visualizer)))
     (unless (jump-tree-visualizer-data-p v)
       (setf (jump-tree-node-meta-data ,node)
             (plist-put (jump-tree-node-meta-data ,node) :visualizer
                        (setq v (jump-tree-make-visualizer-data)))))
     (setf (jump-tree-visualizer-data-cwidth v) ,val)))

(defsetf jump-tree-node-rwidth (node) (val)
  `(let ((v (plist-get (jump-tree-node-meta-data ,node) :visualizer)))
     (unless (jump-tree-visualizer-data-p v)
       (setf (jump-tree-node-meta-data ,node)
             (plist-put (jump-tree-node-meta-data ,node) :visualizer
                        (setq v (jump-tree-make-visualizer-data)))))
     (setf (jump-tree-visualizer-data-rwidth v) ,val)))

(defsetf jump-tree-node-marker (node) (val)
  `(let ((v (plist-get (jump-tree-node-meta-data ,node) :visualizer)))
     (unless (jump-tree-visualizer-data-p v)
       (setf (jump-tree-node-meta-data ,node)
             (plist-put (jump-tree-node-meta-data ,node) :visualizer
                        (setq v (jump-tree-make-visualizer-data)))))
     (setf (jump-tree-visualizer-data-marker v) ,val)))


;;; =====================================================================
;;;                   Visualizer utility functions

(defun jump-tree-compute-widths (node)
  "Recursively compute widths for nodes below NODE."
  (let ((stack (list node))
        res)
    (while stack
      ;; try to compute widths for node at top of stack
      (if (jump-tree-node-p
           (setq res (jump-tree-node-compute-widths (car stack))))
          ;; if computation fails, it returns a node whose widths still need
          ;; computing, which we push onto the stack
          (push res stack)
        ;; otherwise, store widths and remove it from stack
        (setf (jump-tree-node-lwidth (car stack)) (aref res 0)
              (jump-tree-node-cwidth (car stack)) (aref res 1)
              (jump-tree-node-rwidth (car stack)) (aref res 2))
        (pop stack)))))

(defun jump-tree-node-compute-widths (node)
  "Compute NODE's left-, centre-, and right-subtree widths.
Returns widths (in a vector) if successful.  Otherwise, returns a node whose
widths need calculating before NODE's can be calculated."
  (let ((num-children (length (jump-tree-node-next node)))
        (lwidth 0) (cwidth 0) (rwidth 0) p)
    (catch 'need-widths
      (cond
       ;; leaf nodes have 0 width
       ((= 0 num-children)
        (setf cwidth 1
              (jump-tree-node-lwidth node) 0
              (jump-tree-node-cwidth node) 1
              (jump-tree-node-rwidth node) 0))

       ;; odd number of children
       ((= (mod num-children 2) 1)
        (setq p (jump-tree-node-next node))
        ;; compute left-width
        (dotimes (i (/ num-children 2))
          (if (jump-tree-node-lwidth (car p))
              (incf lwidth (+ (jump-tree-node-lwidth (car p))
                              (jump-tree-node-cwidth (car p))
                              (jump-tree-node-rwidth (car p))))
            ;; if child's widths haven't been computed, return that child
            (throw 'need-widths (car p)))
          (setq p (cdr p)))
        (if (jump-tree-node-lwidth (car p))
            (incf lwidth (jump-tree-node-lwidth (car p)))
          (throw 'need-widths (car p)))
        ;; centre-width is inherited from middle child
        (setf cwidth (jump-tree-node-cwidth (car p)))
        ;; compute right-width
        (incf rwidth (jump-tree-node-rwidth (car p)))
        (setq p (cdr p))
        (dotimes (i (/ num-children 2))
          (if (jump-tree-node-lwidth (car p))
              (incf rwidth (+ (jump-tree-node-lwidth (car p))
                              (jump-tree-node-cwidth (car p))
                              (jump-tree-node-rwidth (car p))))
            (throw 'need-widths (car p)))
          (setq p (cdr p))))

       ;; even number of children
       (t
        (setq p (jump-tree-node-next node))
        ;; compute left-width
        (dotimes (i (/ num-children 2))
          (if (jump-tree-node-lwidth (car p))
              (incf lwidth (+ (jump-tree-node-lwidth (car p))
                              (jump-tree-node-cwidth (car p))
                              (jump-tree-node-rwidth (car p))))
            (throw 'need-widths (car p)))
          (setq p (cdr p)))
        ;; centre-width is 0 when number of children is even
        (setq cwidth 0)
        ;; compute right-width
        (dotimes (i (/ num-children 2))
          (if (jump-tree-node-lwidth (car p))
              (incf rwidth (+ (jump-tree-node-lwidth (car p))
                              (jump-tree-node-cwidth (car p))
                              (jump-tree-node-rwidth (car p))))
            (throw 'need-widths (car p)))
          (setq p (cdr p)))))

      ;; return left-, centre- and right-widths
      (vector lwidth cwidth rwidth))))

(defun jump-tree-clear-visualizer-data (tree)
  "Clear visualizer data of TREE."
  (jump-tree-mapc
   (lambda (n) (jump-tree-node-clear-visualizer-data n))
   (jump-tree-root tree)))


;;; =====================================================================
;;;                    Visualizer drawing functions
(defun jump-tree-visualize ()
  "Visualize the current buffer's position tree."
  (interactive "*")
  (unless jump-tree-mode
    (user-error "`jump-tree-mode' not enabled in buffer"))
  (deactivate-mark)
  ;; throw error if position is disabled in buffer
  (when (eq jump-tree-pos-list t)
    (user-error "No position information in this buffer"))
  ;; transfer entries accumulated in `jump-tree-pos-list' to `jump-tree-pos-tree'
  (jump-tree-pos-list-transfer-to-tree)
  ;; add hook to kill visualizer buffer if original buffer is changed
  (add-hook 'before-change-functions 'jump-tree-kill-visualizer nil t)
  ;; prepare *jump-tree* buffer, then draw tree in it
  (let ((jump-tree jump-tree-pos-tree)
        (buff (current-buffer))
        (display-buffer-mark-dedicated 'soft))
    (switch-to-buffer-other-window
     (get-buffer-create jump-tree-visualizer-buffer-name))
    (setq jump-tree-visualizer-parent-buffer buff)
    (setq jump-tree-visualizer-parent-mtime
          (and (buffer-file-name buff)
               (nth 5 (file-attributes (buffer-file-name buff)))))
    (setq jump-tree-visualizer-initial-node (jump-tree-current jump-tree))
    (setq jump-tree-visualizer-spacing
          (jump-tree-visualizer-calculate-spacing))
    (make-local-variable 'jump-tree-visualizer-timestamps)
    (setq jump-tree-pos-tree jump-tree)
    (jump-tree-visualizer-mode)
    ;; FIXME; don't know why `jump-tree-visualizer-mode' clears this
    (setq jump-tree-pos-tree jump-tree)
    (set (make-local-variable 'jump-tree-visualizer-lazy-drawing)
         (or (eq jump-tree-visualizer-lazy-drawing t)
             (and (numberp jump-tree-visualizer-lazy-drawing)
                  (>= (jump-tree-count jump-tree)
                      jump-tree-visualizer-lazy-drawing))))
    (let ((inhibit-read-only t)) (jump-tree-draw-tree jump-tree))))

(defun jump-tree-kill-visualizer ()
  "Kill visualizer.
Added to `before-change-functions' hook of original buffer when
visualizer is invoked."
  (unless (or jump-tree-inhibit-kill-visualizer
              (null (get-buffer jump-tree-visualizer-buffer-name)))
    (with-current-buffer jump-tree-visualizer-buffer-name
      (jump-tree-visualizer-quit))))

(defun jump-tree-draw-tree (jump-tree)
  "Draw JUMP-TREE in current buffer starting from root."
  (let ((node (if jump-tree-visualizer-lazy-drawing
                  (jump-tree-current jump-tree)
                (jump-tree-root jump-tree))))
    (erase-buffer)
    (setq jump-tree-visualizer-needs-extending-down nil
          jump-tree-visualizer-needs-extending-up nil)
    (jump-tree-clear-visualizer-data jump-tree)
    (jump-tree-compute-widths node)
    ;; lazy drawing starts vertically centred and displaced horizontally to
    ;; the left (window-width/4), since trees will typically grow right
    (if jump-tree-visualizer-lazy-drawing
        (progn
          (jump-tree-move-down (/ (window-height) 2))
          (jump-tree-move-forward (max 2 (/ (window-width) 4)))) ; left margin
      ;; non-lazy drawing starts in centre at top of buffer
      (jump-tree-move-down 1)  ; top margin
      (jump-tree-move-forward
       (max (/ (window-width) 2)
            (+ (jump-tree-node-char-lwidth node)
               ;; add space for left part of left-most time-stamp
               (if jump-tree-visualizer-timestamps
                   (/ (- jump-tree-visualizer-spacing 4) 2)
                 0)
               2))))  ; left margin
    ;; link starting node to its representation in visualizer
    (setf (jump-tree-node-marker node) (make-marker))
    (set-marker-insertion-type (jump-tree-node-marker node) nil)
    (move-marker (jump-tree-node-marker node) (point))
    ;; draw jump-tree
    (let ((jump-tree-insert-face 'jump-tree-visualizer-default-face)
          node-list)
      (if (not jump-tree-visualizer-lazy-drawing)
          (jump-tree-extend-down node t)
        (jump-tree-extend-down node)
        (jump-tree-extend-up node)
        (setq node-list jump-tree-visualizer-needs-extending-down
              jump-tree-visualizer-needs-extending-down nil)
        (while node-list (jump-tree-extend-down (pop node-list)))))
    ;; highlight active branch
    (let ((jump-tree-insert-face 'jump-tree-visualizer-active-branch-face))
      (jump-tree-highlight-active-branch
       (or jump-tree-visualizer-needs-extending-up
           (jump-tree-root jump-tree))))
    ;; highlight current node
    (jump-tree-draw-node (jump-tree-current jump-tree) 'current)))

(defun jump-tree-extend-down (node &optional bottom)
  "Extend tree downwards starting from NODE and point.
If BOTTOM is t,extend all the way down to the leaves.
If BOTTOM is a node, extend down as far as that node.
If BOTTOM is an integer, extend down as far as that line.
Otherwise, only extend visible portion of tree.  NODE is assumed to
already have a node marker.  Returns non-nil if anything was actually
extended."
  (let ((extended nil)
        (cur-stack (list node))
        next-stack)
    ;; don't bother extending if BOTTOM specifies an already-drawn node
    (unless (and (jump-tree-node-p bottom) (jump-tree-node-marker bottom))
      ;; draw nodes layer by layer
      (while (or cur-stack
                 (prog1 (setq cur-stack next-stack)
                   (setq next-stack nil)))
        (setq node (pop cur-stack))
        ;; if node is within range being drawn...
        (if (or (eq bottom t)
                (and (jump-tree-node-p bottom)
                     (not (eq (jump-tree-node-previous node) bottom)))
                (and (integerp bottom)
                     (>= bottom (line-number-at-pos
                                 (jump-tree-node-marker node))))
                (and (null bottom)
                     (pos-visible-in-window-p (jump-tree-node-marker node)
                                              nil t)))
            ;; ...draw one layer of node's subtree (if not already drawn)
            (progn
              (unless (and (jump-tree-node-next node)
                           (jump-tree-node-marker
                            (nth (jump-tree-node-branch node)
                                 (jump-tree-node-next node))))
                (goto-char (jump-tree-node-marker node))
                (jump-tree-draw-subtree node)
                (setq extended t))
              (setq next-stack
                    (append (jump-tree-node-next node) next-stack)))
          ;; ...otherwise, postpone drawing until later
          (push node jump-tree-visualizer-needs-extending-down))))
    extended))

(defun jump-tree-extend-up (node &optional top)
  "Extend tree upwards starting from NODE.
If TOP is t, extend all the way to root.  If TOP is a node, extend up
as far as that node.  If TOP is an integer, extend up as far as that line.
Otherwise, only extend visible portion of tree.  NODE is assumed to already
have a node marker.  Returns non-nil if anything was actually extended."
  (let ((extended nil) parent)
    ;; don't bother extending if TOP specifies an already-drawn node
    (unless (and (jump-tree-node-p top) (jump-tree-node-marker top))
      (while node
        (setq parent (jump-tree-node-previous node))
        ;; if we haven't reached root...
        (if parent
            ;; ...and node is within range being drawn...
            (if (or (eq top t)
                    (and (jump-tree-node-p top) (not (eq node top)))
                    (and (integerp top)
                         (< top (line-number-at-pos
                                 (jump-tree-node-marker node))))
                    (and (null top)
                         ;; NOTE: we check point in case window-start is outdated
                         (< (min (line-number-at-pos (point))
                                 (line-number-at-pos (window-start)))
                            (line-number-at-pos
                             (jump-tree-node-marker node)))))
                ;; ...and it hasn't already been drawn
                (when (not (jump-tree-node-marker parent))
                  ;; link parent node to its representation in visualizer
                  (jump-tree-compute-widths parent)
                  (jump-tree-move-to-parent node)
                  (setf (jump-tree-node-marker parent) (make-marker))
                  (set-marker-insertion-type
                   (jump-tree-node-marker parent) nil)
                  (move-marker (jump-tree-node-marker parent) (point))
                  ;; draw subtree beneath parent
                  (setq jump-tree-visualizer-needs-extending-down
                        (nconc (delq node (jump-tree-draw-subtree parent))
                               jump-tree-visualizer-needs-extending-down))
                  (setq extended t))
              ;; ...otherwise, postpone drawing for later and exit
              (setq jump-tree-visualizer-needs-extending-up (when parent node)
                    parent nil))
          ;; if we've reached root, stop extending and add top margin
          (setq jump-tree-visualizer-needs-extending-up nil)
          (goto-char (jump-tree-node-marker node))
          (jump-tree-move-up 1)  ; top margin
          (delete-region (point-min) (line-beginning-position)))
        ;; next iteration
        (setq node parent)))
    extended))

(defun jump-tree-expand-down (from &optional to)
  "Expand tree downwards.
FROM is the node to start expanding from.  Stop expanding at TO if specified.
Otherwise, just expand visible portion of tree and highlight active branch
from FROM."
  (when jump-tree-visualizer-needs-extending-down
    (let ((inhibit-read-only t)
          node-list extended)
      ;; extend down as far as TO node
      (when to
        (setq extended (jump-tree-extend-down from to))
        (goto-char (jump-tree-node-marker to))
        (redisplay t))  ; force redisplay to scroll buffer if necessary
      ;; extend visible portion of tree downwards
      (setq node-list jump-tree-visualizer-needs-extending-down
            jump-tree-visualizer-needs-extending-down nil)
      (when node-list
        (dolist (n node-list)
          (when (jump-tree-extend-down n) (setq extended t)))
        ;; highlight active branch in newly-extended-down portion, if any
        (when extended
          (let ((jump-tree-insert-face
                 'jump-tree-visualizer-active-branch-face))
            (jump-tree-highlight-active-branch from)))))))

(defun jump-tree-expand-up (from &optional to)
  "Expand tree upwards.
FROM is the node to start expanding from, TO is the node to stop expanding at.
If TO node isn't specified, just expand visible portion of tree and highlight
active branch down to FROM."
  (when jump-tree-visualizer-needs-extending-up
    (let ((inhibit-read-only t)
          extended node-list)
      ;; extend up as far as TO node
      (when to
        (setq extended (jump-tree-extend-up from to))
        (goto-char (jump-tree-node-marker to))
        ;; simulate auto-scrolling if close to top of buffer
        (when (<= (line-number-at-pos (point)) scroll-margin)
          (jump-tree-move-up (if (= scroll-conservatively 0)
                                 (/ (window-height) 2) 3))
          (when (jump-tree-extend-up to) (setq extended t))
          (goto-char (jump-tree-node-marker to))
          (unless (= scroll-conservatively 0) (recenter scroll-margin))))
      ;; extend visible portion of tree upwards
      (and jump-tree-visualizer-needs-extending-up
           (jump-tree-extend-up jump-tree-visualizer-needs-extending-up)
           (setq extended t))
      ;; extend visible portion of tree downwards
      (setq node-list jump-tree-visualizer-needs-extending-down
            jump-tree-visualizer-needs-extending-down nil)
      (dolist (n node-list) (jump-tree-extend-down n))
      ;; highlight active branch in newly-extended-up portion, if any
      (when extended
        (let ((jump-tree-insert-face
               'jump-tree-visualizer-active-branch-face))
          (jump-tree-highlight-active-branch
           (or jump-tree-visualizer-needs-extending-up
               (jump-tree-root jump-tree-pos-tree))
           from))))))

(defun jump-tree-highlight-active-branch (node &optional end)
  "Draw highlighted active branch below NODE in current buffer.
Stop highlighting at END node if specified."
  (let ((stack (list node)))
    ;; draw active branch
    (while stack
      (setq node (pop stack))
      (unless (or (eq node end)
                  (memq node jump-tree-visualizer-needs-extending-down))
        (goto-char (jump-tree-node-marker node))
        (setq node (jump-tree-draw-subtree node 'active)
              stack (nconc stack node))))))

(defun jump-tree-draw-node (node &optional current)
  "Draw symbol representing NODE in visualizer.
If CURRENT is non-nil, node is current node."
  (goto-char (jump-tree-node-marker node))
  (when jump-tree-visualizer-timestamps
    (jump-tree-move-backward (/ jump-tree-visualizer-spacing 2)))
  (let* ((jump-tree-insert-face (and jump-tree-insert-face
                                     (or (and (consp jump-tree-insert-face)
                                              jump-tree-insert-face)
                                         (list jump-tree-insert-face))))
         (register (jump-tree-node-register node))
         node-string)
    ;; check node's register (if any) still stores appropriate jump-tree state
    (unless (and register
                 (jump-tree-register-data-p
                  (registerv-data (get-register register)))
                 (eq node (jump-tree-register-data-node
                           (registerv-data (get-register register)))))
      (setq register nil))
    ;; represent node by different symbols, depending on whether it's the
    ;; current node, is saved in a register
    ;; buffer
    (setq node-string
          (cond
           (jump-tree-visualizer-timestamps
            (jump-tree-timestamp-to-string
             (jump-tree-node-timestamp node)
             jump-tree-visualizer-relative-timestamps
             current register))
           (register (char-to-string register))
           (current "x")
           (t "o"))
          jump-tree-insert-face
          (nconc
           (cond
            (current    '(jump-tree-visualizer-current-face))
            (register   '(jump-tree-visualizer-register-face)))
           jump-tree-insert-face))
    ;; draw node and link it to its representation in visualizer
    (jump-tree-insert node-string)
    (jump-tree-move-backward (if jump-tree-visualizer-timestamps
                                 (1+ (/ jump-tree-visualizer-spacing 2))
                               1))
    (move-marker (jump-tree-node-marker node) (point))
    (put-text-property (point) (1+ (point)) 'jump-tree-node node)))

(defun jump-tree-draw-subtree (node &optional active-branch)
  "Draw subtree rooted at NODE.  The subtree will start from point.
If ACTIVE-BRANCH is non-nil, just draw active branch below NODE.  Returns
list of nodes below NODE."
  (let ((num-children (length (jump-tree-node-next node)))
        node-list pos trunk-pos n)
    ;; draw node itself
    (jump-tree-draw-node node)
    (cond
     ;; if we're at a leaf node, we're done
     ((= num-children 0))
     ;; if node has only one child, draw it (not strictly necessary to deal
     ;; with this case separately, but as it's by far the most common case
     ;; this makes the code clearer and more efficient)
     ((= num-children 1)
      (jump-tree-move-down 1)
      (jump-tree-insert ?|)
      (jump-tree-move-backward 1)
      (jump-tree-move-down 1)
      (jump-tree-insert ?|)
      (jump-tree-move-backward 1)
      (jump-tree-move-down 1)
      (setq n (car (jump-tree-node-next node)))
      ;; link next node to its representation in visualizer
      (unless (markerp (jump-tree-node-marker n))
        (setf (jump-tree-node-marker n) (make-marker))
        (set-marker-insertion-type (jump-tree-node-marker n) nil))
      (move-marker (jump-tree-node-marker n) (point))
      ;; add next node to list of nodes to draw next
      (push n node-list))
     ;; if node has multiple children, draw branches
     (t
      (jump-tree-move-down 1)
      (jump-tree-insert ?|)
      (jump-tree-move-backward 1)
      (move-marker (setq trunk-pos (make-marker)) (point))
      ;; left subtrees
      (jump-tree-move-backward
       (- (jump-tree-node-char-lwidth node)
          (jump-tree-node-char-lwidth
           (car (jump-tree-node-next node)))))
      (move-marker (setq pos (make-marker)) (point))
      (setq n (cons nil (jump-tree-node-next node)))
      (dotimes (i (/ num-children 2))
        (setq n (cdr n))
        (when (or (null active-branch)
                  (eq (car n)
                      (nth (jump-tree-node-branch node)
                           (jump-tree-node-next node))))
          (jump-tree-move-forward 2)
          (jump-tree-insert ?_ (- trunk-pos pos 2))
          (goto-char pos)
          (jump-tree-move-forward 1)
          (jump-tree-move-down 1)
          (jump-tree-insert ?/)
          (jump-tree-move-backward 2)
          (jump-tree-move-down 1)
          ;; link node to its representation in visualizer
          (unless (markerp (jump-tree-node-marker (car n)))
            (setf (jump-tree-node-marker (car n)) (make-marker))
            (set-marker-insertion-type (jump-tree-node-marker (car n)) nil))
          (move-marker (jump-tree-node-marker (car n)) (point))
          ;; add node to list of nodes to draw next
          (push (car n) node-list))
        (goto-char pos)
        (jump-tree-move-forward
         (+ (jump-tree-node-char-rwidth (car n))
            (jump-tree-node-char-lwidth (cadr n))
            jump-tree-visualizer-spacing 1))
        (move-marker pos (point)))
      ;; middle subtree (only when number of children is odd)
      (when (= (mod num-children 2) 1)
        (setq n (cdr n))
        (when (or (null active-branch)
                  (eq (car n)
                      (nth (jump-tree-node-branch node)
                           (jump-tree-node-next node))))
          (jump-tree-move-down 1)
          (jump-tree-insert ?|)
          (jump-tree-move-backward 1)
          (jump-tree-move-down 1)
          ;; link node to its representation in visualizer
          (unless (markerp (jump-tree-node-marker (car n)))
            (setf (jump-tree-node-marker (car n)) (make-marker))
            (set-marker-insertion-type (jump-tree-node-marker (car n)) nil))
          (move-marker (jump-tree-node-marker (car n)) (point))
          ;; add node to list of nodes to draw next
          (push (car n) node-list))
        (goto-char pos)
        (jump-tree-move-forward
         (+ (jump-tree-node-char-rwidth (car n))
            (if (cadr n) (jump-tree-node-char-lwidth (cadr n)) 0)
            jump-tree-visualizer-spacing 1))
        (move-marker pos (point)))
      ;; right subtrees
      (move-marker trunk-pos (1+ trunk-pos))
      (dotimes (i (/ num-children 2))
        (setq n (cdr n))
        (when (or (null active-branch)
                  (eq (car n)
                      (nth (jump-tree-node-branch node)
                           (jump-tree-node-next node))))
          (goto-char trunk-pos)
          (jump-tree-insert ?_ (- pos trunk-pos 1))
          (goto-char pos)
          (jump-tree-move-backward 1)
          (jump-tree-move-down 1)
          (jump-tree-insert ?\\)
          (jump-tree-move-down 1)
          ;; link node to its representation in visualizer
          (unless (markerp (jump-tree-node-marker (car n)))
            (setf (jump-tree-node-marker (car n)) (make-marker))
            (set-marker-insertion-type (jump-tree-node-marker (car n)) nil))
          (move-marker (jump-tree-node-marker (car n)) (point))
          ;; add node to list of nodes to draw next
          (push (car n) node-list))
        (when (cdr n)
          (goto-char pos)
          (jump-tree-move-forward
           (+ (jump-tree-node-char-rwidth (car n))
              (if (cadr n) (jump-tree-node-char-lwidth (cadr n)) 0)
              jump-tree-visualizer-spacing 1))
          (move-marker pos (point))))
      ))
    ;; return list of nodes to draw next
    (nreverse node-list)))

(defun jump-tree-node-char-lwidth (node)
  "Return left-width of NODE measured in characters."
  (if (= (length (jump-tree-node-next node)) 0) 0
    (- (* (+ jump-tree-visualizer-spacing 1) (jump-tree-node-lwidth node))
       (if (= (jump-tree-node-cwidth node) 0)
           (1+ (/ jump-tree-visualizer-spacing 2)) 0))))

(defun jump-tree-node-char-rwidth (node)
  "Return right-width of NODE measured in characters."
  (if (= (length (jump-tree-node-next node)) 0) 0
    (- (* (+ jump-tree-visualizer-spacing 1) (jump-tree-node-rwidth node))
       (if (= (jump-tree-node-cwidth node) 0)
           (1+ (/ jump-tree-visualizer-spacing 2)) 0))))

(defun jump-tree-insert (str &optional arg)
  "Insert character or string STR ARG times.
Overwriting and using `jump-tree-insert-face'."
  (unless arg (setq arg 1))
  (when (characterp str)
    (setq str (make-string arg str))
    (setq arg 1))
  (dotimes (i arg) (insert str))
  (setq arg (* arg (length str)))
  (jump-tree-move-forward arg)
  ;; make sure mark isn't active, otherwise `backward-delete-char' might
  ;; delete region instead of single char if transient-mark-mode is enabled
  (setq mark-active nil)
  (backward-delete-char arg)
  (when jump-tree-insert-face
    (put-text-property (- (point) arg) (point) 'face jump-tree-insert-face)))

(defun jump-tree-move-down (&optional arg)
  "Move down, extending buffer if necessary.
A numeric ARG serves as a repeat count."
  (let ((row (line-number-at-pos))
        (col (current-column))
        line)
    (unless arg (setq arg 1))
    (forward-line arg)
    (setq line (line-number-at-pos))
    ;; if buffer doesn't have enough lines, add some
    (when (/= line (+ row arg))
      (cond
       ((< arg 0)
        (insert (make-string (- line row arg) ?\n))
        (forward-line (+ arg (- row line))))
       (t (insert (make-string (- arg (- line row)) ?\n)))))
    (jump-tree-move-forward col)))

(defun jump-tree-move-up (&optional arg)
  "Move up, extending buffer if necessary.
A numeric ARG serves as a repeat count."
  (unless arg (setq arg 1))
  (jump-tree-move-down (- arg)))

(defun jump-tree-move-forward (&optional arg)
  "Move forward, extending buffer if necessary.
A numeric ARG serves as a repeat count."
  (unless arg (setq arg 1))
  (let (n)
    (cond
     ((>= arg 0)
      (setq n (- (line-end-position) (point)))
      (if (> n arg)
          (forward-char arg)
        (end-of-line)
        (insert (make-string (- arg n) ? ))))
     ((< arg 0)
      (setq arg (- arg))
      (setq n (- (point) (line-beginning-position)))
      (when (< (- n 2) arg)  ; -2 to create left-margin
        ;; no space left - shift entire buffer contents right!
        (let ((pos (move-marker (make-marker) (point))))
          (set-marker-insertion-type pos t)
          (goto-char (point-min))
          (while (not (eobp))
            (insert-before-markers (make-string (- arg -2 n) ? ))
            (forward-line 1))
          (goto-char pos)))
      (backward-char arg)))))

(defun jump-tree-move-backward (&optional arg)
  "Move backward, extending buffer if necessary.
A numeric ARG serves as a repeat count."
  (unless arg (setq arg 1))
  (jump-tree-move-forward (- arg)))

(defun jump-tree-move-to-parent (node)
  "Move to position of parent of NODE, extending buffer if necessary."
  (let* ((parent (jump-tree-node-previous node))
         (n (jump-tree-node-next parent))
         (l (length n)) p)
    (goto-char (jump-tree-node-marker node))
    (unless (= l 1)
      ;; move horizontally
      (setq p (jump-tree-index node n))
      (cond
       ;; node in centre subtree: no horizontal movement
       ((and (= (mod l 2) 1) (= p (/ l 2))))
       ;; node in left subtree: move right
       ((< p (/ l 2))
        (setq n (nthcdr p n))
        (jump-tree-move-forward
         (+ (jump-tree-node-char-rwidth (car n))
            (/ jump-tree-visualizer-spacing 2) 1))
        (dotimes (i (- (/ l 2) p 1))
          (setq n (cdr n))
          (jump-tree-move-forward
           (+ (jump-tree-node-char-lwidth (car n))
              (jump-tree-node-char-rwidth (car n))
              jump-tree-visualizer-spacing 1)))
        (when (= (mod l 2) 1)
          (setq n (cdr n))
          (jump-tree-move-forward
           (+ (jump-tree-node-char-lwidth (car n))
              (/ jump-tree-visualizer-spacing 2) 1))))
       (t ;; node in right subtree: move left
        (setq n (nthcdr (/ l 2) n))
        (when (= (mod l 2) 1)
          (jump-tree-move-backward
           (+ (jump-tree-node-char-rwidth (car n))
              (/ jump-tree-visualizer-spacing 2) 1))
          (setq n (cdr n)))
        (dotimes (i (- p (/ l 2) (mod l 2)))
          (jump-tree-move-backward
           (+ (jump-tree-node-char-lwidth (car n))
              (jump-tree-node-char-rwidth (car n))
              jump-tree-visualizer-spacing 1))
          (setq n (cdr n)))
        (jump-tree-move-backward
         (+ (jump-tree-node-char-lwidth (car n))
            (/ jump-tree-visualizer-spacing 2) 1)))))
    ;; move vertically
    (jump-tree-move-up 3)))

(defun jump-tree-timestamp-to-string
    (timestamp &optional relative current register)
  "Convert TIMESTAMP to string (either absolute or RELATIVE time).
Indicating if it's the CURRENT node and/or has an associated REGISTER."
  (if relative
      ;; relative time
      (let ((time (floor (float-time
                          (subtract-time (current-time) timestamp))))
            n)
        (setq time
              ;; years
              (if (> (setq n (/ time 315360000)) 0)
                  (if (> n 999) "-ages" (format "-%dy" n))
                (setq time (% time 315360000))
                ;; days
                (if (> (setq n (/ time 86400)) 0)
                    (format "-%dd" n)
                  (setq time (% time 86400))
                  ;; hours
                  (if (> (setq n (/ time 3600)) 0)
                      (format "-%dh" n)
                    (setq time (% time 3600))
                    ;; mins
                    (if (> (setq n (/ time 60)) 0)
                        (format "-%dm" n)
                      ;; secs
                      (format "-%ds" (% time 60)))))))
        (setq time (concat
                    (if current "*" " ")
                    time
                    (if register (concat "[" (char-to-string register) "]")
                      "   ")))
        (setq n (length time))
        (if (< n 9)
            (concat (make-string (- 9 n) ? ) time)
          time))
    ;; absolute time
    (concat (if current " *" "  ")
            (format-time-string "%H:%M:%S" timestamp)
            (if register
                (concat "[" (char-to-string register) "]")
              "   "))))


;;; =====================================================================
;;;                        Visualizer commands
(define-derived-mode
  jump-tree-visualizer-mode special-mode "jump-tree-visualizer"
  "Major mode used in jump-tree visualizer.
The jump-tree visualizer can only be invoked from a buffer in
which `jump-tree-mode' is enabled. The visualizer displays the
position history tree graphically, and allows you to browse around
the position history, jump-preving or jump-nexting the corresponding changes in
the parent buffer.
Within the jump-tree visualizer, the following keys are available:
  \\{jump-tree-visualizer-mode-map}"
  :syntax-table nil
  :abbrev-table nil
  (setq truncate-lines t)
  (setq cursor-type nil)
  (setq jump-tree-visualizer-selected-node nil))

(defun jump-tree-visualize-jump-prev (&optional arg)
  "Jump to the previous position.
A numeric ARG serves as a repeat count."
  (interactive "p")
  (unless (eq major-mode 'jump-tree-visualizer-mode)
    (user-error "`jump-tree-mode' not enabled in buffer"))
  (let ((old (jump-tree-current jump-tree-pos-tree))
        current)
    ;; unhighlight old current node
    (let ((jump-tree-insert-face 'jump-tree-visualizer-active-branch-face)
          (inhibit-read-only t))
      (jump-tree-draw-node old))
    ;; position in parent buffer
    (setq jump-tree-visualizer-parent-buffer (jump-tree-node-buffer old))
    (switch-to-buffer-other-window jump-tree-visualizer-parent-buffer)
    (deactivate-mark)
    (unwind-protect
        (let ((jump-tree-inhibit-kill-visualizer t))
          (jump-tree-jump-prev-1 arg))
      (setq current (jump-tree-current jump-tree-pos-tree))
      (setq jump-tree-visualizer-parent-buffer (current-buffer))
      (switch-to-buffer-other-window jump-tree-visualizer-buffer-name)
      ;; when using lazy drawing, extend tree upwards as required
      (when jump-tree-visualizer-lazy-drawing
        (jump-tree-expand-up old current))
      ;; redraw the tree, jump-prev-1 may add new node.
      (let ((inhibit-read-only t)) (jump-tree-draw-tree jump-tree-pos-tree)))))

(defun jump-tree-visualize-jump-next (&optional arg)
  "Jump to the next position.
A numeric ARG serves as a repeat count."
  (interactive "p")
  (unless (eq major-mode 'jump-tree-visualizer-mode)
    (user-error "`jump-tree-mode' not enabled in buffer"))
  (let ((old (jump-tree-current jump-tree-pos-tree))
        current)
    ;; unhighlight old current node
    (let ((jump-tree-insert-face 'jump-tree-visualizer-active-branch-face)
          (inhibit-read-only t))
      (jump-tree-draw-node (jump-tree-current jump-tree-pos-tree)))
    ;; jump-next in parent buffer
    (switch-to-buffer-other-window jump-tree-visualizer-parent-buffer)
    (deactivate-mark)
    (unwind-protect
        (let ((jump-tree-inhibit-kill-visualizer t)) (jump-tree-jump-next-1 arg))
      (setq current (jump-tree-current jump-tree-pos-tree))
      (setq jump-tree-visualizer-parent-buffer (current-buffer))
      (switch-to-buffer-other-window jump-tree-visualizer-buffer-name)
      ;; when using lazy drawing, extend tree downwards as required
      (when jump-tree-visualizer-lazy-drawing
        (jump-tree-expand-down old current))
      ;; highlight new current node
      (let ((inhibit-read-only t)) (jump-tree-draw-node current 'current)))))

(defun jump-tree-visualize-switch-branch-right (arg)
  "Switch to next branch of the position tree.
This will affect which branch to descend when *jump-nexting* changes
using `jump-tree-jump-next' or `jump-tree-visualizer-jump-next'.
A numeric ARG serves as a repeat count."
  (interactive "p")
  (unless (eq major-mode 'jump-tree-visualizer-mode)
    (user-error "`jump-tree-mode' not enabled in buffer"))
  ;; un-highlight old active branch below current node
  (goto-char (jump-tree-node-marker (jump-tree-current jump-tree-pos-tree)))
  (let ((jump-tree-insert-face 'jump-tree-visualizer-default-face)
        (inhibit-read-only t))
    (jump-tree-highlight-active-branch (jump-tree-current jump-tree-pos-tree)))
  ;; increment branch
  (let ((branch (jump-tree-node-branch (jump-tree-current jump-tree-pos-tree))))
    (setf (jump-tree-node-branch (jump-tree-current jump-tree-pos-tree))
          (cond
           ((>= (+ branch arg) (jump-tree-num-branches))
            (1- (jump-tree-num-branches)))
           ((<= (+ branch arg) 0) 0)
           (t (+ branch arg))))
    (let ((inhibit-read-only t))
      ;; highlight new active branch below current node
      (goto-char (jump-tree-node-marker (jump-tree-current jump-tree-pos-tree)))
      (let ((jump-tree-insert-face 'jump-tree-visualizer-active-branch-face))
        (jump-tree-highlight-active-branch (jump-tree-current jump-tree-pos-tree)))
      ;; re-highlight current node
      (jump-tree-draw-node (jump-tree-current jump-tree-pos-tree) 'current))))

(defun jump-tree-visualize-switch-branch-left (arg)
  "Switch to previous branch of the position tree.
This will affect which branch to descend when *jump-nexting* changes
using `jump-tree-jump-next' or `jump-tree-visualizer-jump-next'.
A numeric ARG serves as a repeat count."
  (interactive "p")
  (jump-tree-visualize-switch-branch-right (- arg)))

(defun jump-tree-visualizer-quit ()
  "Quit the jump-tree visualizer."
  (interactive)
  (unless (eq major-mode 'jump-tree-visualizer-mode)
    (user-error "`jump-tree-mode' not enabled in buffer"))
  (jump-tree-clear-visualizer-data jump-tree-pos-tree)
  ;; remove kill visualizer hook from parent buffer
  (unwind-protect
      (with-current-buffer jump-tree-visualizer-parent-buffer
        (remove-hook 'before-change-functions 'jump-tree-kill-visualizer t))
    (let* ((parent jump-tree-visualizer-parent-buffer)
           window)
      ;; kill visualizer buffer
      (kill-buffer nil)
      ;; switch back to parent buffer
      (unwind-protect
          (if (setq window (get-buffer-window parent))
              (select-window window)
            (switch-to-buffer parent))))))

(defun jump-tree-visualizer-abort ()
  "Quit the jump-tree visualizer and return buffer to original state."
  (interactive)
  (unless (eq major-mode 'jump-tree-visualizer-mode)
    (user-error "`jump-tree-mode' not enabled in buffer"))
  (let ((node jump-tree-visualizer-initial-node))
    (jump-tree-visualizer-quit)
    (jump-tree-set node)))

(defun jump-tree-visualizer-set (&optional pos)
  "Set buffer to state corresponding to position tree node at POS.
Or point if POS is nil."
  (interactive)
  (unless (eq major-mode 'jump-tree-visualizer-mode)
    (user-error "`jump-tree-mode' not enabled in buffer"))
  (unless pos (setq pos (point)))
  (let ((node (get-text-property pos 'jump-tree-node)))
    (when node
      ;; set parent buffer to state corresponding to node at POS
      (switch-to-buffer-other-window jump-tree-visualizer-parent-buffer)
      (let ((jump-tree-inhibit-kill-visualizer t)) (jump-tree-set node))
      (switch-to-buffer-other-window jump-tree-visualizer-buffer-name)
      ;; re-draw position tree
      (let ((inhibit-read-only t)) (jump-tree-draw-tree jump-tree-pos-tree)))))

(defun jump-tree-visualizer-mouse-set (pos)
  "Set buffer to state corresponding to position tree node at mouse event POS."

  (interactive "@e")
  (unless (eq major-mode 'jump-tree-visualizer-mode)
    (user-error "`jump-tree-mode' not enabled in buffer"))
  (jump-tree-visualizer-set (event-start (nth 1 pos))))

(defun jump-tree-visualize-jump-prev-to-x (&optional x)
  "Jump-Prev to last branch point, register, or saved state.
If X is the symbol `branch', position to last branch point.  If X is
the symbol `register', position to last register.  If X is the sumbol
`saved', position to last saved state.  If X is null, position to first of
these that's encountered.
Interactively, a single \\[universal-argument] specifies
`branch', a double \\[universal-argument] \\[universal-argument]
specifies `saved', and a negative prefix argument specifies
`register'."
  (interactive "P")
  (unless (eq major-mode 'jump-tree-visualizer-mode)
    (user-error "`jump-tree-mode' not enabled in buffer"))
  (when (and (called-interactively-p 'any) x)
    (setq x (prefix-numeric-value x)
          x (cond
             ((< x 0)  'register)
             ((<= x 4) 'branch)
             (t        'saved))))
  (let ((current (if jump-tree-visualizer-selection-mode
                     jump-tree-visualizer-selected-node
                   (jump-tree-current jump-tree-pos-tree))))
    (unwind-protect
        (jump-tree-expand-up
         (jump-tree-node-previous current)))
    ))

(defun jump-tree-visualize-jump-next-to-x (&optional x)
  "Jump-Next to last branch point, register, or saved state.
If X is the symbol `branch', position to last branch point.  If X is
the symbol `register', position to last register.  If X is the sumbol
`saved', position to last saved state.  If X is null, position to first of
these that's encountered.
Interactively, a single \\[universal-argument] specifies
`branch', a double \\[universal-argument] \\[universal-argument]
specifies `saved', and a negative prefix argument specifies
`register'."
  (interactive "P")
  (unless (eq major-mode 'jump-tree-visualizer-mode)
    (user-error "`jump-tree-mode' not enabled in buffer"))
  (when (and (called-interactively-p 'any) x)
    (setq x (prefix-numeric-value x)
          x (cond
             ((< x 0)  'register)
             ((<= x 4) 'branch)
             (t        'saved))))
  (let ((current (if jump-tree-visualizer-selection-mode
                     jump-tree-visualizer-selected-node
                   (jump-tree-current jump-tree-pos-tree))))
    (unwind-protect
        (jump-tree-expand-up
         (jump-tree-node-next current)))
    ))

(defun jump-tree-visualizer-toggle-timestamps ()
  "Toggle display of time-stamps."
  (interactive)
  (unless (eq major-mode 'jump-tree-visualizer-mode)
    (user-error "`jump-tree-mode' not enabled in buffer"))
  (setq jump-tree-visualizer-timestamps (not jump-tree-visualizer-timestamps))
  (setq jump-tree-visualizer-spacing (jump-tree-visualizer-calculate-spacing))
  ;; redraw tree
  (let ((inhibit-read-only t)) (jump-tree-draw-tree jump-tree-pos-tree)))

(defun jump-tree-visualizer-scroll-left (&optional arg)
  "The scroll the window contents left.
A numeric ARG serves as a repeat count."
  (interactive "p")
  (unless (eq major-mode 'jump-tree-visualizer-mode)
    (user-error "`jump-tree-mode' not enabled in buffer"))
  (scroll-left (or arg 1) t))

(defun jump-tree-visualizer-scroll-right (&optional arg)
  "The scroll the window contents right.
A numeric ARG serves as a repeat count."
  (interactive "p")
  (unless (eq major-mode 'jump-tree-visualizer-mode)
    (user-error "`jump-tree-mode' not enabled in buffer"))
  (scroll-right (or arg 1) t))

(defun jump-tree-visualizer-scroll-up (&optional arg)
  "The scroll the window contents up.
A numeric ARG serves as a repeat count."
  (interactive "P")
  (unless (eq major-mode 'jump-tree-visualizer-mode)
    (user-error "`jump-tree-mode' not enabled in buffer"))
  (if (or (and (numberp arg) (< arg 0)) (eq arg '-))
      (jump-tree-visualizer-scroll-down arg)
    ;; scroll up and expand newly-visible portion of tree
    (unwind-protect
        (scroll-up-command arg)
      (jump-tree-expand-down
       (nth (jump-tree-node-branch (jump-tree-current jump-tree-pos-tree))
            (jump-tree-node-next (jump-tree-current jump-tree-pos-tree)))))
    ;; signal error if at eob
    (when (and (not jump-tree-visualizer-needs-extending-down) (eobp))
      (scroll-up))))

(defun jump-tree-visualizer-scroll-down (&optional arg)
  "The scroll the window contents down.
A numeric ARG serves as a repeat count."
  (interactive "P")
  (unless (eq major-mode 'jump-tree-visualizer-mode)
    (user-error "`jump-tree-mode' not enabled in buffer"))
  (if (or (and (numberp arg) (< arg 0)) (eq arg '-))
      (jump-tree-visualizer-scroll-up arg)
    ;; ensure there's enough room at top of buffer to scroll
    (let ((scroll-lines
           (or arg (- (window-height) next-screen-context-lines)))
          (window-line (1- (line-number-at-pos (window-start)))))
      (when (and jump-tree-visualizer-needs-extending-up
                 (< window-line scroll-lines))
        (let ((inhibit-read-only t))
          (goto-char (point-min))
          (jump-tree-move-up (- scroll-lines window-line)))))
    ;; scroll down and expand newly-visible portion of tree
    (unwind-protect
        (scroll-down-command arg)
      (jump-tree-expand-up
       (jump-tree-node-previous (jump-tree-current jump-tree-pos-tree))))
    ;; signal error if at bob
    (when (and (not jump-tree-visualizer-needs-extending-down) (bobp))
      (scroll-down))))


;;; =====================================================================
;;;                    Visualizer selection mode
(define-minor-mode jump-tree-visualizer-selection-mode
  "Toggle mode to select nodes in jump-tree visualizer."
  :lighter "Select"
  :keymap jump-tree-visualizer-selection-mode-map
  :group jump-tree
  (cond
   ;; enable selection mode
   (jump-tree-visualizer-selection-mode
    (setq cursor-type 'box)
    (setq jump-tree-visualizer-selected-node
          (jump-tree-current jump-tree-pos-tree)))
   (t ;; disable selection mode
    (setq cursor-type nil)
    (setq jump-tree-visualizer-selected-node nil)
    (goto-char (jump-tree-node-marker (jump-tree-current jump-tree-pos-tree))))))

(defun jump-tree-visualizer-select-previous (&optional arg)
  "Move to previous node.
A numeric ARG serves as a repeat count."
  (interactive "p")
  (unless (eq major-mode 'jump-tree-visualizer-mode)
    (user-error "`jump-tree-mode' not enabled in buffer"))
  (let ((node jump-tree-visualizer-selected-node))
    (catch 'top
      (dotimes (i (or arg 1))
        (unless (jump-tree-node-previous node) (throw 'top t))
        (setq node (jump-tree-node-previous node))))
    ;; when using lazy drawing, extend tree upwards as required
    (when jump-tree-visualizer-lazy-drawing
      (jump-tree-expand-up jump-tree-visualizer-selected-node node))
    ;; move to selected node
    (goto-char (jump-tree-node-marker node))
    (setq jump-tree-visualizer-selected-node node)))

(defun jump-tree-visualizer-select-next (&optional arg)
  "Move to next node.
A numeric ARG serves as a repeat count."
  (interactive "p")
  (unless (eq major-mode 'jump-tree-visualizer-mode)
    (user-error "`jump-tree-mode' not enabled in buffer"))
  (let ((node jump-tree-visualizer-selected-node))
    (catch 'bottom
      (dotimes (i (or arg 1))
        (unless (nth (jump-tree-node-branch node) (jump-tree-node-next node))
          (throw 'bottom t))
        (setq node
              (nth (jump-tree-node-branch node) (jump-tree-node-next node)))))
    ;; when using lazy drawing, extend tree downwards as required
    (when jump-tree-visualizer-lazy-drawing
      (jump-tree-expand-down jump-tree-visualizer-selected-node node))
    ;; move to selected node
    (goto-char (jump-tree-node-marker node))
    (setq jump-tree-visualizer-selected-node node)))

(defun jump-tree-visualizer-select-right (&optional arg)
  "Move right to a sibling node.
A numeric ARG serves as a repeat count."
  (interactive "p")
  (unless (eq major-mode 'jump-tree-visualizer-mode)
    (user-error "`jump-tree-mode' not enabled in buffer"))
  (let ((node jump-tree-visualizer-selected-node)
        end)
    (goto-char (jump-tree-node-marker jump-tree-visualizer-selected-node))
    (setq end (line-end-position))
    (catch 'end
      (dotimes (i arg)
        (while (or (null node) (eq node jump-tree-visualizer-selected-node))
          (forward-char)
          (setq node (get-text-property (point) 'jump-tree-node))
          (when (= (point) end) (throw 'end t)))))
    (goto-char (jump-tree-node-marker
                (or node jump-tree-visualizer-selected-node)))
    (when node (setq jump-tree-visualizer-selected-node node))))

(defun jump-tree-visualizer-select-left (&optional arg)
  "Move left to a sibling node.
A numeric ARG serves as a repeat count."
  (interactive "p")
  (unless (eq major-mode 'jump-tree-visualizer-mode)
    (user-error "`jump-tree-mode' not enabled in buffer"))
  (let ((node (get-text-property (point) 'jump-tree-node))
        beg)
    (goto-char (jump-tree-node-marker jump-tree-visualizer-selected-node))
    (setq beg (line-beginning-position))
    (catch 'beg
      (dotimes (i arg)
        (while (or (null node) (eq node jump-tree-visualizer-selected-node))
          (backward-char)
          (setq node (get-text-property (point) 'jump-tree-node))
          (when (= (point) beg) (throw 'beg t)))))
    (goto-char (jump-tree-node-marker
                (or node jump-tree-visualizer-selected-node)))
    (when node (setq jump-tree-visualizer-selected-node node))))

(defun jump-tree-visualizer-select (pos)
  "Select position tree node at enter event POS."
  (let ((node (get-text-property pos 'jump-tree-node)))
    (when node
      ;; select node at POS
      (goto-char (jump-tree-node-marker node))
      ;; when using lazy drawing, extend tree up and down as required
      (when jump-tree-visualizer-lazy-drawing
        (jump-tree-expand-up jump-tree-visualizer-selected-node node)
        (jump-tree-expand-down jump-tree-visualizer-selected-node node))
      ;; update selected node
      (setq jump-tree-visualizer-selected-node node)
      )))

(defun jump-tree-visualizer-mouse-select (pos)
  "Select position tree node at mouse event POS."
  (interactive "@e")
  (unless (eq major-mode 'jump-tree-visualizer-mode)
    (user-error "`jump-tree-mode' not enabled in buffer"))
  (jump-tree-visualizer-select (event-start (nth 1 pos))))

(provide 'jump-tree-visualizer)
;;; jump-tree-visualizer.el ends here
