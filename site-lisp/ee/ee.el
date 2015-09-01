;;; ee.el --- Emacs information manager

;; Copyright (C) 2002, 2003, 2004, 2010  Juri Linkov <juri@jurta.org>

;; Author: Juri Linkov <juri@jurta.org>
;; Keywords: ee, convenience, tools, outlines

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

;; This file is the core of the ee package.

;; See the file README and documentation for more information.


;;; Code:


;;; Constants

(defconst ee-version "0.1.0"
  "Version numbers of this version of Ee.")


;;; Customizable Variables

(defgroup ee nil
  "Emacs information manager."
  :prefix "ee-"
  :group 'data
  :group 'tools
  :group 'convenience)

(defcustom ee-data-directory "~/.emacs.d/ee/"
  "Name of default directory where persistent data files are saved
and searched to read when relative filename is given."
  :type 'directory
  :group 'ee)

(defcustom ee-view-data-directory "~/.emacs.d/ee/"
  "Name of default directory where persistent view data files are saved
and searched to read when relative filename is given."
  :type 'directory
  :group 'ee)

(defcustom ee-data-file-save-format 'records
  "Format used in the saved data files.
If 'pp, then save data to the file pretty-printed.
If 'records, then save every record on own line.
If nil, then save unformatted."
  :type 'symbol
  :group 'ee)

;; TODO: move to view-data?
(defcustom ee-quick-keys t ;; TODO: nil
  "Define additional key bindings for faster tree navigation.
Additonal key bindings include arrow keys with combinations
of C- and S- modifiers.
Also useful mouse actions are bound to [mouse-1] button.
This takes effect when first loading the ee package."
  :type 'boolean
  :group 'ee)

(defcustom ee-mouse-expansion-sensitivity 3
  "Number of positions mouse should be moved on the expansion line
in one direction to the left or to the right before expansion
is shown or hidden."
  :type 'integer
  :group 'ee)

(defcustom ee-mouse-scroll-margin 2
  "Number of lines of margin at the top and bottom of a window.
Scroll the window downward or upward whenever mouse motions
get within this many lines of the top or bottom of the window.
The scrolling margin is ignored when window already displays
the beginning of buffer."
  :type 'integer
  :group 'ee)

(defcustom ee-mouse-scroll-lines 1
  "Number of lines to scroll at the top and bottom of a window.
Scroll the window downward or upward this many lines
when mouse is moved of the top or bottom of the window."
  :type 'integer
  :group 'ee)

(defcustom ee-mode-hook nil
  "Hook functions run after entering ee mode."
  :type 'hook
  :group 'ee)

(defcustom ee-view-goto-hook '(ee-view-goto-hook-default)
  "Hook functions run after moving point into some line in the ee buffer."
  :type 'hook
  :group 'ee)

(defcustom ee-view-expansion-show-hook nil
  "Hook functions run after expansion is expanded."
  :type 'hook
  :group 'ee)

(defcustom ee-view-expansion-hide-hook nil
  "Hook functions run after expansion is collapsed."
  :type 'hook
  :group 'ee)

(defcustom ee-view-buffer-revert-function 'ee-view-buffer-revert-function-default
  "Function to use to revert ee buffer."
  :type 'function
  :group 'ee)

(defcustom ee-root-data-file "ee.ee"
  "Name of data file that holds the index of available ee extensions."
  :type 'file
  :group 'ee)


;;; Global Variables

(defvar ee-mode-map nil
  "Local keymap for ee-mode buffers.")

(defvar data-getters)
(defvar data-setters)


;;; Buffer-Local Variables

(defvar ee-data-file nil
  "Name of data file where persistent data are saved.")
(make-variable-buffer-local 'ee-data-file)

(defvar ee-data-file-auto-save nil
  "*If this is t, then save data to the file automatically without confirmation,
when data are modified.")
(make-variable-buffer-local 'ee-data-file-auto-save)

(defvar ee-data nil
  "Data structure loaded from data file or extracted
from alternate data source.")
(make-variable-buffer-local 'ee-data)

(defvar ee-view-data-file nil
  "Name of view data file where view description data are saved.")
(make-variable-buffer-local 'ee-view-data-file)

(defvar ee-view-data nil
  "Data structure containing all views descriptions.")
(make-variable-buffer-local 'ee-view-data)

(defvar ee-view nil
  "Data structure containing part of `ee-view-data'
that describes only the current view.")
(make-variable-buffer-local 'ee-view)

;; TODO: move to view-data?
;; TODO: rename to ee-folded-expansions?
(defvar ee-hidden-expansions nil
  "Folded expansions.")
(make-variable-buffer-local 'ee-hidden-expansions)

(defvar ee-parent-buffer nil
  "Buffer associated with the current ee buffer.
Most often, it is a buffer where current ee command was invoked.
For example, ee-outline view buffer can be associated
with Emacs buffer where command `ee-outline' was invoked
and from which the ee-outline view buffer was generated
and where ee-outline commands operate.")
(make-variable-buffer-local 'ee-parent-buffer)

(defvar ee-view-filter-omit nil)
(make-variable-buffer-local 'ee-view-filter-omit)

;; TODO: replace next by ee-goal-field, e.g. (setq ee-goal-field 'buffer-name)
(defvar ee-goal-column nil
  "*Goal column for vertical motion.")
(make-variable-buffer-local 'ee-goal-column)

(defvar ee-current-c-key-field nil
  "Key used to identify current record.")
(make-variable-buffer-local 'ee-current-c-key-field)

(defvar ee-current-r-key-field nil
  "Key used to identify current record.")
(make-variable-buffer-local 'ee-current-r-key-field)

;; TODO: move to view descriptions
;; (setq ee-faces '(nil info-xref font-lock-type-face nil))
;; qv vc-annotate-color-map
;; qv outline-font-lock-keywords
;; TODO: defface: ee-category-1-face ee-category-2-face ee-category-3-face ee-category-4-face
;; qv outline-font-lock-faces
(defvar ee-faces-default '[font-lock-warning-face
                           ee-category;font-lock-function-name-face
                           font-lock-type-face
                           font-lock-keyword-face
                           font-lock-builtin-face
                           font-lock-variable-name-face
                           font-lock-constant-face
                           font-lock-comment-face
                           font-lock-type-face
                           font-lock-string-face])
;; another alternative
;; (defvar ee-faces-default '[font-lock-warning-face
;;                            font-lock-function-name-face
;;                            font-lock-type-face
;;                            font-lock-string-face
;;                            font-lock-keyword-face
;;                            font-lock-variable-name-face
;;                            font-lock-builtin-face
;;                            font-lock-constant-face])
;; yet another alternative
;;       '(font-lock-variable-name-face
;;         font-lock-constant-face
;;         font-lock-function-name-face
;;         font-lock-builtin-face
;;         font-lock-comment-face
;;         font-lock-keyword-face
;;         font-lock-type-face
;;         font-lock-string-face)

;; TODO: make variable with hash for all view data instead of next:
(defvar ee-c-faces nil)
(make-variable-buffer-local 'ee-c-faces)
(defvar ee-r-faces nil)
(make-variable-buffer-local 'ee-r-faces)

;;; Logical Faces

(defface ee-category
  '((((type tty) (class color)) (:foreground "blue"))
    (((background light)) (:foreground "Blue"))
    (((background dark)) (:foreground "LightSkyBlue"))
    (t (:italic t)))
  "Face used to display category lines."
  :group 'ee)
(put 'ee-face-category-face 'face-alias 'ee-category)

;; (defface ee-faded
;;   '((((type tty) (class color)) (:foreground "gray"))
;;     (((background light)) (:foreground "DimGray"))
;;     (((background dark)) (:foreground "DimGray"))
;;     (t (:italic t)))
;;   "Face used to display faded items."
;;   :group 'ee)
;; (put 'ee-face-faded-face 'face-alias 'ee-faded)

;; TODO: better name ee-dim?
;; TODO: better name ee-fuzzy?
;; TODO: better name ee-shaded?
;; TODO: better name ee-faded?
;; TODO: try color #cccccc for faded-face
(if (facep 'shadow)
    (defface ee-shadow
      '((t :inherit shadow))
      "Face used to display shadowed items."
      :group 'ee)
  (defface ee-shadow
    '((((type tty pc) (class color)) (:foreground "yellow"))
      (((background dark))  (:foreground "grey50"))
      (((background light)) (:foreground "grey50")))
    "Face used to display shadowed items."
    :group 'ee))
(put 'ee-face-faded-face 'face-alias 'ee-shadow)

;; TODO: rename to ee-ignored similar to dired-face-ignored
(defface ee-omitted
  '((((type tty) (class color)) (:foreground "green"))
    (((class grayscale) (background light)) (:foreground "DimGray"))
    (((class grayscale) (background dark)) (:foreground "LightGray"))
    (((class color) (background light)) (:foreground "RosyBrown"))
    (((class color) (background dark)) (:foreground "LightSalmon"))
    (t (:italic t)))
  "Face used to display omitted items."
  :group 'ee)
(put 'ee-face-omitted-face 'face-alias 'ee-omitted)

(defface ee-marked
  '((((type tty) (class color)) (:foreground "red"))
    (((class color) (background light)) (:foreground "Red"))
    (((class color) (background dark)) (:foreground "Red"))
    (t (:inverse-video t :bold t)))
  "Face used to display marked items."
  :group 'ee)
(put 'ee-face-marked-face 'face-alias 'ee-marked)

(defface ee-bookmarked ;; TODO: better name?
  '((((type tty) (class color)) (:foreground "gray"))
    (((class grayscale) (background light))
     (:foreground "LightGray" :bold t :underline t))
    (((class grayscale) (background dark))
     (:foreground "Gray50" :bold t :underline t))
    (((class color) (background light)) (:foreground "CadetBlue"))
    (((class color) (background dark)) (:foreground "Aquamarine"))
    (t (:bold t :underline t)))
  "Face used to display bookmarked items."
  :group 'ee)
(put 'ee-face-bookmarked-face 'face-alias 'ee-bookmarked)

;; backward compatibility for pre-22.0 Emacs
(or (get 'link 'face-defface-spec)
(defface link
  '((((class color) (background light))
     :foreground "blue" :underline t)
    (((class color) (background dark))
     :foreground "cyan" :underline t)
    (t :inherit underline))
  "Basic face for unvisited links."
  :group 'basic-faces))

(defface ee-link
  '((t :inherit link))
  "Face used to display link items."
  :group 'ee)
(put 'ee-face-link-face 'face-alias 'ee-link)

;; backward compatibility for pre-22.0 Emacs
(or (get 'link-visited 'face-defface-spec)
(defface link-visited
  '((((class color) (background light))
     :foreground "magenta4" :underline t)
    (((class color) (background dark))
     :foreground "violet" :underline t)
    (t :inherit underline))
  "Basic face for visited links."
  :group 'basic-faces))

(defface ee-link-visited
  '((t :inherit link-visited))
  "Face used to display visited link items."
  :group 'ee)
(put 'ee-face-visited-link-face 'face-alias 'ee-link-visited)


;;; Markers

(defconst ee-mark-attr-alist '_a ;; '__@
  "Unique symbol used for marking the beginning of attrubutes alist
in the internal view tree structure.")

(defconst ee-mark-record-tree '_r ;; '__/
  "Unique symbol used for marking the beginning of record tree
in the internal view tree structure.")

(defconst ee-mark-subcategory-tree '_s ;; '__|
  "Unique symbol used for marking the beginning of subcategory tree
in the internal view tree structure.")

(defvar ee-data-mark-field-name 'mark
  "The name of data field used for marking.")
(make-variable-buffer-local 'ee-data-mark-field-name)

(defvar ee-mark-mark '*
  "The generic mark symbol.")

;; not used yet, because visited records are marked by separate field
(defvar ee-mark-visited 'R
  "Symbol used to mark visited records.")

;; not used yet, because bookmarked records are marked by separate field
(defvar ee-mark-bookmarked 'B
  "Symbol used to mark bookmarked records.")

(defvar ee-mark-del 'D ;; TODO: ?D - character instead of symbol?
  "Symbol used to mark records for deletion.")


;;; Key Bindings

;; TODO: move to defvar?
(defun ee-mode-map-make-default ()
  "Defines default key bindings for `ee-mode-map'.
If `ee-quick-keys' is t, then defines additional key bindings
for faster tree navigation."
  (let ((map (make-keymap)))
    (suppress-keymap map)
    ;; Expansion visibility
    (define-key map "+" 'ee-view-expansion-show)
    (define-key map "-" 'ee-view-expansion-hide)
    (define-key map "=" 'ee-view-expansion-show) ; on some keyboards "=" is on same key as "+", but typed w/o shift
    (define-key map "*" 'ee-view-expansion-show-subtree)
    (define-key map "/" 'ee-view-expansion-hide-subtree)
    ;; Record motion
    (define-key map " "           'ee-view-record-next)
    (define-key map [tab]         'ee-view-record-next)
    (define-key map "\t"          'ee-view-record-next) ; for tty
    (define-key map [backtab]     'ee-view-record-prev)
    (define-key map [(shift tab)] 'ee-view-record-prev)
    (define-key map [return]      'ee-view-record-select-or-expansion-show-or-hide)
    (define-key map "\C-m"        'ee-view-record-select-or-expansion-show-or-hide) ; for tty
    ;; Generic motion
    (define-key map [down-mouse-2] 'ee-mouse-navigation)
    (define-key map "n" 'next-line)
    (define-key map "p" 'previous-line)
    ;; View definition
    (define-key map "v" 'ee-views)
    (define-key map "V" 'ee-view-change-view-file)
    (define-key map "f" 'ee-fields)
    ;; Record manipulation
    (define-key map "c" 'ee-view-record-copy)
    (define-key map "D" 'ee-view-records-delete)
    ;; TODO: mark by regexp as in dired
    (define-key map "m" 'ee-view-records-mark)
    (define-key map "d" 'ee-view-records-mark-delete)
    (define-key map "k" 'ee-view-records-mark-delete)
    (define-key map "\C-d" 'ee-view-records-mark-delete-backwards)
    (define-key map "\C-k" 'ee-view-records-delete)
    (define-key map "\C-y" 'ee-view-records-yank)
    (define-key map "x" 'ee-view-records-execute)
    (define-key map "u" 'ee-view-records-unmark)
    (define-key map [backspace] 'ee-view-records-unmark-backwards)
    (define-key map "\177" 'ee-view-records-unmark-backwards) ; for tty
    ;; Help
    (define-key map "?" 'describe-mode)
    (define-key map "h" 'describe-mode)
    (define-key map "r" (lambda () (interactive) (message "%S" (ee-view-record-get))))
    (define-key map "\C-c\C-hr" (lambda () (interactive) (message "%S" (ee-view-record-get))))
    ;; Buffer
    (define-key map "g" 'ee-view-buffer-revert)
    (define-key map "\C-x\C-s" 'ee-data-file-save)
    (define-key map "q" 'quit-window)
    ;; outline-like key bindings
    (define-key map "\C-c\C-n" 'ee-view-expansion-next-visible)
    (define-key map "\C-c\C-p" 'ee-view-expansion-prev-visible)
    (define-key map "\C-c\C-f" 'ee-view-expansion-next-same-level)
    (define-key map "\C-c\C-b" 'ee-view-expansion-prev-same-level)
    (define-key map "\C-c\C-u" 'ee-view-expansion-up)
    (define-key map "\C-c\C-i" 'ee-view-expansion-show-children)
    (define-key map "\C-c\C-s" 'ee-view-expansion-show-subtree)
    (define-key map "\C-c\C-d" 'ee-view-expansion-hide-subtree)
    (define-key map "\C-c\C-t" 'ee-view-expansion-hide-body)
    (define-key map "\C-c\C-a" 'ee-view-expansion-show-all)
    (define-key map "\C-c\C-l" 'ee-view-expansion-hide-leaves)
    (define-key map "\C-c\C-k" 'ee-view-expansion-show-branches)
    (define-key map "\C-c\C-q" 'ee-view-expansion-hide-sublevels)
    (define-key map "\C-c\C-o" 'ee-view-expansion-hide-other)
    ;; dired-like key bindings
    (define-key map "$" 'ee-view-expansion-show-or-hide)
    (define-key map ">" 'ee-view-expansion-next)
    (define-key map "<" 'ee-view-expansion-prev)
    (define-key map "^" 'ee-view-expansion-up)
    (define-key map [(meta ?o)] 'ee-view-filter-omit)
    (when ee-quick-keys
      (define-key map [down-mouse-1] 'ee-mouse-navigation)
      (define-key map [right] 'ee-view-expansion-show-or-next)
      (define-key map [left] 'ee-view-expansion-hide-or-up-or-prev)
      (define-key map [(meta up)] 'ee-view-expansion-prev-sibling)
      (define-key map [(meta down)] 'ee-view-expansion-next-sibling)
      (define-key map [(meta right)] 'ee-view-expansion-up)
      (define-key map [(meta left)] 'ee-view-expansion-down)
      (define-key map [(control ?+)] 'ee-view-expansion-show-all)
      (define-key map [(control ?-)] 'ee-view-expansion-hide-all)
      ;; TODO: self-insertion letters could start isearch
      ;; (add-hook 'isearch-mode-hook '(lambda () (setq isearch-string "ise" isearch-message "ise") (isearch-message)))
      ;; (add-hook 'isearch-mode-end-hook '(lambda () (setq  isearch-mode-hook nil)))
      )
    (setq ee-mode-map map)))

(or ee-mode-map
    (ee-mode-map-make-default))


;;; Major Mode

(defun ee-mode ()
  ;; TODO: write more here
  "Mode for displaying and manipulating a relational data
grouped into hierarchical categories.
ee mode provides commands for browsing through the expansion tree.
Typing \\<ee-mode-map>\\[ee-views] will select the different view.
Typing \\<ee-mode-map>\\[ee-fields] will edit the record's fields.

\\{ee-mode-map}
"
  ;; NOT (interactive)
  (kill-all-local-variables)
  (use-local-map ee-mode-map)
  (setq major-mode 'ee-mode)
  (setq mode-name "ee")
  (set (make-local-variable 'line-move-ignore-invisible) t)
  (setq buffer-file-name nil)
  (set-buffer-modified-p nil)
  (setq buffer-read-only t)
  (auto-save-mode 0)
  (buffer-disable-undo (current-buffer))
  (setq truncate-lines t)
  (if ee-view-buffer-revert-function
      (set (make-local-variable 'revert-buffer-function)
           ee-view-buffer-revert-function))
  (run-hooks 'ee-mode-hook))

;; ee mode is suitable only for specially formatted data
(put 'ee-mode 'mode-class 'special)


;;; View Generation Functions

(defun ee-view-buffer-create (name mode keymap data &optional view-data parent-buffer new-buffer-p data-file data-file-auto-save)
  (let ((view-buffer
         (ee-view-buffer-create-noselect name mode keymap data view-data parent-buffer new-buffer-p data-file data-file-auto-save)))
    (if view-buffer
        (switch-to-buffer view-buffer))))

(defun ee-view-buffer-create-noselect (name mode keymap data &optional view-data parent-buffer new-buffer-p data-file data-file-auto-save)
  (let ((curr-buffer (or parent-buffer (current-buffer)))
        (view-buffer (get-buffer name)))
    (condition-case err
        (if (and (not new-buffer-p) view-buffer)
            (with-current-buffer view-buffer
              (setq ee-parent-buffer curr-buffer)
              (ee-view-buffer-update t))
          (setq view-buffer (get-buffer-create name))
          (with-current-buffer view-buffer
            (ee-mode)
            (if mode-name (setq mode-name mode))
            (if keymap (use-local-map keymap))
            (setq ee-parent-buffer curr-buffer)
            (if data-file
                (ee-data-update 'data data data-file data-file-auto-save)
              (ee-data-update 'data data data-file data-file-auto-save t))
            (ee-data-update 'view-data view-data)
            (ee-view-buffer-update)))
      (bad ;; TODO: here should be `error' symbol instead of `bad'!
       (if view-buffer (kill-buffer view-buffer))
       (setq view-buffer nil)
       ;; TODO: any better way to continue standard error handling after that?
       ;; (message "%s" (error-message-string err))
       (error err)))
    view-buffer))

(defun ee-view-buffer-generate ()
  "Generate in the current buffer the hierarchical representation of
relational data from `ee-data' according to descritions in `ee-view-data'."
  (if (and ee-data ee-view-data)
      (save-excursion
        ;; Erase buffer before generation
        ;; TODO: maybe much faster to del buffer, and create a new?
        (let ((inhibit-read-only t))
          (widen)
          (goto-char (point-min))
          (remove-overlays)
          (set-text-properties (point-min) (point-max) nil)
          (erase-buffer)
          (set-buffer-modified-p nil))))
  (setq ee-view (and ee-view-data
                     (or (car (ee-data-records-find ee-view-data '(default . t)))
                         (aref ee-view-data 1))))
  (if (and ee-data ee-view-data ee-view)
      (let* ((data-getters (ee-data-meta-getters-get-set ee-data))
             (data-setters (ee-data-meta-setters-get-set ee-data))
             (view-getters (ee-data-meta-getters-get-set ee-view-data))
             (r-filter (if (null ee-view-filter-omit) (ee-data-field-get 'r-filter ee-view view-getters)))
             (c-path-finder (ee-data-field-get 'c-path-finder ee-view view-getters))
             (c-tree-builder (ee-data-field-get 'c-tree-builder ee-view view-getters))
             (r-tree-builder (ee-data-field-get 'r-tree-builder ee-view view-getters))
             (parent-child-key-fields (ee-data-field-get 'r-parent-child-key-fields ee-view view-getters))
             (child-parent-key-fields (ee-data-field-get 'r-child-parent-key-fields ee-view view-getters))
             (parent-field
              (cond (parent-child-key-fields (car parent-child-key-fields))
                    (child-parent-key-fields (cadr child-parent-key-fields))))
             (child-field
              (cond (parent-child-key-fields (cadr parent-child-key-fields))
                    (child-parent-key-fields (car child-parent-key-fields))))
             (view-atree (list "root"))
             (inhibit-read-only t))
        (setq ee-c-faces (or (ee-data-field-get 'c-faces ee-view view-getters) ee-faces-default))
        (setq ee-r-faces (or (ee-data-field-get 'r-faces ee-view view-getters) ee-faces-default))
        (cond
         (c-tree-builder
          (ee-gen-add-path-atree nil (funcall c-tree-builder) view-atree))
         (t
          (ee-data-records-do
           ee-data
           (lambda (r ri)
             (if (or (null r-filter)
                     (and (functionp r-filter)
                          (funcall r-filter r)))
                 (let ((c-path-list
                        (delq nil (and (functionp c-path-finder)
                                       (funcall c-path-finder r)))))
                   (if c-path-list
                       (while c-path-list
                         (ee-gen-add-path-atree
                          (append (if (consp (car c-path-list))
                                      (car c-path-list)
                                    (list (car c-path-list)))
                                  (list ee-mark-record-tree))
                          (cond
                           (r-tree-builder
                            (funcall r-tree-builder ri))
                           (parent-child-key-fields
                            ;; TODO: make start-index-p configurable
                            (ee-gen-r-tree-parent-child ee-data data-getters parent-field child-field ri t))
                           (child-parent-key-fields
                            (ee-gen-r-tree-child-parent ee-data data-getters parent-field child-field ri))
                           (t ri))
                          view-atree)
                         (setq c-path-list (cdr c-path-list)))
                     (ee-gen-add-path-atree
                      (list ee-mark-record-tree)
                      (cond
                       (r-tree-builder
                        (funcall r-tree-builder ri))
                       (parent-child-key-fields
                        ;; TODO: make start-index-p configurable
                        (ee-gen-r-tree-parent-child ee-data data-getters parent-field child-field ri t))
                       (child-parent-key-fields
                        (ee-gen-r-tree-child-parent ee-data data-getters parent-field child-field ri))
                       (t ri))
                      view-atree)))))))
         ;; (setcdr view-atree (sort (cdr view-atree) 'test-csort))
         ;; (ee-sort-atree (cdr view-atree)) ; TODO: if unsorted then nreverse
         )
        ;; (funcall (cadr (assq 'r-printer ee-view))
        ;;          (apply 'vector (cadr (assq 'r-fields ee-view))) 0 0 nil)
        (insert (or (ee-data-field-get 'c-title ee-view view-getters) ""))
        (insert (or (ee-data-field-get 'r-title ee-view view-getters) ""))
        (if (ee-data-field-get 'c-title-printer ee-view view-getters)
            (funcall (ee-data-field-get 'c-title-printer ee-view view-getters)))
        (if (ee-data-field-get 'r-title-printer ee-view view-getters)
            (funcall (ee-data-field-get 'r-title-printer ee-view view-getters)))
        (let ((hidden-expansions ee-hidden-expansions))
          (while hidden-expansions
            (ee-gen-add-to-path-atree
             (car hidden-expansions)
             (list ee-mark-attr-alist '(hide t))
             view-atree)
            (setq hidden-expansions (cdr hidden-expansions))))
        ;; Separate sort step not used now;
        ;; currently sort performed simultaneously with print
        ;;     (if (or (cadr (assq 'c-sorter ee-view))
        ;;             (cadr (assq 'r-sorter ee-view)))
        ;;     (ee-gen-c-tree-sort (cdr view-atree) 0 0 0 nil
        ;;                         (ee-data-field-get 'c-sorter ee-view view-getters)
        ;;                         (ee-data-field-get 'r-sorter ee-view view-getters))
        ;;       )
        ;; TODO: make generic calculator with arbitrary names, e.g.:
        ;; (c-calculator (lambda (r a-level r-level children-p result)
        ;;                 (list (list 'size (ee-field 'size r))
        ;;                       (list 'count 1)
        ;;                       (list 'marked (if (ee-field ee-data-mark-field-name r) 1 0)))))
        ;; TODO: make generic collector (very low priority, needed?), e.g.:
        ;; (c-collector (lambda (r a-level r-level children-p result)
        ;;                 (list (list 'max-size (max result (ee-field 'size r))))))
        (if (or (ee-data-field-get 'c-counter ee-view view-getters)
                (ee-data-field-get 'r-counter ee-view view-getters))
            (ee-gen-c-tree-calc (cdr view-atree) 0 0 0
                                (ee-data-field-get 'c-counter ee-view view-getters)
                                (ee-data-field-get 'r-counter ee-view view-getters)
                                'counter))
        (if (or (ee-data-field-get 'c-calculator ee-view view-getters)
                (ee-data-field-get 'r-calculator ee-view view-getters))
            (ee-gen-c-tree-calc (cdr view-atree) 0 0 0
                                (ee-data-field-get 'c-calculator ee-view view-getters)
                                (ee-data-field-get 'r-calculator ee-view view-getters)
                                'result))
        ;; (message "%s" (pp view-atree))
        (ee-gen-c-tree-print (cdr view-atree) 0 0 0 nil
                             (ee-data-field-get 'c-printer ee-view view-getters)
                             (ee-data-field-get 'c-sorter ee-view  view-getters)
                             (ee-data-field-get 'r-printer ee-view view-getters)
                             (ee-data-field-get 'r-sorter ee-view  view-getters))
        (insert "\n")                   ; Insert final newline
        (goto-char (point-min))
        (and (eolp) (delete-char 1))    ; Delete 1st empty line
        (set-buffer-modified-p nil)
        (if (ee-data-field-get 'post-generate ee-view view-getters)
            (funcall (ee-data-field-get 'post-generate ee-view view-getters))))))

(defun ee-gen-r-tree-parent-child (data data-getters parent-field-name child-field-name ri &optional start-index-p)
  (if ri
      (cons ri
            (nreverse
             (mapcar
              (lambda (child-field-value)
                (ee-gen-r-tree-parent-child
                 data data-getters parent-field-name child-field-name
                 (ee-data-record-index-find
                  data parent-field-name child-field-value
                  data-getters
                  (if start-index-p ri))))
              (ee-data-field-get child-field-name (aref data ri) data-getters))))))

(defun ee-gen-r-tree-child-parent (data data-getters child-field-name parent-field-name ri &optional ri-done)
  (if ri
      (cons ri
            (nreverse
             (delq nil
                   (mapcar
                    (lambda (child-ri)
                      (when (not (memq child-ri ri-done))
                        (setq ri-done (cons ri (cons child-ri ri-done)))
                        (ee-gen-r-tree-child-parent
                         data data-getters child-field-name parent-field-name
                         child-ri
                         ri-done)))
                    (ee-data-record-indexes-find
                     data (cons child-field-name
                                (ee-data-field-get
                                 parent-field-name
                                 (aref data ri) data-getters))
                     data-getters)))))))

(defun ee-gen-add-path-atree (path new-atree atree)
  "Create path and add new atree."
  (if path
      (let ((aelem (assoc (car path) atree)))
        (if aelem
            (ee-gen-add-path-atree (cdr path) new-atree aelem)
          (setcdr atree (cons (ee-gen-list-to-atree path new-atree) (cdr atree)))))
    (setcdr atree (cons new-atree (cdr atree)))))

(defun ee-gen-add-to-path-atree (path new-atree atree)
  "Don't create path, but instead follow path, if possible, and then add new atree."
  (if path
      (let ((aelem (assoc (car path) atree)))
        (if aelem
            (ee-gen-add-to-path-atree (cdr path) new-atree aelem)
          ;; (setcdr atree (cons (ee-gen-list-to-atree path new-atree) (cdr atree)))
          ))
    (setcdr atree (cons new-atree (cdr atree)))))

(defun ee-gen-list-to-atree (list atree)
  (if list
      (cons (car list) (list (ee-gen-list-to-atree (cdr list) atree)))
    atree))

;; (ee-split-string "a/b/c/" "/") -> ("a" _s "b" _s "c")
(defun ee-split-string (string string-separator)
  "Split string `string' by `string-separator' into list,
and separates element of new list by value of variable
`ee-mark-subcategory-tree', which marks subcategory subtrees."
  (if (stringp string)
      (let ((list (delete ""
                          ;; starting from Emacs 21.3.50 the default behavior
                          ;; of `split-string' was changed, so delete ""
                          ;; to make it compatible with earlier versions
                          (split-string string string-separator)))
            (list-separator ee-mark-subcategory-tree))
        (if (car list)
            (cons (car list)
                  (mapcan (lambda (elt)
                            (list list-separator elt))
                          (cdr list)))))))

(defun ee-gen-c-tree-print (atree a-level c-level s-level root-path c-printer c-sorter r-printer r-sorter)
  ;; Input:
  ;; a-level - absolute level
  ;; c-level - category level
  ;; s-level - relative subcategory level
  (let ((a-level (1+ a-level))
        (c-level (1+ c-level)))
    (let ((sorter (if c-sorter
                      (funcall c-sorter a-level c-level (abs s-level)
                               (assq ee-mark-attr-alist atree)))))
      (if sorter
          (setq atree (sort atree sorter))
        (setq atree (nreverse atree)))) ; reverse is hack
    (while atree
      (let* ((asubtree (car atree))
             (aname (car asubtree))
             b p)
        (cond
         ((eq aname ee-mark-attr-alist)) ; Skip attr-alist
         ((eq aname ee-mark-record-tree) ; Start record hierarchy
          (setq asubtree (cdr asubtree))
          (let ((sorter (if r-sorter
                            (funcall r-sorter a-level 0
                                     (assq ee-mark-attr-alist asubtree)))))
            (if sorter
                (setq asubtree (sort asubtree sorter))
              (setq asubtree (nreverse asubtree)))) ; reverse is hack
          (while asubtree
            (ee-gen-r-tree-print (car asubtree) a-level 0 r-printer r-sorter)
            (setq asubtree (cdr asubtree))))
         ((eq aname ee-mark-subcategory-tree) ; Subcategory separator
          (ee-gen-c-tree-print
           ;; Retain c-level, increase a-level and s-level;
           ;; note that a-level and c-level are automatically increased twice
           ;; at the beginning of current call and next call of ee-gen-c-tree-print
           (cdr asubtree) (- a-level 1) (- c-level 2) (1+ (abs s-level))
           (cons aname root-path) c-printer c-sorter r-printer r-sorter))
         (t                             ; else insert category line
          (insert "\n")
          (setq b (point))
          ;; Setting s-level to 0 is postponed to second level:
          ;; at first call it is set to negative value,
          ;; if there are no next subcategory separator,
          ;; converting it back to positive value,
          ;; then negative value at next call is set to 0
          (let ((s-level (if (< s-level 0) 0 (- s-level))))
            (if c-printer
                (funcall c-printer a-level c-level (abs s-level)
                         aname (assq ee-mark-attr-alist asubtree)))
            (setq p (point))
            (ee-gen-c-tree-print
             (cdr asubtree) a-level c-level s-level
             (cons aname root-path) c-printer c-sorter r-printer r-sorter)
            (if (< p (point))  ; Make expansion only if children exist
                (add-text-properties b (1+ b) ;; p
                                     (list 'ee-expansion (make-overlay p (point))
                                           'ee-level a-level
                                           'ee-path (cons aname root-path)))
              ;; needed?: (add-text-properties b p (list 'mouse-face 'highlight))
              )
            ;; Make overlay invisible if property "hide" exists
            (if (assq 'hide (assq ee-mark-attr-alist asubtree))
                (save-excursion (goto-char b) (ee-view-expansion-hide)))))))
      (setq atree (cdr atree)))))

(defun ee-gen-r-tree-print (atree a-level r-level r-printer r-sorter)
  (let ((head (if (consp atree) (car atree) atree))
        (tail (if (consp atree) (cdr atree)))
        (attr-alist (if (consp atree) (assq ee-mark-attr-alist atree)))
        b p)
    (insert "\n")
    (setq b (point))
    (let ((r (if (integerp head) (aref ee-data head) head)))
      (if r-printer
          (funcall r-printer r a-level r-level
                   (and (> (- (length tail) (if attr-alist 1 0)) 0) t) attr-alist))
      (add-text-properties b (1+ b);;(point)
                           ;; "ri" is "record index"
                           (list 'ee-ri head
                                 'ee-level a-level
                                 'ee-rlevel r-level
                                 ;; TODO: add children if not null
                                 'ee-childrenp (and (> (- (length tail) (if attr-alist 1 0)) 0) t)
                                 ;; TODO: split attr to separate props
                                 'ee-attrs attr-alist)))
    (setq p (point))
    (when tail
      (let ((sorter (if r-sorter
                        (funcall r-sorter a-level r-level (assq ee-mark-attr-alist tail)))))
        (if sorter
            (setq tail (sort tail sorter))
          (setq tail (nreverse tail)))) ; reverse
      (while tail
        (if (not (eq (caar tail) ee-mark-attr-alist)) ; if not attr-alist
            (ee-gen-r-tree-print (car tail) (1+ a-level) (1+ r-level) r-printer r-sorter))
        (setq tail (cdr tail)))
      ;; Make expansion only if children exist
      (if (< p (point))
          (add-text-properties b (1+ b);;p
                               (list 'ee-expansion (make-overlay p (point))
                                     'ee-level a-level))))))

(defmacro ee-sort! (list predicate)
  `(let ((new-list (sort (cons (car ,list) (cdr ,list)) ,predicate)))
     (setcar ,list (car new-list))
     (setcdr ,list (cdr new-list))))

;; Alternative function instead of macro `ee-sort!'
;; (defun ee-sort! (list predicate)
;;   (let ((new-list (sort (cons (car list) (cdr list)) predicate)))
;;     (setcar list (car new-list))
;;     (setcdr list (cdr new-list))))

(defmacro ee-reverse! (list)
  `(let ((new-list (nreverse (cons (car ,list) (cdr ,list)))))
     (setcar ,list (car new-list))
     (setcdr ,list (cdr new-list))))

;; Alternative function instead of macro `ee-reverse!'
;; (defun ee-reverse! (list)
;;   (let ((new-list (nreverse (cons (car list) (cdr list)))))
;;     (setcar list (car new-list))
;;     (setcdr list (cdr new-list))))

;; NOT USED currently, because sort is done simultaneously with print
(defun ee-gen-c-tree-sort (atree a-level c-level s-level root-path c-sorter r-sorter)
  (let* ((a-level (1+ a-level))
         (c-level (1+ c-level)))
    (if c-sorter
        (ee-sort! atree (funcall c-sorter a-level c-level s-level (assq ee-mark-attr-alist atree)))
      (ee-reverse! atree))
    (while atree
      (let* ((asubtree (car atree))
             (aname (car asubtree)))
        (cond
         ((eq aname ee-mark-attr-alist)) ; Skip attr-alist
         ((eq aname ee-mark-record-tree) ; Start record hierarchy
          (setq asubtree (cdr asubtree))
;           (if r-sorter (setq asubtree (sort asubtree (car r-sorter))))
;           (while asubtree
;             (ee-gen-r-tree-sort (car asubtree) a-level 0 r-sorter)
;             (setq asubtree (cdr asubtree)))
;           (ee-gen-r-tree-sort (list nil asubtree) ; fake root
;                           a-level 0 r-sorter)
          (ee-gen-r-tree-sort (cons nil asubtree) ; fake root
                          a-level 0 r-sorter)
          )
         ((eq aname ee-mark-subcategory-tree) ; Subcategory separator
          (ee-gen-c-tree-sort
           (cdr asubtree) (- a-level 1) (- c-level 2) (1+ (abs s-level))
           (cons aname root-path) c-sorter r-sorter))
         (t                             ; else insert category line
          (let ((s-level (if (< s-level 0) 0 (- s-level))))
            (ee-gen-c-tree-sort
             (cdr asubtree) a-level c-level s-level
             (cons aname root-path) c-sorter r-sorter)))))
      (setq atree (cdr atree)))))

;; NOT USED currently, because sort is done simultaneously with print
(defun ee-gen-r-tree-sort (atree a-level r-level r-sorter)
  (let ((head (if (consp atree) (car atree) atree))
        (tail (if (consp atree) (cdr atree)))
;         (attr-alist (if (consp atree) (assq ee-mark-attr-alist atree)))
        )
;     (let ((r (if (integerp head) (aref ee-data head) head)))
;       (funcall r-sorter r a-level r-level
;                (and (> (- (length tail) (length attr-alist)) 0) t) attr-alist))
    (when tail
      (if r-sorter
          (ee-sort! tail (funcall r-sorter a-level r-level (assq ee-mark-attr-alist atree)))
        (ee-reverse! tail))
;       (if r-sorter
;           (setcdr atree (sort tail (funcall r-sorter a-level r-level attr-alist))))
      (while tail
;         (if (not (eq (caar tail) ee-mark-attr-alist))   ; if not attr-alist
            (if (consp (car tail))
                (ee-gen-r-tree-sort (car tail) (1+ a-level) (1+ r-level) r-sorter))
;           )
        (setq tail (cdr tail))))))

(defun ee-gen-c-tree-calc (atree a-level c-level s-level c-calculator r-calculator result-aname)
  (let* ((orig-atree atree)
         (a-level (1+ a-level))
         (c-level (1+ c-level))
         (result 0))
    (while atree
      (let* ((asubtree (car atree))
             (aname (car asubtree)))
        (cond
         ((eq aname ee-mark-attr-alist))
         ((eq aname ee-mark-record-tree)
          (setq asubtree (cdr asubtree))
          (while asubtree
            (setq result (+ result (ee-gen-r-tree-calc (car asubtree) a-level 0 r-calculator result-aname)))
            (setq asubtree (cdr asubtree))))
         ((eq aname ee-mark-subcategory-tree)
          (setq result (+ result (ee-gen-c-tree-calc (cdr asubtree) (- a-level 1) (- c-level 2) (1+ (abs s-level)) c-calculator r-calculator result-aname))))
         (t
          (let ((s-level (if (< s-level 0) 0 (- s-level))))
            (if c-calculator
                (setq result (+ result (funcall c-calculator a-level c-level (abs s-level) aname (assq ee-mark-attr-alist asubtree)))))
            (setq result (+ result (ee-gen-c-tree-calc (cdr asubtree) a-level c-level s-level c-calculator r-calculator result-aname)))))))
      (setq atree (cdr atree)))
    (if (> result 0)
        (ee-gen-add-path-atree (list ee-mark-attr-alist) (list result-aname result) orig-atree))
    result))

(defun ee-gen-r-tree-calc (atree a-level r-level r-calculator result-aname)
  (let ((head (if (consp atree) (car atree) atree))
        (tail (if (consp atree) (cdr atree)))
        (result 0))
    (when tail
      (while tail
        (setq result (+ result (ee-gen-r-tree-calc (car tail) (1+ a-level) (1+ r-level) r-calculator result-aname)))
        (setq tail (cdr tail))))
    ;; Add sum of subnodes to attribute alist of current node
    (if (> result 0)
        (ee-gen-add-path-atree (list ee-mark-attr-alist) (list result-aname result) (if (consp atree) atree (list atree))))
    ;; Calculate value of current node after the adding result to attribute alist,
    ;; so value of current node is not added to node's result
    (let ((r (if (integerp head) (aref ee-data head) head)))
      (if r-calculator
          (setq result (+ result (funcall r-calculator r a-level r-level (and tail t) result)))))
    result))


;;; Useful functions to use in view descriptions (TODO: add more)

;; c-printer: category exapansion line printer

(defun ee-c-printer-1 (a-level c-level s-level header)
  (insert (make-string a-level ?\040) "- " header))

(defun ee-c-printer-2 (a-level c-level s-level header)
  (insert (make-string (* 2 a-level) ?\040) "- " header))

(defun ee-c-printer-1-1 (a-level c-level s-level header)
  (insert (make-string (1- a-level) ?\040) "- " header))

(defun ee-c-printer-2-1 (a-level c-level s-level header)
  (insert (make-string (* 2 (1- a-level)) ?\040) "- " header))

(defun ee-c-printer-1-faces (a-level c-level s-level header)
  (let ((b (point))
        (face ))
    (insert (make-string a-level ?\040) "- " header)
    (if (< c-level (length ee-c-faces))
        (add-text-properties b (point) (list 'face (aref ee-c-faces c-level))))))

(defun ee-c-printer-2-faces (a-level c-level s-level header)
  (let ((b (point)))
    (insert (make-string (* 2 a-level) ?\040) "- " header)
    (add-text-properties b (point) (list 'face (aref ee-c-faces c-level)))))

(defun ee-c-printer-1-1-faces (a-level c-level s-level header)
  (let ((b (point)))
    (insert (make-string (1- a-level) ?\040) "- " header)
    (add-text-properties b (point) (list 'face (aref ee-c-faces c-level)))))

(defun ee-c-printer-2-1-faces (a-level c-level s-level header)
  (let ((b (point)))
    (insert (make-string (* 2 (1- a-level)) ?\040) "- " header)
    (add-text-properties b (point) (list 'face (aref ee-c-faces c-level)))))

(defun ee-c-face (c-level &optional default-index)
  (if (< c-level (length ee-c-faces))
      (aref ee-c-faces c-level)
    (aref ee-c-faces (or default-index 0))))

(defun ee-r-face (r-level &optional default-index)
  (if (< r-level (length ee-r-faces))
      (aref ee-r-faces r-level)
    (aref ee-r-faces (or default-index 0))))


;;; Data processing functions

;; TODO: add to subr.el after add-to-list (also delete-from-list from emacs.patches.el)
;; TODO: compare with (aput) from assoc.el
(defun ee-data-add-to-alist (alist-var aelement &optional append)
  "Add to the value of ALIST-VAR the element AELEMENT if it isn't there yet.
AELEMENT is association whose CAR is the key, and the CDR is the value.
The test for presence of key of AELEMENT is done with `assoc'.
If AELEMENT is added, it is added at the beginning of the alist,
unless the optional argument APPEND is non-nil, in which case
AELEMENT is added at the end.
Examples: (setq trees '((oak . acorns) (maple . seeds)))
          (add-to-alist 'trees '(pine . cones))
               => ((pine . cones) (oak . acorns) (maple . seeds))
          (add-to-alist 'trees '(pine . pineapple))
               => ((pine . pineapple) (oak . acorns) (maple . seeds))
          (add-to-alist 'trees '(pine . nil))
               => ((oak . acorns) (maple . seeds))

If you want to use `add-to-alist' on a variable that is not defined
until a certain package is loaded, you should put the call to `add-to-alist'
into a hook function that will be run only after loading the package.
`eval-after-load' provides one way to do this.  In some cases
other hooks, such as major mode hooks, can do the job."
  (let ((old-aelement (assoc (car aelement) (symbol-value alist-var))))
    (if old-aelement
        (if (cdr aelement)
            (setcdr old-aelement (cdr aelement))
          (set alist-var
               (delete old-aelement (symbol-value alist-var))))
      (set alist-var
           (if append
               (append (symbol-value alist-var) (list aelement))
             (cons aelement (symbol-value alist-var)))))
    (symbol-value alist-var)))

;; (ee-data-convert-lists-to-vectors '((a b c) (d e f)))
;; -> [meta-data [a b c] [d e f]]
(defun ee-data-convert-lists-to-vectors (lists)
  (apply 'vector
         'meta-data ;; placeholder for meta data
         (mapcar
          (lambda (list)
            (apply 'vector list))
          lists)))


;;; Data record-related functions

(defun ee-data-meta-get (data)
  (and data (aref data 0)))

(defun ee-data-meta-set (data value)
  (and data (aset data 0 value)))

(defun ee-data-meta-field-get (data field-name)
  (cdr (assq field-name (cdr (ee-data-meta-get data))))
  ;; TODO: use next code in ee-data-meta-[gs]etters-create too
  ;;   (let ((elt (cdr (assq field-name (cdr (ee-data-meta-get data))))))
  ;;     (if (and (consp elt)
  ;;              (eq (length elt) 1)
  ;;              (not (consp (car elt))))
  ;;         (car elt)
  ;;       elt))
  )

(defun ee-data-meta-field-set (data field-name field-value)
  (let ((meta (ee-data-meta-get data)))
    (ee-data-add-to-alist 'meta (cons field-name field-value) t)
    (ee-data-meta-set data meta)))

(defun ee-data-meta-getters-get-set (data)
  (or
   (ee-data-meta-field-get data 'getters)
   (let ((getters (ee-data-meta-getters-create data)))
     (ee-data-meta-field-set data 'getters getters)
     getters)))

(defun ee-data-meta-setters-get-set (data)
  (or
   (ee-data-meta-field-get data 'setters)
   (let ((setters (ee-data-meta-setters-create data)))
     (ee-data-meta-field-set data 'setters setters)
     setters)))

(defun ee-data-meta-getters-create (data)
  (let ((getters-hash (make-hash-table))
        (fields (ee-data-meta-field-get data 'fields))
        (fi 0))
    (while fields
      (let ((name (if (and (consp (car fields)) (eq (caar fields) 'field))
                      (cadr (assq 'name (car fields)))
                    (car fields))))
        ;; If field has no name, then use it for all additional fields
        (or name (setq name '(nil)))
        (cond
         ((consp name)
          (while name
            (puthash (car name)
                     ;; make "closure" with current field index
                     `(lambda (record field-name)
                        (cdr (assq field-name (aref record ,fi))))
                     getters-hash)
            (setq name (cdr name))))
         (t
          (puthash name
                   ;; make "closure" with current field index
                   `(lambda (record field-name)
                      (aref record ,fi))
                   getters-hash))))
      (setq fields (cdr fields)
            fi (1+ fi)))
    ;; TEST types: (list (cons 'buffer getters-hash))
    getters-hash))

(defun ee-data-meta-setters-create (data)
  (let ((setters-hash (make-hash-table))
        (fields (ee-data-meta-field-get data 'fields))
        (fi 0))
    (while fields
      (let ((name (if (and (consp (car fields)) (eq (caar fields) 'field))
                      (cadr (assq 'name (car fields)))
                    (car fields))))
        ;; If field has no name, then use it for all additional fields
        (or name (setq name '(nil)))
        (cond
         ((consp name)
          (while name
            (puthash (car name)
                     ;; make "closure" with current field index
                     `(lambda (record field-name field-value)
                        (let* ((field (aref record ,fi))
                               (old-value (assq field-name field)))
                          (if old-value
                              (setcdr old-value field-value)
                            (aset record ,fi (cons (cons field-name field-value) field)))))
                     setters-hash)
            (setq name (cdr name))))
         (t
          (puthash name
                   ;; make "closure" with current field index
                   `(lambda (record field-name field-value)
                      (aset record ,fi field-value))
                   setters-hash))))
      (setq fields (cdr fields)
            fi (1+ fi)))
    ;; TEST types: (list (cons 'buffer setters-hash))
    setters-hash))

(defun ee-data-field-get (field-name &optional record getters)
  (or record
      (setq record (ee-view-record-get)))
  (or getters
      (setq getters (or (and (boundp 'data-getters) data-getters)
                        (ee-data-meta-getters-get-set ee-data))))
  ;;   (if (consp getters)
  ;;       (setq getters (cdr (assq (aref record 0) getters))))
  (if (and record field-name getters)
      ;; At first try `field-name' and then `nil' for rest fields
      (let ((getter (or (gethash field-name getters)
                        (gethash nil getters))))
        (if (functionp getter)
            (funcall getter record field-name)))))

(defun ee-data-field-set (field-name field-value &optional record setters)
  (or record
      (setq record (ee-view-record-get)))
  (or setters
      (setq setters (or (and (boundp 'data-setters) data-setters)
                        (ee-data-meta-setters-get-set ee-data))))
  ;;   (if (consp setters)
  ;;       (setq setters (cdr (assq (aref record 0) setters))))
  (if (and record field-name setters)
      ;; At first try `field-name' and then `nil' for rest fields
      (let ((setter (or (gethash field-name setters)
                        (gethash nil setters))))
        (if (functionp setter)
            (funcall setter record field-name field-value)))))

;; Aliases
(fset 'ee-field     'ee-data-field-get)
(fset 'ee-field-get 'ee-data-field-get)
(fset 'ee-field-set 'ee-data-field-set)

(defun ee-data-field-names (data &optional record)
  (let ((fields (ee-data-meta-field-get data 'fields))
        (fi 0)
        res)
    (while fields
      (let ((name (if (and (consp (car fields)) (eq (caar fields) 'field))
                      (cadr (assq 'name (car fields)))
                    (car fields))))
        (cond
         ;; If field has no name, then extract field names from given record
         ((null name)
          (if record
              (setq res (append res (mapcar (lambda (x) (car x)) (aref record fi))))
            (setq res (append res '(nil)))))
         ((consp name)
          (while name
            (setq res (append res (list (car name))))
            (setq name (cdr name))))
         (t
          (setq res (append res (list name))))))
      (setq fields (cdr fields)
            fi (1+ fi)))
    res))

(defun ee-data-find-fields (list)
  (let ((field-names))
    (while (consp list)
      (if (eq (car list) 'ee-field)
          (setq field-names (cons (cadr (cadr list)) field-names)))
      (if (consp (car list))
          (setq field-names (append (ee-data-find-fields (car list)) field-names)))
      (setq list (cdr list)))
    field-names))

(defun ee-data-size (data)
  (if data
      ;; takes into account the metadata record
      (1- (length data))
    0))

;; TODO: defmacro?
(defun ee-data-records-do (data fun &optional start-index)
  (let ((_len (length data))
        (_i (or start-index 1))
        break) ; lambda can change variable `break'
    ;; TODO: let data-getters data-setters?
    (if (functionp fun)
        (while (and (< _i _len) (not break))
          (if (aref data _i)
              (funcall fun (aref data _i) _i))
          (setq _i (1+ _i))))))

(defun ee-data-records-find (data condition &optional getters)
  ;; Current format of `condition' is (field-name . field-value)
  ;; TODO: argument alist instead of field-name and field-value:
  ;; (and (field-name1 . field-value1) (field-name2 . field-value2))
  ;; (or  (field-name1 . field-value1) (field-name2 . field-value2))
  "Find all records from `data' using `condition'
in the format (field-name . field-value) where value of field
with name `field-name' is equal to `field-value'."
  (mapcar (lambda (ri)
            (aref data ri))
          (ee-data-record-indexes-find data condition getters)))

(defun ee-data-record-indexes-find (data condition &optional getters)
  ;; Current format of `condition' is (field-name . field-value)
  ;; TODO: argument alist instead of field-name and field-value:
  ;; (and (field-name1 . field-value1) (field-name2 . field-value2))
  ;; (or  (field-name1 . field-value1) (field-name2 . field-value2))
  "Find all records from `data' using `condition'
in the format (field-name . field-value) where value of field
with name `field-name' is equal to `field-value'."
  (let ((condition-type (if (consp (cdr condition)) (car condition)))
        (field-name (car condition))
        (field-value (cdr condition))
        (data-getters (or getters (ee-data-meta-getters-get-set data)))
        (len (length data))
        (ri 1)
        res)
    (ee-data-records-do
     data
     (lambda (r ri)
       (if (equal (ee-data-field-get field-name r data-getters) field-value)
           (setq res (cons ri res)))))
    (nreverse res)))

(defun ee-data-record-index-find (data field-name field-value &optional getters start-index)
  "Find first record index from `data' where value of field
with name `field-name' is equal to `field-value'."
  (let ((data-getters (or getters (ee-data-meta-getters-get-set data)))
        (len (length data))
        (i (or start-index 1))
        found)
    (while (and (not found) (< i len))
      (if (equal (ee-data-field-get field-name (aref data i) data-getters)
                 field-value)
          (setq found i))
      (setq i (1+ i)))
    found))

;; Next is obsoleted by ee-data-record-index-find
;; ;; TODO: call (car ee-data-records-find)?
;; (defun ee-data-record-index-by-key (key-field-name key-field-value data &optional getters start-index)
;;   (let ((data-getters (or getters (ee-data-meta-getters-get-set data)))
;;         record-index)
;;     (ee-data-records-do
;;      data
;;      (lambda (r ri)
;;        (if (equal (ee-data-field-get key-field-name r data-getters)
;;                   key-field-value)
;;            (setq record-index ri
;;                  break t)))
;;      start-index)
;;     record-index))

(defun ee-data-record-add (record &optional data)
  (let ((data (or data 'ee-data)))
    (if (eval data)
        (set data (vconcat (eval data) record)))))

(defun ee-data-record-delete (ri &optional squeeze)
  (when ee-data
    (aset ee-data ri nil)
    (if squeeze
        (setq ee-data (vconcat (delq nil (append ee-data nil)))))))

(defun ee-data-update (&optional data-type data data-file data-file-auto-save data-collect)
  ;; TODO: if data is nil, then in case of persistent data reread data from file
  (if (vectorp data)
      (if (eq data-type 'view-data)
          (setq ee-view-data data)
        (setq ee-data data)))
  (let ((data-file (or data-file
                       (if (eq data-type 'view-data)
                           (or ee-view-data-file
                               (ee-data-meta-field-get
                                (or data ee-data) 'view-data-file))
                         (or ee-data-file
                             (ee-data-meta-field-get
                              (or data ee-data) 'data-file))))))
    (if data-file
        (if (eq data-type 'view-data)
            (setq ee-view-data-file (or (ee-data-file-locate data-file)
                                        ;; Create new
                                        (ee-data-file-absolute-name data-file ee-data-directory))
                  data-file ee-view-data-file)
          (setq ee-data-file (or (ee-data-file-locate data-file)
                                 ;; Create new
                                 (ee-data-file-absolute-name data-file ee-data-directory))
                data-file ee-data-file)))
    (cond ((and (not data-collect)
                data-file
                (ee-data-file-exists-p data-file))
           (if (eq data-type 'view-data)
               (setq ee-view-data (ee-data-file-read data-file))
             (setq ee-data (ee-data-file-read data-file))))
          (t ;; (vectorp data)
           (let ((collector (ee-data-meta-field-get
                             (or data (if (eq data-type 'view-data)
                                          ee-view-data
                                        ee-data))
                             'collector)))
             (if (functionp collector)
                 (if (eq data-type 'view-data)
                     (let ((data-getters (ee-data-meta-getters-get-set ee-view-data)))
                       (setq ee-view-data
                             (funcall collector ee-view-data)))
                   (let ((data-getters (ee-data-meta-getters-get-set ee-data)))
                     (setq ee-data
                           (funcall collector ee-data))))))
           (if data-file-auto-save
               (ee-data-file-save data-type)))))
  (let ((mark-field-name (car (ee-data-meta-field-get ee-data 'mark-field))))
    (if mark-field-name
        (setq ee-data-mark-field-name mark-field-name))))


;;; Data file related functions

(defun ee-data-file-absolute-name (data-file data-directory)
  (if data-file
      (if (file-name-absolute-p data-file)
          data-file
        (expand-file-name data-file data-directory))))

(defun ee-data-file-exists-p (filename)
  (and (stringp filename)
       (file-exists-p filename)
       (not (file-directory-p filename))))

(defun ee-data-file-locate (filename)
  (let ((path (append (list ee-data-directory ee-view-data-directory)
                      load-path
                      (list ".")))
        found)
    (while (and path (not found))
      (if (ee-data-file-exists-p (ee-data-file-absolute-name filename (car path)))
          (setq found (ee-data-file-absolute-name filename (car path))))
      (setq path (cdr path)))
    found))

(defun ee-data-file-read (data-file)
  (if (ee-data-file-exists-p data-file)
      (let (data)
        (message "Reading data from %s..." data-file)
        (with-current-buffer (find-file-noselect data-file)
          (save-excursion
            (goto-char (point-min))
            (setq data (read (current-buffer)))))
        (message "Reading data from %s...done" data-file)
        data)))

(defun ee-data-file-save (&optional data-type format)
  (interactive)
  (if (if (eq data-type 'view-data)
          ee-data-file
        ee-view-data-file)
      (let ((format (or format ee-data-file-save-format))
            (data (if (eq data-type 'view-data)
                      ee-view-data
                    ee-data))
            (data-file (if (eq data-type 'view-data)
                           (ee-data-file-absolute-name
                            ee-view-data-file ee-view-data-directory)
                         (ee-data-file-absolute-name
                          ee-data-file ee-data-directory))))
        (if (not (and data data-file))
            (error "Wrong filename")
          (ee-data-meta-field-set data 'getters nil)
          (ee-data-meta-field-set data 'setters nil)
          (message "Saving data to %s..." data-file)
          (make-directory (file-name-directory data-file) t)
          (with-current-buffer (find-file-noselect data-file)
            (save-excursion
              (erase-buffer)
              (cond
               ((eq format 'records)
                (princ "[" (current-buffer))
                (pp (aref data 0) (current-buffer))
                (ee-data-records-do
                 data
                 (lambda (r ri)
                   (prin1 r (current-buffer))
                   (princ "\n" (current-buffer))))
                (princ "]" (current-buffer)))
               ((eq format 'pp)
                (pp data (current-buffer)))
               (t
                (prin1 data (current-buffer))))
              (princ "\n" (current-buffer))
              (save-buffer)))
          (message "Saving data to %s...done" data-file)))
    (if (interactive-p)
        (error "Filename not given"))))


;;; View expansion-related functions

(defmacro ee-view-expansion-get (point)
  `(or (get-text-property ,point 'ee-expansion)
       (save-excursion
         (goto-char ,point)
         (get-text-property (line-beginning-position) 'ee-expansion))))

(defmacro ee-view-expansion-level-get (point)
  `(or (get-text-property ,point 'ee-level)
       (save-excursion
         (goto-char ,point)
         (get-text-property (line-beginning-position) 'ee-level))))

(defmacro ee-view-expansion-path-get (point)
  `(or (get-text-property ,point 'ee-path)
       (save-excursion
         (goto-char ,point)
         (get-text-property (line-beginning-position) 'ee-path))))

(defun ee-view-on-expansion-line-p (&optional point)
  (and (ee-view-expansion-get (or point (point))) t))

(defun ee-view-expansion-visible-p (&optional point)
  "Non-nil if the expansion after point is visible."
  (let ((e (ee-view-expansion-get (or point (point)))))
    (and e (not (overlay-get e 'invisible)))
    ;; TODO:? (if (not e) (error "Not on expansion line"))
    ))


;;; View expansions visibility controlling commands

(defun ee-view-expansion-show (&optional p)
  (interactive "P")
  (let ((e (ee-view-expansion-get (or p (point)))))
    (if e
        (progn
          (overlay-put e 'invisible nil)
          (ee-view-expansion-update-buffer 'show p))
      (message "Not on expansion line.")))
  (if (interactive-p)
      (run-hooks 'ee-view-expansion-show-hook)))

(defun ee-view-expansion-hide (&optional p)
  (interactive "P")
  (let ((e (ee-view-expansion-get (or p (point)))))
    (if e
        (progn
          (overlay-put e 'invisible 'expansion) ; (overlay-put o 'invisible t)?
          (ee-view-expansion-update-buffer 'hide p))
      (message "Not on expansion line.")))
  (if (interactive-p)
      (run-hooks 'ee-view-expansion-hide-hook)))

(defun ee-view-expansion-update-buffer (&optional action p)
  ;; TODO: maybe, handle mode expansion styles here: ellipses, buttons, ...
  ;; ellipses = (add-to-invisibility-spec '(expansion . t))
  ;; TODO: maybe, call c-printer here or similar
  "Change the expansion character on the current line."
  (if (ee-view-on-expansion-line-p p)
      (save-excursion
        (or action (setq action (if (ee-view-expansion-visible-p p) 'hide 'show)))
        (and p (goto-char p))
        (beginning-of-line)
        (if (re-search-forward "\\s-*\\([-+]\\)" (line-end-position) t)
            (let ((modified-p (buffer-modified-p))
                  (inhibit-read-only t))
              (goto-char (1+ (match-beginning 1)))
              (insert-char (if (eq action 'show) ?- ?+) 1 t)
              ;; (insert-and-inherit (if (eq action 'show) "-" "+"))
              (forward-char -2)
              (delete-char 1)
              (set-buffer-modified-p modified-p))))))

(defun ee-view-expansion-show-or-hide-region (&optional from to action)
  (or from (setq from (point-min)))
  (or to   (setq to   (point-max)))
  (or action (setq action 'show))
  (let ((p (if (get-text-property from 'ee-expansion)
               from
             (or
              (previous-single-property-change from 'ee-expansion) ; TODO: 1-
              (next-single-property-change from 'ee-expansion)))))
    (while (and p
                (< p to)
                (setq p (next-single-property-change p 'ee-expansion)))
      (if (eq action 'show) ;;(not (ee-view-expansion-visible-p p))
          (ee-view-expansion-show p)
        (ee-view-expansion-hide p))
      (setq p (next-single-property-change p 'ee-expansion))))
;;   (save-excursion
;;     (goto-char from)
;;     (while (< (point) to);;(not (eobp))
;;       ;(beginning-of-line)               ; hack
;;       (if (and (ee-view-on-expansion-line-p)
;;                (not (ee-view-expansion-visible-p)))
;;           (ee-view-expansion-show))
;;       (forward-line 1) ;(next-line 1) ; next-line to ignore invisible lines
;;       ))
  )

(defun ee-view-expansion-show-all ()
  (interactive)
  (ee-view-expansion-show-or-hide-region (point-min) (point-max)))

(defun ee-view-expansion-show-subtree ()
  (interactive)
  (let ((e (ee-view-expansion-get (point))))
    (if e
        (ee-view-expansion-show-or-hide-region (overlay-start e)
                                               (overlay-end e)))))

(defun ee-view-expansion-show-children (&optional level)
  "Shows own children up to level, but hides children expansions."
  (interactive)
  ;; TODO: implement it
  )

;; Convenience functions
(defun ee-view-expansion-show-or-hide (&optional arg)
  (interactive "P")
  (or (ee-view-on-expansion-line-p)
      (ee-view-expansion-prev-visible 1))
  (if (ee-view-on-expansion-line-p)
      (if (ee-view-expansion-visible-p)
          (ee-view-expansion-hide arg)
        (ee-view-expansion-show arg))
    (message "Not on expansion line.")))

(defun ee-view-expansion-show-or-next ()
  (interactive)
  (if (and (ee-view-on-expansion-line-p)
           (not (ee-view-expansion-visible-p)))
      (ee-view-expansion-show)
    ;; (next-line 1)
    ;; (forward-char)
    (ee-view-expansion-next)))

(defun ee-view-expansion-hide-all-visible ()
  (interactive)
  (ee-view-key-save)
  (save-excursion
    (goto-char (point-max))
    (while (not (and (bobp) (not (ee-view-expansion-visible-p))))
      (beginning-of-line)               ; hack
      (if (and (ee-view-on-expansion-line-p)
               (ee-view-expansion-visible-p))
          (ee-view-expansion-hide))
      (or (bobp) (previous-line 1)) ; previous-line to ignore invisible lines
      ))
  (ee-view-key-restore)
  ;; (ee-view-expansion-prev)
  )

(defun ee-view-expansion-hide-all ()
  (interactive)
  ;; TODO: implement by going throught all invisible expansions
  ;;? (ee-view-expansion-show-all)
  ;; (ee-view-expansion-hide-all-visible)
  (ee-view-expansion-show-or-hide-region (point-min) (point-max) 'hide))

(defun ee-view-expansion-hide-subtree ()
  (interactive)
  (let ((e (ee-view-expansion-get (point))))
    (if e
        (ee-view-expansion-show-or-hide-region (overlay-start e)
                                               (overlay-end e)
                                               'hide))))

(defun ee-view-expansion-hide-or-up-or-prev ()
  (interactive)
  (if (and (ee-view-on-expansion-line-p)
           (ee-view-expansion-visible-p))
      (ee-view-expansion-hide)
    ;; (backward-char)
    (let ((point (point)))
      (ee-view-expansion-up 1)
      (if (eq point (point))
          (ee-view-expansion-prev-visible 1)))))

;; TODO: treat marks similar to the hidden expansions?
;; qv dired-remember-hidden and dired-remember-marks
(defun ee-view-expansion-save-all-hidden ()
  (let ((p (point-min))
        hidden-expansions)
    (while (and p (or (get-text-property p 'ee-path)
                      (setq p (next-single-property-change p 'ee-path))))
      (if (not (ee-view-expansion-visible-p p))
          (setq hidden-expansions (cons (reverse (get-text-property p 'ee-path)) hidden-expansions)))
      (setq p (next-single-property-change p 'ee-path)))
    hidden-expansions))


;;; View expansions navigation (movement) commands

(defun ee-view-goto-hook-default ()
  (cond ((ee-view-on-record-line-p)
         (if ee-goal-column
             (move-to-column ee-goal-column)))
        ((ee-view-on-expansion-line-p) ;; TODO: should be (ee-view-on-category-line-p)?
         (beginning-of-line))))

(defun ee-view-expansion-next ()
  "Move to the next (possibly invisible) expansion heading line."
  (interactive)
  (let ((point (point)))
    (if (ee-view-expansion-get point) ; move off expansion heading line
        (setq point (next-single-property-change point 'ee-expansion)))
    (if point
        (setq point (next-single-property-change point 'ee-expansion)))
    (if point
        (goto-char point)))
  (run-hooks 'ee-view-goto-hook))

(defun ee-view-expansion-prev ()
  "Move to the prev (possibly invisible) expansion heading line."
  (interactive)
  (let ((point (point)))
    (if (ee-view-expansion-get point) ; move off expansion heading line
        (setq point (previous-single-property-change point 'ee-expansion)))
    (if point
        (setq point (previous-single-property-change point 'ee-expansion)))
    (if point
        (goto-char point)))
  (run-hooks 'ee-view-goto-hook))

(defun ee-view-expansion-next-visible (arg)
  "Move to the next visible heading line.
With argument, repeats or can move backward if negative."
  (interactive "p")
  (while (and (not (bobp)) (< arg 0))
    (previous-line 1)        ; previous-line to ignore invisible lines
    (while (and (not (bobp))
                (not (ee-view-on-expansion-line-p)))
      (previous-line 1))
    (setq arg (1+ arg)))
  (while (and (not (eobp)) (> arg 0))
    (next-line 1)                ; next-line to ignore invisible lines
    (while (and (not (eobp))
                (not (ee-view-on-expansion-line-p)))
      (next-line 1))
    (setq arg (1- arg)))
  (run-hooks 'ee-view-goto-hook))

(defun ee-view-expansion-prev-visible (arg)
  "Move to the previous expansion heading line.
With argument, repeats or can move forward if negative."
  (interactive "p")
  (ee-view-expansion-next-visible (- arg)))

(defun ee-view-expansion-up (arg)
  "Move to the expansion heading line of which the current line is a subheading.
With argument, move up ARG levels."
  (interactive "p")
  (if (not (ee-view-on-expansion-line-p))
      (ee-view-expansion-prev-visible 1)
    (while (and (> (ee-view-expansion-level-get (point)) 1)
                (> arg 0)
                (not (bobp)))
      (let ((curr-level (ee-view-expansion-level-get (point))))
        (while (and (not (< (ee-view-expansion-level-get (point)) curr-level))
                    (not (bobp)))
          (ee-view-expansion-prev-visible 1))
        (setq arg (- arg 1)))))
  (run-hooks 'ee-view-goto-hook))

(defun ee-view-expansion-down ()
  (interactive)
  ;; (goto-char (ee-find-expansion-down))
  )

;; TODO: ee-view-expansion-current

(defun ee-view-expansion-sibling-next ()
  (interactive)
  (let ((level (ee-view-expansion-level-get (point))))
    ;; save-excursion
    (forward-line 1)
    ;; TODO: find prev prop with ee-level=level
    (text-property-any (point) (point-max) 'ee-level level)))

(defun ee-view-expansion-sibling-prev ()
  (interactive)
  ;; (goto-char (ee-find-expansion-next-sibling))
  (beginning-of-line))


;;; View record-related functions

;; generic fun
(defmacro ee-view-prop-get (prop point)
  `(or (get-text-property ,point ,prop)
       (save-excursion
         (goto-char ,point)
         (get-text-property (line-beginning-position) ,prop))))

(defmacro ee-view-record-index-get (point)
  `(or (get-text-property ,point 'ee-ri)
       (save-excursion
         (goto-char ,point)
         (get-text-property (line-beginning-position) 'ee-ri))))

(defun ee-view-on-record-line-p (&optional point)
  (and (ee-view-record-index-get (or point (if (eolp) (max (1- (point)) (point-min)) (point)))) t))

(defun ee-view-record-get (&optional point)
  (let ((ri (ee-view-record-index-get (or point (point)))))
    (and ee-data ri (aref ee-data ri))))

;; (fset 'ee-view-record-current 'ee-view-record-get)

;; TODO: rename to ...-clone
(defun ee-view-record-copy (&optional point)
  (interactive)
  (setq ee-data (vconcat ee-data (list (ee-view-record-get))))
  (ee-view-buffer-update))

;; TODO: confirmation
(defun ee-view-record-delete (&optional point)
  (interactive)
  (let ((ri (ee-view-record-index-get (or point (point)))))
    (if (and ee-data ri)
        (ee-data-record-delete ri)))
  (ee-view-buffer-update))


;;; View records navigation (movement) commands

(defun ee-view-record-first ()
  (interactive)
  (goto-char (point-min))
  (if (not (ee-view-on-record-line-p))
      (ee-view-record-next))
  (run-hooks 'ee-view-goto-hook))

(defun ee-view-record-next (&optional arg)
  ;; TODO: use arg
  (interactive)
;;   (message "1:[%s]" (line-number-at-pos (point)))
  (when (not (eobp))
;;     (message "!1:[%s]" (eobp))
    (next-line 1)                ; next-line to ignore invisible lines
;;     (message "!2:[%s]" (eobp))
    (while (not (or (ee-view-on-record-line-p) (eobp)))
;;       (message "?:[%s]" (eolp))
      (next-line 1)))
;;   (message "2:[%s]" (line-number-at-pos (point)))
  (run-hooks 'ee-view-goto-hook))

(defun ee-view-record-next-with (fun &optional arg)
  ;; TODO: use arg
  (interactive)
  (when (and fun (not (eobp)))
    (next-line 1)                ; next-line to ignore invisible lines
    (while (not (or (and (ee-view-on-record-line-p) (funcall fun)) (eobp)))
      (next-line 1)))
  (run-hooks 'ee-view-goto-hook))

(defun ee-view-record-next-or-first (arg)
  ;; TODO: implement it
  )

(defun ee-view-record-last ()
  ;; TODO: implement it
  )

(defun ee-view-record-prev-or-last ()
  ;; TODO: implement it
  )

(defun ee-view-record-prev (&optional arg)
  ;; TODO: use arg
  (interactive)
  (when (not (bobp))
    (previous-line 1)        ; previous-line to ignore invisible lines
    (while (not (or (ee-view-on-record-line-p) (bobp)))
      (previous-line 1)))
  (run-hooks 'ee-view-goto-hook))

(defun ee-view-record-with (function)
  ;; e.g. (ee-view-record-with (lambda () (ee-data-field-get 'unread)))
  )

;; old (and still better?) name: ee-view-goto-r-line
(defun ee-view-record-by-key (key-field-value)
  (let* ( ;; TODO: multiple key fields (currently only first key is considered)
         (key-field-name (car (ee-data-meta-field-get ee-data 'key-fields)))
         (ri (ee-data-record-index-find ee-data key-field-name key-field-value)))
    (if ri
        (ee-view-record-by-index ri))))

(defun ee-view-record-by-index (record-index)
  "Return non-nil if record was found."
  (let ((p (text-property-any (point-min) (point-max) 'ee-ri record-index)))
    (when p
      (goto-char p)
      (run-hooks 'ee-view-goto-hook)
      p)))


;;; View records marking commands

;; Commands to mark or flag item(s) at or near current line.
;; TODO: (ee-view-repeat-over-lines) - DONE below
;; TODO: (if (and transient-mark-mode mark-active) (ee-view-mark-region))
;; (defun ee-view-mark (mark-field-name mark-field-value arg)
;;   ;; NOT COMPLETED: moving to previous expansion line is not implemented, etc.
;;   ;; TODO: split to different functions?
;;   "Mark buffer on this line.
;; Prefix arg is how many records to mark.
;; Negative arg means mark backwards."
;;   (let ((e-line-p (ee-view-on-expansion-line-p)))
;;     (if (or (null arg) (= arg 0))
;;         (setq arg 1))
;;     (while (> arg 0)
;;       (ee-set-field (ee-view-record-get) mark-field-name mark-field-value)
;;       (if e-line-p
;;           (ee-view-expansion-line-next)
;;         (ee-view-record-next))
;;       (setq arg (1- arg)))
;;     (while (< arg 0)
;;       (ee-set-field (ee-view-record-get) mark-field-name mark-field-value)
;;       (if e-line-p
;;           (ee-view-expansion-line-prev)
;;         (ee-view-record-prev))
;;       (setq arg (1+ arg))))
;;   (ee-view-buffer-generate))

(defun ee-view-mark-lines (mark-field-name mark-field-value arg)
  "Mark all record lines under current expansion line.
Advances point."
  (interactive)
  (if (ee-view-on-expansion-line-p)
      (ee-view-repeat-over-lines
       'e
       (prefix-numeric-value arg)
       (function (lambda () (ee-view-mark-expansion mark-field-name mark-field-value))))
    (ee-view-repeat-over-lines
     'r
     (prefix-numeric-value arg)
     (function (lambda () (ee-view-mark-record mark-field-name mark-field-value)))))
  (ee-view-buffer-update))

;; adapted from dired-repeat-over-lines
;; TODO: maybe better to make 2 separate functions instead of line-type argument?
;; ee-view-repeat-over-r-lines and ee-view-repeat-over-e-lines
;; TODO: compare with ee-view-record-next-with
(defun ee-view-repeat-over-lines (line-type arg function)
  ;; This version skips non-record lines.
  (let ((pos (make-marker)))
    (beginning-of-line)
    (while (and (> arg 0) (not (eobp)))
      (setq arg (1- arg))
      (beginning-of-line)
;;       (while (and (not (eobp))
;;                   ;; TODO: rename ee-view-on-expansion-line to ee-view-on-e-line
;;                   ;; TODO: rename ee-view-on-record-line to ee-view-on-r-line
;;                   (not (or (and (eq line-type 'e) (ee-view-on-expansion-line-p))
;;                            (and (eq line-type 'r) (ee-view-on-record-line-p)))))
;;         (forward-line 1))
      (save-excursion
        ;; TODO: rename next functions
        (cond ((eq line-type 'e) (ee-view-expansion-next))
              ((eq line-type 'r) (ee-view-record-next)))
        (move-marker pos (1+ (point))))
      (save-excursion (funcall function))
      ;; Advance to the next line--actually, to the line that *was* next.
      ;; (If FUNCTION inserted some new lines in between, skip them.)
      (goto-char pos))
    (while (and (< arg 0) (not (bobp)))
      (setq arg (1+ arg))
      ;; TODO: rename next functions:
      ;; (ee-view-e-next -1) (ee-view-expansion-next -1)
      ;; (ee-view-r-next -1) (ee-view-record-next -1)
      (cond ((eq line-type 'e) (ee-view-expansion-prev))
            ((eq line-type 'r) (ee-view-record-prev)))
;;       (while (and (not (eobp))
;;                   ;; TODO: rename ee-view-on-expansion-line to ee-view-on-e-line
;;                   ;; TODO: rename ee-view-on-record-line to ee-view-on-r-line
;;                   (not (or (and (eq line-type 'e) (ee-view-on-expansion-line-p))
;;                            (and (eq line-type 'r) (ee-view-on-record-line-p)))))
      (beginning-of-line)
      (save-excursion (funcall function)))
    (move-marker pos nil)))

(defun ee-view-mark-record (mark-field-name mark-field-value)
  (let ((old-marks (ee-data-field-get mark-field-name
                                      (ee-view-record-get)
                                      (ee-data-meta-getters-get-set ee-data))))
    (ee-data-field-set mark-field-name
                       (if mark-field-value
                           (if (memq mark-field-value old-marks)
                               old-marks
                             (list mark-field-value))
                         mark-field-value)
                       (ee-view-record-get)
                       (ee-data-meta-setters-get-set ee-data))))

(defun ee-view-mark-expansion (mark-field-name mark-field-value)
  "Mark all record lines under current expansion line."
  (let ((e (ee-view-expansion-get (point))))
    (and e (ee-view-mark-region mark-field-name mark-field-value
                                (point)
                                (overlay-end e) ;TODO: make function
                                ))))

(defun ee-view-mark-region (mark-field-name mark-field-value from to)
  "Mark all record lines in region."
  (or from (setq from (point-min)))
  (or to   (setq to   (point-max)))
  (save-excursion
    (goto-char from)
    (let ((setters (ee-data-meta-setters-get-set ee-data)))
      (while (< (point) to) ;;(not (eobp))
        (when (ee-view-on-record-line-p)
          ;;(ee-data-field-set mark-field-name mark-field-value (ee-view-record-get) setters)
          (ee-view-mark-record mark-field-name mark-field-value)
          ;;(ee-view-update '(mark))
          )
        (forward-line 1) ;(next-line 1)            ; next-line to ignore invisible lines
        ))))

(defun ee-view-records-unmark (&optional arg)
  "Cancel all requested operations on this line and move down."
  (interactive "P")
;   (ee-view-mark ee-data-mark-field-name nil arg)
  ;; TODO: unmark only prev used mark
  (ee-view-mark-lines ee-data-mark-field-name nil arg)
;;   (if (ee-view-on-expansion-line-p)
;;       (ee-view-expansion-next-visible 1)
;;     (ee-view-record-next))
;;     (next-line 1) ;; BAD: ?(ee-view-record-next)
  )

(defun ee-view-records-unmark-backwards (&optional arg)
  "Move up and cancel all requested operations on this line."
  (interactive "p")
;;   (if (ee-view-on-expansion-line-p)
;;       (ee-view-expansion-prev-visible 1)
;;     (ee-view-record-prev))
;;     (next-line 1) ;; BAD: ?(ee-view-record-next)
;;   (ee-view-mark ee-data-mark-field-name nil arg)
  ;; TODO: unmark only prev used mark
  (ee-view-mark-lines ee-data-mark-field-name nil (- arg)))

;; TODO: create ee-mark-if (similar dired-mark-if)
;; TODO: create ee-mark-files-containing-regexp (similar dired-mark-files-containing-regexp)

(defun ee-view-records-mark (&optional arg)
  "Mark buffer on this line to be deleted by \\<ee-mode-map>\\[ee-view-records-execute] command.
Prefix arg is how many records to delete.
Negative arg means delete backwards."
  (interactive "p")
  (ee-view-mark-lines ee-data-mark-field-name ee-mark-mark arg))

(defun ee-view-records-mark-delete (&optional arg)
  "Mark buffer on this line to be deleted by \\<ee-mode-map>\\[ee-view-records-execute] command.
Prefix arg is how many records to delete.
Negative arg means delete backwards."
  (interactive "p")
  ;; (ee-view-mark ee-data-mark-field-name ee-mark-del arg)
  (ee-view-mark-lines ee-data-mark-field-name ee-mark-del arg)
  ;;   (if (ee-view-on-expansion-line-p)
  ;;       (ee-view-expansion-next-visible 1)
  ;;     (ee-view-record-next))
  ;;     (next-line 1) ;; BAD: ?(ee-view-record-next)
  )

(defun ee-view-records-mark-delete-backwards (&optional arg)
  "Mark buffer on this line to be deleted by \\<ee-mode-map>\\[ee-view-records-execute] command
and then move up one line.  Prefix arg means move that many lines."
  (interactive "p")
  (ee-view-mark-lines ee-data-mark-field-name ee-mark-del (- (or arg 1))))

(defun ee-view-records-delete ()
  "Delete records immediately."
  (interactive)
  (let* ((data-getters (ee-data-meta-getters-get-set ee-data))
         (view-getters (ee-data-meta-getters-get-set ee-view-data))
         (r (ee-view-record-get))
         (ri (ee-view-record-index-get (point)))
         (r-execute (ee-data-field-get 'r-execute ee-view view-getters)))
    (if (and r (functionp r-execute))
        (funcall r-execute r (list ee-mark-del)))
    (ee-data-record-delete ri))
  (ee-view-buffer-update t))

(defun ee-view-records-execute ()
  "Execute records marked with marking commands."
  (interactive)
  (let* ((data-getters (ee-data-meta-getters-get-set ee-data))
         (view-getters (ee-data-meta-getters-get-set ee-view-data))
         (r-execute (ee-data-field-get 'r-execute ee-view view-getters)))
    (ee-data-records-do
     ee-data
     (lambda (r ri)
       (if (functionp r-execute)
           (funcall r-execute r (ee-data-field-get ee-data-mark-field-name r data-getters)))
       (if (memq ee-mark-del (ee-data-field-get ee-data-mark-field-name r data-getters))
           (ee-data-record-delete ri)))))
  (ee-view-buffer-update t))


;;; View categories navigation (movement) commands


;;; Action-related functions

(defun ee-view-record-select-or-expansion-show-or-hide (&optional arg)
  (interactive "P")
  (if (ee-view-on-record-line-p)
      (ee-view-record-select arg)
    (ee-view-expansion-show-or-hide arg)))

(defun ee-view-record-select (&optional arg)
  (interactive "P")
  (if (ee-view-on-record-line-p)
      (let* ((data-getters (ee-data-meta-getters-get-set ee-data))
             (data-setters (ee-data-meta-setters-get-set ee-data))
             (view-getters (ee-data-meta-getters-get-set ee-view-data))
             (r-select (ee-data-field-get 'r-select ee-view view-getters)))
        (if (functionp r-select)
            (funcall r-select arg)))))


;;; View updating

(defun ee-view-record-update ()
  (save-excursion
    (goto-char (line-beginning-position))
    (let* ((inhibit-read-only t)
           (modified-p (buffer-modified-p))
           (b (point-marker))
           (e (point-marker))
           (plist (text-properties-at b))
           (r (ee-view-record-get))
           ;; TODO: make fun ee-view-record-get-info similar to ee-view-record-index-get
           )
      (set-marker b (line-beginning-position))
      (set-marker e (line-end-position))
      (set-marker-insertion-type b t)
      ;; (ee-gen-r-tree-print (ee-view-record-get)
      ;;                      (ee-view-prop-get 'ee-level (point))
      ;;                      (ee-view-prop-get 'ee-rlevel (point))
      ;;                      (ee-data-field-get 'r-printer ee-view (ee-data-meta-getters-get-set ee-view-data))
      ;;                      nil)
      (funcall (ee-data-field-get 'r-printer ee-view (ee-data-meta-getters-get-set ee-view-data))
               r ;; (ee-view-record-get)
               (plist-get plist 'ee-level) ;; (ee-view-prop-get 'ee-level (point))
               (plist-get plist 'ee-rlevel) ;; (ee-view-prop-get 'ee-rlevel (point))
               (plist-get plist 'ee-childrenp) ;; (ee-view-prop-get 'ee-childrenp (point))
               (plist-get plist 'ee-attrs) ;; (ee-view-prop-get 'ee-attrs (point))
               )
      (delete-region b e)
      (set-marker b nil nil)
      (set-marker e nil nil)
      ;; TODO: preserve "+" for collapsed category
      (while plist
        (if (string-match "^ee-" (symbol-name (car plist)))
            (add-text-properties (line-beginning-position)
                                 (1+ (line-beginning-position))
                                 (list (car plist) (cadr plist))))
        (setq plist (cddr plist))
        (set-buffer-modified-p modified-p)))))

(defun ee-view-update (&optional field-names)
  (let ((view (aref ee-view 0))
        alist
        (record-update-p t))
    (while view
      (setq alist (cons (cons (caar view)
                              (ee-data-find-fields (cdar view)))
                        alist))
      (setq view (cdr view)))
    (while field-names
      (if (or (memq (car field-names) (cdr (assq 'r-filter alist)))
              (memq (car field-names) (cdr (assq 'c-path-finder alist)))
              (memq (car field-names) (cdr (assq 'r-parent-child-key-fields alist)))
              (memq (car field-names) (cdr (assq 'r-calculator alist)))
              (memq (car field-names) (cdr (assq 'c-printer alist))))
          (setq record-update-p nil))
      (setq field-names (cdr field-names)))
    (cond
     (record-update-p (ee-view-record-update))
     (t (ee-view-buffer-update)))))

(defun ee-view-key-save ()
  (if (ee-view-on-record-line-p)
      (setq ee-current-r-key-field
            ;; TODO: multiply key fields (currently only first key is considered)
            (ee-data-field-get (car (ee-data-meta-field-get ee-data 'key-fields))
                               (ee-view-record-get)
                               (ee-data-meta-getters-get-set ee-data)))
    (setq ee-current-c-key-field (nreverse (ee-view-expansion-path-get (point)))
          ee-current-r-key-field nil)))

(defun ee-view-key-restore ()
  (if ee-current-r-key-field
      (ee-view-record-by-key ee-current-r-key-field)
    (ee-view-category-goto-by-path ee-current-c-key-field)))

(defun ee-view-buffer-update (&optional update-data)
  (interactive)
  (setq ee-hidden-expansions (ee-view-expansion-save-all-hidden))
  (ee-view-key-save)
  ;; BAD: in case of persistent data reread data from file
  ;; GOOD: force to collect data again
  (if update-data
      (if (eq update-data 'collect)
          (ee-data-update nil nil nil nil t)
        (ee-data-update)))
  (ee-view-buffer-generate)
  (ee-view-key-restore)
  (let ((update-hook (ee-data-field-get 'post-update ee-view
                                        ;; TODO: default getters or global variable
                                        (ee-data-meta-getters-get-set ee-view-data))))
    (if update-hook;;nil;TEST:update-hook
        (funcall update-hook))))

;; old name: ee-view-goto-c-line
(defun ee-view-category-goto-by-path (c-path)
  (setq c-path (reverse c-path))
  (let ((p (point-min)))
    (while (and p (or (get-text-property p 'ee-path)
                      (setq p (next-single-property-change p 'ee-path))))
      (if (equal c-path (get-text-property p 'ee-path))
          (goto-char p))
      (setq p (next-single-property-change p 'ee-path)))))

(defun ee-view-buffer-revert ()
  "Update the current buffer."
  (interactive)
  (if revert-buffer-function
      (revert-buffer)
    (message "No revert function is associated with this buffer.")))

(defun ee-view-buffer-revert-function-default (ignore1 ignore2)
  "Default revert buffer function."
  (ee-view-buffer-update 'collect))

;; TODO: dynamically add search filters
(defun ee-view-filter-omit ()
  "Refresh w/o filter, i.e. show all records."
  (interactive)
  (setq ee-view-filter-omit (not ee-view-filter-omit))
  (ee-view-buffer-revert))

;; TODO: bind to M-C-l
(defun ee-view-reposition-window ()
  (interactive)
  ;; TODO: implement it
  )


;;; One-click mouse gesture hierarchical navigation

(defun ee-mouse-navigation (&optional event)
  "One-click mouse gesture expansion tree navigation.
This function is called when mouse button is pressed.
Mouse motion to right direction on the expansion line shows expansion.
Mouse motion to left direction on the expansion line hides expansion.
The moment of starting these actions depends on the value
of `ee-mouse-expansion-sensitivity', which defines how many positions
mouse should be moved in one direction before expansion is shown or hidden.
Any mouse motion on top window lines scrolls the window downward.
Any mouse motion on bottom window line scrolls the window upward.
Number of lines of margin is defined by `ee-mouse-scroll-margin'.
Number of lines to scroll is defined by `ee-mouse-scroll-lines'.
Releasing mouse button calls default select action on the line
where button was released, if this line is not expansion line.
On the expansion lines releasing mouse button shows or hides
expansion, only when no mouse motions were performed,
i.e. button was only pressed and released. If mouse was moved
\(with possible expansions or collapses during mouse movement)
and released on expansion line, then no action is performed."
  (interactive "e")
  (if event
      (select-window (car (event-start event))))
  (let (prev-x
        prev-y
        (x-motions 0) ; Accumulates number of motions in one direction on one line:
                      ; motion to the left decreases negative number
                      ; motion to the right increases positive number
        (top-margin (- ee-mouse-scroll-margin 1))
        (bottom-margin (- (window-height) 1 ee-mouse-scroll-margin)))
    (track-mouse
      (or event (setq event (read-event)))
      (while (not (ee-mouse-button-release-event-p event))
        (if (eq (car-safe event) 'mouse-movement)
            (let* ((posn (posn-col-row-sans-header (event-end event)))
                   (next-x (car posn))
                   (next-y (cdr posn)))
              (if (eq next-y prev-y)
                  (cond
                   ((> next-x prev-x)
                    (setq x-motions
                          (1+ (if (> x-motions 0) x-motions 0))))
                   ((< next-x prev-x)
                    (setq x-motions
                          (1- (if (< x-motions 0) x-motions 0)))))
                (setq x-motions 0))
              (cond
               ((and (<= next-y top-margin)
                     (> (window-start) (point-min)))
                (ignore-errors (scroll-up (- ee-mouse-scroll-lines))))
               ((>= next-y bottom-margin)
                (ignore-errors (scroll-up ee-mouse-scroll-lines)))
               ((>= x-motions ee-mouse-expansion-sensitivity)
                (setq x-motions 0)
                (move-to-window-line next-y)
                (ee-view-expansion-show))
               ((>= (- x-motions) ee-mouse-expansion-sensitivity)
                (setq x-motions 0)
                (move-to-window-line next-y)
                (ee-view-expansion-hide)))
              (setq prev-x next-x
                    prev-y next-y)))
        (setq event (read-event))))
    (move-to-window-line (cdr (posn-col-row-sans-header (event-end event))))
    (if prev-y
        ;; If button was released after motions
        (ee-view-record-select)
      ;; If button was released without motions
      (ee-view-record-select-or-expansion-show-or-hide))))

(defun posn-col-row-sans-header (position)
  (let ((pair (posn-col-row position)))
    (if (or (and (boundp 'header-line-format) header-line-format)
            (and (boundp 'default-header-line-format) default-header-line-format))
        (cons (car pair) (- (cdr pair) 1))
      pair)))

(defun ee-mouse-button-release-event-p (obj)
  ;; borrowed from levents.el
  ;; (require 'levents) ?
  ;; TODO: test in other versions of Emacs
  "True if the argument is a mouse-button-release event object."
  (and (consp obj)
       (symbolp (car obj))
       (or (memq 'click (get (car obj) 'event-symbol-elements))
           (memq 'drag (get (car obj) 'event-symbol-elements)))))


;;; Utility Functions

;; TODO: move next function to view/links.ee
;; TODO: make the same view in bbdb mails
(defun ee-links-url-to-list (url)
  ;; TODO: use standard URL regexps like thing-at-point-url-regexp
  (let ((host (ee-split-string
               (if (string-match "[^:/]+[:/]+\\([^:/]+\\)" url)
                   (match-string 1 url)
                 url)
               "[.@]")))
    (if (equal (car host) "www")
        (setq host (cdr host)))
    (nreverse host)))

;; TODO: move next function to view/links.ee
(defun ee-links-select (&optional arg)
  (interactive)
  (cond
   ((ee-data-field-get 'command)
    (let ((command (ee-data-field-get 'command)))
      (and ee-parent-buffer (set-buffer ee-parent-buffer))
      (and command (funcall command))))
   ((ee-data-field-get 'url)
    (browse-url (ee-data-field-get 'url)))
   ((ee-data-field-get 'url) ; TODO: better
    (browse-url (car (ee-data-field-get 'locations))))))


;;; Compatibility Functions

;; TODO: use package prefix for aliases
;; qv on emacs-devel Subject: Compatibility aliases, defsubsts, and macros...
;; (if (fboundp 'mapcan)
;;     (defalias 'ee-mapcan 'mapcan)
;;   (defun ee-mapcan (func seq)
;;     (apply 'nconc (mapcar func seq))))
;; (defalias 'ee-mapcan ;; defsubst
;;   (if (fboundp 'mapcan)
;;       'mapcan
;;     'mapcan??))

(or (fboundp 'mapcan)
(defun mapcan (func seq)
  "Like `mapcar', but nconc's together the values returned by the function."
  (apply 'nconc (mapcar func seq))))

;; GNU Emacs 20.7 compatibility
(or (fboundp 'mapc)
(defun mapc (function sequence)
  "Apply FUNCTION to each element of SEQUENCE for side effects only.
Unlike `mapcar', don't accumulate the results.  Return SEQUENCE.
SEQUENCE may be a list, a vector, a bool-vector, or a string."
  (mapcar function sequence)
  sequence))

(or (fboundp 'ignore-errors)
(defmacro ignore-errors (&rest body)
  "Execute BODY; if an error occurs, return nil.
Otherwise, return result of last form in BODY."
  `(condition-case nil (progn ,@body) (error nil))))

(or (fboundp 'delete-dups)
;; from GNU Emacs 22.0
(defun delete-dups (list)
  "Destructively remove `equal' duplicates from LIST.
Store the result in LIST and return it.  LIST must be a proper list.
Of several `equal' occurrences of an element in LIST, the first
one is kept."
  (let ((tail list))
    (while tail
      (setcdr tail (delete (car tail) (cdr tail)))
      (setq tail (cdr tail))))
  list))

(or (fboundp 'remove-overlays)
;; like in GNU Emacs 22.0, but works only on the whole buffer
(defun remove-overlays ()
  (mapc 'delete-overlay (overlays-in (point-min) (point-max)))))

;; GNU Emacs 20.7 compatibility
(or (fboundp 'puthash)
(defalias 'puthash 'cl-puthash))
(or (fboundp 'gethash)
(defalias 'gethash 'cl-gethash))

;; GNU Emacs 20.7 compatibility
(or (fboundp 'float-time)
(defun float-time (&optional time)
  "Return the current time, as a float number of seconds since the epoch.
If SPECIFIED-TIME is given, it is the time to convert to float
instead of the current time.  The argument should have the form
\(HIGH LOW . IGNORED). Thus, you can use times obtained from
`current-time' and from `file-attributes'.  SPECIFIED-TIME can also
have the form (HIGH . LOW), but this is considered obsolete.

WARNING: Since the result is floating point, it may not be exact.
Do not use this function if precise time stamps are required."
  (let ((time (or time (current-time))))
    (+ (* (car time) 65536.0) (cadr time)))))

;; GNU Emacs 20.7 compatibility
(or (fboundp 'substring-no-properties)
(defun substring-no-properties (string &optional from to)
  "Return a substring of STRING, without text properties.
It starts at index FROM and ending before TO.
TO may be nil or omitted; then the substring runs to the end of STRING.
If FROM is nil or omitted, the substring starts at the beginning of STRING.
If FROM or TO is negative, it counts from the end.

With one argument, just copy STRING without its properties."
  (let ((substring (substring string from to)))
    (set-text-properties 0 (length substring) nil substring)
    substring)))

;; XEmacs compatibility from `fsf-compat' package
(when (featurep 'xemacs)
  (require 'overlay)
  (require 'goto-addr)
  (or (fboundp 'quit-window)
      (defalias 'quit-window 'bury-buffer)))


;;; Maintenence Functions

(defun ee-version-update ()
  "Show places where version numbers should be updated before release."
  (interactive)
  (mapc (lambda (item)
          (let ((filename (car item))
                (place (cadr item)))
            (split-window)
            (with-current-buffer (find-file filename)
              (goto-char (point-min))
              (search-forward place))))
        '(("ee.el" "defconst ee-version ")
          ("ee.texi" "@set VERSION")
          ("Makefile" "VERSION ="))))


;;; Display and call the available ee extensions

;;;###autoload
(defun ee (&optional file)
  "Enter top-level index of all available ee extensions.
Optional argument FILE specifies the file to examine;
the default is the top-level mode list.
In interactive use, a prefix argument directs this command
to read a root file name from the minibuffer."
  (interactive (if current-prefix-arg
                   (list (read-file-name "ee root file name: " nil nil t))))
  (ee-datafile nil (or file ee-root-data-file))
  ;; (find-file (ee-data-file-locate (or file ee-root-data-file)))
  ;;   (ee-data-file)
  ;;   (ee-links "root.ee")
  )

(provide 'ee)

;;; ee.el ends here
