;;; ctable.el --- Table component for Emacs Lisp

;; Copyright (C) 2011 SAKURAI Masashi

;; Author:  <m.sakurai at kiwanami.net>
;; Keywords: table

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

;; This program is a table component for Emacs Lisp.
;; Other programs can use this table component for the application UI.

;;; Installation:

;; Place this program in your load path and add following code.

;; (require 'ctable)

;;; Usage:

;; Executing the command `ctbl:open-table-buffer', switch to the table buffer.

;; Table data which are shown in the table view, are collected
;; by the `ctbl:model' objects. See the function `ctbl:demo' for example.

;;; Code:

(eval-when-compile (require 'cl))


;;; Models and Parameters

;; ctbl:model / table model structure
;;
;;   data : Table data as a list of rows. A row contains a list of columns.
;;   column-model : A list of column models.
;;   sort-state : The current sort order as a list of column indexes.
;;                The index number of the first column is 1.
;;                If the index is negative, the sort order is reversed.

(defstruct ctbl:model data column-model sort-state)

;; ctbl:cmodel / table column model structure
;;
;;   title : title string.
;;   sorter : sorting function which transforms a cell value into sort value.
;;            It should return -1, 0 and 1. If nil, `ctbl:sort-string-lessp' is used.
;;   align : text alignment: 'left, 'right and 'center. (default: right)
;;   max-width : maximum width of the column. if nil, no constraint. (default: nil)
;;   min-width : minimum width of the column. if nil, no constraint. (default: nil)
;;   click-hooks : a list of click action functions with two arguments
;;                 the `ctbl:component' object and the `ctbl:cmodel' one.
;;               (default: '(`ctbl:cmodel-sort-action'))

(defstruct ctbl:cmodel title sorter align max-width min-width
  (click-hooks '(ctbl:cmodel-sort-action)))

;; ctbl:param / rendering parameters
;;

(defstruct ctbl:param
  display-header ;; if t, display the header row with column models.
  fixed-header   ;; if t, display the header row in the header-line area.
  bg-colors      ;; '(((row-id . col-id) . colorstr) (t . default-color) ... ) or (lambda (model row-id col-id) colorstr or nil)
  vline-colors   ;; "#RRGGBB" or '((0 . colorstr) (t . default-color)) or (lambda (model col-index) colorstr or nil)
  hline-colors   ;; "#RRGGBB" or '((0 . colorstr) (t . default-color)) or (lambda (model row-index) colorstr or nil)
  draw-vlines    ;; 'all or '(0 1 2 .. -1) or (lambda (model col-index) t or nil )
  draw-hlines    ;; 'all or '(0 1 2 .. -1) or (lambda (model row-index) t or nil )
  vertical-line horizontal-line ;; | -
  left-top-corner right-top-corner left-bottom-corner right-bottom-corner  ;; +
  top-junction bottom-junction left-junction right-junction cross-junction ;; +
  )

(defvar ctbl:default-rendering-param
  (make-ctbl:param
   :display-header      t
   :fixed-header        nil
   :bg-colors           nil
   :vline-colors        "DarkGray"
   :hline-colors        "DarkGray"
   :draw-vlines         'all
   :draw-hlines         '(1)
   :vertical-line       ?|
   :horizontal-line     ?-
   :left-top-corner     ?+
   :right-top-corner    ?+
   :left-bottom-corner  ?+
   :right-bottom-corner ?+
   :top-junction        ?+
   :bottom-junction     ?+
   :left-junction       ?+
   :right-junction      ?+
   :cross-junction      ?+
   )
  "Default rendering parameters.")

;;; Faces

(defface ctbl:face-row-select
  '((((class color) (background light))
     :background "WhiteSmoke")
    (((class color) (background dark))
     :background "Blue4"))
  "Face for row selection" :group 'ctable)

(defface ctbl:face-cell-select
  '((((class color) (background light))
     :background "Mistyrose1")
    (((class color) (background dark))
     :background "Blue2"))
  "Face for cell selection" :group 'ctable)

(defface ctbl:face-continue-bar
  '((((class color) (background light))
     :background "OldLace")
    (((class color) (background dark))
     :background "Gray26"))
  "Face for continue bar" :group 'ctable)

;;; Utilities

(defun ctbl:define-keymap (keymap-list &optional prefix)
  "[internal] Keymap utility."
  (let ((map (make-sparse-keymap)))
    (mapc
     (lambda (i)
       (define-key map
         (if (stringp (car i))
             (read-kbd-macro
              (if prefix
                  (replace-regexp-in-string "prefix" prefix (car i))
                (car i)))
           (car i))
         (cdr i)))
     keymap-list)
    map))

(defun ctbl:cell-id (row-id col-id)
  "[internal] Create a cell-id object"
  (cons row-id col-id))

(defun ctbl:tp (text prop value)
  "[internal] Put a text property to the entire text string."
  (if (< 0 (length text))
    (put-text-property 0 (length text) prop value text))
  text)

(defvar ctbl:uid 1)

(defun ctbl:uid ()
  "[internal] Generate an unique number."
  (incf ctbl:uid))

(defun ctbl:fill-keymap-property (begin end keymap)
  "[internal] Put the given text property to the region between BEGIN and END.
If the text already has some keymap property, the text is skipped."
  (save-excursion
    (goto-char begin)
    (loop with pos = begin with nxt = nil
          until (or (null pos) (<= end pos))
          when (get-text-property pos 'keymap) do
          (setq pos (next-single-property-change pos 'keymap))
          else do
          (setq nxt (next-single-property-change pos 'keymap))
          (when (null nxt) (setq nxt end))
          (put-text-property pos (min nxt end) 'keymap keymap))))

;; Model functions

(defun ctbl:model-column-length (model)
  "[internal] Return the column number."
  (length (car (ctbl:model-data model))))

(defun ctbl:model-row-length (model)
  "[internal] Return the row number."
  (length (ctbl:model-data model)))

(defun ctbl:model-modify-sort-key (model col-index)
  "Modify the list of sort keys for the column headers."
  (let* ((sort-keys (ctbl:model-sort-state model))
         (col-key (1+ col-index)))
    (cond
     ((eq (car sort-keys) col-key)
      (setf (ctbl:model-sort-state model)
            (cons (- col-key) (cdr sort-keys))))
     ((eq (car sort-keys) (- col-key))
      (setf (ctbl:model-sort-state model)
            (cons col-key (cdr sort-keys))))
     (t
      (setf (ctbl:model-sort-state model)
            (cons col-key (delete (- col-key)
                                  (delete col-key sort-keys))))))
    (ctbl:model-sort-state model)))

(defun ctbl:cmodel-sort-action (cp col-index)
  "Sorting action for click on the column headers"
  (let* ((model (ctbl:cp-get-model cp)))
    (ctbl:model-modify-sort-key model col-index)
    (ctbl:cp-update cp)))


;;; Structures

;; Component

;; This structure defines attributes of the table component.
;; These attributes are internal use. Other programs should access
;; through the functions of the component interface.

;; [ctbl:component]
;; dest         : an object of `ctbl:dest'
;; model        : an object of the table model
;; selected     : selected cell-id: (row index . col index)
;; param        : rendering parameter object
;; sorted-data  : sorted data to display the table view. 
;;    see `ctbl:cp-get-selected-data-row' and `ctbl:cp-get-selected-data-cell'.
;; update-hooks : a list of hook functions for update event
;; selection-change-hooks : a list of hook functions for selection change event
;; click-hooks            : a list of hook functions for click event

(defstruct ctbl:component dest model param selected sorted-data
  update-hooks selection-change-hooks click-hooks)


;; Rendering Destination

;; This structure object is the abstraction of the rendering
;; destinations, such as buffers, regions and so on.

;; [ctbl:dest]
;; type        : identify symbol for destination type. (buffer, region, text)
;; buffer      : a buffer object of rendering destination.
;; min-func    : a function that returns upper limit of rendering destination.
;; max-func    : a function that returns lower limit of rendering destination.
;; width       : width of the reference size. (number, nil or full)
;; height      : height of the reference size. (number, nil or full)
;; clear-func  : a function that clears the rendering destination.
;; before-update-func : a function that is called at the beginning of rendering routine.
;; after-update-func  : a function that is called at the end of rendering routine.
;; select-ol   : a list of overlays for selection

(defstruct ctbl:dest
  type buffer min-func max-func width height
  clear-func before-update-func after-update-func select-ol)

(eval-when-compile
  (defmacro ctbl:dest-with-region (dest &rest body)
    (declare (debug (form &rest form)))
    (let (($dest (gensym)))
      `(let ((,$dest ,dest))
         (with-current-buffer (ctbl:dest-buffer ,$dest)
           (save-restriction
             (narrow-to-region
              (ctbl:dest-point-min ,$dest) (ctbl:dest-point-max ,$dest))
             ,@body))))))
(put 'ctbl:dest-with-region 'lisp-indent-function 1)

(defun ctbl:dest-point-min (c)
  (funcall (ctbl:dest-min-func c)))

(defun ctbl:dest-point-max (c)
  (funcall (ctbl:dest-max-func c)))

(defun ctbl:dest-clear (c)
  (funcall (ctbl:dest-clear-func c)))

(defun ctbl:dest-before-update (c)
  (when (ctbl:dest-before-update-func c)
    (funcall (ctbl:dest-before-update-func c))))

(defun ctbl:dest-after-update (c)
  (when (ctbl:dest-after-update-func c)
    (funcall (ctbl:dest-after-update-func c))))


;; Buffer

(defconst ctbl:table-buffer-name "*ctbl-table*" "[internal] Default buffer name for the table view.")

(defun ctbl:dest-init-buffer (&optional buf width height custom-map)
  "Create a buffer destination.
This destination uses an entire buffer and set up the major-mode
`ctbl:table-mode' and the key map `ctbl:table-mode-map'.  BUF is
a buffer name to render the table view. If BUF is nil, the
default buffer name is used.  WIDTH and HEIGHT are reference size
of the table view. If those are nil, the size of table is
calculated from the window that shows BUF or the selected window.
The component object is stored at the buffer local variable
`ctbl:component'.  CUSTOM-MAP is the additional keymap that is
added to default keymap `ctbl:table-mode-map'."
  (lexical-let
      ((buffer (or buf (get-buffer-create (format "*Table: %d*" (ctbl:uid)))))
       (window (or (and buf (get-buffer-window buf)) (selected-window)))
       dest)
    (setq dest
          (make-ctbl:dest
           :type 'buffer
           :min-func 'point-min
           :max-func 'point-max
           :buffer buffer
           :width  width
           :height height
           :clear-func (lambda ()
                         (with-current-buffer buffer
                           (erase-buffer)))))
    (with-current-buffer buffer
      (unless (eq major-mode 'ctbl:table-mode)
        (ctbl:table-mode custom-map)))
    dest))

;; Region

(defun ctbl:dest-init-region (buf mark-begin mark-end &optional width height)
  "Create a region destination.  The table is drew between
MARK-BEGIN and MARK-END in the buffer BUF.  MARK-BEGIN and
MARK-END are separated by more than one character, such as a
space.  This destination is employed to be embedded in the some
application buffer.  Because this destination does not set up
any modes and key maps for the buffer, the application that uses
the calfw is responsible to manage the buffer and key maps."
  (lexical-let
      ((mark-begin mark-begin) (mark-end mark-end)
       (window (or (get-buffer-window buf) (selected-window))))
    (make-ctbl:dest
     :type 'region
     :min-func (lambda () (marker-position mark-begin))
     :max-func (lambda () (marker-position mark-end))
     :buffer buf
     :width  width
     :height height
     :clear-func
     (lambda ()
         (ctbl:dest-region-clear (marker-position mark-begin)
                                (marker-position mark-end)))
     )))

(defun ctbl:dest-region-clear (begin end)
  "[internal] Clear the content text."
  (when (< 2 (- end begin))
    (delete-region begin (1- end)))
  (goto-char begin))

;; Inline text

(defconst ctbl:dest-background-buffer " *ctbl:dest-background*")

(defun ctbl:dest-init-inline (width height)
  "Create a text destination."
  (lexical-let
      ((buffer (get-buffer-create ctbl:dest-background-buffer))
       (window (selected-window))
       dest)
    (setq dest
          (make-ctbl:dest
           :type 'text
           :min-func 'point-min
           :max-func 'point-max
           :buffer buffer
           :width  width
           :height height
           :clear-func (lambda ()
                         (with-current-buffer buffer
                           (erase-buffer)))))
    dest))

;; private functions

(defun ctbl:dest-ol-selection-clear (dest)
  "[internal] Clear the selection overlays on the current table view."
  (loop for i in (ctbl:dest-select-ol dest)
        do (delete-overlay i))
  (setf (ctbl:dest-select-ol dest) nil))

(defun ctbl:dest-ol-selection-set (dest cell-id)
  "[internal] Put a selection overlay on CELL-ID. The selection overlay can be
 put on some cells, calling this function many times.  This
 function does not manage the selections, just put the overlay."
  (lexical-let (ols (row-id (car cell-id)) (col-id (cdr cell-id)))
    (ctbl:dest-with-region dest
      (ctbl:find-all-by-row-id
       dest row-id
       (lambda (tcell-id begin end)
         (let ((overlay (make-overlay begin end)))
           (overlay-put overlay 'face
                        (if (= (cdr tcell-id) col-id)
                            'ctbl:face-cell-select
                          'ctbl:face-row-select))
           (push overlay ols)))))
    (setf (ctbl:dest-select-ol dest) ols)))


;; Component

(defun ctbl:cp-new (dest model param)
  "[internal] Create a new component object.
DEST is a ctbl:dest object.  MODEL is a model object.  PARAM is a
rendering parameter object.  This function is called by the
initialization functions, `ctbl:create-table-component-buffer',
`ctbl:create-table-component-region' and `ctbl:get-table-text'."
  (let ((cp (make-ctbl:component
             :selected '(0 . 0)
             :dest  dest
             :model model
             :param (or param ctbl:default-rendering-param))))
    (ctbl:cp-update cp)
    cp))

(defun ctbl:cp-get-component ()
  "Return the component object on the current cursor position.
Firstly, getting a text property `ctbl:component' on the current
position. If no object is found in the text property, the buffer
local variable `ctbl:component' is tried to get. If no object is
found at the variable, return nil."
  (let ((component (get-text-property (point) 'ctbl:component)))
    (unless component
      (unless (local-variable-p 'ctbl:component (current-buffer))
        (error "Not found ctbl:component attribute..."))
      (setq component (buffer-local-value 'ctbl:component (current-buffer))))
    component))

;; Component : getters

(defun ctbl:cp-get-selected (component)
  "Return the selected cell-id of the component."
  (ctbl:component-selected component))

(defun ctbl:cp-get-selected-data-row (component)
  "Return the selected row data. If no cell is selected, return nil."
  (let* ((rows (ctbl:component-sorted-data component))
         (cell-id (ctbl:component-selected component))
         (row-id (car cell-id)) (col-id (cdr cell-id)))
    (if row-id (nth row-id rows) nil)))

(defun ctbl:cp-get-selected-data-cell (component)
  "Return the selected cell data. If no cell is selected, return nil."
  (let* ((rows (ctbl:component-sorted-data component))
         (cell-id (ctbl:component-selected component))
         (row-id (car cell-id)) (col-id (cdr cell-id)))
    (if row-id 
        (nth col-id (nth row-id rows))
      nil)))

(defun ctbl:cp-get-model (component)
  "Return the model object."
  (ctbl:component-model component))

(defun ctbl:cp-get-param (component)
  "Return a rendering parameter object."
  (ctbl:component-param component))

(defun ctbl:cp-get-buffer (component)
  "Return a buffer object on which the component draws the content."
  (ctbl:dest-buffer (ctbl:component-dest component)))

;; Component : setters

(defun ctbl:cp-move-cursor (dest cell-id)
  "[internal] Just move the cursor onto the CELL-ID.
If CELL-ID is not found, return nil. This function
is called by `ctbl:cp-set-selected-cell'."
  (let ((pos (ctbl:find-by-cell-id dest cell-id)))
    (cond
     (pos
      (goto-char pos)
      (unless (eql (selected-window) (get-buffer-window (current-buffer)))
        (set-window-point (get-buffer-window (current-buffer)) pos))
      t)
     (t nil))))

(defun ctbl:cp-set-selected-cell (component cell-id)
  "Select the cell on the component. If the current view doesn't contain the cell,
this function updates the view to display the cell."
  (let ((last (ctbl:component-selected component))
        (dest (ctbl:component-dest component))
        (model (ctbl:component-model component)))
    (when (ctbl:cp-move-cursor dest cell-id)
      (setf (ctbl:component-selected component) cell-id)
      (ctbl:dest-before-update dest)
      (ctbl:dest-ol-selection-clear dest)
      (ctbl:dest-ol-selection-set dest cell-id)
      (ctbl:dest-after-update dest)
      (unless (equal last cell-id)
        (ctbl:cp-fire-selection-change-hooks component)))))

;; Hook

(defun ctbl:cp-add-update-hook (component hook)
  "Add the update hook function to the component.
HOOK is a function that has no argument."
  (push hook (ctbl:component-update-hooks component)))

(defun ctbl:cp-add-selection-change-hook (component hook)
  "Add the selection change hook function to the component.
HOOK is a function that has no argument."
  (push hook (ctbl:component-selection-change-hooks component)))

(defun ctbl:cp-add-click-hook (component hook)
  "Add the click hook function to the component.
HOOK is a function that has no argument."
  (push hook (ctbl:component-click-hooks component)))

;; Component : privates

(defun ctbl:cp-update (component)
  "[internal] Clear and re-draw the component content."
  (let* ((buf  (ctbl:cp-get-buffer component))
         (dest (ctbl:component-dest component)))
    (with-current-buffer buf
      (ctbl:dest-before-update dest)
      (ctbl:dest-ol-selection-clear dest)
      (let (buffer-read-only)
        (ctbl:dest-with-region dest
          (ctbl:dest-clear dest)
          (setf (ctbl:component-sorted-data component)
                (ctbl:render-main
                 dest
                 (ctbl:component-model component)
                 (ctbl:component-param component)))))
      (ctbl:cp-set-selected-cell
       component (ctbl:component-selected component))
      (ctbl:dest-after-update dest)
      (ctbl:cp-fire-update-hooks component))))

(defun ctbl:cp-fire-click-hooks (component)
  "[internal] Call click hook functions of the component with no arguments."
  (loop for f in (ctbl:component-click-hooks component)
        do (condition-case err
               (funcall f)
             (error (message "CTable: Click / Hook error %S [%s]" f err)))))

(defun ctbl:cp-fire-selection-change-hooks (component)
  "[internal] Call selection change hook functions of the component with no arguments."
  (loop for f in (ctbl:component-selection-change-hooks component)
        do (condition-case err
               (funcall f)
             (error (message "CTable: Selection change / Hook error %S [%s]" f err)))))

(defun ctbl:cp-fire-update-hooks (component)
  "[internal] Call update hook functions of the component with no arguments."
  (loop for f in (ctbl:component-update-hooks component)
        do (condition-case err
               (funcall f)
             (error (message "Ctable: Update / Hook error %S [%s]" f err)))))


(defun ctbl:find-by-cell-id (dest cell-id)
  "[internal] Return a point where the text property `ctbl:cell-id'
is equal to cell-id in the current table view. If CELL-ID is not
found in the current view, return nil."
  (loop with pos = (ctbl:dest-point-min dest)
        with end = (ctbl:dest-point-max dest)
        for next = (next-single-property-change pos 'ctbl:cell-id nil end)
        for text-cell = (and next (ctbl:cursor-to-cell next))
        while (and next (< next end)) do
        (if (and text-cell (equal cell-id text-cell))
            (return next))
        (setq pos next)))

(defun ctbl:find-all-by-cell-id (dest cell-id func)
  "[internal] Call the function FUNC in each regions where the
text-property `ctbl:cell-id' is equal to CELL-ID. The argument function FUNC
receives two arguments, begin position and end one. This function is
mainly used at functions for putting overlays."
  (loop with pos = (ctbl:dest-point-min dest)
        with end = (ctbl:dest-point-max dest)
        for next = (next-single-property-change pos 'ctbl:cell-id nil end)
        for text-id = (and next (ctbl:cursor-to-cell next))
        while (and next (< next end)) do
        (if (and text-id (equal cell-id text-id))
            (let ((cend (next-single-property-change
                         next 'ctbl:cell-id nil end)))
              (funcall func next cend)))
        (setq pos next)))

(defun ctbl:find-all-by-row-id (dest row-id func)
  "[internal] Call the function FUNC in each regions where the
row-id of the text-property `ctbl:cell-id' is equal to
ROW-ID. The argument function FUNC receives three arguments,
cell-id, begin position and end one. This function is mainly used
at functions for putting overlays."
  (loop with pos = (ctbl:dest-point-min dest)
        with end = (ctbl:dest-point-max dest)
        for next = (next-single-property-change pos 'ctbl:cell-id nil end)
        for text-id = (and next (ctbl:cursor-to-cell next))
        while (and next (< next end)) do
        (if (and text-id (equal row-id (car text-id)))
            (let ((cend (next-single-property-change
                         next 'ctbl:cell-id nil end)))
              (funcall func text-id next cend)))
        (setq pos next)))

(defun ctbl:find-first-cell (dest)
  "[internal] Return the first cell in the current buffer."
  (let ((pos (next-single-property-change
              (ctbl:dest-point-min dest) 'ctbl:cell-id)))
    (and pos (ctbl:cursor-to-cell pos))))

(defun ctbl:find-last-cell (dest)
  "[internal] Return the last cell in the current buffer."
  (let ((pos (previous-single-property-change
              (ctbl:dest-point-max dest) 'ctbl:cell-id)))
    (and pos (ctbl:cursor-to-cell (1- pos)))))

(defun ctbl:cursor-to-cell (&optional pos)
  "[internal] Return the cell-id at the cursor. If the text does not
have the text-property `ctbl:cell-id', return nil."
  (get-text-property (or pos (point)) 'ctbl:cell-id))

(defun ctbl:cursor-to-nearest-cell ()
  "Return the cell-id at the cursor. If the point of cursor does
not have the cell-id, search the cell-id around the cursor
position. If the current buffer is not table view (it may be
bug), this function may return nil."
  (or (ctbl:cursor-to-cell)
      (let* ((r (lambda () (when (not (eolp)) (forward-char))))
             (l (lambda () (when (not (bolp)) (backward-char))))
             (u (lambda () (when (not (bobp)) (line-move 1))))
             (d (lambda () (when (not (eobp)) (line-move -1))))
             (dest (ctbl:component-dest (ctbl:cp-get-component)))
             get)
        (setq get (lambda (cmds)
                    (save-excursion
                      (if (null cmds) (ctbl:cursor-to-cell)
                        (ignore-errors
                          (funcall (car cmds)) (funcall get (cdr cmds)))))))
        (or (loop for i in `((,d) (,r) (,u) (,l)
                             (,d ,r) (,d ,l) (,u ,r) (,u ,l)
                             (,d ,d) (,r ,r) (,u ,u) (,l ,l))
                  for id = (funcall get i)
                  if id return id)
            (cond
             ((> (/ (point-max) 2) (point))
              (ctbl:find-first-cell dest))
             (t (ctbl:find-last-cell dest)))))))


;; Commands

(defun ctbl:navi-move-gen (drow dcol)
  "[internal] Move to the cell with the abstract position."
  (let* ((cp (ctbl:cp-get-component))
         (cell-id (ctbl:cursor-to-nearest-cell))
         (row-id (car cell-id)) (col-id (cdr cell-id)))
    (when (and cp cell-id)
      (ctbl:navi-goto-cell (ctbl:cell-id (+ drow row-id)
                                         (+ dcol col-id))))))

(defun ctbl:navi-move-up (&optional num)
  "Move to the up neighbor cell."
  (interactive "p")
  (unless num (setq num 1))
  (ctbl:navi-move-gen (- num) 0))

(defun ctbl:navi-move-down (&optional num)
  "Move to the down neighbor cell."
  (interactive "p")
  (unless num (setq num 1))
  (ctbl:navi-move-gen num 0))

(defun ctbl:navi-move-right (&optional num)
  "Move to the right neighbor cell."
  (interactive "p")
  (unless num (setq num 1))
  (ctbl:navi-move-gen 0 num))

(defun ctbl:navi-move-left (&optional num)
  "Move to the left neighbor cell."
  (interactive "p")
  (unless num (setq num 1))
  (ctbl:navi-move-gen 0 (- num)))

(defun ctbl:navi-move-left-most ()
  "Move to the left most cell."
  (interactive)
  (let* ((cp (ctbl:cp-get-component))
         (cell-id (ctbl:cursor-to-nearest-cell))
         (row-id (car cell-id)))
    (when (and cp cell-id)
      (ctbl:navi-goto-cell (ctbl:cell-id row-id 0)))))

(defun ctbl:navi-move-right-most ()
  "Move to the right most cell."
  (interactive)
  (let* ((cp (ctbl:cp-get-component))
         (cell-id (ctbl:cursor-to-nearest-cell))
         (row-id (car cell-id))
         (model (ctbl:cp-get-model cp))
         (cols (ctbl:model-column-length model)))
    (when (and cp cell-id)
      (ctbl:navi-goto-cell (ctbl:cell-id row-id (1- cols))))))

(defun ctbl:navi-goto-cell (cell-id)
  "Move the cursor to CELL-ID and put selection."
  (let ((cp (ctbl:cp-get-component)))
    (when cp
      (ctbl:cp-set-selected-cell cp cell-id))))

(defun ctbl:navi-on-click ()
  "Action handler on the cells."
  (interactive)
  (let ((cp (ctbl:cp-get-component))
        (cell-id (ctbl:cursor-to-nearest-cell)))
    (when (and cp cell-id)
      (ctbl:cp-set-selected-cell cp cell-id)
      (ctbl:cp-fire-click-hooks cp))))

(defun ctbl:action-update-buffer ()
  "Update action for the latest table model."
  (interactive)
  (let ((cp (ctbl:cp-get-component)))
    (when cp
      (ctbl:cp-update cp))))

(defun ctbl:action-column-header ()
  "Action handler on the header columns. (for normal key events)"
  (interactive)
  (ctbl:fire-column-header-action
   (ctbl:cp-get-component)
   (get-text-property (point) 'ctbl:col-id)))

(defun ctbl:fire-column-header-action (cp col-id)
  "[internal] Execute action handlers on the header columns."
  (when (and cp col-id)
    (loop with cmodel = (nth col-id (ctbl:model-column-model (ctbl:cp-get-model cp)))
          for f in (ctbl:cmodel-click-hooks cmodel)
          do (condition-case err
                 (funcall f cp col-id)
               (error (message "Ctable: Header Click / Hook error %S [%s]"
                               f err))))))

(defun ctbl:render-column-header-keymap (col-id)
  "[internal] Generate action handler on the header columns. (for header-line-format)"
  (lexical-let ((col-id col-id))
    (let ((keymap (copy-keymap ctbl:column-header-keymap)))
      (define-key keymap [header-line mouse-1]
        (lambda ()
          (interactive)
          (ctbl:fire-column-header-action (ctbl:cp-get-component) col-id)))
      keymap)))

(defvar ctbl:column-header-keymap
  (ctbl:define-keymap
   '(([mouse-1] . ctbl:action-column-header)
     ("C-m" . ctbl:action-column-header)
     ("RET" . ctbl:action-column-header)
     ))
  "Keymap for the header columns.")

(defvar ctbl:table-mode-map
  (ctbl:define-keymap
   '(
     ("k" . ctbl:navi-move-up)
     ("j" . ctbl:navi-move-down)
     ("h" . ctbl:navi-move-left)
     ("l" . ctbl:navi-move-right)

     ("p" . ctbl:navi-move-up)
     ("n" . ctbl:navi-move-down)
     ("b" . ctbl:navi-move-left)
     ("f" . ctbl:navi-move-right)

     ("e" . ctbl:navi-move-right-most)
     ("a" . ctbl:navi-move-left-most)

     ("g" . ctbl:action-update-buffer)

     ([mouse-1] . ctbl:navi-on-click)
     ("C-m" . ctbl:navi-on-click)
     ("RET" . ctbl:navi-on-click)

     )) "Keymap for the table-mode buffer.")

(defun ctbl:table-mode-map (&optional custom-map)
  "[internal] Return a keymap object for the table buffer."
  (cond
   (custom-map
    (set-keymap-parent custom-map ctbl:table-mode-map)
    custom-map)
   (t ctbl:table-mode-map)))

(defvar ctbl:table-mode-hook nil
  "This hook is called at end of setting up major mode `ctbl:table-mode'.")

(defun ctbl:table-mode (&optional custom-map)
  "Set up major mode `ctbl:table-mode'.

\\{ctbl:table-mode-map}"
  (kill-all-local-variables)
  (setq truncate-lines t)
  (use-local-map (ctbl:table-mode-map custom-map))
  (setq major-mode 'ctbl:table-mode
        mode-name "Table Mode")
  (setq buffer-undo-list t
        buffer-read-only t)
  (run-hooks 'ctbl:table-mode-hook))


;; Rendering

(defun ctbl:render-check-cell-width (rows cmodels column-widths)
  "[internal] Return a list of rows. This function makes side effects:
cell widths are stored at COLUMN-WIDTHS, longer cell strings are truncated by
maximum width of the column models."
  (loop for row in rows collect
        (loop for c in row
              for cm in cmodels
              for cwmax = (ctbl:cmodel-max-width cm)
              for i from 0
              for cw = (nth i column-widths)
              for val = (format "%s" c)
              collect
              (progn
                (when (and cwmax (< cwmax (string-width val)))
                  (setq val (truncate-string-to-width val cwmax)))
                (when (< cw (string-width val))
                  (setf (nth i column-widths) (string-width val)))
                val))))

(defun ctbl:render-adjust-cell-width (cmodels column-widths total-width)
  "[internal] Adjust column widths and return a list of column widths.
If TOTAL-WIDTH is nil, this function just returns COLUMN-WIDTHS.
If TOTAL-WIDTHS is shorter than sum of COLUMN-WIDTHS, this
function expands columns.  The residual width is distributed over
the columns.  If TOTAL-WIDTHS is longer than sum of
COLUMN-WIDTHS, this function shrinks columns to reduce the
surplus width."
  (let ((init-total (loop for i in column-widths sum i)))
    (cond
     ((or (null total-width)
          (= total-width init-total)) column-widths)
     ((< total-width init-total)
      (ctbl:render-adjust-cell-width-shrink
       cmodels column-widths total-width init-total))
     (t
      (ctbl:render-adjust-cell-width-expand
       cmodels column-widths total-width init-total)))))

(defun ctbl:render-adjust-cell-width-shrink (cmodels column-widths total-width init-total )
  "[internal] shrink column widths."
  (let* ((column-widths (copy-sequence column-widths))
         (column-indexes (loop for i from 0 below (length cmodels) collect i))
         (residual (- init-total total-width)))
    (loop for cnum = (length column-indexes)
          until (or (= 0 cnum) (= 0 residual))
          do
          (loop with ave-shrink = (max 1 (/ residual cnum))
                for idx in column-indexes
                for cmodel = (nth idx cmodels)
                for cwidth = (nth idx column-widths)
                for min-width = (or (ctbl:cmodel-min-width cmodel) 1)
                do
                (cond
                 ((<= residual 0) (return)) ; complete
                 ((<= cwidth min-width)     ; reject
                  (setq column-indexes (delete idx column-indexes)))
                 (t ; reduce
                  (let ((next-width (max 1 (- cwidth ave-shrink))))
                    (incf residual (- next-width cwidth))
                    (setf (nth idx column-widths) next-width))))))
    column-widths))

(defun ctbl:render-adjust-cell-width-expand (cmodels column-widths total-width init-total )
  "[internal] expand column widths."
  (let* ((column-widths (copy-sequence column-widths))
         (column-indexes (loop for i from 0 below (length cmodels) collect i))
         (residual (- total-width init-total)))
    (loop for cnum = (length column-indexes)
          until (or (= 0 cnum) (= 0 residual))
          do
          (loop with ave-expand = (max 1 (/ residual cnum))
                for idx in column-indexes
                for cmodel = (nth idx cmodels)
                for cwidth = (nth idx column-widths)
                for max-width = (or (ctbl:cmodel-max-width cmodel) total-width)
                do
                (cond
                 ((<= residual 0) (return)) ; complete
                 ((<= max-width cwidth)     ; reject
                  (setq column-indexes (delete idx column-indexes)))
                 (t ; expand
                  (let ((next-width (min max-width (+ cwidth ave-expand))))
                    (incf residual (- cwidth next-width))
                    (setf (nth idx column-widths) next-width))))))
    column-widths))

(defun ctbl:render-get-formats (cmodels column-widths)
  "[internal] Return a list of the format functions."
  (loop for cw in column-widths
        for cm in cmodels
        for al = (ctbl:cmodel-align cm)
        collect
        (lexical-let ((cw cw))
          (cond
           ((eq al 'left)
            (lambda (s) (ctbl:format-left cw s)))
           ((eq al 'center)
            (lambda (s) (ctbl:format-center cw s)))
           (t
            (lambda (s) (ctbl:format-right cw s)))))))

(defun ctbl:render-choose-color (model param index)
  "[internal] Choose rendering color."
  (cond
   ((null param) nil)
   ((stringp param) param)
   ((functionp param)
    (funcall param model index))
   (t (let ((val (or (assq index param)
                     (assq t param))))
        (if val (cdr val) nil)))))

(defun ctbl:render-bg-color (str row-id col-id model param)
  "[internal] Return nil or the color string at the cell (row-id . cell-id)."
  (let ((bgc-param (ctbl:param-bg-colors param)))
    (cond
     ((null bgc-param) nil)
     ((functionp bgc-param)
      (funcall bgc-param model row-id col-id str))
     (t
      (let ((pair (or (assoc (cons row-id col-id) bgc-param)
                      (assoc t bgc-param))))
        (if pair (cdr pair) nil))))))

(defun ctbl:render-bg-color-put (str row-id col-id model param)
  "[internal] Return the string with the background face."
  (let ((bgcolor (ctbl:render-bg-color str row-id col-id model param)))
    (if bgcolor
        (let ((org-face (get-text-property 0 'face str)))
          (propertize
           (copy-sequence str)
           'face (if org-face
                     (append org-face (list ':background  bgcolor))
                   (list ':background  bgcolor))))
      str)))

(defun ctbl:render-line-color (str model param index)
  "[internal] Return the propertize string."
  (propertize (copy-sequence str)
              'face (list
                     ':foreground
                     (ctbl:render-choose-color model param index))))

(defun ctbl:render-vline-color (str model param index)
  "[internal] Return the propertize string for vertical lines."
  (ctbl:render-line-color str model (ctbl:param-vline-colors param) index))

(defun ctbl:render-hline-color (str model param index)
  "[internal] Return the propertize string for horizontal lines."
  (ctbl:render-line-color str model (ctbl:param-hline-colors param) index))

(defun ctbl:render-draw-vline-p (model param index)
  "[internal] If a vertical line is needed at the column index, return t."
  (cond
   ((null param) nil)
   ((eq 'all param) t)
   ((functionp param) (funcall param model index))
   (t (and (consp param) (memq index param)))))

(defun ctbl:render-draw-hline-p (model param index)
  "[internal] If a horizontal line is needed at the row index, return t."
  (cond
   ((null param) nil)
   ((eq 'all param) t)
   ((functionp param) (funcall param model index))
   (t (memq index param))))

(defun ctbl:render-make-hline (column-widths model param index)
  "[internal] "
  (let ((vparam (ctbl:param-draw-vlines param))
        (hline (ctbl:param-horizontal-line param))
        left joint right)
    (if (not (ctbl:render-draw-hline-p
              model (ctbl:param-draw-hlines param) index))
        ""
      (cond
       ((eq 0 index)
        (setq left  (char-to-string (ctbl:param-left-top-corner param))
              joint (char-to-string (ctbl:param-top-junction param))
              right (char-to-string (ctbl:param-right-top-corner param))))
       ((eq -1 index)
        (setq left  (char-to-string (ctbl:param-left-bottom-corner param))
              joint (char-to-string (ctbl:param-bottom-junction param))
              right (char-to-string (ctbl:param-right-bottom-corner param))))
       (t
        (setq left  (char-to-string (ctbl:param-left-junction param))
              joint (char-to-string (ctbl:param-cross-junction param))
              right (char-to-string (ctbl:param-right-junction param)))))
      (ctbl:render-hline-color
       (concat
        (if (ctbl:render-draw-vline-p model vparam 0) left)
        (loop with ret = nil with endi = (length column-widths)
              for cw in column-widths
              for ci from 1
              for endp = (equal ci endi)
              do
              (push (make-string cw hline) ret)
              (when (and (ctbl:render-draw-vline-p model vparam ci)
                         (not endp))
                (push joint ret))
              finally return (apply 'concat (reverse ret)))
        (if (ctbl:render-draw-vline-p model vparam -1) right)
        "\n")
       model param index))))

(defun ctbl:render-join-columns (columns model param)
  "[internal] Join a list of column strings with vertical lines."
  (let (ret (V (char-to-string (ctbl:param-vertical-line param))))
    ;; left border line
    (setq ret (if (ctbl:render-draw-vline-p
                   model (ctbl:param-draw-vlines param) 0)
                  (list (ctbl:render-vline-color V model param 0))
                nil))
    ;; content line
    (loop with param-vl = (ctbl:param-draw-vlines param)
          with param-vc = (ctbl:param-vline-colors param)
          with endi = (length columns)
          for i from 1 for endp = (equal i endi)
          for cv in columns
          for color = (ctbl:render-choose-color model param-vc i)
          do
          (push cv ret)
          (when (and (ctbl:render-draw-vline-p
                      model (ctbl:param-draw-vlines param) i)
                     (not endp))
            (push (ctbl:render-vline-color V model param i) ret)))
    ;; right border line
    (when (ctbl:render-draw-vline-p
           model (ctbl:param-draw-vlines param) -1)
      (push (ctbl:render-vline-color V model param -1) ret))
    ;; join them
    (mapconcat 'identity (reverse ret) "")))

(defun ctbl:render-sum-vline-widths (cmodels model param)
  "[internal] Return a sum of the widths of vertical lines."
  (let ((sum 0))
    ;; left border line
    (when (ctbl:render-draw-vline-p model (ctbl:param-draw-vlines param) 0)
      (incf sum))
    ;; content line
    (loop with param-vl = (ctbl:param-draw-vlines param)
          with endi = (length cmodels)
          for i from 1 upto (length cmodels)
          for endp = (equal i endi) do
          (when (and (ctbl:render-draw-vline-p
                      model (ctbl:param-draw-vlines param) i)
                     (not endp))
            (incf sum)))
    ;; right border line
    (when (ctbl:render-draw-vline-p
           model (ctbl:param-draw-vlines param) -1)
      (incf sum))
    sum))

(defun ctbl:state-new (max-height data)
  "[internal] Create output state object. see `ctbl:render-insert' function."
  ;; (current-line max-height data)
  (list 0 max-height data))

(defun ctbl:state-current (state)
  "[internal] Return the current line number."
  (car state))

(defun ctbl:state-max (state)
  "[internal] Return the maximum line number or nil."
  (cadr state))

(defun ctbl:state-increment (state)
  "[internal] Increment the current line number."
  (incf (car state)))

(defun ctbl:state-set-current-data (state data)
  "[internal] Set DATA at the data slot of STATE."
  (setf (nth 2 state) data))

(defun ctbl:state-get-current-data (state)
  "[internal] Return an object in the data slot of STATE."
  (nth 2 state))

(defun ctbl:state-over-p (state)
  "[internal] Return t if the current line number is over the
maximum line number."
  (and (ctbl:state-max state) 
       (<= (ctbl:state-max state) (ctbl:state-current state))))

(defvar ctbl:continue-button-keymap
  (ctbl:define-keymap
   '(([mouse-1] . ctbl:action-continue-clicked)
     ("C-m" . ctbl:action-continue-clicked)
     ("RET" . ctbl:action-continue-clicked)
     ))
  "Keymap for the continue button.")

(defun ctbl:render-insert (state &rest args)
  "[internal] Insert ARGS into the current buffer.
If the current line number is over the limit, this function
throws `ctbl:insert-break' symbol to break loop."
  (let ((str (apply 'concat args)))
    (unless (or (null args) (equal "" str))
      (insert str)
      (ctbl:state-increment state)
      (when (ctbl:state-over-p state)
        (let* ((msg (format "[Continue... (%s)]" ; data => remain row number
                            (ctbl:state-get-current-data state)))
               (nextbar (ctbl:format-center ; -1 => chop EOL
                        (1- (length str)) msg)))
          (insert (propertize nextbar
                              'keymap ctbl:continue-button-keymap
                              'face 'ctbl:face-continue-bar
                              'mouse-face 'highlight) "\n"))
        (throw 'ctbl:insert-break nil)))))
(put 'ctbl:render-insert 'lisp-indent-function 1)

(defun ctbl:action-continue-clicked ()
  "Action for clicking the continue button."
  (interactive)
  (let ((cp (ctbl:cp-get-component)))
    (when cp
      (let ((dest (ctbl:component-dest cp)))
        (setf (ctbl:dest-height dest) nil)
        (ctbl:cp-update cp)))))

(defun ctbl:dest-width-get (dest)
  "[internal] Return the column number to draw the table view.
Return nil, if the width is not given. Then, the renderer draws freely."
  (let ((dwidth (ctbl:dest-width dest)) ; dwidth must not be nil
        (dwin (get-buffer-window)))
    (cond
     ((numberp dwidth) dwidth)
     ((eq 'full dwidth) (window-width dwin))
     (t nil))))

(defun ctbl:dest-height-get (dest)
  "[internal] Return the row number to draw the table view.
Return nil, if the height is not given. Then, the renderer draws freely."
  (let ((dheight (ctbl:dest-height dest)) ; dheight must not be nil
        (dwin (get-buffer-window)))
    (cond
     ((numberp dheight) dheight)
     ((eq 'full dheight) (1- (window-height dwin)))
     (t nil))))

(defun ctbl:render-main (dest model param)
  "[internal] Rendering the table view.
This function assumes that the current buffer is the destination buffer."
  (let* ((EOL "\n") drows
         (cmodels (ctbl:model-column-model model))
         (rows (ctbl:sort
                (copy-sequence (ctbl:model-data model)) cmodels
                (ctbl:model-sort-state model)))
         (dstate (ctbl:state-new (ctbl:dest-height-get dest) rows))
         (column-widths
          (loop for c in cmodels
                for title = (ctbl:cmodel-title c)
                collect (max (or (ctbl:cmodel-min-width c) 0)
                             (or (and title (length title)) 0))))
         column-format)
    ;; check cell widths
    (setq drows (ctbl:render-check-cell-width rows cmodels column-widths))
    ;; adjust cell widths for ctbl:dest width
    (when (ctbl:dest-width-get dest)
      (setq column-widths
            (ctbl:render-adjust-cell-width
             cmodels column-widths
             (- (ctbl:dest-width-get dest)
                (ctbl:render-sum-vline-widths
                 cmodels model param)))))
    (setq column-format (ctbl:render-get-formats cmodels column-widths))
    (catch 'ctbl:insert-break
      (ctbl:render-main-header dest model param 
                               cmodels dstate column-widths)
      (ctbl:render-main-content dest model param 
                                cmodels drows dstate column-widths column-format))
    ;; return the sorted list
    rows))

(defun ctbl:render-main-header (dest model param cmodels dstate column-widths)
  "[internal] Render the table header."
  (let ((EOL "\n") 
        (header-string
         (ctbl:render-join-columns
          (loop for cm in cmodels
                for i from 0
                for cw in column-widths
                collect
                (propertize
                 (ctbl:format-center cw (ctbl:cmodel-title cm))
                 'ctbl:col-id i
                 'local-map (ctbl:render-column-header-keymap i)
                 'mouse-face 'highlight))
          model param)))
    (cond
     ((and (eq 'buffer (ctbl:dest-type dest))
           (ctbl:param-fixed-header param))
      ;; buffer header-line
      (let ((fcol (/ (car (window-fringes))
                     (frame-char-width))))
        (setq header-line-format
              (concat (make-string fcol ? ) header-string))))
     (t
      ;; content area
      (ctbl:render-insert dstate ; border line
        (ctbl:render-make-hline column-widths model param 0))
      (ctbl:render-insert dstate header-string EOL)  ; header columns
      ))))

(defun ctbl:render-main-content (dest model param cmodels rows 
                                      dstate column-widths column-format)
  "[internal] Render the table content."
  (let ((EOL "\n") (row-num (length rows)))
    (loop for cols in rows
          for row-index from 0
          do
          (ctbl:render-insert dstate
            (ctbl:render-make-hline
             column-widths model param (1+ row-index)))
          (ctbl:render-insert dstate
            (ctbl:render-join-columns
             (loop for i in cols
                   for s = (if (stringp i) i (format "%s" i))
                   for fmt in column-format
                   for col-index from 0
                   for str = (ctbl:render-bg-color-put
                              (funcall fmt i) row-index col-index
                              model param)
                   collect
                   (ctbl:tp str 'ctbl:cell-id (cons row-index col-index)))
             model param) EOL)
          (ctbl:state-set-current-data dstate (- row-num row-index)))
    ;; bottom border line
    (ctbl:render-insert dstate
      (ctbl:render-make-hline column-widths model param -1))))


;; Rendering utilities

(defun ctbl:format-truncate (org limit-width &optional ellipsis)
  "[internal] Truncate a string ORG with LIMIT-WIDTH, like `truncate-string-to-width'."
  (setq org (replace-regexp-in-string "\n" " " org))
  (if (< limit-width (string-width org))
      (let ((str (truncate-string-to-width
                  (substring org 0) limit-width 0 nil ellipsis)))
        (when (< limit-width (string-width str))
          (setq str (truncate-string-to-width (substring org 0) 
                                              limit-width)))
        (propertize str 'mouse-face 'highlight)
        (unless (get-text-property 0 'help-echo str)
          (propertize str 'help-echo org))
        str)
    org))

(defun ctbl:format-right (width string &optional padding)
  "[internal] Format STRING, padding on the left with the character PADDING."
  (let* ((padding (or padding ?\ ))
         (cnt (or (and string
                       (ctbl:format-truncate string width t))
                  ""))
         (len (string-width cnt))
         (margin (max 0 (- width len))))
    (concat (make-string margin padding) cnt)))

(defun ctbl:format-center (width string &optional padding)
  "[internal] Format STRING in the center, padding on the both
sides with the character PADDING."
  (let* ((padding (or padding ?\ ))
         (cnt (or (and string
                       (ctbl:format-truncate string width t))
                  ""))
         (len (string-width cnt))
         (margin (max 0 (/ (- width len) 2))))
    (concat
     (make-string margin padding) cnt
     (make-string (max 0 (- width len margin)) padding))))

(defun ctbl:format-left (width string &optional padding)
  "[internal] Format STRING, padding on the right with the character PADDING."
  (let* ((padding (or padding ?\ ))
         (cnt (or (and string
                       (ctbl:format-truncate string width t))
                  ""))
         (len (string-width cnt))
         (margin (max 0 (- width len))))
    (concat cnt (make-string margin padding))))

(defun ctbl:sort-string-lessp (i j)
  "[internal] String comparator."
  (cond
   ((string= i j) 0)
   ((string< i j) -1)
   (t 1)))

(defun ctbl:sort-number-lessp (i j)
  "[internal] Number comparator."
  (cond
   ((= i j) 0)
   ((< i j) -1)
   (t 1)))

(defun ctbl:sort (rows cmodels orders)
  "[internal] Sort rows according to order indexes and column models."
  (let*
      ((comparator
        (lambda (ref)
          (lexical-let
              ((ref ref)
               (f (or (ctbl:cmodel-sorter (nth ref cmodels))
                      'ctbl:sort-string-lessp)))
            (lambda (i j)
              (funcall f (nth ref i) (nth ref j))))))
       (negative-comparator
        (lambda (ref)
          (lexical-let ((cp (funcall comparator ref)))
            (lambda (i j) (- (funcall cp i j))))))
       (to-bool
        (lambda (f)
          (lexical-let ((f f))
            (lambda (i j)
              (< (funcall f i j) 0)))))
       (chain
        (lambda (fs)
          (lexical-let ((fs fs))
            (lambda (i j)
              (loop for f in fs
                    for v = (funcall f i j)
                    unless (eq 0 v)
                    return v
                    finally return 0))))))
    (sort rows
          (loop with fs = nil
                for o in (reverse (copy-sequence orders))
                for gen = (if (< 0 o) comparator negative-comparator)
                for f = (funcall gen (1- (abs o)))
                do (push f fs)
                finally return (funcall to-bool (funcall chain fs))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; CTable API

;; buffer

(defun* ctbl:open-table-buffer(&key buffer width height custom-map model param)
  "Open a table buffer simply.
This function uses the function
`ctbl:create-table-component-buffer' internally."
  (let ((cp (ctbl:create-table-component-buffer
             :buffer buffer :width width :height height
             :custom-map custom-map :model model :param param)))
    (switch-to-buffer (ctbl:cp-get-buffer cp))))

(defun* ctbl:create-table-component-buffer(&key buffer width height custom-map model param)
  "Return a table buffer with some customize parameters.

This function binds the component object at the
buffer local variable `ctbl:component'.

The size of table is calculated from the window that shows BUFFER or the selected window.
BUFFER is the buffer to be rendered. If BUFFER is nil, this function creates a new buffer.
CUSTOM-MAP is the additional keymap that is added to default keymap `ctbl:table-mode-map'."
  (let* ((dest  (ctbl:dest-init-buffer buffer width height custom-map))
         (cp (ctbl:cp-new dest model param)))
    (with-current-buffer (ctbl:dest-buffer dest)
      (set (make-local-variable 'ctbl:component) cp))
    cp))

(defun ctbl:popup-table-buffer-easy (rows &optional header-row)
  "Popup a table buffer from a list of rows."
  (pop-to-buffer (ctbl:create-table-buffer-easy rows header-row)))

(defun ctbl:open-table-buffer-easy (rows &optional header-row)
  "Open a table buffer from a list of rows."
  (switch-to-buffer (ctbl:create-table-buffer-easy rows header-row)))

(defun ctbl:create-table-buffer-easy (rows &optional header-row)
  "Return a table buffer from a list of rows."
  (let* ((col-num (or (and header-row (length header-row))
                      (and (car rows) (length (car rows)))))
         (column-models
          (if header-row
              (loop for i in header-row
                    collect (make-ctbl:cmodel :title (format "%s" i) :min-width 5))
            (loop for i from 0 below col-num
                  for ch = (char-to-string (+ ?A i))
                  collect (make-ctbl:cmodel :title ch :min-width 5))))
         (model 
          (make-ctbl:model
           :column-model column-models :data rows))
         (cp (ctbl:create-table-component-buffer
              :model model)))
    (ctbl:cp-get-buffer cp)))

;; region

(defun* ctbl:create-table-component-region(&key width height keymap model param)
  "Insert markers of the rendering destination at current point and display the table view.

This function returns a component object and stores it at the text property `ctbl:component'.

WIDTH and HEIGHT are reference size of the table view. If those are nil, the size is calculated from the selected window.
KEYMAP is the keymap that is put to the text property `keymap'. If KEYMAP is nil, `ctbl:table-mode-map' is used."
  (let (mark-begin mark-end)
    (setq mark-begin (point-marker))
    (insert " ")
    (setq mark-end (point-marker))
    (save-excursion
      (let* ((dest (ctbl:dest-init-region (current-buffer) mark-begin mark-end width height))
             (cp (ctbl:cp-new dest model param))
             (after-update-func
              (lexical-let ((keymap keymap) (cp cp))
                (lambda ()
                  (ctbl:dest-with-region (ctbl:component-dest cp)
                    (let (buffer-read-only)
                      (put-text-property (point-min) (1- (point-max))
                                         'ctbl:component cp)
                      (ctbl:fill-keymap-property
                       (point-min) (1- (point-max))
                       (or keymap ctbl:table-mode-map))))))))
        (setf (ctbl:dest-after-update-func dest) after-update-func)
        (funcall after-update-func)
        cp))))


;; inline

(defun* ctbl:get-table-text(&key width height model param)
  "Return a text that is drew the table view.

In this case, the rendering destination object is disposable. So,
one can not modify the obtained text with `ctbl:xxx' functions.

WIDTH and HEIGHT are reference size of the table view."
  (let* ((dest (ctbl:dest-init-inline width height))
         (cp (ctbl:cp-new dest model param))
         text)
    (setq text
          (with-current-buffer (ctbl:cp-get-buffer cp)
            (buffer-substring (point-min) (point-max))))
    (kill-buffer (ctbl:cp-get-buffer cp))
    text))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Demo

(defun ctbl:demo ()
  "Sample code for implementation for the table model."
  (interactive)
  (let ((param (copy-ctbl:param ctbl:default-rendering-param)))
    ;; rendering parameters
    (setf (ctbl:param-fixed-header param) t)
    (setf (ctbl:param-hline-colors param)
          '((0 . "#00000") (1 . "#909090") (-1 . "#ff0000") (t . "#00ff00")))
    (setf (ctbl:param-draw-hlines param)
          (lambda (model row-index)
            (cond ((memq row-index '(0 1 -1)) t)
                  (t (= 0 (% (1- row-index) 5))))))
    (setf (ctbl:param-bg-colors param)
          (lambda (model row-id col-id str)
            (cond ((string-match "CoCo" str) "LightPink")
                  ((= 0 (% (1- row-index) 2)) "Darkseagreen1")
                  (t nil))))
    (let ((cp
           (ctbl:create-table-component-buffer
            :width nil :height nil
            :model
            (make-ctbl:model
             :column-model
             (list (make-ctbl:cmodel
                    :title "A" :sorter 'ctbl:sort-number-lessp
                    :min-width 5 :align 'right)
                   (make-ctbl:cmodel
                    :title "Title" :align 'center
                    :sorter (lambda (a b) (ctbl:sort-number-lessp (length a) (length b))))
                   (make-ctbl:cmodel
                    :title "Comment" :align 'left))
             :data
             '((1  "Bon Tanaka" "8 Year Curry." 'a)
               (2  "Bon Tanaka" "Nan-ban Curry." 'b)
               (3  "Bon Tanaka" "Half Curry." 'c)
               (4  "Bon Tanaka" "Katsu Curry." 'd)
               (5  "Bon Tanaka" "Gyu-don." 'e)
               (6  "CoCo Ichi"  "Beaf Curry." 'f)
               (7  "CoCo Ichi"  "Poke Curry." 'g)
               (8  "CoCo Ichi"  "Yasai Curry." 'h)
               (9  "Berkley"    "Hamburger Curry." 'i)
               (10 "Berkley"    "Lunch set." 'j)
               (11 "Berkley"    "Coffee." k))
             :sort-state
             '(2 1)
             )
            :param param)))
      (ctbl:cp-add-click-hook 
       cp (lambda () (message "CTable : Click Hook [%S]" 
                              (ctbl:cp-get-selected-data-row cp))))
      (ctbl:cp-add-selection-change-hook cp (lambda () (message "CTable : Select Hook")))
      (ctbl:cp-add-update-hook cp (lambda () (message "CTable : Update Hook")))
      (switch-to-buffer (ctbl:cp-get-buffer cp)))))

;; (progn (eval-current-buffer) (ctbl:demo))

(provide 'ctable)
;;; ctable.el ends here
