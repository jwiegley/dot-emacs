;;; direx-ctable.el --- direx table extension

;; Copyright (C) 2013  SAKURAI Masashi

;; Author: SAKURAI Masashi <m.sakurai at kiwanami.net>
;; Keywords: dired, ctable

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

;; collaboration between direx and ctable.

;; ref: direx-el
;;   https://github.com/m2ym/direx-el

;;; Code:

(require 'ctable)
(require 'direx)

(defun dxt:collect-entries (direx-buf)
  "[internal] "
  (with-current-buffer direx-buf
    (goto-char (point-min))
    (loop with data-list = nil
          with goaheadp = t
          for item = (direx:item-at-point)
          while goaheadp do 
          (when (and item (direx:item-visible-p item))
            (push item data-list))
          (setq goaheadp (zerop (forward-line)))
          finally return (nreverse data-list))))


(defun dxt:item-render (item)
  "[internal] "
  (concat
   (direx:item-render-indent-part item)
   (direx:item-render-icon-part item)
   (direx:item-render-name-part item)))

(defun dxt:make-model-data-sort-prop (row item)
  "[internal] "
  (loop with head = (ctbl:format-left 
                     64 (file-name-directory (direx:file-full-name (direx:item-tree item))))
        for i in row
        collect
        (if (stringp i)
            (propertize i 'dxt:sorter (message (format "%s%64s" head i))) i)))

(defun dxt:make-model-data (buf)
  "[internal] "
  (loop for i in (dxt:collect-entries buf)
        for itree = (direx:item-tree i)
        for attr = (file-attributes (direx:file-full-name itree))
        collect
        (dxt:make-model-data-sort-prop
         (list 
          (dxt:item-render i)
          (if (direx:item-leaf-p i)
              (format "%d" (nth 7 attr)) " ")
          (format-time-string   "%Y/%m/%d %H:%M:%S" (nth 5 attr))
          i) i)))

(defun dxt:make-model (buf)
  "[internal] "
  (make-ctbl:model
   :column-model
   (list
    (make-ctbl:cmodel
     :title "File" :min-width 10 :align 'left :sorter 'dxt:sort-item-lessp)
    (make-ctbl:cmodel
     :title "Size" :min-width 6 :align 'right :sorter 'dxt:sort-item-lessp)
    (make-ctbl:cmodel
     :title "Last Modified" :align 'left :sorter 'dxt:sort-item-lessp))
   :data
   (dxt:make-model-data buf)))

(defun dxt:sort-item-lessp (i j)
  "[internal] Direx item comparator."
  (let ((ii (get-text-property 0 'dxt:sorter i))
        (jj (get-text-property 0 'dxt:sorter j)))
    (cond
     ((string= ii jj) 0)
     ((string< ii jj) -1)
     (t 1))))

(defun dxt:node-action (direx-buf cp row)
  "[internal] action handler"
  (let ((item (nth 3 row)))
    (cond
     ((direx:item-leaf-p item)
      (direx:find-item item))
     (t
      (with-current-buffer direx-buf
        (direx:item-toggle item))
      (ctbl:cp-set-model cp (dxt:make-model direx-buf))))))

(defun dxt:open (dirname)
  (interactive "DDirex (directory): ")
  (lexical-let*
      ((dxbuf (direx:ensure-buffer-for-root
               (direx:make-directory dirname)))
       (cp
        (ctbl:create-table-component-buffer
         :width nil :height nil
         :model
         (dxt:make-model dxbuf))))
    (ctbl:cp-add-click-hook 
     cp (lambda () 
          (dxt:node-action
           dxbuf cp (ctbl:cp-get-selected-data-row cp))))
    (switch-to-buffer (ctbl:cp-get-buffer cp))))

(defun dxt:open-here ()
  (interactive)
  (dxt:open default-directory))

;; (progn (eval-current-buffer) (dxt:open-here))

(provide 'direx-ctable)
;;; direx-ctable.el ends here

