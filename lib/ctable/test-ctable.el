;;; test-ctable.el --- tests for ctable

;; Copyright (C) 2012 SAKURAI Masashi

;; Author:  <m.sakurai at kiwanami.net>
;; Keywords: test

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

(defvar ctbl:test-buffer-name "*ctbl:test*")

(defun ctbl:test-get-buffer ()
  (cond
   ((not (equal (buffer-name) ctbl:test-buffer-name))
    (pop-to-buffer (get-buffer-create ctbl:test-buffer-name))
    (erase-buffer))
   (t (insert "--------------------------------------------------\n")))
  (get-buffer ctbl:test-buffer-name))



;; test code

(defun ctbl:test-adjust-widths ()
  "[internal] Test function for `ctbl:render-adjust-cell-width'."
  (interactive)
  (let ((cmodels
         (list (make-ctbl:cmodel)
               (make-ctbl:cmodel :min-width 5)
               (make-ctbl:cmodel :max-width 5)))
        (init-column-widths '(1 6 3)) ; total = 10
        (tests
         '( ; (total-width . (result widths))
           (nil . (1 6 3))
           (13  . (2 7 4)) ; res:3 -> 1
           (21  . (6 10 5)) ; res:11 -> 3...2
           (8   . (1 5 2)) ; res:-2 -> 1
           (6   . (1 5 1)) ; res:-4 -> 1
           )))

    (ctbl:test-get-buffer)
    (loop for (total-width . expected-widths) in tests
          for result = (ctbl:render-adjust-cell-width
                        cmodels (copy-sequence init-column-widths) total-width)
          if (equal result expected-widths)
          do (insert (format "OK : cols %S\n" expected-widths))
          else
          do (insert (format "NG : Expected %S -> Result %S\n" expected-widths result)))))

;; (ctbl:test-adjust-widths)

(defun ctbl:test-sort ()
  "[internal] Test function for `ctbl:sort'."
  (interactive)
  (let ((cmodels
         (list (make-ctbl:cmodel :sorter 'ctbl:sort-number-lessp)
               (make-ctbl:cmodel :sorter 'ctbl:sort-string-lessp)
               (make-ctbl:cmodel)))
        (rows
         '((1 "c" "E")
           (2 "b" "D")
           (3 "b" "B")
           (4 "a" "C")
           (5 "a" "A")))
        (tests '(( (  ) . (1 2 3 4 5))
                 ( ( 1) . (1 2 3 4 5))
                 ( (-1) . (5 4 3 2 1))
                 ( ( 2) . (4 5 2 3 1))
                 ( (-2) . (1 2 3 4 5))
                 ( ( 3) . (5 3 4 2 1))
                 ( (-3) . (1 2 4 3 5))
                 ( ( 1 2) . (1 2 3 4 5))
                 ( ( 2 1) . (4 5 2 3 1))
                 ( (-2 1) . (1 2 3 4 5))
                 ( (2 -1) . (5 4 3 2 1))
                 ( ( 2 3) . (5 4 3 2 1))
                 ( (2 -3) . (4 5 2 3 1)))))
    (ctbl:test-get-buffer)
    (loop for (keys . order) in tests
          for sorted = (ctbl:sort (copy-sequence rows) cmodels keys)
          for nums = (mapcar 'car sorted)
          if (equal order nums)
          do (insert (format "OK : Keys %S\n" keys sorted))
          else
          do (insert (format "NG : Keys %S -> sorted %S\n" keys sorted)))))

;; (ctbl:test-sort)

(defun ctbl:test-modify-sort-key ()
  (interactive)
  (let ((model (make-ctbl:model :data 'data :sort-state nil))
        (tests
         '((0 . (1))     (0 . (-1))    (0 . (1))
           (1 . (2 1))   (1 . (-2 1))  (1 . (2 1))
           (2 . (3 2 1)) (0 . (1 3 2)) (0 . (-1 3 2)) (1 . (2 -1 3))
           (0 . (1 2 3)))))
    (ctbl:test-get-buffer)
    (loop for (col-index . order) in tests
          for keys = (ctbl:model-modify-sort-key model col-index)
          if (equal order keys)
          do (insert (format "OK : Col %s | Keys %S\n" col-index keys))
          else
          do (insert (format "NG : Col %s | Keys %S -> sorted %S\n" col-index order keys)))))

;; (ctbl:test-modify-sort-key)

(defun ctbl:test-render-join ()
  (lexical-let*
      ((param (copy-ctbl:param ctbl:default-rendering-param))
       (model 'model) ; dummy
       (src '("11" "22" "33" "44"))
       (tests
        (list
         (cons "|11|22|33|44|"
               (lambda ()
                 (setf (ctbl:param-vline-colors param) "DarkGray")
                 (setf (ctbl:param-draw-vlines param) 'all)
                 (ctbl:render-join-columns (copy-sequence src) model param)))
         (cons "|112233|44"
               (lambda ()
                 (setf (ctbl:param-vline-colors param) '((0 . "Red") (3 . "Blue")))
                 (setf (ctbl:param-draw-vlines param) '(0 3))
                 (ctbl:render-join-columns (copy-sequence src) model param)))
         (cons "|11|223344|"
               (lambda ()
                 (setf (ctbl:param-vline-colors param) '((0 . "Red") (-1 . "Blue")))
                 (setf (ctbl:param-draw-vlines param) '(0 1 -1))
                 (ctbl:render-join-columns (copy-sequence src) model param)))
         (cons "|1122|3344|"
               (lambda ()
                 (setf (ctbl:param-vline-colors param)
                       (lambda (model col-index)
                         (nth col-index '("Gray" "White" "Pink"))))
                 (setf (ctbl:param-draw-vlines param)
                       (lambda (model col-index)
                         (memq col-index '(0 -1 2))))
                 (ctbl:render-join-columns (copy-sequence src) model param))))))
    (ctbl:test-get-buffer)
    (loop for (exp . test) in tests
          for res = (condition-case err (funcall test) (t err))
          if (equal res exp)
          do (insert (format "OK  %s\n" res))
          else
          do (insert (format "NG  %s -> %s\n" exp res)))))

;; (ctbl:test-render-join)

(defun ctbl:test-bg-colors ()
  (let* ((param (copy-ctbl:param ctbl:default-rendering-param))
         (model 'model) ; dummy
         (tests
          (list
           (cons '((0 0 nil) (1 1 nil))
                 nil)
           (cons '((0 0 "black") (1 1 "white"))
                 '(((0 . 0) . "black") (t . "white")))
           (cons '((0 0 "blue") (1 1 "red"))
                 (lambda (m row-id col-id str)
                   (let ((pair (cons row-id col-id)))
                     (cond
                      ((equal '(0 . 0) pair)
                       "blue")
                      ((equal '(1 . 1) pair)
                       "red")
                      (t (error "BUG %S" pair))))))
           (cons '((0 0 nil) (1 0 "green") (2 0 nil) (3 0 "green"))
                 (lambda (m row-id col-id str)
                   (cond
                    ((= 0 (% row-id 2)) nil)
                    (t "green")))))))
    (ctbl:test-get-buffer)
    (loop for (samples . test) in tests
          for test-id from 1 do
          (setf (ctbl:param-bg-colors param) test)
          (loop for (row-id col-id exp) in samples
                for enum-id from 1
                for res = (condition-case err
                              (ctbl:render-bg-color
                               "dummy" row-id col-id model param ) (t err))
                if (equal res exp)
                do (insert (format "OK [%s-%s] %s\n" test-id enum-id res))
                else
                do (insert (format "NG [%s-%s] %s -> %s | %S\n" test-id enum-id exp res ))))))

;; (ctbl:test-bg-colors)

(defun ctbl:test-make-hline ()
  (let*
      ((param (copy-ctbl:param ctbl:default-rendering-param))
       (model 'model) ; dummy
       (cols '(1 2 3 4))
       (tests
        (list
         (cons 0  "1-2--2---2----3\n")
         (cons 1  "7-8--8---8----9\n")
         (cons -1 "4-5--5---5----6\n"))))
    (setf (ctbl:param-draw-vlines    param) 'all
          (ctbl:param-draw-hlines  param) 'all
          (ctbl:param-left-top-corner        param) ?1
          (ctbl:param-top-junction           param) ?2
          (ctbl:param-right-top-corner       param) ?3
          (ctbl:param-left-bottom-corner     param) ?4
          (ctbl:param-bottom-junction        param) ?5
          (ctbl:param-right-bottom-corner    param) ?6
          (ctbl:param-left-junction          param) ?7
          (ctbl:param-cross-junction         param) ?8
          (ctbl:param-right-junction         param) ?9)
    (ctbl:test-get-buffer)
    (loop for (pos . exp) in tests
          for res = (ctbl:render-make-hline cols model param pos)
          if (equal res exp)
          do (insert (format "OK  %s" res))
          else
          do (insert (format "NG  %s -> %s" exp res)))
    ))

;; (ctbl:test-make-hline)

(defun ctbl:test-all ()
  (interactive)
  (ctbl:test-adjust-widths)
  (ctbl:test-sort)
  (ctbl:test-bg-colors)
  (ctbl:test-modify-sort-key)
  (ctbl:test-render-join)
  (ctbl:test-make-hline)
  )

;; (progn (eval-current-buffer) (ctbl:test-all))

(provide 'test-ctable)
;;; test-ctable.el ends here
