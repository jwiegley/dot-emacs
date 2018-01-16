(require 'ctable)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Simple samples

;; popup a table

(ctbl:popup-table-buffer-easy 
 '((1 2 3 4)
   (5 6 7 8)
   (9 10 11 12)))  ; <- C-x C-e here to evaluate


;; popup a table with header

(ctbl:popup-table-buffer-easy 
 '((1 2 3 4) 
   (5 6 7 8)
   (9 10 11 12))
 '(aaa bbb ccc ddd))  ; <- C-x C-e here to evaluate




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Complicated samples

;; Model and View

(let* ((column-model ; column model
        (list (make-ctbl:cmodel
              :title "A" :sorter 'ctbl:sort-number-lessp
              :min-width 5 :align 'right)
              (make-ctbl:cmodel
               :title "Title" :align 'center
               :sorter (lambda (a b) (ctbl:sort-number-lessp (length a) (length b))))
              (make-ctbl:cmodel
               :title "Comment" :align 'left)))
       (data
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
          (11 "Berkley"    "Coffee." k)))
       (model ; data model
          (make-ctbl:model
           :column-model column-model :data data))
       (component ; ctable component
        (ctbl:create-table-component-buffer
         :model model)))
  (pop-to-buffer (ctbl:cp-get-buffer component)))  ; <- C-x C-e here to evaluate


;; Rendering parameters

(let* ((param 
        (copy-ctbl:param ctbl:default-rendering-param))
       (column-model ; column model
        (list (make-ctbl:cmodel
              :title "A" :sorter 'ctbl:sort-number-lessp
              :min-width 5 :align 'right)
              (make-ctbl:cmodel
               :title "Title" :align 'center
               :sorter (lambda (a b) (ctbl:sort-number-lessp (length a) (length b))))
              (make-ctbl:cmodel
               :title "Comment" :align 'left)))
       (data
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
          (11 "Berkley"    "Coffee." k)))
       (model ; data model
          (make-ctbl:model
           :column-model column-model :data data))
       component)

  (setf (ctbl:param-fixed-header param) t) ; set header parameters
  (setf (ctbl:param-hline-colors param)    ; horizontal line color
        '((0 . "#00000") (1 . "#909090") (-1 . "#ff0000") (t . "#00ff00"))) 
  (setf (ctbl:param-draw-hlines param)     ; horizontal line draw conditions
        (lambda (model row-index)
          (cond ((memq row-index '(0 1 -1)) t)
                (t (= 0 (% (1- row-index) 5))))))
  (setf (ctbl:param-bg-colors param)       ; cell background color
        (lambda (model row-id col-id str)
          (cond ((string-match "CoCo" str) "LightPink")
                ((= 0 (% (1- row-index) 2)) "Darkseagreen1")
                (t nil))))

  (setq component ; building a ctable component
        (ctbl:create-table-component-buffer
         :model model :param param)) ; apply the parameter to component rendering

  (pop-to-buffer (ctbl:cp-get-buffer component)))  ; <- C-x C-e here to evaluate



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Event handling

(lexical-let*
    ((column-model ; column model
      (list (make-ctbl:cmodel
             :title "A" :sorter 'ctbl:sort-number-lessp
             :min-width 5 :align 'right)
            (make-ctbl:cmodel
             :title "Title" :align 'center
             :sorter (lambda (a b) (ctbl:sort-number-lessp (length a) (length b))))
            (make-ctbl:cmodel
               :title "Comment" :align 'left)))
     (data
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
        (11 "Berkley"    "Coffee." k)))
     (model ; data model
      (make-ctbl:model
       :column-model column-model :data data))
     component)
  
  (setq component ; building a ctable component
        (ctbl:create-table-component-buffer
         :model model))
  
  ;; Click event handler
  (ctbl:cp-add-click-hook
   component (lambda () 
               (let ((row (ctbl:cp-get-selected-data-row component)))
                 (message "CTable : Click Hook [%S]" row)
                 ;; increment ID column
                 (when (= 0 (cdr (ctbl:cp-get-selected component)))
                   (message ">> %S" row)
                   (incf (car row)))
                 (ctbl:cp-update component)))) ; update table

  ;; Selection change event handler
  (ctbl:cp-add-selection-change-hook
   component (lambda () (message "CTable : Select Hook %S"
                          (ctbl:cp-get-selected component))))

  ;; Update event handler
  (ctbl:cp-add-update-hook
   component (lambda () (message "CTable : Update Hook")))
  
  (pop-to-buffer (ctbl:cp-get-buffer component)))  ; <- C-x C-e here to evaluate
