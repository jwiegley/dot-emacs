;;; An asynchronous data model sample for ctable.el 

(require 'ctable)
(require 'deferred)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; synchronous version

(defun ctbl:sync-demo1 ()
  (interactive)
  (ctbl:open-table-buffer-easy
   (loop with lim = 4000
         for i from 0 upto lim
         for d = (/ (random 1000) 1000.0)
         collect 
         (list i d (exp (- (/ i 1.0 lim))) (exp (* (- (/ i 1.0 lim)) d))))))

;; (ctbl:sync-demo1)  ; 5 seconds to display!


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; asynchronous version

(defun ctbl:async-demo ()
  "Sample code for implementation for async data model table."
  (interactive)
  (let ((param (copy-ctbl:param ctbl:default-rendering-param)))
    (setf (ctbl:param-fixed-header param) t)
    (let* ((async-model ; define async-data-model
            (make-ctbl:async-model
             :request 'ctbl:async-demo-request
             :cancel  'ctbl:async-demo-cancel
             :reset   'ctbl:async-demo-reset
             :init-num 40 :more-num 20))
           (cp
            (ctbl:create-table-component-buffer
             :model
             (make-ctbl:model
              :column-model
              (list (make-ctbl:cmodel :title "row")
                    (make-ctbl:cmodel :title "delta")
                    (make-ctbl:cmodel :title "exp")
                    (make-ctbl:cmodel :title "exp-delta"))
             :data async-model) ; here!
            :param param)))
      (ctbl:cp-add-click-hook
       cp (lambda () (message "CTable : Click Hook [%S]"
                              (ctbl:cp-get-selected-data-row cp))))
      (pop-to-buffer (ctbl:cp-get-buffer cp)))))

(defvar ctbl:async-demo-timer nil)

(defun ctbl:async-demo-request (row-num len responsef errorf &rest)
  (lexical-let 
      ((row-num row-num) (len len)
       (responsef responsef) (errorf errorf))
  (setq ctbl:async-demo-timer
        (deferred:$
          (deferred:wait 500)
          (deferred:nextc it
            (lambda (x) 
              (setq ctbl:async-demo-timer nil)
              (funcall responsef
                       (if (< 500 row-num) nil
                         (loop with lim = 100
                               for i from row-num below (+ row-num len)
                               for d = (/ (random 1000) 1000.0)
                               collect
                               (list i d (exp (- (/ i 1.0 lim)))
                                     (exp (* (- (/ i 1.0 lim)) d))))))))))))

(defun ctbl:async-demo-reset (&rest)
  (message "RESET async data!!"))

(defun ctbl:async-demo-cancel (&rest)
  (when ctbl:async-demo-timer
    (deferred:cancel ctbl:async-demo-timer)))

;; (progn (eval-current-buffer) (ctbl:async-demo))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; async wrapper version

(defun ctbl:sync-demo2 ()
  (interactive)
  (let* ((async-model ; wrapping a huge data in async-data-model
          (ctbl:async-model-wrapper
           (loop with lim = 4000
                 for i from 0 upto lim
                 for d = (/ (random 1000) 1000.0)
                 collect 
                 (list i d (exp (- (/ i 1.0 lim))) (exp (* (- (/ i 1.0 lim)) d))))))
         (cp
          (ctbl:create-table-component-buffer
           :model
           (make-ctbl:model
            :column-model
            (list (make-ctbl:cmodel :title "row")
                  (make-ctbl:cmodel :title "delta")
                  (make-ctbl:cmodel :title "exp")
                  (make-ctbl:cmodel :title "exp-delta"))
            :data async-model))))
    (pop-to-buffer (ctbl:cp-get-buffer cp))))

;; (progn (eval-current-buffer) (ctbl:sync-demo2))


