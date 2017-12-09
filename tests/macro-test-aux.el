(require 'names)

(defmacro !cdr (list)
  "Destructive: Set LIST to the cdr of LIST."
  `(setq ,list (cdr ,list)))

(define-namespace test- 
(defmacro each (list &rest body)
  (declare (debug (form body))
           (indent 1))
  (let ((l (make-symbol "list")))
    `(let ((,l ,list)
           (it-index 0))
       (while ,l
         (let ((it (car ,l)))
           ,@body)
         (setq it-index (1+ it-index))
         (!cdr ,l)))))

(defun message ()
  (let ((out))
    (each
     '(1 2 3 4)
     (push (format "%s" it) out))
    out)))

;; (progn
;;   (defmacro la-each (list &rest body)
;;     (declare (debug (form body))
;;              (indent 1))
;;     (let ((l (make-symbol "list")))
;;       `(let ((,l ,list)
;;              (it-index 0))
;;          (while ,l
;;            (let ((it (car ,l)))
;;              ,@body)
;;            (setq it-index (1+ it-index))
;;            (!cdr ,l)))))
;;   (defmacro lo-each (list &rest body)
;;     (declare (debug (form body))
;;              (indent 1))
;;     `(la-each ,list ,@body)))
;; (progn
;;   (defun la-message ()
;;     (let ((out))
;;       (lo-each
;;        '(1 2 3 4)
;;        (push (format "%s" it) out))
;;       out)))

(provide 'macro-test-aux)
