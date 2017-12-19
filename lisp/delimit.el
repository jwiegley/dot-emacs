;; -*- lexical-binding: t -*-

(defun shift (k entry)
  (if (eq (nth 0 k) 'outer)
      (throw (nth 1 k)
             (funcall entry #'(lambda (val)
                                (funcall (nth 2 k)
                                         (list 'inner val)))))
    (nth 1 k)))

(defun reset (thunk)
  (let ((bound (make-symbol "reset--bound")))
    (catch bound
      (funcall thunk (list 'outer bound thunk)))))

(reset
 #'(lambda (_)
     (+ 4 (reset
           #'(lambda (p)
               (* 2 (shift p #'(lambda (k)
                                 (funcall k (funcall k 4))))))))))
;; (+ 4 (* 2 (* 2 4)))
;; => 20

(reset
 #'(lambda (q)
     (+ 4 (reset
           #'(lambda (_)
               (* 2 (shift q #'(lambda (k)
                                 (funcall k (funcall k 4))))))))))
;; (+ 4 (* 2 (+ 4 (* 2 4))))
;; => 28

(let ((data '(1 2 3)))
  (reset
   #'(lambda (p)
       (list 'a 'b (shift p #'(lambda (k)
                                (append (funcall k 0)
                                        (mapcar (apply-partially k)
                                                data))))))))
;; => (a b 0
;;     (a b 1)
;;     (a b 2)
;;     (a b 3))
