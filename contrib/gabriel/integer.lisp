
(defun pi-inv (bits &aux (m 0))
  (declare (type integer bits m))
  (let* ((n (+ bits (integer-length bits) 11))
         (tt (truncate (ash 1 n) 882))
         (d (* 4 882 882))
         (s 0))
    (declare (type integer s d tt n))
;    (print (list n tt d s))
    (do ((i 2 (+ i 2))
         (j 1123 (+ j 21460)))
        ((zerop tt) (cons s (- (+ n 2))))
      (declare (type integer i j))
        (setq s (+ s (* j tt))
              m (- (* (- i 1) (- (* 2 i) 1) (- (* 2 i) 3)))
              tt (truncate (* m tt) (* d (the integer (expt i 3))))))))

(defun dvide (x y n)
  (let* ((ew (+ (integer-length (car y)) (- (integer-length (car x))) n 1))
         (mw (truncate (ash (car x) ew) (car y)))
         (ew (- (cdr x) (cdr y) ew)))
    (cons mw ew)))

(defun pi (bits) (dvide (cons 1 0) (pi-inv bits) bits))

(defun test-float (x) (scale-float (coerce (car x) 'long-float) (cdr x)))

(defun factorial (n)
  (declare (type fixnum n))
  (do ((i 1 (+ i 1))
       (ans 1 (* i ans)))
      ((> i n) ans)
    (declare (type fixnum i) (type integer ans))))

