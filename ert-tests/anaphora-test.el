
(require 'anaphora)
(anaphora--install-traditional-aliases)

;; some tests (but no code) adapted from anaphora.lisp

;;; anaphoric-if

(ert-deftest anaphoric-if-01 nil
  (should (= 3
             (aif (1+ 1)
                 (1+ it)))))

(ert-deftest anaphoric-if-02 nil
  (should (= 3
             (aif (1+ 1)
                 (progn
                   (1+ it)
                   (1+ it))))))

(ert-deftest anaphoric-if-03 nil
  (should (= 4
             (aif (1+ 1)
                 (progn
                   (incf it)
                   (1+ it))))))

(ert-deftest anaphoric-if-04 nil
  (should
   (aif nil
       (+ 5 it)
     (null it))))

(ert-deftest anaphoric-if-05 nil
  (should (equal '(nil 1)
                 (let ((x 0))
                   (aif (eval `(and ,(incf x) nil))
                       :never
                     (list it x))))))


;;; anaphoric-prog1

(ert-deftest anaphoric-prog1-01 nil
  (should (= 5
             (aprog1 5
               (assert (eq it 5))
               10))))

(ert-deftest anaphoric-prog1-02 nil
  (should (= 6
             (aprog1 5
               (incf it)
               10))))

(ert-deftest anaphoric-prog1-03 nil
  (should-error
   (aprog1 (1+ it)
     (1+ it))))


;;; anaphoric-prog2

(ert-deftest anaphoric-prog2-01 nil
  (should (= 5
             (aprog2 1 5
               (assert (eq it 5))
               10))))

(ert-deftest anaphoric-prog2-02 nil
  (should (= 6
             (aprog2 1 5
               (incf it)
               10))))

(ert-deftest anaphoric-prog2-03 nil
  (should-error
   (aprog2 (1+ it) 1
     1))
  (should-error
   (aprog2 1 (1+ it)
     1)))


;;; anaphoric-when

(ert-deftest anaphoric-when-01 nil
  (should (= 3
             (awhen (1+ 1)
               (1+ it)))))

(ert-deftest anaphoric-when-02 nil
  (should (= 4
             (awhen (1+ 1)
               (incf it)
               (1+ it)))))

(ert-deftest anaphoric-when-03 nil
  (should (= 2
             (let ((x 0))
               (awhen (incf x)
                 (+ 1 it))))))

(ert-deftest anaphoric-when-04 nil
  (should (= 1
             (let ((x 0))
               (or (awhen (not (incf x))
                     t)
                   x)))))


;;; anaphoric-while

(ert-deftest anaphoric-while-01 nil
  (should (equal '((4) (3 4) (2 3 4) (1 2 3 4))
                 (let ((list '(1 2 3 4))
                       (out nil))
                   (awhile list
                     (push it out)
                     (pop list))
                   out))))

(ert-deftest anaphoric-while-02 nil
  (should (equal '((5 4) (5 3 4) (5 2 3 4) (5 1 2 3 4))
                 (let ((list '(1 2 3 4))
                       (out nil))
                   (awhile list
                     (push 5 it)
                     (push it out)
                     (pop list))
                   out))))


;;; anaphoric-and

(ert-deftest anaphoric-and-01 nil
  (should (= 3
             (aand (1+ 1)
                   (1+ it)))))

(ert-deftest anaphoric-and-02 nil
  (should (= 5
             (aand (1+ 1)
                   (1+ it)
                   (1+ it)
                   (1+ it)))))

(ert-deftest anaphoric-and-03 nil
  (should (= 5
             (aand (1+ 1)
                   (1+ it)
                   (incf it)
                   (1+ it)))))

(ert-deftest anaphoric-and-04 nil
  (should (equal '(1 2 3)
                 (aand (1+ 1)
                       '(1 2 3)
                       it))))

(ert-deftest anaphoric-and-05 nil
  (should-error
   (aand (1+ it)
         (1+ it))))


;;; anaphoric-cond

(ert-deftest anaphoric-cond-01 nil
  (should (= 1
             (acond (1)))))

(ert-deftest anaphoric-cond-02 nil
  (should-not
   (acond (1 nil))))

(ert-deftest anaphoric-cond-03 nil
  (should
   (acond (1 t))))

(ert-deftest anaphoric-cond-04 nil
  (should (eq :foo
              (acond (:foo) ("bar") (:baz)))))

(ert-deftest anaphoric-cond-05 nil
  (should (= 1
             (acond (:foo 1) ("bar") (:baz)))))

(ert-deftest anaphoric-cond-06 nil
  (should (= 1
             (acond (1 it)))))

(ert-deftest anaphoric-cond-07 nil
  (should (= 2
             (acond (1 (1+ it))))))

(ert-deftest anaphoric-cond-08 nil
  (should (= 3
             (acond
               (nil 4)
               (2 (1+ it))))))

(ert-deftest anaphoric-cond-09 nil
  (should (equal '(:yes 3)
                 (acond
                   ((null 1)
                    (list :no it))
                   ((+ 1 2)
                    (list :yes it))
                   (t
                    :nono)))))

(ert-deftest anaphoric-cond-10 nil
  (should (eq :yes
              (acond
                ((= 1 2)
                 :no)
                (nil
                 :nono)
                (t
                 :yes)))))

(ert-deftest anaphoric-cond-11 nil
  (should (= 42
             (let ((foo))
               (acond
                 ((+ 2 2)
                  (setf foo 38)
                  (incf foo it)
                  foo)
                 (t
                  nil))))))


;;; anaphoric-lambda

(ert-deftest anaphoric-lambda-01 nil
  (should (= 120
             (funcall (alambda (x)
                        (if (= x 0) 1 (* x (self (1- x))))) 5))))

(ert-deftest anaphoric-lambda-02 nil
  (should (equal '(1 2 1 2)
                 (let ((obj 'a))
                   (mapcar (alambda (list)
                             (if (consp list)
                                 (+ (if (eq (car list) obj) 1 0)
                                    (self (car list))
                                    (self (cdr list)))
                               0))
                           '((a b c) (d a r (p a)) (d a r) (a a)))))))


;;; anaphoric-block

(ert-deftest anaphoric-block-01 nil
  (should-not
   (ablock testing
     1
     (1+ it)
     (1+ it)
     (return-from testing))))

(ert-deftest anaphoric-block-02 nil
  (should (= 4
             (ablock testing
               1
               (1+ it)
               (1+ it)
               (return-from testing (1+ it))))))

(ert-deftest anaphoric-block-03 nil
  (should (= 3
             (ablock testing
               1
               (1+ it)
               (1+ it)))))

(ert-deftest anaphoric-block-04 nil
  (should (= 0
             (ablock testing
               1
               (1+ it)
               (1+ it)
               0))))


;;; anaphoric-case

(ert-deftest anaphoric-case-01 nil
  (should (equal '(:yes 1)
                 (let ((x 0))
                   (acase (incf x)
                     (0 :no)
                     (1 (list :yes it))
                     (2 :nono))))))

(ert-deftest anaphoric-case-02 nil
  (should (equal '(:yes 1)
                 (let ((x 0))
                   (acase (incf x)
                     (0 :no)
                     ((incf it) (list :yes it))
                     (1 (list :yes it)))))))

(ert-deftest anaphoric-case-03 nil
  (should (equal "bb"
                 (acase ?b
                   (?a "a")
                   (?c "c")
                   (?d "d")
                   (otherwise (string ?b it))))))


;;; anaphoric-ecase

(ert-deftest anaphoric-ecase-01 nil
  (should (equal '(:yes 1)
                 (let ((x 0))
                   (aecase (incf x)
                     (0 :no)
                     (1 (list :yes it))
                     (2 :nono))))))

(ert-deftest anaphoric-ecase-02 nil
  (should-error
   (aecase ?b
     (?a "a")
     (?c "c")
     (?d "d"))))


;;; anaphoric-typecase

(ert-deftest anaphoric-typecase-01 nil
  (should (= 0.0
             (atypecase 1.0
               (integer
                (+ 2 it))
               (float
                (1- it))))))

(ert-deftest anaphoric-typecase-02 nil
  (should-not
   (atypecase "Foo"
     (fixnum
      :no)
     (hash-table
      :nono))))

;;; anaphoric-etypecase

(ert-deftest anaphoric-etypecase-01 nil
  (should (= 0.0
             (aetypecase 1.0
               (integer
                (+ 2 it))
               (float
                (1- it))))))

(ert-deftest anaphoric-etypecase-02 nil
  (should-error
   (aetypecase "Foo"
     (fixnum
      :no)
     (hash-table
      :nono))))


;;; anaphoric-let

(ert-deftest anaphoric-let-01 nil
  (should (= 1
             (alet ((x 1)
                    (y 2)
                    (z 3))
               x))))

(ert-deftest anaphoric-let-02 nil
  (should (equal '(y 2)
                 (alet ((x 1)
                        (y 2)
                        (z 3))
                   (nth 1 it)))))

(ert-deftest anaphoric-let-03 nil
  (should (eq 'y
              (alet (x y z)
                (car (memq 'y it))))))

(ert-deftest anaphoric-let-04 nil
  (should (equal '(x y z)
                 (let ((vars '((x 1)
                               (y 2)
                               (z 3))))
                   (eval `(alet ,vars
                            (mapcar 'car it)))))))


;;; anaphoric-+

(ert-deftest anaphoric-+-01 nil
  (should (= 0
             (a+))))

(ert-deftest anaphoric-+-02 nil
  (should (= 2
             (a+ 2))))

(ert-deftest anaphoric-+-03 nil
  (should-error
   (progn
     (a+ it))))

(ert-deftest anaphoric-+-04 nil
  (should (= 9
             (a+ 2 3 4))))

(ert-deftest anaphoric-+-05 nil
  (should (= 13
             (a+ 2 3 4 it))))

(ert-deftest anaphoric-+-06 nil
  (should (= 15
             (a+ 2 3 4 it 2))))


;;; anaphoric--

(ert-deftest anaphoric---01 nil
  (should (= 0
             (a-))))

(ert-deftest anaphoric---02 nil
  (should (= -2
             (a- 2))))

(ert-deftest anaphoric---03 nil
  (should-error
   (progn
     (a- it))))

(ert-deftest anaphoric---04 nil
  (should (= 13
             (a- 20 3 4))))

(ert-deftest anaphoric---05 nil
  (should (= 9
             (a- 20 3 4 it))))

(ert-deftest anaphoric---06 nil
  (should (= 7
             (a- 20 3 4 it 2))))


;;; anaphoric-*

(ert-deftest anaphoric-*-01 nil
  (should (= 1
             (a*))))

(ert-deftest anaphoric-*-02 nil
  (should (= 2
             (a* 2))))

(ert-deftest anaphoric-*-03 nil
  (should-error
   (progn
     (a* it))))

(ert-deftest anaphoric-*-04 nil
  (should (= 24
             (a* 2 3 4))))

(ert-deftest anaphoric-*-05 nil
  (should (= 96
             (a* 2 3 4 it))))

(ert-deftest anaphoric-*-06 nil
  (should (= 192
             (a* 2 3 4 it 2))))


;;; anaphoric-/

(ert-deftest anaphoric-/-01 nil
  (should-error
   (progn
     (a/))))

(ert-deftest anaphoric-/-02 nil
  (should-error
   (progn
     (a/ 200))))

(ert-deftest anaphoric-/-03 nil
  (should (= 40
             (a/ 200 5))))

(ert-deftest anaphoric-/-04 nil
  (should-error
   (progn
     (a/ 200 it))))

(ert-deftest anaphoric-/-05 nil
  (should (= 20
             (a/ 200 5 2))))

(ert-deftest anaphoric-/-06 nil
  (should (= 10
             (a/ 200 5 2 it))))

(ert-deftest anaphoric-/-07 nil
  (should (= 2
             (a/ 200 5 2 it 5))))


;;; anaphoric-set

(ert-deftest anaphoric-set-01 nil
  (should-error
   (progn
     (anaphoric-set))))

(ert-deftest anaphoric-set-02 nil
  (should (= 2
             (let ((variable 0))
               (anaphoric-set 'variable 2)))))

(ert-deftest anaphoric-set-03 nil
  (should (eq 'variable
             (let ((variable 0))
               (anaphoric-set 'variable it)))))

(ert-deftest anaphoric-set-04 nil
  (should (equal "name-variable"
                 (let ((variable 0))
                   (anaphoric-set 'variable (format "name-%s" it))))))


;;; anaphoric-setq

(ert-deftest anaphoric-setq-01 nil
  (should-not
   (anaphoric-setq)))

(ert-deftest anaphoric-setq-02 nil
  (should (= 2
             (let ((variable 0))
               (anaphoric-setq variable 2)))))

(ert-deftest anaphoric-setq-03 nil
  (should (eq 'variable
             (let ((variable 0))
               (anaphoric-setq variable it)))))

(ert-deftest anaphoric-setq-04 nil
  (should (equal "name-variable"
             (let ((variable 0))
               (anaphoric-setq variable (format "name-%s" it))))))

(ert-deftest anaphoric-setq-05 nil
  (should (equal '("name-variable-1" "name-variable-2")
                 (let ((variable-1 0)
                       (variable-2 0))
                   (anaphoric-setq variable-1 (format "name-%s" it)
                                   variable-2 (format "name-%s" it))
                   (list variable-1 variable-2)))))

;;; anaphoric-setf

(ert-deftest anaphoric-setf-01 nil
  "Matching ordinary setf."
  :expected-result (if (fboundp 'cl-setf-do-modify) :passed :failed)
  (should (equal '(A 2 3 4 5 6 7 8 9 10)
                 (let ((sequence (number-sequence 1 10)))
                   (anaphoric-setf-experimental (car sequence) 'A)
                   sequence))))

(ert-deftest anaphoric-setf-02 nil
  "Matching ordinary setf."
  :expected-result (if (fboundp 'cl-setf-do-modify) :passed :failed)
  (should (equal '(1 2 3 4 . Z)
                 (let ((sequence (number-sequence 1 10)))
                   (anaphoric-setf-experimental (nthcdr 4 sequence) 'Z)
                   sequence))))

(ert-deftest anaphoric-setf-03 nil
  "Matching ordinary setf."
  :expected-result (if (fboundp 'cl-setf-do-modify) :passed :failed)
  (should (equal '(1 Z 3 4 5 6 7 8 9 10)
                 (let ((sequence (number-sequence 1 10)))
                   (anaphoric-setf-experimental (second sequence) 'Z)
                   sequence))))

(ert-deftest anaphoric-setf-04 nil
  "Matching ordinary setf."
  :expected-result (if (fboundp 'cl-setf-do-modify) :passed :failed)
  (should (equal '[1 2 3 4 Z 6]
                 (let ((sequence [1 2 3 4 5 6]))
                   (anaphoric-setf-experimental (aref sequence 4) 'Z)
                   sequence))))

(ert-deftest anaphoric-setf-05 nil
  "Make sure (incf counter) is called only once."
  :expected-result (if (fboundp 'cl-setf-do-modify) :passed :failed)
  (should (equal '(4 (1 2 3 4 . Z))
                 (let ((sequence (number-sequence 1 10))
                       (counter 3))
                   (anaphoric-setf-experimental (nthcdr (incf counter) sequence) 'Z)
                   (list counter sequence)))))

(ert-deftest anaphoric-setf-06 nil
  :expected-result (if (fboundp 'cl-setf-do-modify) :passed :failed)
  (should (equal '(1 2 3 4 . Z)
                 (let ((sequence (number-sequence 1 10)))
                   (anaphoric-setf-experimental (nthcdr (position 5 sequence) sequence) 'Z)
                   sequence))))

(ert-deftest anaphoric-setf-07 nil
  :expected-result (if (fboundp 'cl-setf-do-modify) :passed :failed)
  (should (equal '(1 2 3 . Z)
                 (let ((sequence (number-sequence 1 10)))
                   (anaphoric-setf-experimental (cdr (memq 3 sequence)) 'Z)
                   sequence))))

(ert-deftest anaphoric-setf-08 nil
  :expected-result (if (fboundp 'cl-setf-do-modify) :passed :failed)
  (should (equal '(1 2 3 . 7)
                 (let ((sequence (number-sequence 1 10)))
                   (anaphoric-setf-experimental (cdr (memq 3 sequence)) (length it))
                   sequence))))

(ert-deftest anaphoric-setf-09 nil
  :expected-result (if (fboundp 'cl-setf-do-modify) :passed :failed)
  (should (equal '(1 2 3 4 5 6 7 8 9 10 11 12 "88 elements removed")
                 (let ((sequence (number-sequence 1 100)))
                   (anaphoric-setf-experimental (nthcdr 12 sequence) (list (format "%s elements removed" (length it))))
                   sequence))))

(ert-deftest anaphoric-setf-10 nil
  "BUG TODO, this works with plain setf"
  :expected-result :failed
  (should (equal '("First element replaced" 2 3 4 5 6 7 8 9 10 11 12 13 14 15)
                 (let ((sequence (number-sequence 1 15)))
                   (anaphoric-setf-experimental (nthcdr 0 (car sequence)) (list "First element replaced"))
                   sequence))))

(ert-deftest anaphoric-setf-11 nil
  "Splicing out a series of members from the middle of a list."
  :expected-result (if (fboundp 'cl-setf-do-modify) :passed :failed)
  (should (equal '(1 2 3 4 7 8 9 10)
                 (let ((sequence (number-sequence 1 10)))
                   (anaphoric-setf-experimental (nthcdr 4 sequence) (cddr it))
                   sequence))))

(ert-deftest anaphoric-setf-12 nil
  "Splicing out a single member from the middle of a list."
  :expected-result (if (fboundp 'cl-setf-do-modify) :passed :failed)
  (should (equal '(1 2 3 4 6 7 8 9 10)
                 (let ((sequence (number-sequence 1 10)))
                   (anaphoric-setf-experimental (nthcdr (position 5 sequence) sequence) (cdr it))
                   sequence))))

(ert-deftest anaphoric-setf-13 nil
  "Splicing out a pair from a plist."
  :expected-result (if (fboundp 'cl-setf-do-modify) :passed :failed)
  (should (equal '(:one 1 :two 2 :four 4 :five 5)
                 (let ((sequence '(:one 1 :two 2 :three 3 :four 4 :five 5)))
                   (anaphoric-setf-experimental (nthcdr (position :three sequence) sequence) (cddr it))
                   sequence))))

(ert-deftest anaphoric-setf-14 nil
  :expected-result (if (fboundp 'cl-setf-do-modify) :passed :failed)
  (should (equal '("a" ?b ?c)
                 (let ((sequence '(?a ?b ?c)))
                   (anaphoric-setf-experimental (car sequence) (string it))
                   sequence))))

(ert-deftest anaphoric-setf-15 nil
  :expected-result (if (fboundp 'cl-setf-do-modify) :passed :failed)
  (should (equal '("1" 2 3)
                 (let ((sequence '(1 2 3)))
                   (anaphoric-setf-experimental (car sequence) (number-to-string it))
                   sequence))))

(ert-deftest anaphoric-setf-16 nil
  "A contrived example not workable with callf"
  :expected-result (if (fboundp 'cl-setf-do-modify) :passed :failed)
  (should (equal '(1 2 3 . "7 elements removed: (4 5 6 7 8 9 10)")
                 (let ((sequence (number-sequence 1 10))
                       (counter 2))
                   (anaphoric-setf-experimental (nthcdr (incf counter) sequence) (format "%s elements removed: %s" (length it) it))
                   sequence))))

;;
;; Emacs
;;
;; Local Variables:
;; indent-tabs-mode: nil
;; mangle-whitespace: t
;; require-final-newline: t
;; coding: utf-8
;; byte-compile-warnings: (not cl-functions)
;; End:
;;

;;; anaphora-test.el ends here
