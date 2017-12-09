;;; -*- lexical-binding: t -*-

(require 'ert)
(require 'seq)
(require 'typ)

(typ--default-annotations-load)

(ert-deftest typ-noreturn ()
  (dolist (f '(throw error signal user-error))
    (should (typ-noreturn? f))))

(ert-deftest typ-combine ()
  (pcase-dolist
      (`[,t1 ,t2 -> ,want]
       '(;;; Numeric types combinations.
         [:number :number -> :number]
         [:number :integer -> :number]
         [:number :float -> :number]
         [:number :nil -> nil]
         [:integer :integer -> :integer]
         [:integer :float -> :number]
         [:integer :nil -> nil]
         [:float :float -> :float]
         [:float :nil -> nil]
         ;;; Parametric types combinations.
         ;; Single-level combinations.
         [(:sequence . :integer) (:sequence . :float) -> (:sequence . :number)]
         [(:sequence . :integer) (:list . :float) -> (:sequence . :number)]
         [(:sequence . :integer) (:array . :float) -> (:sequence . :number)]
         [(:sequence . :boolean) :bool-vector -> (:sequence . :boolean)]
         [(:sequence . :integer) :string -> (:sequence . :integer)]
         [(:sequence . :integer) (:vector . :float) -> (:sequence . :number)]
         [(:list . :integer) (:list . :float) -> (:list . :number)]
         [(:list . :integer) (:array . :float) -> (:sequence . :number)]
         [(:list . :boolean) :bool-vector -> (:sequence . :boolean)]
         [(:list . :integer) :string -> (:sequence . :integer)]
         [(:list . :integer) (:vector . :float) -> (:sequence . :number)]
         [(:array . :integer) (:array . :float) -> (:array . :number)]
         [(:array . :boolean) :bool-vector -> (:array . :boolean)]
         [(:array . :integer) :string -> (:array . :integer)]
         [(:array . :integer) (:vector . :float) -> (:array . :number)]
         [(:vector . :integer) (:vector . :float) -> (:vector . :number)]
         ;; Multi-level combinations.
         [(:list :list . :integer) (:list :list . :float) -> (:list :list . :number)]
         [(:sequence :list . :nil) (:array :list . :nil) -> (:sequence :list . :nil)]
         [(:sequence :vector . :nil) (:list :list . :nil) -> (:sequence :sequence . :nil)]
         [(:list . :string) (:list :array . :integer) -> (:list :array . :integer)]
         [(:list :list . :string) (:vector :list :sequence . :integer) -> (:sequence :list :sequence . :integer)]
         [(:list :list . :bool-vector) (:vector :list :array . :boolean) -> (:sequence :list :array . :boolean)]
         [(:list :list . :string) (:vector :vector . :string) -> (:sequence :sequence . :string)]
         [(:vector :vector :vector . :float) (:array :array :array . :integer) -> (:array :array :array . :number)]
         ;; Special cases.
         [:string :bool-vector -> (:array . nil)]
         [(:vector . :float) :bool-vector -> (:array . nil)]
         [(:vector . :nil) :bool-vector -> (:array . nil)]
         [(:vector . :float) :string -> (:array . :number)]
         [(:vector . :string) :string -> (:array . nil)]
         ;; Nil propagation.
         [(:sequence . :integer) (:list . nil) -> (:sequence . nil)]
         [(:list . :integer) (:list . nil) -> (:list . nil)]
         [(:list :list . :integer) (:list :list . nil) -> (:list :list . nil)]
         ))
    ;; Perform merge in both directions.
    ;; `combine' operation must be commutative.
    (should (and (equal want
                        (typ-combine t1 t2))
                 (equal want
                        (typ-combine t2 t1))))))

(ert-deftest typ-infer-lit ()
  (pcase-dolist
      (`[,lit ,want]
       '([10 :integer]
         [10.0 :float]
         ["" :string]
         [t :boolean]
         [sym :symbol]
         [nil :nil]
         [() :nil]
         ))
    (should (eq want
                (typ-infer lit)))))

(ert-deftest typ-simple-predicates ()
  (pcase-dolist
      (`[,pred ,arg ,want]
       '([typ-infer-integer? 10 t]
         [typ-infer-integer? nil nil]
         [typ-infer-float? 10.0 t]
         [typ-infer-float? nil nil]
         [typ-infer-string? "" t]
         [typ-infer-string? nil nil]
         [typ-infer-hash-table? #s(hash-table size 1 data nil) t]
         [typ-infer-hash-table? nil nil]
         [typ-infer-boolean? t t]
         [typ-infer-boolean? nil nil]
         [typ-infer-symbol? sym t]
         [typ-infer-symbol? nil nil]
         ))
    (should (eq want
                (funcall pred arg t)))))

(ert-deftest typ-abstract-predicates ()
  (pcase-dolist
      (`[,pred ,arg ,want]
       '([typ-infer-number? 1 t]
         [typ-infer-number? 1.0 t]
         [typ-infer-number? nil nil]
         [typ-infer-sequence? "1" t]
         [typ-infer-sequence? (1) t]
         [typ-infer-sequence? [1] t]
         [typ-infer-sequence? 1 nil]
         [typ-infer-sequence? nil nil]
         [typ-infer-array? "1" t]
         [typ-infer-array? [1] t]
         [typ-infer-array? (1) nil]
         [typ-infer-array? 1 nil]
         [typ-infer-array? nil nil]
         ))
    (should (eq want
                (not (not (funcall pred arg t)))))))

(ert-deftest typ-infer-quoted ()
  (pcase-dolist
      (`[,expr ,want]
       '([(+ a b) (:list . :symbol)]
         [(+ 1 2) (:list . nil)]
         [(1 2) (:list . :integer)]
         [(1 2.0) (:list . :number)]
         [((1) (2)) (:list :list . :integer)]
         [((1) (2.0)) (:list :list . :number)]
         [((1) [2]) (:list :sequence . :integer)]
         [[1] (:vector . :integer)]
         [[] (:vector . nil)]
         [[() ()] (:vector . :nil)]
         [[[] []] (:vector :vector . nil)]
         ))
    (should (equal want
                   (typ-infer expr t)))))

(ert-deftest typ-infer-elt ()
  (pcase-dolist
      (`[,seq ,want]
       '([(1 "2") nil]
         [[1 "2"] nil]
         [(1 2) :integer]
         [[1 2] :integer]
         ["1 2" :integer]
         [(1 2.0) :number]
         [[1 2.0] :number]
         [(1.0 2.0) :float]
         [["1" "2"] :string]
         [[[1] [2]] (:vector . :integer)]
         [(((1)) ((2))) (:list :list . :integer)]
         [(((1)) ((2.0))) (:list :list . :number)]
         [(((1)) (("2"))) (:list :list . nil)]
         ))
    (should (equal want
                   (typ-infer-elt seq t)))))

(ert-deftest typ-infer-integer ()
  (dolist (expr '((lsh x y)
                  (char-syntax ?c)
                  (point)
                  (length xs)
                  ))
    (should (equal :integer
                   (typ-infer expr)))))

(ert-deftest typ-infer-float ()
  (dolist (expr '((float x)
                  ))
    (should (equal :float
                   (typ-infer expr)))))

(ert-deftest typ-infer-number ()
  (dolist (expr '((string-to-number x)
                  ))
    (should (equal :number
                   (typ-infer expr)))))

(ert-deftest typ-infer-string ()
  (dolist (expr '((int-to-string x)
                  (number-to-string x)
                  (char-to-string x)
                  (concat x y z)
                  (symbol-name sym)
                  ))
    (should (equal :string
                   (typ-infer expr)))))

(ert-deftest typ-infer-symbol ()
  (dolist (expr '((intern "sym")
                  ))
    (should (equal :symbol
                   (typ-infer expr)))))

(ert-deftest typ-infer-boolean ()
  (dolist (expr '((not x)
                  (symbolp x)
                  (stringp x)
                  (consp x)
                  (listp x)
                  ))
    (should (equal :boolean
                   (typ-infer expr)))))

(ert-deftest typ-infer-mixed ()
  (pcase-dolist
      (`[,expr ,want]
       '([(+ 1 2) :integer]
         [(+ 1 2.0) :float]
         [(+ 1.0 2) :float]
         [(+ 1.0 2.0) :float]
         [(+ x 1.0) :float]
         [(+ x 1) :number]
         [(+ x y) :number]
         [(elt [1 2] 0) :integer]
         [(elt '("1" "2") 0) :string]
         [(elt "" 0) :integer]
         [(aref [1 2] 0) :integer]
         [(aref "" 0) :integer]
         [(aref '(1 2.0) 0) nil]
         [(nth 1 '(1 2.0)) :number]
         [(nth 1 [1 2.0] nil) nil]
         ))
    (should (equal want
                   (typ-infer expr)))))
