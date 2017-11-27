(require 'kv)
(require 'ert)

(ert-deftest kvhash->alist ()
  "Test making alists from hashes."
  (should
   (equal
    (sort
     (kvhash->alist
      (kvalist->hash '((name1 . value1)
                       (name2 . value2))))
     (lambda (a b)
       (string-lessp (symbol-name (car a))
                     (symbol-name (car b)))))
    '((name1 . value1)
      (name2 . value2))))
  (should
   (equal
    (sort '((a . 1)
            (c . 3)) 'kvcmp)
    (sort (kvhash->alist
           (kvalist->hash '((a . 1)(b . 2)(c . 3)))
           (lambda (k v) (and (memq k '(a c)) v))) 'kvcmp))))

(ert-deftest kvalist-sort ()
  (should
   (equal
    (kvalist-sort
     (list '("z" . 20)
           '("a" . 20)
           '("b" . 17))
     'string-lessp)
    '(("a" . 20)
      ("b" . 17)
      ("z" . 20)))))

(ert-deftest kvalist-sort-by-value ()
  (should
   (equal
    (kvalist-sort-by-value
     (list '("z" . 20)
           '("a" . 20)
           '("b" . 17))
     '<)
    '(("b" . 17)
      ("z" . 20)
      ("a" . 20)))))

(ert-deftest kvcmp ()
  "Test the general cmp function."
  (should
   (equal
    '((a . 10)(b . 20)(c . 5))
   (sort '((a . 10)(b . 20)(c . 5)) 'kvcmp)))
  (should
   (equal
    '((a . 10)(b . 20)(c . 5))
   (sort '((b . 20)(c . 5)(a . 10)) 'kvcmp))))

(ert-deftest kvalist-keys->symbols ()
  "Test the key transformation."
  (should
   (equal
    '((a . 10)(\10 . 20)(\(a\ b\ c\) . 30))
    (kvalist-keys->symbols
     '(("a" . 10)(10 . 20)((a b c) . 30)))))
  (should
   (equal
    '((a . 10)(\10 . 20)(\(a\ b\ c\) . 30))
    (kvalist-keys->symbols
     '(("A" . 10)(10 . 20)((a b c) . 30))
     :first-fn 'downcase))))

(ert-deftest kvfa ()
  "Destructuring kva through functions."
  (should
   (equal '("b")
          (kvfa "a" '((:a :b)("a" "b"))
                (lambda (key &rest result) result))))
  (should
   (equal "b"
          (kvfa "a" '((:a :b)("a" "b"))
                (lambda (k v &rest any) v))))
  (should
   (equal "b"
          (kvfa "a" '((:a . :b)("a" . "b"))
                (cl-function
                 (lambda (k v &rest any) v)))))
  (should
   (equal 1
          (kvfa "a" '((:a :b :c 1)("a" "b" :a 1))
                (cl-function
                 (lambda (k v &key a) a))))))

(ert-deftest kva ()
  "Test the simple assoc."
  (should (equal :b (kva :a '((:a . :b)("a" . "b")))))
  (should (equal "b" (kva "a" '((:a . :b)("a" . "b")))))
  (should-not (kva "b" '((:a . :b)("a" . "b")))))

(ert-deftest kvaq ()
  "Test the simple assq."
  (should (equal :b (kvaq :a '((:a . :b)("a" . "b")))))
  (should (equal 2 (kvaq 1 '((1 . 2)("a" . "b")))))
  (should-not (equal "b" (kvaq "a" '((:a . :b)("a" . "b")))))
  (should-not (kvaq "b" '((:a . :b)("a" . "b")))))

(ert-deftest kvaq ()
  "Test the simple assq."
  (should (equal :b (kvaq :a '((:a . :b)("a" . "b")))))
  (should (equal 2 (kvaq 1 '((1 . 2)("a" . "b")))))
  (should-not (equal "b" (kvaq "a" '((:a . :b)("a" . "b")))))
  (should-not (kvaq "b" '((:a . :b)("a" . "b")))))

(ert-deftest kvaqc ()
  "Test the simple assq."
  (should (equal :b (kvaqc :a '((:a . :b)("a" . "b")))))
  (should (equal 2 (kvaqc 1 '((1 . 2)("a" . "b")))))
  (should (equal "b" (kvaqc "a" '((:a . :b)("a" . "b")))))
  (should-not (kvaqc "b" '((:a . :b)("a" . "b")))))

(ert-deftest kvassoc= ()
  (should
   (equal
    '("testkey" . "testvalue")
    (kvassoc= "testkey" "testvalue" '(("testkey" . "testvalue"))))))

(ert-deftest kvassoq= ()
  (should
   (equal
    '(testkey . "testvalue")
    (kvassoq= 'testkey "testvalue" '((testkey . "testvalue")))))
  (should
   (equal
    '("testkey" . "testvalue")
    (kvassoq= "testkey" "testvalue" '(("testkey" . "testvalue")))))
  ;; Not sure about this - should we really find strings with symbols?
  (should
   (equal
    '("testkey" . "testvalue")
    (kvassoq= 'testkey "testvalue" '(("testkey" . "testvalue")))))
  ;; The nil case, the key isn't present
  (should
   (equal
    nil
    (kvassoq= 'blah "testvalue" '(("testkey" . "testvalue"))))))

(ert-deftest kvalist2-filter ()
  (should
   (equal
    '(((a . 1)(b . 2)))
    (kvalist2-filter
     '(((a . 1)(b . 2))((c . 1)(d . 2)))
     (lambda (alist)
       (or
        (memq 'a (kvalist->keys alist))
        (memq 'b (kvalist->keys alist))))))))

(ert-deftest kvquery->func ()
  "Test the query language."
  (should
   (equal
    '((("a" . 1)("b" . 2))(("c" . 1)("d" . 2)))
    (kvalist2-filter
     '((("a" . 1)("b" . 2))(("c" . 1)("d" . 2)))
     (kvquery->func '(|(= "a" 1)(= "d" 2))))))
  (should
   (equal
    '((("a" . 1)("b" . 2)))
    (kvalist2-filter
     '((("a" . 1)("b" . 2))(("c" . 1)("d" . 2)))
     (kvquery->func '(= "a" 1)))))
  (should
   (equal
    '()
    (kvalist2-filter
     '((("a" . 1)("b" . 2))(("c" . 1)("d" . 2)))
     (kvquery->func '(&(= "a" 1)(= "c" 1))))))
  (should
   (equal
    '((("a" . 1)("b" . 2)))
    (kvalist2-filter
     '((("a" . 1)("b" . 2))(("c" . 1)("d" . 2)))
     (kvquery->func '(&(= "a" 1)(= "b" 2)))))))

(ert-deftest kvdotassoc ()
  (should
   (equal
    (dotassoc "a.b.c" '(("a" . (("b" . (("c" . 10)))))))
    10)))

(ert-deftest kvdotassq ()
  (should
   (equal
    (dotassq 'a.b.c '((a . ((b . ((c . 10)))))))
    10)))

(ert-deftest keyword->symbol ()
  "Convert keyword into a symbol without the leading `:'"
  (should
   (eq
    'key
    (keyword->symbol :key)))
  (should
   (eq
    'key
    (keyword->symbol 'key)))
  (let ((sym (gensym)))
    (should
     (eq
      sym
      (keyword->symbol sym)))))


(ert-deftest kvthing->keyword ()
  (should (equal :one (kvthing->keyword "one")))
  (should (equal :one (kvthing->keyword ":one"))))

(ert-deftest kvalist->plist ()
  "Make alists into plists."
  (should
   (equal
    '(:a1 value1 :a2 value2)
    (kvalist->plist '((a1 . value1) (a2 . value2))))))

(ert-deftest kvplist->alist ()
  "Make plists into alists."
  (should
   (equal
    '((a1 . value1) (a2 . value2))
    (kvplist->alist '(:a1  value1 :a2 value2)))))

(ert-deftest kvplist->filter-keys ()
  (should
   (equal
    (list :key1 "value1" :key4 10)
    (kvplist->filter-keys
     (list :key1 "value1" :key2 t :key3 '(big list of symbols) :key4 10)
     'key1 'key4))))

(ert-deftest kvplist-merge ()
  (should
   (equal
    '(:key1 "value1" :key2 "new value" :key3 "entirely new")
    (kvplist-merge '(:key1 "value1" :key2 "old value")
                   '(:key2 "new value" :key3 "entirely new")))))

(ert-deftest kvplist-merge-multiple ()
  (should
   (equal
    '(:key1 "value1" :key2 "new value" :key3 "overwritten new one" :key4 "second entirely new")
    (kvplist-merge '(:key1 "value1" :key2 "old value")
                   '(:key2 "new value" :key3 "entirely new")
                   '(:key3 "overwritten new one" :key4 "second entirely new")))))

;;; kv-tests.el ends here
