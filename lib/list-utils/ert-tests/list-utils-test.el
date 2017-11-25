
(require 'list-utils)

(eval-and-compile
  (require 'cl)
  (unless (fboundp 'cl-remove-duplicates)
    (defalias 'cl-remove-duplicates 'remove-duplicates))
  (unless (fboundp 'cl-set-difference)
    (defalias 'cl-set-difference 'set-difference))
  (unless (fboundp 'cl-set-exclusive-or)
    (defalias 'cl-set-exclusive-or 'set-exclusive-or))
  (unless (fboundp 'cl-intersection)
    (defalias 'cl-intersection 'intersection)))

;;; utility functions for testing

(defun list-utils-test-soft-string-lessp (x y)
  (string-lessp (if x (format "%s" x) "")
                (if y (format "%s" y) "")))

;;; make-tconc

(ert-deftest make-tconc-01 nil
  (should (equal '[cl-struct-tconc nil nil]
                 (make-tconc))))

(ert-deftest make-tconc-02 nil
  (should (equal '[cl-struct-tconc (1 2 3) (3)]
                 (let ((lst '(1 2 3)))
                   (make-tconc :head lst :tail (last lst))))))


;;; tconc-list

(ert-deftest tconc-list-01 nil
  (should (equal '(1 2 3 4 5)
                 (let ((tc (make-tconc)))
                   (tconc-list tc '(1 2 3))
                   (tconc-list tc '(4 5))))))

(ert-deftest tconc-list-02 nil
  (should (equal '[cl-struct-tconc (1 2 3 4 5) (5)]
                 (let ((tc (make-tconc)))
                   (tconc-list tc '(1 2 3))
                   (tconc-list tc '(4 5))
                   tc))))


;;; tconc

(ert-deftest tconc-01 nil
  (should (equal '(1 2 3 4 5)
                 (let ((tc (make-tconc)))
                   (tconc tc 1 2 3)
                   (tconc tc 4 5)))))

(ert-deftest tconc-02 nil
  (should (equal '[cl-struct-tconc (1 2 3 4 5) (5)]
                 (let ((tc (make-tconc)))
                   (tconc tc 1 2 3)
                   (tconc tc 4 5)
                   tc))))


;;; list-utils-cons-cell-p

(ert-deftest list-utils-cons-cell-p-01 nil
  (should-not
   (list-utils-cons-cell-p '(a b c d e f))))

(ert-deftest list-utils-cons-cell-p-02 nil
  (should-not
   (list-utils-cons-cell-p nil)))

(ert-deftest list-utils-cons-cell-p-03 nil
  (should-not
   (list-utils-cons-cell-p 1)))

(ert-deftest list-utils-cons-cell-p-04 nil
  (should (= 2
             (list-utils-cons-cell-p '(1 . 2)))))

(ert-deftest list-utils-cons-cell-p-05 nil
  (should (= 6
             (list-utils-cons-cell-p '(1 2 3 4 5 . 6)))))


;;; list-utils-make-proper-copy

(ert-deftest list-utils-make-proper-copy-01 nil
  "Already proper"
  (let* ((proper '(a b c d e f))
         (copy (copy-tree proper)))
    (should
     (equal proper copy))
    (should
     (equal proper
            (list-utils-make-proper-copy copy)))
    (should
     (equal proper copy))))

(ert-deftest list-utils-make-proper-copy-02 nil
  "nil"
  (should-not
   (list-utils-make-proper-copy nil)))

(ert-deftest list-utils-make-proper-copy-03 nil
  "Non-list"
  (should-error
   (list-utils-make-proper-copy 1)))

(ert-deftest list-utils-make-proper-copy-04 nil
  "Two elt cons"
  (let* ((proper '(1 2))
         (improper (apply 'list* proper))
         (backup (copy-tree improper)))
    (should-not
     (equal proper improper))
    (should
     (equal proper
            (list-utils-make-proper-copy improper)))
    (should
     ;; was not changed inplace
     (equal backup improper))))

(ert-deftest list-utils-make-proper-copy-05 nil
  "Multi-elt improper list"
  (let* ((proper '(a b c d e f))
         (improper (apply 'list* proper))
         (backup (copy-tree improper)))
    (should-not
     (equal proper improper))
    (should
     (equal proper
            (list-utils-make-proper-copy improper)))
    (should
     ;; was not changed inplace
     (equal backup improper))))

(ert-deftest list-utils-make-proper-copy-06 nil
  "Single-elt list"
  (let* ((proper '(1))
         (copy (copy-tree proper)))
    (should
     (equal proper copy))
    (should
     (equal proper
            (list-utils-make-proper-copy copy)))
    (should
     (equal proper copy))))

(ert-deftest list-utils-make-proper-copy-07 nil
  "With 'tree. Already proper"
  (let* ((proper '(a b c d e f))
         (copy (copy-tree proper)))
    (should
     (equal proper copy))
    (should
     (equal proper
            (list-utils-make-proper-copy copy 'tree)))
    (should
     (equal proper copy))))

(ert-deftest list-utils-make-proper-copy-08 nil
  "With 'tree. nil"
  (should-not
   (list-utils-make-proper-copy nil 'tree)))

(ert-deftest list-utils-make-proper-copy-09 nil
  "With 'tree. Non-list"
  (should-error
   (list-utils-make-proper-copy 1)))

(ert-deftest list-utils-make-proper-copy-10 nil
  "With 'tree. Two elt cons"
  (let* ((proper '(1 2))
         (improper (apply 'list* proper))
         (backup (copy-tree improper)))
    (should-not
     (equal proper improper))
    (should
     (equal proper
            (list-utils-make-proper-copy improper 'tree)))
    (should
     ;; was not changed inplace
     (equal backup improper))))

(ert-deftest list-utils-make-proper-copy-11 nil
  "With 'tree. Multi-elt improper list"
  (let* ((proper '(a b c d e f))
         (improper (apply 'list* proper))
         (backup (copy-tree improper)))
    (should-not
     (equal proper improper))
    (should
     (equal proper
            (list-utils-make-proper-copy improper 'tree)))
    (should
     ;; was not changed inplace
     (equal backup improper))))

(ert-deftest list-utils-make-proper-copy-12 nil
  "With 'tree. Single-elt list"
  (let* ((proper '(1))
         (copy (copy-tree proper)))
    (should
     (equal proper copy))
    (should
     (equal proper
            (list-utils-make-proper-copy copy 'tree)))
    (should
     (equal proper copy))))

(ert-deftest list-utils-make-proper-copy-13 nil
  "With 'tree. Deep structure."
  (let* ((proper '(a (b) (c d) (e (f g h) i) ((j k) l) m))
         (improper '(a (b) (c . d) (e (f g . h) . i) ((j . k) . l) . m))
         (backup (copy-tree improper)))
    (should-not
     (equal proper improper))
    (should
     (equal proper
            (list-utils-make-proper-copy improper 'tree)))
    (should
     ;; was not changed inplace
     (equal backup improper))))


;;; list-utils-make-proper-inplace

(ert-deftest list-utils-make-proper-inplace-01 nil
  "Already proper"
  (let* ((proper '(a b c d e f))
         (copy (copy-tree proper)))
    (should
     (equal proper copy))
    (should
     (equal proper
            (list-utils-make-proper-inplace copy)))
    (should
     (equal proper copy))))

(ert-deftest list-utils-make-proper-inplace-02 nil
  "nil"
  (should-not
   (list-utils-make-proper-inplace nil)))

(ert-deftest list-utils-make-proper-inplace-03 nil
  "Non-list"
  (should-error
   (list-utils-make-proper-inplace 1)))

(ert-deftest list-utils-make-proper-inplace-04 nil
  "Two elt cons"
  (let* ((proper '(1 2))
         (improper (apply 'list* proper)))
    (should-not
     (equal proper improper))
    (should
     (equal proper
            (list-utils-make-proper-inplace improper)))
    (should
     ;; was changed inplace
     (equal proper improper))))

(ert-deftest list-utils-make-proper-inplace-05 nil
  "Multi-elt improper list"
  (let* ((proper '(a b c d e f))
         (improper (apply 'list* proper)))
    (should-not
     (equal proper improper))
    (should
     (equal proper
            (list-utils-make-proper-inplace improper)))
    (should
     ;; was changed inplace
     (equal proper improper))))

(ert-deftest list-utils-make-proper-inplace-06 nil
  "Single-elt list"
  (let* ((proper '(1))
         (copy (copy-tree proper)))
    (should
     (equal proper copy))
    (should
     (equal proper
            (list-utils-make-proper-inplace copy)))
    (should
     (equal proper copy))))

(ert-deftest list-utils-make-proper-inplace-07 nil
  "With 'tree. Already proper"
  (let* ((proper '(a b c d e f))
         (copy (copy-tree proper)))
    (should
     (equal proper copy))
    (should
     (equal proper
            (list-utils-make-proper-inplace copy 'tree)))
    (should
     (equal proper copy))))

(ert-deftest list-utils-make-proper-inplace-08 nil
  "With 'tree. nil"
  (should-not
   (list-utils-make-proper-inplace nil 'tree)))

(ert-deftest list-utils-make-proper-inplace-09 nil
  "With 'tree. Non-list"
  (should-error
   (list-utils-make-proper-inplace 1 'tree)))

(ert-deftest list-utils-make-proper-inplace-10 nil
  "With 'tree. Two elt cons"
  (let* ((proper '(1 2))
         (improper (apply 'list* proper)))
    (should-not
     (equal proper improper))
    (should
     (equal proper
            (list-utils-make-proper-inplace improper 'tree)))
    (should
     ;; was changed inplace
     (equal proper improper))))

(ert-deftest list-utils-make-proper-inplace-11 nil
  "With 'tree. Multi-elt improper list"
  (let* ((proper '(a b c d e f))
         (improper (apply 'list* proper)))
    (should-not
     (equal proper improper))
    (should
     (equal proper
            (list-utils-make-proper-inplace improper 'tree)))
    (should
     ;; was changed inplace
     (equal proper improper))))

(ert-deftest list-utils-make-proper-inplace-12 nil
  "With 'tree. Single-elt list"
  (let* ((proper '(1))
         (copy (copy-tree proper)))
    (should
     (equal proper copy))
    (should
     (equal proper
            (list-utils-make-proper-inplace copy 'tree)))
    (should
     (equal proper copy))))

(ert-deftest list-utils-make-proper-inplace-13 nil
  "With 'tree. Deep structure."
  (let* ((proper '(a (b) (c d) (e (f g h) i) ((j k) l) m))
         (improper '(a (b) (c . d) (e (f g . h) . i) ((j . k) . l) . m)))
    (should-not
     (equal proper improper))
    (should
     (equal proper
            (list-utils-make-proper-inplace improper 'tree)))
    (should
     ;; was changed inplace
     (equal proper improper))))


;;; list-utils-make-improper-copy

(ert-deftest list-utils-make-improper-copy-01 nil
  "Already improper"
  (let* ((improper '(1 2 3 4 5 . 6))
         (copy (copy-tree improper)))
    (should
     (equal improper copy))
    (should
     (equal improper
            (list-utils-make-improper-copy copy)))
    (should
     (equal improper copy))))

(ert-deftest list-utils-make-improper-copy-02 nil
  "Nil"
  (should-error
   (list-utils-make-improper-copy nil)))

(ert-deftest list-utils-make-improper-copy-03 nil
  "Non-list"
  (should-error
   (list-utils-make-improper-copy 1)))

(ert-deftest list-utils-make-improper-copy-04 nil
  "Two elt list"
  (let* ((proper '(1 2))
         (improper (apply 'list* proper))
         (backup (copy-tree proper)))
    (should-not
     (equal improper proper))
    (should
     (equal improper
            (list-utils-make-improper-copy proper)))
    (should
     ;; was not changed inplace
     (equal backup proper))))

(ert-deftest list-utils-make-improper-copy-05 nil
  "Multi-elt list"
  (let* ((proper '(a b c d e f))
         (improper (apply 'list* proper))
         (backup (copy-tree proper)))
    (should-not
     (equal improper proper))
    (should
     (equal improper
            (list-utils-make-improper-copy proper)))
    (should
     ;; was not changed inplace
     (equal backup proper))))

(ert-deftest list-utils-make-improper-copy-06 nil
  "Single-elt list"
  (let* ((proper '(1))
         (copy (copy-tree proper)))
    (should
     (equal proper copy))
    (should-error
     (list-utils-make-improper-copy copy))))

(ert-deftest list-utils-make-improper-copy-07 nil
  "With 'tree. Already improper"
  (let* ((improper '(1 2 3 4 5 . 6))
         (copy (copy-tree improper)))
    (should
     (equal improper copy))
    (should
     (equal improper
            (list-utils-make-improper-copy copy 'tree)))
    (should
     (equal improper copy))))

(ert-deftest list-utils-make-improper-copy-08 nil
  "With 'tree. Nil"
  (should-error
   (list-utils-make-improper-copy nil 'tree)))

(ert-deftest list-utils-make-improper-copy-09 nil
  "With 'tree. Non-list"
  (should-error
   (list-utils-make-improper-copy 1 'tree)))

(ert-deftest list-utils-make-improper-copy-10 nil
  "With 'tree. Two elt list"
  (let* ((proper '(1 2))
         (improper (apply 'list* proper))
         (backup (copy-tree proper)))
    (should-not
     (equal improper proper))
    (should
     (equal improper
            (list-utils-make-improper-copy proper 'tree)))
    (should
     ;; was not changed inplace
     (equal backup proper))))

(ert-deftest list-utils-make-improper-copy-11 nil
  "With 'tree. Multi-elt list"
  (let* ((proper '(a b c d e f))
         (improper (apply 'list* proper))
         (backup (copy-tree proper)))
    (should-not
     (equal improper proper))
    (should
     (equal improper
            (list-utils-make-improper-copy proper 'tree)))
    (should
     ;; was not changed inplace
     (equal backup proper))))

(ert-deftest list-utils-make-improper-copy-12 nil
  "With 'tree. Single-elt list"
  (let* ((proper '(1))
         (copy (copy-tree proper)))
    (should
     (equal proper copy))
    (should-error
     (list-utils-make-improper-copy copy 'tree))))

(ert-deftest list-utils-make-improper-copy-13 nil
  "With 'tree. Deep structure."
  (let* ((proper '(a (b) (c d) (e (f g h) i) ((j k) l) m))
         (improper '(a (b) (c . d) (e (f g . h) . i) ((j . k) . l) . m))
         (backup (copy-tree proper)))
    (should-not
     (equal improper proper))
    (should
     (equal improper
            (list-utils-make-improper-copy proper 'tree)))
    (should
     ;; was not changed inplace
     (equal backup proper))))


;;; list-utils-make-improper-inplace

(ert-deftest list-utils-make-improper-inplace-01 nil
  "Already improper"
  (let* ((improper '(1 2 3 4 5 . 6))
         (copy (copy-tree improper)))
    (should
     (equal improper copy))
    (should
     (equal improper
            (list-utils-make-improper-inplace copy)))
    (should
     (equal improper copy))))

(ert-deftest list-utils-make-improper-inplace-02 nil
  "Nil"
  (should-error
   (list-utils-make-improper-inplace nil)))

(ert-deftest list-utils-make-improper-inplace-03 nil
  "Non-list"
  (should-error
   (list-utils-make-improper-inplace 1)))

(ert-deftest list-utils-make-improper-inplace-04 nil
  "Two elt list"
  (let* ((proper '(1 2))
         (improper (apply 'list* proper)))
    (should-not
     (equal improper proper))
    (should
     (equal improper
            (list-utils-make-improper-inplace proper)))
    (should
     ;; was changed inplace
     (equal improper proper))))

(ert-deftest list-utils-make-improper-inplace-05 nil
  "Multi-elt list"
  (let* ((proper '(a b c d e f))
         (improper (apply 'list* proper)))
    (should-not
     (equal improper proper))
    (should
     (equal improper
            (list-utils-make-improper-inplace proper)))
    (should
     ;; was changed inplace
     (equal improper proper))))

(ert-deftest list-utils-make-improper-inplace-06 nil
  "Single-elt list"
  (let* ((proper '(1))
         (copy (copy-tree proper)))
    (should
     (equal proper copy))
    (should-error
     (list-utils-make-improper-inplace copy))))

(ert-deftest list-utils-make-improper-inplace-07 nil
  "With 'tree. Already improper"
  (let* ((improper '(1 2 3 4 5 . 6))
         (copy (copy-tree improper)))
    (should
     (equal improper copy))
    (should
     (equal improper
            (list-utils-make-improper-inplace copy 'tree)))
    (should
     (equal improper copy))))

(ert-deftest list-utils-make-improper-inplace-08 nil
  "With 'tree. Nil"
  (should-error
   (list-utils-make-improper-inplace nil 'tree)))

(ert-deftest list-utils-make-improper-inplace-09 nil
  "With 'tree. Non-list"
  (should-error
   (list-utils-make-improper-inplace 1 'tree)))

(ert-deftest list-utils-make-improper-inplace-10 nil
  "With 'tree. Two elt list"
  (let* ((proper '(1 2))
         (improper (apply 'list* proper)))
    (should-not
     (equal improper proper))
    (should
     (equal improper
            (list-utils-make-improper-inplace proper 'tree)))
    (should
     ;; was changed inplace
     (equal improper proper))))

(ert-deftest list-utils-make-improper-inplace-11 nil
  "With 'tree. Multi-elt list"
  (let* ((proper '(a b c d e f))
         (improper (apply 'list* proper)))
    (should-not
     (equal improper proper))
    (should
     (equal improper
            (list-utils-make-improper-inplace proper 'tree)))
    (should
     ;; was changed inplace
     (equal improper proper))))

(ert-deftest list-utils-make-improper-inplace-12 nil
  "With 'tree. Single-elt list"
  (let* ((proper '(1))
         (copy (copy-tree proper)))
    (should
     (equal proper copy))
    (should-error
     (list-utils-make-improper-inplace copy 'tree))))

(ert-deftest list-utils-make-improper-inplace-13 nil
  "With 'tree. Deep structure."
  (let* ((proper '(a (b) (c d) (e (f g h) i) ((j k) l) m))
         (improper '(a (b) (c . d) (e (f g . h) . i) ((j . k) . l) . m)))
    (should-not
     (equal improper proper))
    (should
     (equal improper
            (list-utils-make-improper-inplace proper 'tree)))
    (should
     ;; was not changed inplace
     (equal improper proper))))


;;; list-utils-cyclic-length

(ert-deftest list-utils-cyclic-length-01 nil
  (should (= 8
             (let ((cyclic '(a b c d e f g h)))
               (nconc cyclic cyclic)
               (list-utils-cyclic-length cyclic)))))

(ert-deftest list-utils-cyclic-length-02 nil
  (should (= 7
             (let ((cyclic '(a b c d e f g h)))
               (nconc cyclic (cdr cyclic))
               (list-utils-cyclic-length cyclic)))))

(ert-deftest list-utils-cyclic-length-03 nil
  (should (= 1
             (let ((cyclic '(a b c d e f g h)))
               (nconc cyclic (last cyclic))
               (list-utils-cyclic-length cyclic)))))

(ert-deftest list-utils-cyclic-length-04 nil
  (should (= 0
             (list-utils-cyclic-length (cons 1 2)))))

(ert-deftest list-utils-cyclic-length-05 nil
  (should (= 0
             (list-utils-cyclic-length (list* 1 2 3)))))

(ert-deftest list-utils-cyclic-length-06 nil
  (let ((cyclic '(1)))
    (nconc cyclic cyclic)
    (should (= 1
               (list-utils-cyclic-length cyclic)))))


;;; list-utils-cyclic-subseq

(ert-deftest list-utils-cyclic-subseq-01 nil
  (should (equal '(1 2 3 4 5 6 7 8)
                 (let ((cyclic '(1 2 3 4 5 6 7 8)))
                   (nconc cyclic cyclic)
                   (sort (list-utils-flatten (list-utils-cyclic-subseq cyclic)) '<)))))

(ert-deftest list-utils-cyclic-subseq-02 nil
  (should (equal '(2 3 4 5 6 7 8)
                 (let ((cyclic '(1 2 3 4 5 6 7 8)))
                   (nconc cyclic (cdr cyclic))
                   (sort (list-utils-flatten (list-utils-cyclic-subseq cyclic)) '<)))))

(ert-deftest list-utils-cyclic-subseq-03 nil
  (should (equal '(2 3 4 5 6 7 8)
                 (let ((cyclic '(1 2 3 4 5 6 7 8)))
                   (nconc cyclic (cdr cyclic))
                   (list-utils-flatten (list-utils-cyclic-subseq cyclic 'from-start))))))

(ert-deftest list-utils-cyclic-subseq-04 nil
  (should (equal '(8)
                 (let ((cyclic '(1 2 3 4 5 6 7 8)))
                   (nconc cyclic (last cyclic))
                   (list-utils-flatten (list-utils-cyclic-subseq cyclic))))))

(ert-deftest list-utils-cyclic-subseq-05 nil
  (should-not
   (list-utils-cyclic-subseq '(1 2 3))))

(ert-deftest list-utils-cyclic-subseq-06 nil
  (should-not
   (list-utils-cyclic-subseq nil)))

(ert-deftest list-utils-cyclic-subseq-07 nil
  (should-not
   (list-utils-cyclic-subseq (cons 1 2))))

(ert-deftest list-utils-cyclic-subseq-08 nil
  (should-not
   (list-utils-cyclic-subseq (list* 1 2 3))))

(ert-deftest list-utils-cyclic-subseq-09 nil
  (let ((cyclic '(1)))
    (nconc cyclic cyclic)
    (should (equal '(1)
                   (list-utils-flatten (list-utils-cyclic-subseq cyclic))))))



;;; list-utils-cyclic-p

(ert-deftest list-utils-cyclic-p-01 nil
  (should
   (let ((cyclic '(1 2 3 4 5 6 7 8)))
     (nconc cyclic cyclic)
     (list-utils-cyclic-p cyclic))))

(ert-deftest list-utils-cyclic-p-02 nil
  (should
   (let ((cyclic '(1 2 3 4 5 6 7 8)))
     (nconc cyclic cyclic)
     (list-utils-cyclic-p cyclic 'perfect))))

(ert-deftest list-utils-cyclic-p-03 nil
  (should
   (let ((cyclic '(1 2 3 4 5 6 7 8)))
     (nconc cyclic (cdr cyclic))
     (list-utils-cyclic-p cyclic))))

(ert-deftest list-utils-cyclic-p-04 nil
  (should-not
   (let ((cyclic '(1 2 3 4 5 6 7 8)))
     (nconc cyclic (cdr cyclic))
     (list-utils-cyclic-p cyclic 'perfect))))

(ert-deftest list-utils-cyclic-p-05 nil
  (should
   (let ((cyclic '(1 2 3 4 5 6 7 8)))
     (nconc cyclic (last cyclic))
     (list-utils-cyclic-p cyclic))))

(ert-deftest list-utils-cyclic-p-06 nil
  (should-not
   (list-utils-cyclic-p '(1 2 3))))

(ert-deftest list-utils-cyclic-p-07 nil
  (should-not
   (list-utils-cyclic-p nil)))

(ert-deftest list-utils-cyclic-p-08 nil
  (should-not
   (list-utils-cyclic-p (cons 1 2))))

(ert-deftest list-utils-cyclic-p-09 nil
  (should-not
   (list-utils-cyclic-p (list* 1 2 3))))

(ert-deftest list-utils-cyclic-p-10 nil
  (should
   (let ((cyclic '(1)))
     (nconc cyclic cyclic)
     (list-utils-cyclic-p cyclic))))


;;; list-utils-linear-p

(ert-deftest list-utils-linear-p-01 nil
  (should-not
   (let ((cyclic '(1 2 3 4 5 6 7 8)))
     (nconc cyclic cyclic)
     (list-utils-linear-p cyclic))))

(ert-deftest list-utils-linear-p-02 nil
  (should-not
   (let ((cyclic '(1 2 3 4 5 6 7 8)))
     (nconc cyclic (cdr cyclic))
     (list-utils-linear-p cyclic))))

(ert-deftest list-utils-linear-p-03 nil
  (should-not
   (let ((cyclic '(1 2 3 4 5 6 7 8)))
     (nconc cyclic (last cyclic))
     (list-utils-linear-p cyclic))))

(ert-deftest list-utils-linear-p-04 nil
  (should
   (list-utils-linear-p '(1 2 3))))

(ert-deftest list-utils-linear-p-05 nil
  (should
   (list-utils-linear-p nil)))

(ert-deftest list-utils-linear-p-06 nil
  (should
   (list-utils-linear-p (cons 1 2))))

(ert-deftest list-utils-linear-p-07 nil
  (should
   (list-utils-linear-p (list* 1 2 3))))

(ert-deftest list-utils-linear-p-08 nil
  (let ((cyclic '(1)))
    (nconc cyclic cyclic)
    (should-not
     (list-utils-linear-p cyclic))))


;;; list-utils-linear-subseq

(ert-deftest list-utils-linear-subseq-01 nil
  (should-not
   (let ((cyclic '(a b c d e f g h)))
     (nconc cyclic cyclic)
     (list-utils-linear-subseq cyclic))))

(ert-deftest list-utils-linear-subseq-02 nil
  (should (equal '(a)
                 (let ((cyclic '(a b c d e f g h)))
                   (nconc cyclic (cdr cyclic))
                   (list-utils-linear-subseq cyclic)))))

(ert-deftest list-utils-linear-subseq-03 nil
  (should (equal '(a b c d e f g)
                 (let ((cyclic '(a b c d e f g h)))
                   (nconc cyclic (last cyclic))
                   (list-utils-linear-subseq cyclic)))))

(ert-deftest list-utils-linear-subseq-04 nil
  (let ((improper (cons 1 2)))
    (should (equal improper
                   (list-utils-linear-subseq improper)))))

(ert-deftest list-utils-linear-subseq-05 nil
  (let ((improper (list* 1 2 3)))
    (should (equal improper
                   (list-utils-linear-subseq (list* 1 2 3))))))

(ert-deftest list-utils-linear-subseq-06 nil
  (let ((cyclic '(1)))
    (nconc cyclic cyclic)
    (should-not
     (list-utils-linear-subseq cyclic))))


;;; list-utils-safe-length

(ert-deftest list-utils-safe-length-01 nil
  (should (= 8
             (let ((cyclic '(a b c d e f g h)))
               (nconc cyclic cyclic)
               (list-utils-safe-length cyclic)))))

(ert-deftest list-utils-safe-length-02 nil
  (should (= 8
             (let ((cyclic '(a b c d e f g h)))
               (nconc cyclic (cdr cyclic))
               (list-utils-safe-length cyclic)))))

(ert-deftest list-utils-safe-length-03 nil
  (should (= 8
             (let ((cyclic '(a b c d e f g h)))
               (nconc cyclic (last cyclic))
               (list-utils-safe-length cyclic)))))

(ert-deftest list-utils-safe-length-04 nil
  (should (= 8
             (let ((cyclic '(a b c d e f g h)))
               (list-utils-safe-length cyclic)))))

(ert-deftest list-utils-safe-length-05 nil
  (should (= 0
             (list-utils-safe-length nil))))

(ert-deftest list-utils-safe-length-06 nil
  (should (= 0
             (list-utils-safe-length :not-a-list))))

(ert-deftest list-utils-safe-length-07 nil
  (should (= 1
             (list-utils-safe-length (cons 1 2)))))

(ert-deftest list-utils-safe-length-08 nil
  (should (= 2
             (list-utils-safe-length (list* 1 2 3)))))

(ert-deftest list-utils-safe-length-09 nil
  (let ((cyclic '(1)))
    (nconc cyclic cyclic)
    (should (= 1
               (list-utils-safe-length cyclic)))))


;;; list-utils-flat-length

(ert-deftest list-utils-flat-length-01 nil
  (let ((mixed '(1 2 3 nil 7 8 9 (4 . 0) 5 6 7 (8 9))))
    (should (= 7
               (list-utils-flat-length mixed)))))


;;; list-utils-make-linear-copy

(ert-deftest list-utils-make-linear-copy-01 nil
  (let* ((value '(1 2 3 4 5))
         (cyclic (copy-tree value)))
    (nconc cyclic cyclic)
    (should
     (equal value
            (list-utils-make-linear-copy cyclic)))))

(ert-deftest list-utils-make-linear-copy-02 nil
  (let* ((value '(1 2 3 4 5))
         (cyclic (copy-tree value)))
    (nconc cyclic (cdr cyclic))
    (should
     (equal value
            (list-utils-make-linear-copy cyclic)))))

(ert-deftest list-utils-make-linear-copy-03 nil
  (let* ((value '(1 2 3 (4 (5 6))))
         (cyclic (copy-tree value)))
    (nconc cyclic (cdr cyclic))
    (should
     (equal value
            (list-utils-make-linear-copy cyclic)))))

(ert-deftest list-utils-make-linear-copy-04 nil
  "LIST argument is unchanged."
  (let* ((value '(1 2 3 (4 (5 6))))
         (cyclic-1 (copy-tree value))
         (cyclic-2 (copy-tree value)))
    (nconc cyclic-1 (cdr cyclic-1))
    (nconc cyclic-2 (cdr cyclic-2))
    (should
     (equal value
            (list-utils-make-linear-copy cyclic-1)))
    (should
     (list-utils-safe-equal cyclic-1 cyclic-2))))

(ert-deftest list-utils-make-linear-copy-05 nil
  "With 'tree"
  (let* ((value '(1 2 3 4 5))
         (cyclic value)
         (list-val (list 'a 'b cyclic))
         (list-copy (copy-tree list-val)))
    (nconc cyclic cyclic)
    (should
     (equal list-copy
            (list-utils-make-linear-copy list-val 'tree)))))

(ert-deftest list-utils-make-linear-copy-06 nil
  "With 'tree"
  (let* ((value '(1 2 3 4 5))
         (cyclic value)
         (list-val (list 'a 'b cyclic))
         (list-copy (copy-tree list-val)))
    (nconc cyclic (cdr cyclic))
    (should
     (equal list-copy
            (list-utils-make-linear-copy list-val 'tree)))))

(ert-deftest list-utils-make-linear-copy-07 nil
  "With 'tree"
  (let* ((value '(1 2 3 4 5))
         (cyclic value)
         (list-val (list 1 2 3 (list 4 (list 5 6 cyclic))))
         (list-copy (copy-tree list-val)))
    (nconc cyclic (cdr cyclic))
    (should
     (equal list-copy
            (list-utils-make-linear-copy list-val 'tree)))))

(ert-deftest list-utils-make-linear-copy-08 nil
  "With 'tree"
  (let* ((value '(1 2 3 4 5))
         (cyclic value)
         (list-val (list 1 2 3 (list 4 (list 5 6 cyclic))))
         (list-copy (copy-tree list-val)))
    (nconc cyclic (cdr cyclic))
    (nconc list-val list-val)
    (should
     (equal list-copy
            (list-utils-make-linear-copy list-val 'tree)))))

(ert-deftest list-utils-make-linear-copy-09 nil
  "With 'tree. LIST argument is not altered."
  (let* ((value '(1 2 3 4 5))
         (cyclic value)
         (list-val (list 'a 'b cyclic))
         (list-copy (copy-tree list-val)))
    (nconc cyclic (cdr cyclic))
    (should
     (equal list-copy
            (list-utils-make-linear-copy list-val 'tree)))
    (should-not
     (list-utils-safe-equal list-copy list-val))))


;;; list-utils-make-linear-inplace

(ert-deftest list-utils-make-linear-inplace-01 nil
  (let* ((value '(1 2 3 4 5))
         (cyclic value))
    (nconc cyclic cyclic)
    (should
     (equal value
            (list-utils-make-linear-inplace cyclic)))))

(ert-deftest list-utils-make-linear-inplace-02 nil
  (let* ((value '(1 2 3 4 5))
         (cyclic value))
    (nconc cyclic (cdr cyclic))
    (should
     (equal value
            (list-utils-make-linear-inplace cyclic)))))

(ert-deftest list-utils-make-linear-inplace-03 nil
  (let* ((value '(1 2 3 (4 (5 6))))
         (cyclic value))
    (nconc cyclic (cdr cyclic))
    (should
     (equal value
            (list-utils-make-linear-inplace cyclic)))))

(ert-deftest list-utils-make-linear-inplace-04 nil
  "LIST argument is altered."
  (let* ((value '(1 2 3 (4 (5 6))))
         (cyclic-1 (copy-tree value)))
    (nconc cyclic-1 (cdr cyclic-1))
    (should
     (equal value
            (list-utils-make-linear-inplace cyclic-1)))
    (should
     (list-utils-safe-equal value cyclic-1))))

(ert-deftest list-utils-make-linear-inplace-05 nil
  "With 'tree"
  (let* ((value '(1 2 3 4 5))
         (cyclic value)
         (list-val (list 'a 'b cyclic))
         (list-copy (copy-tree list-val)))
    (nconc cyclic cyclic)
    (should
     (equal list-copy
            (list-utils-make-linear-inplace list-val 'tree)))))

(ert-deftest list-utils-make-linear-inplace-06 nil
  "With 'tree"
  (let* ((value '(1 2 3 4 5))
         (cyclic value)
         (list-val (list 'a 'b cyclic))
         (list-copy (copy-tree list-val)))
    (nconc cyclic (cdr cyclic))
    (should
     (equal list-copy
            (list-utils-make-linear-inplace list-val 'tree)))))

(ert-deftest list-utils-make-linear-inplace-07 nil
  "With 'tree"
  (let* ((value '(1 2 3 4 5))
         (cyclic value)
         (list-val (list 1 2 3 (list 4 (list 5 6 cyclic))))
         (list-copy (copy-tree list-val)))
    (nconc cyclic (cdr cyclic))
    (should
     (equal list-copy
            (list-utils-make-linear-inplace list-val 'tree)))))

(ert-deftest list-utils-make-linear-inplace-08 nil
  "With 'tree"
  (let* ((value '(1 2 3 4 5))
         (cyclic value)
         (list-val (list 1 2 3 (list 4 (list 5 6 cyclic))))
         (list-copy (copy-tree list-val)))
    (nconc cyclic (cdr cyclic))
    (nconc list-val list-val)
    (should
     (equal list-copy
            (list-utils-make-linear-inplace list-val 'tree)))))

(ert-deftest list-utils-make-linear-inplace-09 nil
  "With 'tree. LIST argument is altered."
  (let* ((value '(1 2 3 4 5))
         (cyclic value)
         (list-val (list 'a 'b cyclic))
         (list-copy (copy-tree list-val)))
    (nconc cyclic (cdr cyclic))
    (should
     (equal list-copy
            (list-utils-make-linear-inplace list-val 'tree)))
    (should
     (equal list-copy list-val))))


;;; list-utils-safe-equal

(ert-deftest list-utils-safe-equal-01 nil
  "Simple list"
  (let* ((value '(1 2 3 4 5))
         (copy (copy-tree value)))
    (should
     (list-utils-safe-equal copy value))))

(ert-deftest list-utils-safe-equal-02 nil
  "Differ by length"
  (let* ((value '(1 2 3 4 5))
         (copy (copy-tree value)))
    (pop copy)
    (should-not
     (list-utils-safe-equal copy value))))

(ert-deftest list-utils-safe-equal-03 nil
  "nonstandard TEST"
  (let* ((value-1 '(1 2 3 4 5))
         (value-2 '(1.0 2.0 3.0 4.0 5.0)))
    (should-not
     (list-utils-safe-equal value-1 value-2))
    (should-not
     (list-utils-safe-equal value-1 value-2 '=))))

(ert-deftest list-utils-safe-equal-04 nil
  "Cyclic 1"
  (let* ((value '(1 2 3 4 5))
         (cyclic-1 (copy-tree value))
         (cyclic-2 (copy-tree value)))
    (nconc cyclic-1 cyclic-1)
    (nconc cyclic-2 cyclic-2)
    (should
     (list-utils-safe-equal cyclic-1 cyclic-2))
    ;; args remain unmodified
    (should-not
     (list-utils-safe-equal cyclic-1 value))
    (should-not
     (list-utils-safe-equal cyclic-2 value))))

(ert-deftest list-utils-safe-equal-05 nil
  "Cyclic 2"
  (let* ((value '(1 2 3 4 5))
         (cyclic-1 (copy-tree value))
         (cyclic-2 (copy-tree value)))
    (nconc cyclic-1 (cdr cyclic-1))
    (nconc cyclic-2 (cdr cyclic-2))
    (should
     (list-utils-safe-equal cyclic-1 cyclic-2))
    ;; args remain unmodified
    (should-not
     (list-utils-safe-equal cyclic-1 value))
    (should-not
     (list-utils-safe-equal cyclic-2 value))))

(ert-deftest list-utils-safe-equal-06 nil
  "Differ only by cyclic structure"
  (let* ((value '(1 2 3 4 5))
         (cyclic-1 (copy-tree value))
         (cyclic-2 (copy-tree value)))
    (nconc cyclic-1 cyclic-1)
    (nconc cyclic-2 (cdr cyclic-2))
    (should-not
     (list-utils-safe-equal cyclic-1 cyclic-2))
    ;; args remain unmodified
    (should-not
     (list-utils-safe-equal cyclic-1 value))
    (should-not
     (list-utils-safe-equal cyclic-2 value))))

(ert-deftest list-utils-safe-equal-07 nil
  "Tree with cycle"
  (let* ((value '(1 2 3 (4 (5 6))))
         (cyclic-1 (copy-tree value))
         (cyclic-2 (copy-tree value)))
    (nconc cyclic-1 (cdr cyclic-1))
    (nconc cyclic-2 (cdr cyclic-2))
    (should
     (list-utils-safe-equal cyclic-1 cyclic-2))
    ;; args remain unmodified
    (should-not
     (list-utils-safe-equal cyclic-1 value))
    (should-not
     (list-utils-safe-equal cyclic-2 value))))

(ert-deftest list-utils-safe-equal-08 nil
  "List containing other cycles"
  (let* ((value '(1 2 3 4 5))
         (cyclic-1 (copy-tree value))
         (cyclic-2 (copy-tree value))
         (list-1 (list 'a 'b cyclic-1))
         (list-2 (list 'a 'b cyclic-2)))
    (nconc cyclic-1 (cdr cyclic-1))
    (nconc cyclic-2 (cdr cyclic-2))
    (should
     (list-utils-safe-equal list-1 list-2))))

(ert-deftest list-utils-safe-equal-09 nil
  "Cyclic list of size one"
  (let* ((value '(1))
         (cyclic-1 (copy-tree value))
         (cyclic-2 (copy-tree value)))
    (nconc cyclic-1 cyclic-1)
    (nconc cyclic-2 cyclic-2)
    (should
     (list-utils-safe-equal cyclic-1 cyclic-2))
    (should-not
     (list-utils-safe-equal cyclic-1 value))
    (should-not
     (list-utils-safe-equal cyclic-2 value))))

(ert-deftest list-utils-safe-equal-10 nil
  "Improper list"
  (let* ((value (list* 1 2 3))
         (copy-1 (copy-tree value))
         (copy-2 (copy-tree value)))
    (should
     (list-utils-safe-equal copy-1 copy-2))
    (should
     (equal copy-1 value))))

(ert-deftest list-utils-safe-equal-11 nil
  "Improper list"
  (let* ((value-1 (list* 1 2 3))
         (value-2 (list* 1 2)))
    (should-not
     (list-utils-safe-equal value-1 value-2))))

(ert-deftest list-utils-safe-equal-12 nil
  "Improper list"
  (let* ((value-1 (list* 1 2 3))
         (value-2 (list* 1 2 4)))
    (should-not
     (list-utils-safe-equal value-1 value-2))))

(ert-deftest list-utils-safe-equal-13 nil
  "Non-list"
  (should
   (list-utils-safe-equal 1 1))
  (should
   (list-utils-safe-equal "1" "1"))
  (should-not
   (list-utils-safe-equal 1 "1")))

(ert-deftest list-utils-safe-equal-14 nil
  "mixed list"
  (should-not
   (list-utils-safe-equal 1 (list 1))))


;;; list-utils-flatten

(ert-deftest list-utils-flatten-01 nil
  (should (equal '(a b c d e f)
                 (list-utils-flatten '(a b c (d e (f)))))))

(ert-deftest list-utils-flatten-02 nil
  (should (equal '(a nil b nil c nil d nil e nil f nil nil nil)
                 (list-utils-flatten '(a nil b nil c nil (d nil e nil (f nil) nil) nil)))))

(ert-deftest list-utils-flatten-03 nil
  (should (equal '(1 2 3 4 5)
                 (list-utils-flatten '(1 2 3 4 . 5)))))

(ert-deftest list-utils-flatten-04 nil
  (should (equal '(1 2 3 4 5)
                 (list-utils-flatten '(1 2 3 (4 . 5))))))

(ert-deftest list-utils-flatten-05 nil
  (should (equal '(1 2 3 4 5)
                 (let ((cyclic '(1 2 3 (4 5))))
                   (nconc cyclic (cdr cyclic))
                   (list-utils-flatten cyclic)))))

(ert-deftest list-utils-flatten-06 nil
  (should (equal '(1 2)
   (list-utils-flatten (cons 1 2)))))

(ert-deftest list-utils-flatten-07 nil
  (let ((cyclic '(1)))
    (nconc cyclic cyclic)
    (should (equal '(1)
                   (list-utils-flatten cyclic)))))

(ert-deftest list-utils-flatten-08 nil
  "Don't modifiy LIST"
  (let ((cyclic-1 '(1 2 3 (4 5)))
        (cyclic-2 '(1 2 3 (4 5))))
    (nconc cyclic-1 (cdr cyclic-1))
    (nconc cyclic-2 (cdr cyclic-2))
    (should
     (equal '(1 2 3 4 5)
        (list-utils-flatten cyclic-1)))
    (should
     (equal (list-utils-linear-subseq cyclic-1)
            (list-utils-linear-subseq cyclic-2)))
    (should
     (equal
      (subseq (list-utils-cyclic-subseq cyclic-1) 0 (list-utils-safe-length (list-utils-cyclic-subseq cyclic-1)))
      (subseq (list-utils-cyclic-subseq cyclic-2) 0 (list-utils-safe-length (list-utils-cyclic-subseq cyclic-2)))))))


;;; list-utils-depth

(ert-deftest list-utils-depth-01 nil
  (should
   (= 0
      (list-utils-depth nil))))

(ert-deftest list-utils-depth-02 nil
  (should
   (= 0
      (list-utils-depth "not a list"))))

(ert-deftest list-utils-depth-03 nil
  (should
   (= 1
      (list-utils-depth '(1 2 3)))))

(ert-deftest list-utils-depth-04 nil
  (should
   (= 1
      (list-utils-depth (cons 1 2)))))

(ert-deftest list-utils-depth-05 nil
  (should
   (= 3
      (list-utils-depth '(a b c (d e (f)))))))

(ert-deftest list-utils-depth-06 nil
  (should
   (= 3
      (list-utils-depth '(a nil b nil c nil (d nil e nil (f nil) nil) nil)))))

(ert-deftest list-utils-depth-07 nil
  (should
   (= 1
      (list-utils-depth '(1 2 3 4 . 5)))))

(ert-deftest list-utils-depth-08 nil
  (should
   (= 2
      (list-utils-depth '(1 2 3 (4 . 5))))))

(ert-deftest list-utils-depth-09 nil
  (should
   (= 1
      (let ((cyclic '(1 2 3 4 5)))
        (nconc cyclic (cdr cyclic))
        (list-utils-depth cyclic)))))

(ert-deftest list-utils-depth-10 nil
  (should
   (= 2
      (let ((cyclic '(1 2 3 (4 5))))
        (nconc cyclic (cdr cyclic))
        (list-utils-depth cyclic)))))

(ert-deftest list-utils-depth-11 nil
  (let* ((value '(a nil (b . 1) nil (c 2 . 3) nil (d nil e nil (f nil) nil) nil))
         (copy (copy-tree value)))
    (list-utils-depth value)
    (should
     (equal value copy))))

(ert-deftest list-utils-depth-12 nil
  (let ((cyclic '(1)))
    (nconc cyclic cyclic)
    (should (= 1
               (list-utils-depth cyclic)))))

(ert-deftest list-utils-depth-13 nil
  "Don't modifiy LIST"
  (let ((cyclic-1 '(1 2 3 (4 5)))
        (cyclic-2 '(1 2 3 (4 5))))
    (nconc cyclic-1 (cdr cyclic-1))
    (nconc cyclic-2 (cdr cyclic-2))
    (should
     (= 2
        (list-utils-depth cyclic-1)))
    (should
     (equal (list-utils-linear-subseq cyclic-1)
            (list-utils-linear-subseq cyclic-2)))
    (should
     (equal
      (subseq (list-utils-cyclic-subseq cyclic-1) 0 (list-utils-safe-length (list-utils-cyclic-subseq cyclic-1)))
      (subseq (list-utils-cyclic-subseq cyclic-2) 0 (list-utils-safe-length (list-utils-cyclic-subseq cyclic-2)))))))


;;; list-utils-alist-or-flat-length

(ert-deftest list-utils-alist-or-flat-length-01 nil
  (let ((mixed '(1 2 3 nil 7 8 9 (4 . 0) 5 6 7 (8 9))))
    (should (= 11
               (list-utils-alist-or-flat-length mixed)))))


;;; list-utils-alist-flatten

(ert-deftest list-utils-alist-flatten-01 nil
  (should (equal '(1 2 3 4 . 5)
                 (list-utils-alist-flatten '(1 2 3 4 . 5)))))

(ert-deftest list-utils-alist-flatten-02 nil
  (should (equal '(1 2 3 (4 . 5))
                 (list-utils-alist-flatten '(1 2 3 (4 . 5))))))

(ert-deftest list-utils-alist-flatten-03 nil
  (should (equal '(1 2 3 (4 . 5))
                 (list-utils-alist-flatten '(1 (2 3) (4 . 5))))))

(ert-deftest list-utils-alist-flatten-04 nil
  (should (equal '((1 . 2) (3 . 4) (5 . 6) (7 . 8))
                 (list-utils-alist-flatten '(((1 . 2) (3 . 4)) ((5 . 6) (7 . 8)))))))

(ert-deftest list-utils-alist-flatten-05 nil
  (should (equal (cons 1 2)
                 (list-utils-alist-flatten (cons 1 2)))))

(ert-deftest list-utils-alist-flatten-06 nil
  "Don't modifiy LIST"
  (let ((cyclic-1 '(1 2 3 ((4 . 5) (6 . 7))))
        (cyclic-2 '(1 2 3 ((4 . 5) (6 . 7)))))
    (nconc cyclic-1 (cdr cyclic-1))
    (nconc cyclic-2 (cdr cyclic-2))
    (should
     (equal '(1 2 3 (4 . 5) (6 . 7))
        (list-utils-alist-flatten cyclic-1)))
    (should
     (equal (list-utils-linear-subseq cyclic-1)
            (list-utils-linear-subseq cyclic-2)))
    (should
     (equal
      (subseq (list-utils-cyclic-subseq cyclic-1) 0 (list-utils-safe-length (list-utils-cyclic-subseq cyclic-1)))
      (subseq (list-utils-cyclic-subseq cyclic-2) 0 (list-utils-safe-length (list-utils-cyclic-subseq cyclic-2)))))))


;;; list-utils-insert-before

(ert-deftest list-utils-insert-before-01 nil
  (should (equal '(1 2 3 four 4 5)
                 (list-utils-insert-before '(1 2 3 4 5) 4 'four))))

(ert-deftest list-utils-insert-before-02 nil
  (should (equal '(elt 1 2 3 4 5)
                 (list-utils-insert-before '(1 2 3 4 5) 1 'elt))))

(ert-deftest list-utils-insert-before-03 nil
  (should (equal '(1 2 3 4 elt 5)
                 (list-utils-insert-before '(1 2 3 4 5) 5 'elt))))

(ert-deftest list-utils-insert-before-04 nil
  (should-error
   (list-utils-insert-before '(1 2 3 4 5) 6 'elt)))

(ert-deftest list-utils-insert-before-05 nil
  (should (equal (list* 'elt 1 2)
             (list-utils-insert-before (cons 1 2) 1 'elt))))

(ert-deftest list-utils-insert-before-06 nil
  (should (equal (list* 1 'elt 2)
                 (list-utils-insert-before (cons 1 2) 2 'elt))))

(ert-deftest list-utils-insert-before-07 nil
  (should (equal (list* 1 'elt 2 3)
                 (list-utils-insert-before (list* 1 2 3) 2 'elt))))

(ert-deftest list-utils-insert-before-08 nil
  (should (equal (list* 1 2 'elt 3)
                 (list-utils-insert-before (list* 1 2 3) 3 'elt))))

(ert-deftest list-utils-insert-before-09 nil
  "set TEST"
  (should-error
   (list-utils-insert-before '(1 2.0 3 4 5) 2 'elt))
  (should
   (equal '(1 elt 2.0 3 4 5)
          (list-utils-insert-before '(1 2.0 3 4 5) 2 'elt '=))))


;;; list-utils-insert-after

(ert-deftest list-utils-insert-after-01 nil
  (should (equal '(1 2 3 4 four 5)
                 (list-utils-insert-after '(1 2 3 4 5) 4 'four))))

(ert-deftest list-utils-insert-after-02 nil
  (should (equal '(1 elt 2 3 4 5)
                 (list-utils-insert-after '(1 2 3 4 5) 1 'elt))))

(ert-deftest list-utils-insert-after-03 nil
  (should (equal '(1 2 3 4 5 elt)
                 (list-utils-insert-after '(1 2 3 4 5) 5 'elt))))

(ert-deftest list-utils-insert-after-04 nil
  (should-error
   (list-utils-insert-after '(1 2 3 4 5) 6 'elt)))

(ert-deftest list-utils-insert-after-05 nil
  (should (equal (list* 1 'elt 2)
                 (list-utils-insert-after (cons 1 2) 1 'elt))))

(ert-deftest list-utils-insert-after-06 nil
  (should (equal (list* 1 2 'elt)
                 (list-utils-insert-after (cons 1 2) 2 'elt))))

(ert-deftest list-utils-insert-after-07 nil
  (should (equal (list* 1 2 'elt 3)
                 (list-utils-insert-after (list* 1 2 3) 2 'elt))))

(ert-deftest list-utils-insert-after-08 nil
  (should (equal (list* 1 2 3 'elt)
                 (list-utils-insert-after (list* 1 2 3) 3 'elt))))

(ert-deftest list-utils-insert-after-09 nil
  "set TEST"
  (should-error
   (list-utils-insert-after '(1 2.0 3 4 5) 2 'elt))
  (should
   (equal '(1 2.0 elt 3 4 5)
          (list-utils-insert-after '(1 2.0 3 4 5) 2 'elt '=))))


;;; list-utils-insert-before-pos

(ert-deftest list-utils-insert-before-pos-01 nil
  (should (equal '(a b c three d e)
                 (list-utils-insert-before-pos '(a b c d e) 3 'three))))

(ert-deftest list-utils-insert-before-pos-02 nil
  (should (equal '(elt a b c d e)
                 (list-utils-insert-before-pos '(a b c d e) 0 'elt))))

(ert-deftest list-utils-insert-before-pos-03 nil
  (should (equal '(a b c d elt e)
                 (list-utils-insert-before-pos '(a b c d e) 4 'elt))))

(ert-deftest list-utils-insert-before-pos-04 nil
  (should-error
   (list-utils-insert-before-pos '(a b c d e) 5 'elt)))

(ert-deftest list-utils-insert-before-pos-05 nil
  (should (equal (list* 'elt 1 2)
                 (list-utils-insert-before-pos (cons 1 2) 0 'elt))))

(ert-deftest list-utils-insert-before-pos-06 nil
  (should (equal (list* 1 'elt 2)
                 (list-utils-insert-before-pos (cons 1 2) 1 'elt))))

(ert-deftest list-utils-insert-before-pos-07 nil
  (should-error
   (list-utils-insert-before-pos (cons 1 2) 2 'elt)))

(ert-deftest list-utils-insert-before-pos-08 nil
  (should (equal (list* 1 'elt 2 3)
                 (list-utils-insert-before-pos (list* 1 2 3) 1 'elt))))

(ert-deftest list-utils-insert-before-pos-09 nil
  (should (equal (list* 1 2 'elt 3)
                 (list-utils-insert-before-pos (list* 1 2 3) 2 'elt))))

(ert-deftest list-utils-insert-before-pos-10 nil
  (should-error
   (list-utils-insert-before-pos (list* 1 2 3) 3 'elt)))


;;; list-utils-insert-after-pos

(ert-deftest list-utils-insert-after-pos-01 nil
  (should (equal '(a b c d three e)
                 (list-utils-insert-after-pos '(a b c d e) 3 'three))))

(ert-deftest list-utils-insert-after-pos-02 nil
  (should (equal '(a elt b c d e)
                 (list-utils-insert-after-pos '(a b c d e) 0 'elt))))

(ert-deftest list-utils-insert-after-pos-03 nil
  (should (equal '(a b c d e elt)
                 (list-utils-insert-after-pos '(a b c d e) 4 'elt))))

(ert-deftest list-utils-insert-after-pos-04 nil
  (should-error
   (list-utils-insert-after-pos '(a b c d e) 5 'elt)))

(ert-deftest list-utils-insert-after-pos-05 nil
  (should (equal (list* 1 'elt 2)
                 (list-utils-insert-after-pos (cons 1 2) 0 'elt))))

(ert-deftest list-utils-insert-after-pos-06 nil
  (should (equal (list* 1 2 'elt)
                 (list-utils-insert-after-pos (cons 1 2) 1 'elt))))

(ert-deftest list-utils-insert-after-pos-07 nil
  (should-error
   (list-utils-insert-after-pos (cons 1 2) 2 'elt)))

(ert-deftest list-utils-insert-after-pos-08 nil
  (should (equal (list* 1 2 'elt 3)
                 (list-utils-insert-after-pos (list* 1 2 3) 1 'elt))))

(ert-deftest list-utils-insert-after-pos-09 nil
  (should (equal (list* 1 2 3 'elt)
                 (list-utils-insert-after-pos (list* 1 2 3) 2 'elt))))

(ert-deftest list-utils-insert-after-pos-10 nil
  (should-error
   (list-utils-insert-after-pos (list* 1 2 3) 3 'elt)))


;;; list-utils-and

(ert-deftest list-utils-and-01 nil
  "Logical AND operation on two lists"
  (let ((list-1 '(A a a 8 8 1 2 3 3 3 4.0 5 6 7 9 9 5))
        (list-2 '(a b c d 1 2 3 4)))
    (should (equal '(a a 1 2 3 3 3)
                   (list-utils-and list-1 list-2)))))

(ert-deftest list-utils-and-02 nil
  "Logical AND operation with size hint, should be identical"
  (let ((list-1 '(A a a 8 8 1 2 3 3 3 4.0 5 6 7 9 9 5))
        (list-2 '(a b c d 1 2 3 4)))
    (should (equal (list-utils-and list-1 list-2)
                   (list-utils-and list-1 list-2 nil 17)))))

(ert-deftest list-utils-and-03 nil
  "Logical AND operation with FLIP param"
  (let ((list-1 '(A a a 8 8 1 2 3 3 3 4.0 5 6 7 9 9 5))
        (list-2 '(a b c d 1 2 3 4)))
    (should (equal '(a 1 2 3)
                   (list-utils-and list-1 list-2 nil nil 'flip)))))

(ert-deftest list-utils-and-04 nil
  "Logical AND operation with FLIP param should be the same as reversing order of list args"
  (let ((list-1 '(A a a 8 8 1 2 3 3 3 4.0 5 6 7 9 9 5))
        (list-2 '(a b c d 1 2 3 4)))
    (should (equal (list-utils-and list-2 list-1)
                   (list-utils-and list-1 list-2 nil nil 'flip)))))

(ert-deftest list-utils-and-05 nil
  "Logical AND operation with numeric hash-table-test"
  (let ((list-1 '(A a a 8 8 1 2 3 3 3 4.0 5 6 7 9 9 5))
        (list-2 '(a b c d 1 2 3 4)))
    (should (equal '(a a 1 2 3 3 3 4.0)
                   (list-utils-and list-1 list-2 'list-utils-htt-=)))))

(ert-deftest list-utils-and-06 nil
  "Logical AND operation with numeric hash-table-test and FLIP param"
  (let ((list-1 '(A a a 8 8 1 2 3 3 3 4.0 5 6 7 9 9 5))
        (list-2 '(a b c d 1 2 3 4)))
    (should (equal '(a 1 2 3 4)
                   (list-utils-and list-1 list-2 'list-utils-htt-= nil 'flip)))))

(ert-deftest list-utils-and-07 nil
  "Logical AND operation with case-insensitive hash-table-test"
  (let ((list-1 '(A a a 8 8 1 2 3 3 3 4.0 5 6 7 9 9 5))
        (list-2 '(a b c d 1 2 3 4)))
    (should (equal '(A a a 1 2 3 3 3)
                   (list-utils-and list-1 list-2 'list-utils-htt-case-fold-equal)))))

(ert-deftest list-utils-and-08 nil
  "Logical AND operation with case-insensitive hash-table-test and FLIP param"
  (let ((list-1 '(A 8 8 1 2 3 3 3 4.0 5 6 7 9 9 5)) ; note different list-1
        (list-2 '(a b c d 1 2 3 4)))
    (should (equal '(a 1 2 3)                       ; element a is still present
                   (list-utils-and list-1 list-2 'list-utils-htt-case-fold-equal nil 'flip)))))

(ert-deftest list-utils-and-09 nil
  "Logical AND operation should be identical to `cl-intersection' after sort/uniq"
  (let ((list-1 '(A a a 8 8 1 2 3 3 3 4.0 5 6 7 9 9 5))
        (list-2 '(a b c d 1 2 3 4)))
    (should (equal (sort (list-utils-uniq (cl-intersection list-1 list-2)) 'list-utils-test-soft-string-lessp)
                   (sort (list-utils-uniq (list-utils-and list-1 list-2)) 'list-utils-test-soft-string-lessp)))))

(ert-deftest list-utils-and-10 nil
  "Logical AND operation with two large lists"
  (let ((list-1          (number-sequence 1 10000))
        (list-2 (reverse (number-sequence 4 10009))))
    (should (equal (number-sequence 4 10000)
                   (list-utils-and list-1 list-2)))))

(ert-deftest list-utils-and-11 nil
  "Logical AND operation with large lists and size hint, should be identical"
  (let ((list-1          (number-sequence 1 10000))
        (list-2 (reverse (number-sequence 4 10009))))
    (should (equal (list-utils-and list-1 list-2)
                   (list-utils-and list-1 list-2 nil 10000)))))

(ert-deftest list-utils-and-12 nil
  "Logical AND operation with large lists and FLIP param"
  (let ((list-1          (number-sequence 1 10000))
        (list-2 (reverse (number-sequence 4 10009))))
    (should (equal (reverse (number-sequence 4 10000))
                   (list-utils-and list-1 list-2 nil nil 'flip)))))

(ert-deftest list-utils-and-13 nil
  "Logical AND operation with large lists and FLIP param should be the same as reversing order of list args"
  (let ((list-1          (number-sequence 1 10000))
        (list-2 (reverse (number-sequence 4 10009))))
    (should (equal (list-utils-and list-2 list-1)
                   (list-utils-and list-1 list-2 nil nil 'flip)))))

(ert-deftest list-utils-and-14 nil
  "Logical AND operation with large lists and numeric hash-table-test"
  (let ((list-1                         (number-sequence 1 10000))
        (list-2 (reverse (mapcar 'float (number-sequence 4 10009)))))
    (should (equal (number-sequence 4 10000)
                   (list-utils-and list-1 list-2 'list-utils-htt-=)))))

(ert-deftest list-utils-and-15 nil
  "Logical AND operation with large lists and case-insensitive hash-table-test"
  (let ((list-1 (mapcar #'(lambda (x) (char-to-string (decode-char 'ucs x)))          (number-sequence 1 10000)))
        (list-2 (mapcar #'(lambda (x) (char-to-string (decode-char 'ucs x))) (reverse (number-sequence 4 10009)))))
    (should (equal (mapcar #'(lambda (x) (char-to-string (decode-char 'ucs x))) (number-sequence 4 10000))
                   (list-utils-and list-1 list-2 'list-utils-htt-case-fold-equal)))))

(ert-deftest list-utils-and-16 nil
  "Logical AND operation with large lists should be identical to `cl-intersection' after sort/uniq"
  (let ((list-1          (number-sequence 1 10000))
        (list-2 (reverse (number-sequence 4 10009))))
    (should (equal (sort (list-utils-uniq (cl-intersection list-1 list-2)) 'list-utils-test-soft-string-lessp)
                   (sort (list-utils-uniq (list-utils-and list-1 list-2)) 'list-utils-test-soft-string-lessp)))))


;;; list-utils-not

(ert-deftest list-utils-not-01 nil
  "Logical NOT operation on two lists"
  (let ((list-1 '(A a a 8 8 1 2 3 3 3 4.0 5 6 7 9 9 5))
        (list-2 '(a b c d 1 2 3 4)))
    (should (equal '(A 8 8 4.0 5 6 7 9 9 5)
                   (list-utils-not list-1 list-2)))))

(ert-deftest list-utils-not-02 nil
  "Logical NOT operation with size hint, should be identical"
  (let ((list-1 '(A a a 8 8 1 2 3 3 3 4.0 5 6 7 9 9 5))
        (list-2 '(a b c d 1 2 3 4)))
    (should (equal (list-utils-not list-1 list-2)
                   (list-utils-not list-1 list-2 nil 17)))))

(ert-deftest list-utils-not-03 nil
  "Logical NOT operation with FLIP param"
  (let ((list-1 '(A a a 8 8 1 2 3 3 3 4.0 5 6 7 9 9 5))
        (list-2 '(a b c d 1 2 3 4)))
    (should (equal '(b c d 4)
                   (list-utils-not list-1 list-2 nil nil 'flip)))))

(ert-deftest list-utils-not-04 nil
  "Logical NOT operation with FLIP param should be the same as reversing order of list args"
  (let ((list-1 '(A a a 8 8 1 2 3 3 3 4.0 5 6 7 9 9 5))
        (list-2 '(a b c d 1 2 3 4)))
    (should (equal (list-utils-not list-2 list-1)
                   (list-utils-not list-1 list-2 nil nil 'flip)))))

(ert-deftest list-utils-not-05 nil
  "Logical NOT operation with numeric hash-table-test"
  (let ((list-1 '(A a a 8 8 1 2 3 3 3 4.0 5 6 7 9 9 5))
        (list-2 '(a b c d 1 2 3 4)))
    (should (equal '(A 8 8 5 6 7 9 9 5) ; no element 4.0
                   (list-utils-not list-1 list-2 'list-utils-htt-=)))))

(ert-deftest list-utils-not-06 nil
  "Logical NOT operation with numeric hash-table-test and FLIP param"
  (let ((list-1 '(A a a 8 8 1 2 3 3 3 4.0 5 6 7 9 9 5))
        (list-2 '(a b c d 1 2 3 4)))
    (should (equal '(b c d) ; no element 4
                   (list-utils-not list-1 list-2 'list-utils-htt-= nil 'flip)))))

(ert-deftest list-utils-not-07 nil
  "Logical NOT operation with case-insensitive hash-table-test"
  (let ((list-1 '(A a a 8 8 1 2 3 3 3 4.0 5 6 7 9 9 5))
        (list-2 '(a b c d 1 2 3 4)))
    (should (equal '(8 8 4.0 5 6 7 9 9 5) ; no element A
                   (list-utils-not list-1 list-2 'list-utils-htt-case-fold-equal)))))

(ert-deftest list-utils-not-08 nil
  "Logical NOT operation with case-insensitive hash-table-test and FLIP param"
  (let ((list-1 '(A a a 8 8 1 2 3 3 3 4.0 5 6 7 9 9 5))
        (list-2 '(a b c d 1 2 3 4)))
    (should (equal '(b c d 4)
                   (list-utils-not list-1 list-2 'list-utils-htt-case-fold-equal nil 'flip)))))

(ert-deftest list-utils-not-09 nil
  "Logical NOT operation should be identical to `cl-set-difference' after sort/uniq"
  (let ((list-1 '(A a a 8 8 1 2 3 3 3 4.0 5 6 7 9 9 5))
        (list-2 '(a b c d 1 2 3 4)))
    (should (equal (sort (list-utils-uniq (cl-set-difference list-1 list-2)) 'list-utils-test-soft-string-lessp)
                   (sort (list-utils-uniq (list-utils-not list-1 list-2)) 'list-utils-test-soft-string-lessp)))))

(ert-deftest list-utils-not-10 nil
  "Logical NOT operation with two large lists"
  (let ((list-1          (number-sequence 1 10000))
        (list-2 (reverse (number-sequence 4 10009))))
    (should (equal (number-sequence 1 3)
                   (list-utils-not list-1 list-2)))))

(ert-deftest list-utils-not-11 nil
  "Logical NOT operation with large lists and size hint, should be identical"
  (let ((list-1          (number-sequence 1 10000))
        (list-2 (reverse (number-sequence 4 10009))))
    (should (equal (list-utils-not list-1 list-2)
                   (list-utils-not list-1 list-2 nil 10000)))))

(ert-deftest list-utils-not-12 nil
  "Logical NOT operation with large lists and FLIP param"
  (let ((list-1          (number-sequence 1 10000))
        (list-2 (reverse (number-sequence 4 10009))))
    (should (equal (reverse (number-sequence 10001 10009))
                   (list-utils-not list-1 list-2 nil nil 'flip)))))

(ert-deftest list-utils-not-13 nil
  "Logical NOT operation with large lists and FLIP param should be the same as reversing order of list args"
  (let ((list-1          (number-sequence 1 10000))
        (list-2 (reverse (number-sequence 4 10009))))
    (should (equal (list-utils-not list-2 list-1)
                   (list-utils-not list-1 list-2 nil nil 'flip)))))

(ert-deftest list-utils-not-14 nil
  "Logical NOT operation with large lists and numeric hash-table-test"
  (let ((list-1                         (number-sequence 1 10000))
        (list-2 (mapcar 'float (reverse (number-sequence 4 10009)))))
    (should (equal (number-sequence 1 3)
                   (list-utils-not list-1 list-2 'list-utils-htt-=)))))

(ert-deftest list-utils-not-15 nil
  "Logical NOT operation with large lists and case-insensitive hash-table-test"
  (let ((list-1 (mapcar #'(lambda (x) (char-to-string (decode-char 'ucs x)))          (number-sequence 1 10000)))
        (list-2 (mapcar #'(lambda (x) (char-to-string (decode-char 'ucs x))) (reverse (number-sequence 4 10009)))))
    (should (equal (mapcar #'(lambda (x) (char-to-string (decode-char 'ucs x))) (number-sequence 1 3))
                   (list-utils-not list-1 list-2 'list-utils-htt-case-fold-equal)))))

(ert-deftest list-utils-not-16 nil
  "Logical NOT operation with large lists should be identical to `cl-set-difference' after sort/uniq"
  (let ((list-1          (number-sequence 1 10000))
        (list-2 (reverse (number-sequence 4 10009))))
    (should (equal (sort (list-utils-uniq (cl-set-difference list-1 list-2)) 'list-utils-test-soft-string-lessp)
                   (sort (list-utils-uniq (list-utils-not list-1 list-2)) 'list-utils-test-soft-string-lessp)))))


;;; list-utils-xor

(ert-deftest list-utils-xor-01 nil
  "Logical XOR operation on two lists"
  (let ((list-1 '(A a a 8 8 1 2 3 3 3 4.0 5 6 7 9 9 5))
        (list-2 '(a b c d 1 2 3 4)))
    (should (equal '(A 8 8 4.0 5 6 7 9 9 5 b c d 4)
                   (list-utils-xor list-1 list-2)))))

(ert-deftest list-utils-xor-02 nil
  "Logical XOR operation with size hint, should be identical"
  (let ((list-1 '(A a a 8 8 1 2 3 3 3 4.0 5 6 7 9 9 5))
        (list-2 '(a b c d 1 2 3 4)))
    (should (equal (list-utils-xor list-1 list-2)
                   (list-utils-xor list-1 list-2 nil 17)))))

(ert-deftest list-utils-xor-03 nil
  "Logical XOR operation with FLIP param"
  (let ((list-1 '(A a a 8 8 1 2 3 3 3 4.0 5 6 7 9 9 5))
        (list-2 '(a b c d 1 2 3 4)))
    (should (equal '(b c d 4 A 8 8 4.0 5 6 7 9 9 5)
                   (list-utils-xor list-1 list-2 nil nil 'flip)))))

(ert-deftest list-utils-xor-04 nil
  "Logical XOR operation with FLIP param should be the same as reversing order of list args"
  (let ((list-1 '(A a a 8 8 1 2 3 3 3 4.0 5 6 7 9 9 5))
        (list-2 '(a b c d 1 2 3 4)))
    (should (equal (list-utils-xor list-2 list-1)
                   (list-utils-xor list-1 list-2 nil nil 'flip)))))

(ert-deftest list-utils-xor-05 nil
  "Logical XOR operation with numeric hash-table-test"
  (let ((list-1 '(A a a 8 8 1 2 3 3 3 4.0 5 6 7 9 9 5))
        (list-2 '(a b c d 1 2 3 4)))
    (should (equal '(A 8 8 5 6 7 9 9 5 b c d) ; no element 4
                   (list-utils-xor list-1 list-2 'list-utils-htt-=)))))

(ert-deftest list-utils-xor-06 nil
  "Logical XOR operation with numeric hash-table-test and FLIP param"
  (let ((list-1 '(A a a 8 8 1 2 3 3 3 4.0 5 6 7 9 9 5))
        (list-2 '(a b c d 1 2 3 4)))
    (should (equal '(b c d A 8 8 5 6 7 9 9 5) ; no element 4
                   (list-utils-xor list-1 list-2 'list-utils-htt-= nil 'flip)))))

(ert-deftest list-utils-xor-07 nil
  "Logical XOR operation with case-insensitive hash-table-test"
  (let ((list-1 '(A a a 8 8 1 2 3 3 3 4.0 5 6 7 9 9 5))
        (list-2 '(a b c d 1 2 3 4)))
    (should (equal '(8 8 4.0 5 6 7 9 9 5 b c d 4)
                   (list-utils-xor list-1 list-2 'list-utils-htt-case-fold-equal)))))

(ert-deftest list-utils-xor-08 nil
  "Logical XOR operation with case-insensitive hash-table-test and FLIP param"
  (let ((list-1 '(A a a 8 8 1 2 3 3 3 4.0 5 6 7 9 9 5))
        (list-2 '(a b c d 1 2 3 4)))
    (should (equal '(b c d 4 8 8 4.0 5 6 7 9 9 5)
                   (list-utils-xor list-1 list-2 'list-utils-htt-case-fold-equal nil 'flip)))))

(ert-deftest list-utils-xor-09 nil
  "Logical XOR operation should be identical to `cl-set-exclusive-or' after sort/uniq"
  (let ((list-1 '(A a a 8 8 1 2 3 3 3 4.0 5 6 7 9 9 5))
        (list-2 '(a b c d 1 2 3 4)))
    (should (equal (sort (list-utils-uniq (cl-set-exclusive-or list-1 list-2)) 'list-utils-test-soft-string-lessp)
                   (sort (list-utils-uniq (list-utils-xor list-1 list-2)) 'list-utils-test-soft-string-lessp)))))

(ert-deftest list-utils-xor-10 nil
  "Logical XOR operation should be identical to itself with FLIP param after sort/uniq"
  (let ((list-1 '(A a a 8 8 1 2 3 3 3 4.0 5 6 7 9 9 5))
        (list-2 '(a b c d 1 2 3 4)))
    (should (equal (sort (list-utils-uniq (list-utils-xor list-2 list-1)) 'list-utils-test-soft-string-lessp)
                   (sort (list-utils-uniq (list-utils-xor list-1 list-2)) 'list-utils-test-soft-string-lessp)))))

(ert-deftest list-utils-xor-11 nil
  "Logical XOR operation with two large lists"
  (let ((list-1          (number-sequence 1 10000))
        (list-2 (reverse (number-sequence 4 10009))))
    (should (equal (append (number-sequence 1 3) (reverse (number-sequence 10001 10009)))
                   (list-utils-xor list-1 list-2)))))

(ert-deftest list-utils-xor-12 nil
  "Logical XOR operation with large lists and size hint, should be identical"
  (let ((list-1          (number-sequence 1 10000))
        (list-2 (reverse (number-sequence 4 10009))))
    (should (equal (list-utils-xor list-1 list-2)
                   (list-utils-xor list-1 list-2 nil 10000)))))

(ert-deftest list-utils-xor-13 nil
  "Logical XOR operation with large lists and FLIP param"
  (let ((list-1          (number-sequence 1 10000))
        (list-2 (reverse (number-sequence 4 10009))))
    (should (equal (append (reverse (number-sequence 10001 10009)) (number-sequence 1 3))
                   (list-utils-xor list-1 list-2 nil nil 'flip)))))

(ert-deftest list-utils-xor-14 nil
  "Logical XOR operation with large lists and FLIP param should be the same as reversing order of list args"
  (let ((list-1          (number-sequence 1 10000))
        (list-2 (reverse (number-sequence 4 10009))))
    (should (equal (list-utils-xor list-2 list-1)
                   (list-utils-xor list-1 list-2 nil nil 'flip)))))

(ert-deftest list-utils-xor-15 nil
  "Logical XOR operation with large lists and numeric hash-table-test"
  (let ((list-1                         (number-sequence 1 10000))
        (list-2 (mapcar 'float (reverse (number-sequence 4 10009)))))
    (should (equal (append (number-sequence 1 3) (mapcar 'float (reverse (number-sequence 10001 10009))))
                   (list-utils-xor list-1 list-2 'list-utils-htt-=)))))

;; todo: use characters relevant to case-insensitivity
(ert-deftest list-utils-xor-16 nil
  "Logical XOR operation with large lists and case-insensitive hash-table-test"
  (let ((list-1 (mapcar #'(lambda (x) (char-to-string (decode-char 'ucs x)))          (number-sequence 1 10000)))
        (list-2 (mapcar #'(lambda (x) (char-to-string (decode-char 'ucs x))) (reverse (number-sequence 4 10009)))))
    (should (equal (mapcar #'(lambda (x) (char-to-string (decode-char 'ucs x))) (append (number-sequence 1 3) (reverse (number-sequence 10001 10009))))
                   (list-utils-xor list-1 list-2 'list-utils-htt-case-fold-equal)))))

(ert-deftest list-utils-xor-17 nil
  "Logical XOR operation with large lists should be identical to `cl-set-exclusive-or' after sort/uniq"
  (let ((list-1          (number-sequence 1 10000))
        (list-2 (reverse (number-sequence 4 10009))))
    (should (equal (sort (list-utils-uniq (cl-set-exclusive-or list-1 list-2)) 'list-utils-test-soft-string-lessp)
                   (sort (list-utils-uniq (list-utils-xor list-1 list-2)) 'list-utils-test-soft-string-lessp)))))

(ert-deftest list-utils-xor-18 nil
  "Logical XOR operation with large lists should be identical to reverse-XOR-operation after sort/uniq"
  (let ((list-1          (number-sequence 1 10000))
        (list-2 (reverse (number-sequence 4 10009))))
    (should (equal (sort (list-utils-uniq (list-utils-xor list-2 list-1)) 'list-utils-test-soft-string-lessp)
                   (sort (list-utils-uniq (list-utils-xor list-1 list-2)) 'list-utils-test-soft-string-lessp)))))


;;; list-utils-uniq

(ert-deftest list-utils-uniq-01 nil
  "UNIQ operation on a list"
  (let ((list '(A a a 8 8 1 2 4 3 3 3 4.0 5 6 7 9 9 5)))
    (should (equal '(A a 8 1 2 4 3 4.0 5 6 7 9)
                   (list-utils-uniq list)))))

(ert-deftest list-utils-uniq-02 nil
  "UNIQ operation with size hint, should be identical"
  (let ((list '(A a a 8 8 1 2 4 3 3 3 4.0 5 6 7 9 9 5)))
    (should (equal (list-utils-uniq list)
                   (list-utils-uniq list nil 17)))))

(ert-deftest list-utils-uniq-03 nil
  "UNIQ operation with numeric hash-table-test"
  (let ((list '(A a a 8 8 1 2 4 3 3 3 4.0 5 6 7 9 9 5)))
    (should (equal '(A a 8 1 2 4 3 5 6 7 9) ; no element 4.0
                   (list-utils-uniq list 'list-utils-htt-=)))))

(ert-deftest list-utils-uniq-04 nil
  "UNIQ operation with case-insensitive hash-table-test"
  (let ((list '(A a a 8 8 1 2 4 3 3 3 4.0 5 6 7 9 9 5)))
    (should (equal '(A 8 1 2 4 3 4.0 5 6 7 9) ; no element a
                   (list-utils-uniq list 'list-utils-htt-case-fold-equal)))))

(ert-deftest list-utils-uniq-05 nil
  "UNIQ operation should be identical to `remove-duplicates' after sort"
  (let ((list '(A a a 8 8 1 2 4 3 3 3 4.0 5 6 7 9 9 5)))
    (should (equal (sort (remove-duplicates list) 'list-utils-test-soft-string-lessp)
                   (sort (list-utils-uniq list) 'list-utils-test-soft-string-lessp)))))

(ert-deftest list-utils-uniq-06 nil
  "UNIQ operation with a large list"
  (let ((list (append (number-sequence 1 10000) (reverse (number-sequence 4 10009)))))
    (should (equal (append (number-sequence 1 10000) (reverse (number-sequence 10001 10009)))
                   (list-utils-uniq list)))))

(ert-deftest list-utils-uniq-07 nil
  "UNIQ operation with large list and size hint, should be identical"
  (let ((list (append (number-sequence 1 10000) (reverse (number-sequence 4 10009)))))
    (should (equal (list-utils-uniq list)
                   (list-utils-uniq list nil 10000)))))

(ert-deftest list-utils-uniq-08 nil
  "UNIQ operation with large list and numeric hash-table-test"
  (let ((list (append (number-sequence 1 10000) (mapcar 'float (reverse (number-sequence 4 10009))))))
    (should (equal (append (number-sequence 1 10000) (mapcar 'float (reverse (number-sequence 10001 10009))))
                   (list-utils-uniq list 'list-utils-htt-=)))))

;; @@@ Todo: figure out what is really the expected result, when casefolding
;;     across so many characters/languages.  That's a complex task, but can
;;     be defined against the results of some other runtime.  The result from
;;     Emacs is only 1674 chars, which seems quite low.  In any case, no
;;     case-folding was applied against the test target set, so in principle
;;     this should not be expected to pass.
(ert-deftest list-utils-uniq-09 nil
  "UNIQ operation with large list and case-insensitive hash-table-test"
  :expected-result :failed
  (let ((list (mapcar #'(lambda (x) (char-to-string (decode-char 'ucs x))) (append (number-sequence 1 10000) (reverse (number-sequence 4 10009))))))
    (should (equal (mapcar #'(lambda (x) (char-to-string (decode-char 'ucs x))) (append (number-sequence 1 10000) (reverse (number-sequence 10001 10009))))
                   (list-utils-uniq list 'list-utils-htt-case-fold-equal)))))

(ert-deftest list-utils-uniq-10 nil
  "UNIQ operation with large list should be identical to `remove-duplicates' after sort"
  (let ((list (append (number-sequence 1 10000) (reverse (number-sequence 4 10009)))))
    (should (equal (sort (remove-duplicates list) 'list-utils-test-soft-string-lessp)
                   (sort (list-utils-uniq list) 'list-utils-test-soft-string-lessp)))))


;;; list-utils-dupes

(ert-deftest list-utils-dupes-01 nil
  "DUPES operation on a list"
  (let ((list '(A a a 8 8 1 2 4 3 3 3 4.0 5 6 7 9 9 5)))
    (should (equal '(a a 8 8 3 3 3 5 9 9 5)
                   (list-utils-dupes list)))))

(ert-deftest list-utils-dupes-02 nil
  "DUPES operation with size hint, should be identical"
  (let ((list '(A a a 8 8 1 2 4 3 3 3 4.0 5 6 7 9 9 5)))
    (should (equal (list-utils-dupes list)
                   (list-utils-dupes list nil 17)))))

(ert-deftest list-utils-dupes-03 nil
  "DUPES operation with numeric hash-table-test"
  (let ((list '(A a a 8 8 1 2 4 3 3 3 4.0 5 6 7 9 9 5)))
    (should (equal '(a a 8 8 4 3 3 3 4.0 5 9 9 5) ; elements 4 / 4.0 present
                   (list-utils-dupes list 'list-utils-htt-=)))))

(ert-deftest list-utils-dupes-04 nil
  "DUPES operation with case-insensitive hash-table-test"
  (let ((list '(A a a 8 8 1 2 4 3 3 3 4.0 5 6 7 9 9 5)))
    (should (equal '(A a a 8 8 3 3 3 5 9 9 5)     ; element A present
                   (list-utils-dupes list 'list-utils-htt-case-fold-equal)))))

(ert-deftest list-utils-dupes-05 nil
  "DUPES operation should be identical to result composed of other list operations"
  (let ((list '(A a a 8 8 1 2 4 3 3 3 4.0 5 6 7 9 9 5)))
    (should (equal (list-utils-and list
                                   (list-utils-singlets
                                    (append (list-utils-singlets list)
                                            (remove-duplicates list))))
                   (list-utils-dupes list)))))

(ert-deftest list-utils-dupes-06 nil
  "DUPES operation with a large list"
  (let ((list (append (number-sequence 1 10000) (reverse (number-sequence 4 10009)))))
    (should (equal (append (number-sequence 4 10000) (reverse (number-sequence 4 10000)))
                   (list-utils-dupes list)))))

(ert-deftest list-utils-dupes-07 nil
  "DUPES operation with large list and size hint, should be identical"
  (let ((list (append (number-sequence 1 10000) (reverse (number-sequence 4 10009)))))
    (should (equal (list-utils-dupes list)
                   (list-utils-dupes list nil 10000)))))

(ert-deftest list-utils-dupes-08 nil
  "DUPES operation with large list and numeric hash-table-test"
  (let ((list (append (number-sequence 1 10000) (mapcar 'float (reverse (number-sequence 4 10009))))))
    (should (equal (append (number-sequence 4 10000) (mapcar 'float (reverse (number-sequence 4 10000))))
                   (list-utils-dupes list 'list-utils-htt-=)))))

;; todo: use characters relevant to case-insensitivity
(ert-deftest list-utils-dupes-09 nil
  "DUPES operation with large list and case-insensitive hash-table-test"
  (let ((list (mapcar #'(lambda (x) (char-to-string (decode-char 'ucs x))) (append (number-sequence 1 10000) (reverse (number-sequence 4 10009))))))
    (should (equal (mapcar #'(lambda (x) (char-to-string (decode-char 'ucs x))) (append (number-sequence 4 10000) (reverse (number-sequence 4 10000))))
                   (list-utils-dupes list 'list-utils-htt-case-fold-equal)))))

(ert-deftest list-utils-dupes-10 nil
  "DUPES operation with large list should be identical to result composed of other list operations"
  (let ((list (append (number-sequence 1 10000) (reverse (number-sequence 4 10009)))))
    (should (equal (list-utils-and list
                                   (list-utils-singlets
                                    (append (list-utils-singlets list)
                                            (remove-duplicates list))))
                   (list-utils-dupes list)))))


;;; list-utils-singlets

(ert-deftest list-utils-singlets-01 nil
  "SINGLETS operation on a list"
  (let ((list '(A a a 8 8 1 2 4 3 3 3 4.0 5 6 7 9 9 5)))
    (should (equal '(A 1 2 4 4.0 6 7)
                   (list-utils-singlets list)))))

(ert-deftest list-utils-singlets-02 nil
  "SINGLETS operation with size hint, should be identical"
  (let ((list '(A a a 8 8 1 2 4 3 3 3 4.0 5 6 7 9 9 5)))
    (should (equal (list-utils-singlets list)
                   (list-utils-singlets list nil 17)))))

(ert-deftest list-utils-singlets-03 nil
  "SINGLETS operation with numeric hash-table-test"
  (let ((list '(A a a 8 8 1 2 4 3 3 3 4.0 5 6 7 9 9 5)))
    (should (equal '(A 1 2 6 7) ; no elements 4 4.0
                   (list-utils-singlets list 'list-utils-htt-=)))))

(ert-deftest list-utils-singlets-04 nil
  "SINGLETS operation with case-insensitive hash-table-test"
  (let ((list '(A a a 8 8 1 2 4 3 3 3 4.0 5 6 7 9 9 5)))
    (should (equal '(1 2 4 4.0 6 7) ; no elements A a
                   (list-utils-singlets list 'list-utils-htt-case-fold-equal)))))

(ert-deftest list-utils-singlets-05 nil
  "SINGLETS operation should be identical to result composed of other list operations"
  (let ((list '(A a a 8 8 1 2 4 3 3 3 4.0 5 6 7 9 9 5)))
    (should (equal (list-utils-not list (list-utils-dupes list))
                   (list-utils-singlets list)))))

(ert-deftest list-utils-singlets-06 nil
  "SINGLETS operation with a large list"
  (let ((list (append (number-sequence 1 10000) (reverse (number-sequence 4 10009)))))
    (should (equal (append (number-sequence 1 3) (reverse (number-sequence 10001 10009)))
                   (list-utils-singlets list)))))

(ert-deftest list-utils-singlets-07 nil
  "SINGLETS operation with large list and size hint, should be identical"
  (let ((list (append (number-sequence 1 10000) (reverse (number-sequence 4 10009)))))
    (should (equal (list-utils-singlets list)
                   (list-utils-singlets list nil 10000)))))

(ert-deftest list-utils-singlets-08 nil
  "SINGLETS operation with large list and numeric hash-table-test"
  (let ((list (append (number-sequence 1 10000) (mapcar 'float (reverse (number-sequence 4 10009))))))
    (should (equal (append (number-sequence 1 3) (mapcar 'float (reverse (number-sequence 10001 10009))))
                   (list-utils-singlets list 'list-utils-htt-=)))))

;; todo: use characters relevant to case-insensitivity
(ert-deftest list-utils-singlets-09 nil
  "SINGLETS operation with large list and case-insensitive hash-table-test"
  (let ((list (mapcar #'(lambda (x) (char-to-string (decode-char 'ucs x))) (append (number-sequence 1 10000) (reverse (number-sequence 4 10009))))))
    (should (equal (mapcar #'(lambda (x) (char-to-string (decode-char 'ucs x))) (append (number-sequence 1 3) (reverse (number-sequence 10001 10009))))
                   (list-utils-singlets list 'list-utils-htt-case-fold-equal)))))

(ert-deftest list-utils-singlets-10 nil
  "SINGLETS operation with large list should be identical to result composed of other list operations"
  (let ((list (append (number-sequence 1 10000) (reverse (number-sequence 4 10009)))))
    (should (equal (list-utils-not list (list-utils-dupes list))
                   (list-utils-singlets list)))))


;;; list-utils-partition-dupes

(ert-deftest list-utils-partition-dupes-01 nil
  "PARTITION DUPES operation on a list"
  (let ((list '(A a a 8 8 1 2 4 3 3 3 4.0 5 6 7 9 9 5)))
    (should (equal '((dupes . (a a 8 8 3 3 3 5 9 9 5))
                     (singlets . (A 1 2 4 4.0 6 7)))
                   (list-utils-partition-dupes list)))))

(ert-deftest list-utils-partition-dupes-02 nil
  "PARTITION DUPES operation with size hint, should be identical"
  (let ((list '(A a a 8 8 1 2 4 3 3 3 4.0 5 6 7 9 9 5)))
    (should (equal (list-utils-partition-dupes list)
                   (list-utils-partition-dupes list nil 17)))))

(ert-deftest list-utils-partition-dupes-03 nil
  "PARTITION DUPES operation with numeric hash-table-test"
  (let ((list '(A a a 8 8 1 2 4 3 3 3 4.0 5 6 7 9 9 5)))
    (should (equal '((dupes . (a a 8 8 4 3 3 3 4.0 5 9 9 5)) ; elements 4 4.0 now in dupes
                     (singlets . (A 1 2 6 7)))
                   (list-utils-partition-dupes list 'list-utils-htt-=)))))

(ert-deftest list-utils-partition-dupes-04 nil
  "PARTITION DUPES operation with case-insensitive hash-table-test"
  (let ((list '(A a a 8 8 1 2 4 3 3 3 4.0 5 6 7 9 9 5)))
    (should (equal '((dupes . (A a a 8 8 3 3 3 5 9 9 5))     ; elements A a now in dupes
                     (singlets . (1 2 4 4.0 6 7)))
                   (list-utils-partition-dupes list 'list-utils-htt-case-fold-equal)))))

(ert-deftest list-utils-partition-dupes-05 nil
  "PARTITION DUPES operation should be identical to result composed of other list operations"
  (let ((list '(A a a 8 8 1 2 4 3 3 3 4.0 5 6 7 9 9 5)))
    (should (equal (list (cons 'dupes (list-utils-dupes list))
                         (cons 'singlets (list-utils-singlets list)))
                   (list-utils-partition-dupes list)))))

(ert-deftest list-utils-partition-dupes-06 nil
  "PARTITION DUPES operation should not remove any values"
  (let ((list '(A a a 8 8 1 2 4 3 3 3 4.0 5 6 7 9 9 5)))
    (should (equal (sort (copy-sequence list) 'list-utils-test-soft-string-lessp)
                   (sort (apply 'append (mapcar 'cdr (list-utils-partition-dupes list)))
                         'list-utils-test-soft-string-lessp)))))

(ert-deftest list-utils-partition-dupes-07 nil
  "PARTITION DUPES operation with a large list"
  (let ((list (append (number-sequence 1 10000) (reverse (number-sequence 4 10009)))))
    (should (equal (list (cons 'dupes    (append (number-sequence 4 10000) (reverse (number-sequence 4 10000))))
                         (cons 'singlets (append (number-sequence 1 3) (reverse (number-sequence 10001 10009)))))
                   (list-utils-partition-dupes list)))))

(ert-deftest list-utils-partition-dupes-08 nil
  "PARTITION DUPES operation with large list and size hint, should be identical"
  (let ((list (append (number-sequence 1 10000) (reverse (number-sequence 4 10009)))))
    (should (equal (list-utils-partition-dupes list)
                   (list-utils-partition-dupes list nil 10000)))))

(ert-deftest list-utils-partition-dupes-09 nil
  "PARTITION DUPES operation with large list and numeric hash-table-test"
  (let ((list (append (number-sequence 1 10000) (mapcar 'float (reverse (number-sequence 4 10009))))))
    (should (equal (list (cons 'dupes    (append (number-sequence 4 10000) (mapcar 'float (reverse (number-sequence 4 10000)))))
                         (cons 'singlets (append (number-sequence 1 3) (mapcar 'float (reverse (number-sequence 10001 10009))))))
                   (list-utils-partition-dupes list 'list-utils-htt-=)))))

;; todo: use characters relevant to case-insensitivity
(ert-deftest list-utils-partition-dupes-10 nil
  "PARTITION DUPES operation with large list and case-insensitive hash-table-test"
  (let ((list (mapcar #'(lambda (x) (char-to-string (decode-char 'ucs x))) (append (number-sequence 1 10000) (reverse (number-sequence 4 10009))))))
    (should (equal (list (cons 'dupes    (mapcar #'(lambda (x) (char-to-string (decode-char 'ucs x))) (append (number-sequence 4 10000) (reverse (number-sequence 4 10000)))))
                         (cons 'singlets (mapcar #'(lambda (x) (char-to-string (decode-char 'ucs x))) (append (number-sequence 1 3) (reverse (number-sequence 10001 10009))))))
                   (list-utils-partition-dupes list 'list-utils-htt-case-fold-equal)))))

(ert-deftest list-utils-partition-dupes-11 nil
  "PARTITION DUPES operation with large list should be identical to result composed of other list operations"
  (let ((list (append (number-sequence 1 10000) (reverse (number-sequence 4 10009)))))
    (should (equal (list (cons 'dupes (list-utils-dupes list))
                         (cons 'singlets (list-utils-singlets list)))
                   (list-utils-partition-dupes list)))))

(ert-deftest list-utils-partition-dupes-12 nil
  "PARTITION DUPES operation with large list should not remove any values"
  (let ((list (append (number-sequence 1 10000) (reverse (number-sequence 4 10009)))))
    (should (equal (sort (copy-sequence list) '<)
                   (sort (apply 'append (mapcar 'cdr (list-utils-partition-dupes list))) '<)))))

;;; list-utils-plist-reverse

(ert-deftest list-utils-plist-reverse-01 nil
  (should (equal '(:four 4 :three 3 :two 2 :one 1)
                 (list-utils-plist-reverse '(:one 1 :two 2 :three 3 :four 4)))))

(ert-deftest list-utils-plist-reverse-02 nil
  (should-error
   (list-utils-plist-reverse '(:one 1 :two 2 :three 3 :four))))

(ert-deftest list-utils-plist-reverse-03 nil
  (should (equal '(:four 4 :three 3 :two 2 :one (1 (1 (1))))
                 (list-utils-plist-reverse '(:one (1 (1 (1))) :two 2 :three 3 :four 4)))))


;;; list-utils-plist-del

(ert-deftest list-utils-plist-del-01 nil
  (should (equal '(:one 1 :two 2 :three 3 :four 4)
                 (list-utils-plist-del '(:one 1 :two 2 :three 3 :four 4) :six))))

(ert-deftest list-utils-plist-del-02 nil
  (should (equal '(:one 1 :two 2 :three 3 :four 4)
                 (list-utils-plist-del '(:one 1 :two 2 :three 3 :four 4) 4))))

(ert-deftest list-utils-plist-del-03 nil
  (should (equal '(:one 1 :two 2 :three 3 :four 4)
                 (list-utils-plist-del '(:one 1 :two 2 :three 3 :four 4) 2))))

(ert-deftest list-utils-plist-del-04 nil
  (should (equal '(:one 1 :three 3 :four 4)
                 (list-utils-plist-del '(:one 1 :two 2 :three 3 :four 4) :two))))

(ert-deftest list-utils-plist-del-05 nil
  (should (equal '(:two 2 :three 3 :four 4)
                 (list-utils-plist-del '(:one 1 :two 2 :three 3 :four 4) :one))))

(ert-deftest list-utils-plist-del-06 nil
  (should (equal '(:one 1 :two 2 :three 3)
                 (list-utils-plist-del '(:one 1 :two 2 :three 3 :four 4) :four))))

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

;;; list-utils-test.el ends here
