;;; m-buffer-test.el --- Tests for m-buffer

;; The contents of this file are subject to the GPL License, Version 3.0.
;;
;; Copyright (C) 2014, Phillip Lord, Newcastle University
;;
;; This program is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Code:
(require 'm-buffer)

(defvar m-buffer-test-path
  (directory-file-name
   (file-name-directory
    (or load-file-name
        (buffer-file-name
         (get-buffer "m-buffer-test.el"))))))

(defmacro m-buffer-wtb-of-file (file &rest body)
  "Run BODY in a temp buffer with the contents of FILE inserted."
  `(with-temp-buffer
     (insert-file-contents
      (concat m-buffer-test-path "/"
              ,file))
     ,@body))


(ert-deftest m-with-temp-buffer-of-file ()
  "Test my test macro."
  (should
   (equal
    "one\ntwo\nthree\n"
    (m-buffer-wtb-of-file
     "with-temp-buffer.txt"
     (buffer-string)))))

(ert-deftest m-buffer-loaded ()
  "Has m-buffer loaded at all?"
  (should
   (fboundp 'm-buffer-match)))


(ert-deftest normalize-args ()
  "Normalize Region"
  ;; just buffer and regexp
  (should
   (equal
    (list (current-buffer) "regexp" nil nil nil nil :default nil)
    (m-buffer--normalize-args
     (list (current-buffer) "regexp"))))

  (should
   (equal
    (list (current-buffer) "regexp" nil nil nil nil :default nil)
    (m-buffer--normalize-args
     (list (current-buffer) :regexp "regexp"))))

  (should
   (equal
    (list (current-buffer) "regexp" 1 2 3 4 :default nil)
    (m-buffer--normalize-args
     (list (current-buffer) "regexp" :begin 1 :end 2 :post-match 3 :widen 4))))

  (should
   (equal
    (list (current-buffer) "regexp" 1 2 3 4 5 nil)
    (m-buffer--normalize-args
     (list (current-buffer) "regexp" :begin 1 :end 2 :post-match 3
           :widen 4 :case-fold-search 5))))

  (should
   (equal
    (list (current-buffer) "regexp" 1 2 3 4 5 6)
    (m-buffer--normalize-args
     (list (current-buffer) "regexp" :begin 1 :end 2 :post-match 3
           :widen 4 :case-fold-search 5 :numeric 6)))))


(defun m-buffer--flatten (l)
  (if (listp l)
      (apply 'append
       (seq-map
        'm-buffer--flatten l))
    (list l)))

(ert-deftest m-buffer-matches ()
  (should
   (= 3
      (length
       (m-buffer-wtb-of-file
        "match-data.txt"
        (m-buffer-match
         (current-buffer)
         "^one$")))))
  (should
   (seq-every-p
    'markerp
    (m-buffer--flatten
     (m-buffer-wtb-of-file
      "match-data.txt"
      (m-buffer-match
       (current-buffer)
       "^one$"))))))

(ert-deftest m-buffer-match-begin ()
  (should
   (seq-every-p
    'markerp
    (m-buffer-wtb-of-file
     "match-data.txt"
     (m-buffer-match-begin
      (current-buffer)
      "^one$")))))


(ert-deftest marker-to-pos ()
  (should
   (equal '(1 1 1)
          (m-buffer-marker-to-pos-nil
           (list
            (copy-marker 1)
            (copy-marker 1)
            (copy-marker 1))))))

(ert-deftest m-buffer-match-begin-pos ()
  (should
   (equal
    '(1 9 17)
    (m-buffer-wtb-of-file
     "match-data.txt"
     (m-buffer-match-begin-pos
      (current-buffer)
      "^one$")))))

(ert-deftest m-buffer-nil-marker ()
  (should
   (m-buffer-wtb-of-file
    "match-data.txt"
    (seq-every-p
     (lambda (marker)
       (and
        (marker-position marker)
        (marker-buffer marker)))
     (m-buffer-match-begin (current-buffer) "^one$"))))
  (should
   (m-buffer-wtb-of-file
    "match-data.txt"
    (seq-every-p
     (lambda (marker)
       (and
        (not (marker-position marker))
        (not (marker-buffer marker))))
     (m-buffer-nil-marker
      (m-buffer-match-begin (current-buffer) "^one$"))))))

(ert-deftest replace-matches ()
  (should
   (equal
    '((1 6) (11 16) (21 26))
    (m-buffer-wtb-of-file
     "match-data.txt"
     (m-buffer-marker-tree-to-pos
      (m-buffer-replace-match
       (m-buffer-match
        (current-buffer) "^one$") "three")))))

  (should
   (equal
    "three\ntwo\nthree\ntwo\nthree\ntwo\n"
    (m-buffer-wtb-of-file
     "match-data.txt"
     (m-buffer-replace-match
      (m-buffer-match
       (current-buffer) "^one$") "three")
     (buffer-string)))))

(ert-deftest page-matches ()
  (should
   (not
    (m-buffer-wtb-of-file
     "match-data.txt"
     (m-buffer-match-page (current-buffer))))))

(ert-deftest paragraph-separate ()
  (should
   (m-buffer-match-paragraph-separate (current-buffer))))

(ert-deftest line-start ()
  (should
   (equal
    '(1 2 3 5 7 10 13)
    (m-buffer-wtb-of-file
     "line-start.txt"
     (m-buffer-marker-to-pos
      (m-buffer-match-line-start (current-buffer)))))))

(ert-deftest line-end ()
  (should
   (equal
    '(1 2 4 6 9 12 13)
    (m-buffer-wtb-of-file
     "line-start.txt"
     (m-buffer-marker-to-pos
      (m-buffer-match-line-end (current-buffer)))))))

(ert-deftest first-line ()
  (should
   (equal
    '((1 1))
    (m-buffer-wtb-of-file
     "line-start.txt"
     (m-buffer-marker-tree-to-pos
      (m-buffer-match-first-line
       (current-buffer)))))))

(ert-deftest multi-match ()
  (should
   (equal
    '((1 4) (5 8) (13 18))
    (m-buffer-wtb-of-file
     "one-two-three.txt"
     (m-buffer-marker-tree-to-pos
      (m-buffer-match-multi
       '("one" "two" "three")
       :buffer (current-buffer))))))
    )

(ert-deftest sentence-end ()
  (should
   (equal
    '(15 32 48)
    (m-buffer-wtb-of-file
     "sentence-end.txt"
     (m-buffer-marker-to-pos
      (m-buffer-match-sentence-end (current-buffer)))))))

(ert-deftest buffer-for-match ()
  (should
   (with-temp-buffer
     (progn
       (insert "a")
       (equal
        (current-buffer)
        (m-buffer-buffer-for-match
         (m-buffer-match (current-buffer) "a")))))))

(ert-deftest match-n ()
  (should
   (equal
    '((1 7 1 4 4 7) (8 14 8 11 11 14) (15 21 15 18 18 21) (22 28 22 25 25 28))
    (m-buffer-wtb-of-file
     "nth.txt"
     (m-buffer-marker-tree-to-pos
      (m-buffer-match
       (current-buffer)
       "\\(one\\)\\(two\\)")))))

  (should
   (equal
    '((1 7)(8 14)(15 21)(22 28))
    (m-buffer-wtb-of-file
     "nth.txt"
     (m-buffer-marker-tree-to-pos
      (m-buffer-match-nth-group
       0 (m-buffer-match
          (current-buffer)
          "\\(one\\)\\(two\\)"))))))

  (should
   (equal
    '((1 4) (8 11) (15 18) (22 25))
    (m-buffer-wtb-of-file
     "nth.txt"
     (m-buffer-marker-tree-to-pos
      (m-buffer-match-nth-group
       1 (m-buffer-match
          (current-buffer)
          "\\(one\\)\\(two\\)")))))))


(ert-deftest apply-functions ()
  (should
   (equal
    '("onetwo" "onetwo" "onetwo" "onetwo" "")
    (m-buffer-wtb-of-file
     "nth.txt"
     (m-buffer-on-region
      (lambda (from to)
        (buffer-substring-no-properties from to))
      (m-buffer-match-line
       (current-buffer)))))))

(ert-deftest case-fold-search ()
  ;; match everything -- technically this is dependent on the buffer-local
  ;; value of case-fold-search
  (should
   (equal
    '((1 2) (3 4) (5 6) (7 8))
    (m-buffer-wtb-of-file
     "case-match.txt"
     (m-buffer-marker-tree-to-pos
      (m-buffer-match
       (current-buffer)
       "A")))))
  ;; match just upper case (i.e. cfs nil)
  (should
   (equal
    '((1 2)(5 6))
    (m-buffer-wtb-of-file
     "case-match.txt"
     (m-buffer-marker-tree-to-pos
      (m-buffer-match
       (current-buffer)
       "A"
       :case-fold-search nil)))))
  ;; match all again
  (should
   (equal
    '((1 2) (3 4) (5 6) (7 8))
    (m-buffer-wtb-of-file
     "case-match.txt"
     (m-buffer-marker-tree-to-pos
      (m-buffer-match
       (current-buffer)
       "A"
       :case-fold-search t))))))


(ert-deftest subtract ()
  (should
   (equal
    '((1 6) (17 23) (34 39))
    (m-buffer-wtb-of-file
     "sentence-end.txt"
     (m-buffer-marker-tree-to-pos
      (m-buffer-match-subtract
       (m-buffer-match-word
        (current-buffer))
       (m-buffer-match
        (current-buffer) "sentence")))))))

(ert-deftest exact-subtract ()
  (should
   (equal
    '((1 1)(2 2)(3 3))
    (m-buffer-match-exact-subtract
     '((0 0) (1 1) (2 2) (3 3) (4 4))
     '((0 0) (4 4)))))

  (should
   (equal
    '((1 1)(2 2)(3 3))
    (m-buffer-match-exact-subtract
     '((0 0) (1 1) (2 2) (3 3) (4 4))
     '((-1 -1) (4 4)))))

  (should
   (equal
    '((1 6) (17 23) (34 39))
    (m-buffer-wtb-of-file
     "sentence-end.txt"
     (m-buffer-marker-tree-to-pos
      (m-buffer-match-exact-subtract
       (m-buffer-match-word
        (current-buffer))
       (m-buffer-match
        (current-buffer) "sentence")))))))

(ert-deftest exact-subtract-with-nil ()
  (should
   (equal
    '((1 1))
    (m-buffer-match-exact-subtract
     '((1 1))
     nil))))

(ert-deftest exact-subtract-error-simplified ()
  (should
   (equal
    '((2 2))
    (m-buffer-match-exact-subtract
     '((1 1) (2 2))
     '((1 1))))))

(ert-deftest exact-subtract-error ()
  "This is a test case for a bug found from linked-buffer."
  (should
   (equal
    '((19 31 19 19))
    (m-buffer-match-exact-subtract
     '((1 18 1 1)
       (19 31 19 19))
     '((1 18))))))


(ert-deftest replace-point-unmoved ()
  "After a replace-match has happened point
should not have moved."
  (should
   (equal
    (m-buffer-wtb-of-file
     "match-data.txt"
     (point-min))
    (m-buffer-wtb-of-file
     "match-data.txt"
     (m-buffer-replace-match
      (m-buffer-match
       (current-buffer) "two")
      "one")
     (point)))))

(ert-deftest match-error ()
  "Should error because we try to override existing args."
  (should-error
   (m-buffer-match-word
    (current-buffer) :regexp "notword")))


(ert-deftest partition-by-markers ()
  (should
   (equal
    '((nil 1)
      (2 2 3 4)
      (5 5 6 7)
      (8 8 9))
    (m-buffer-partition-by-marker
     '(1 2 3 4 5 6 7 8 9)
     '(2 5 8)
     ))))


(ert-deftest point-stationionary-with-current ()
  "This test addresses a bug where m-buffer did not correctly
protect global state when the buffer being operated on was not
current -- in this case, a match could move point.

The two clauses are identical, one changing the current buffer
and one changing a buffer which is not current."
  (should
   (let ((out) (out-point))
     (with-temp-buffer
       (insert "one\ntwo\nthree\n")
       (setq out (current-buffer))
       (setq out-point (point))
       (m-buffer-match-first-line out)
       (= (point) out-point))))

   (should
    (let ((out) (out-point))
      (with-temp-buffer
        (insert "one\ntwo\nthree\n")
        (setq out (current-buffer))
        (setq out-point (point))
        (with-temp-buffer
          (m-buffer-match-first-line out))
        (= (point) out-point)))))

;;; m-buffer-test.el ends here
