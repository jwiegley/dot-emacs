;;; pcre2el.tests.el -- tests for pcre2el/rxt

;;; The bulk of the tests for pcre->elisp conversion are adapted from
;;; part of the PCRE library's test suite. Therefore:

;; This file incorporates work covered by the following copyright and
;; permission notice:
;;
;;
;; PCRE LICENCE
;; ------------

;; PCRE is a library of functions to support regular expressions whose syntax
;; and semantics are as close as possible to those of the Perl 5 language.

;; Release 8 of PCRE is distributed under the terms of the "BSD" licence, as
;; specified below. The documentation for PCRE, supplied in the "doc"
;; directory, is distributed under the same terms as the software itself.

;; The basic library functions are written in C and are freestanding. Also
;; included in the distribution is a set of C++ wrapper functions, and a
;; just-in-time compiler that can be used to optimize pattern matching. These
;; are both optional features that can be omitted when the library is built.


;; THE BASIC LIBRARY FUNCTIONS
;; ---------------------------

;; Written by:       Philip Hazel
;; Email local part: ph10
;; Email domain:     cam.ac.uk

;; University of Cambridge Computing Service,
;; Cambridge, England.

;; Copyright (c) 1997-2012 University of Cambridge
;; All rights reserved.


;; PCRE JUST-IN-TIME COMPILATION SUPPORT
;; -------------------------------------

;; Written by:       Zoltan Herczeg
;; Email local part: hzmester
;; Emain domain:     freemail.hu

;; Copyright(c) 2010-2012 Zoltan Herczeg
;; All rights reserved.


;; STACK-LESS JUST-IN-TIME COMPILER
;; --------------------------------

;; Written by:       Zoltan Herczeg
;; Email local part: hzmester
;; Emain domain:     freemail.hu

;; Copyright(c) 2009-2012 Zoltan Herczeg
;; All rights reserved.

;; THE "BSD" LICENCE
;; -----------------

;; Redistribution and use in source and binary forms, with or without
;; modification, are permitted provided that the following conditions are met:

;;     * Redistributions of source code must retain the above copyright notice,
;;       this list of conditions and the following disclaimer.

;;     * Redistributions in binary form must reproduce the above copyright
;;       notice, this list of conditions and the following disclaimer in the
;;       documentation and/or other materials provided with the distribution.

;;     * Neither the name of the University of Cambridge nor the name of Google
;;       Inc. nor the names of their contributors may be used to endorse or
;;       promote products derived from this software without specific prior
;;       written permission.

;; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
;; AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
;; IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
;; ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
;; LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
;; CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
;; SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
;; INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
;; CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
;; ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
;; POSSIBILITY OF SUCH DAMAGE.


;;;; Code:
(require 'pcre2el)
(require 'ert)
(require 'cl-lib)

;; Some older versions of ert lack `ert-skip'.
(defun rxt-skip-test (message)
  (if (fboundp 'ert-skip)
      (ert-skip message)
    (message (concat "SKIPPING: " message))
    (ert-pass)))


;;; Tests for source-location
(ert-deftest rxt-location ()
  (let ((dummy-1 (cl-gensym))
        (dummy-2 (cl-gensym))
        (location-1 (make-rxt-location :source "dummy 1"
                                       :start 2
                                       :end 5))
        (location-2 (make-rxt-location :source "dummy 2"
                                       :start 0
                                       :end 4)))
    (setf (rxt-location dummy-1) location-1)
    (setf (rxt-location dummy-2) location-2)
    (should (eq (rxt-location dummy-1) location-1))
    (should (eq (rxt-location dummy-2) location-2))))

(ert-deftest rxt-location-text ()
  (let ((location-1 (make-rxt-location :source "dummy 1"
                                       :start 2
                                       :end 5))
        (location-2 (make-rxt-location :source "dummy 2"
                                       :start 0
                                       :end 4)))
    (should (string= (rxt-location-text location-1) "mmy"))
    (should (string= (rxt-location-text location-2) "dumm"))))

(ert-deftest rxt-with-source-location ()
  "Test recording of source location information"
  (let ((string "dummy string") 
        (dummy-1 (cl-gensym))
        (dummy-2 (cl-gensym))
        value-1 value-2)
    (let ((rxt-source-text-string string))
      (with-temp-buffer
        (insert rxt-source-text-string)
        (goto-char (point-min))
        (setq value-1
              (rxt-with-source-location
               (goto-char (point-max))
               dummy-1)))

      (with-temp-buffer
        (insert rxt-source-text-string)
        (goto-char (point-min))
        (setq value-2
              (rxt-with-source-location
               (forward-word)
               dummy-2))))
    
    (should (eq value-1 dummy-1))
    (should (eq value-2 dummy-2))
    (let ((location (rxt-location value-1)))
      (should (not (null location)))
      (should (string= (rxt-location-source location) string))
      (should (= 0 (rxt-location-start location)))
      (should (= (length string) (rxt-location-end location)))
      (should (string= string (rxt-location-text location))))

    (let ((location (rxt-location value-2)))
      (should (not (null location)))
      (should (string= (rxt-location-source location) string))
      (should (= 0 (rxt-location-start location)))
      (should (= 5 (rxt-location-end location)))
      (should (string= "dummy" (rxt-location-text location))))))


;;; Syntax-tree tests
(ert-deftest rxt-trivial-p ()
  (should (rxt-trivial-p (rxt-empty-string))))

(ert-deftest rxt-string-concat ()
  (let* ((source "dummy string")
         (string-1 (rxt-string "dummy "))
         (string-2 (rxt-string "string")))
    
    (should (equal (rxt-string source)
                   (rxt-string-concat string-1 string-2)))
    
    (setf (rxt-location string-1)
          (make-rxt-location :source source :start 0 :end 6))
    (setf (rxt-location string-2)
          (make-rxt-location :source source :start 6 :end 12))
    
    (let ((result (rxt-string-concat string-1 string-2)))
      (should (equal (rxt-string source) result))
      (let ((location (rxt-location result)))
        (should (not (null location)))
        (should (eq source (rxt-location-source location)))
        (should (= 0 (rxt-location-start location)))
        (should (= 12 (rxt-location-end location)))))))

;; Sequence constructor
(ert-deftest rxt-seq-empty ()
  (should (equal (rxt-empty-string) (rxt-seq))))

(ert-deftest rxt-seq-singleton ()
  (let* ((string (rxt-string "sample string"))
         (sequence (rxt-seq string)))
    (should (equal string sequence))))

(ert-deftest rxt-seq-join-strings ()
  ;; Strings with the same case-folding setting are folded together
  (let* ((string-1 (rxt-string "first"))
         (string-2 (rxt-string "second"))
         (string-3 (rxt-string "third"))
         (sequence (rxt-seq string-1 string-2 string-3)))
    (should (equal sequence
                   (rxt-string (concat (rxt-string-chars string-1)
                                       (rxt-string-chars string-2)
                                       (rxt-string-chars string-3))))))

  ;; Strings with different case-folding behaviours are not folded
  ;; together
  (let* ((string-1 (rxt-string "case-sensitive" nil))
         (string-2 (rxt-string "case-insensitive" t))
         (sequence (rxt-seq string-1 string-2)))
    (should (rxt-seq-p sequence))
    (should (equal (rxt-seq-elts sequence)
                   (list string-1 string-2)))))

(ert-deftest rxt-seq-flatten-sequences ()
  (let* ((sequence-1
          (rxt-seq (rxt-bol)
                   (rxt-string "word")))
         (nested-sequence
          (rxt-seq sequence-1
                   (rxt-anything)
                   (rxt-eol)))
         (flat-sequence
          (rxt-seq (rxt-bol)
                   (rxt-string "word")
                   (rxt-anything)
                   (rxt-eol))))
    (should (equal nested-sequence flat-sequence)))

  (let* ((sequence (rxt-seq (rxt-bol)
                            (rxt-anything)
                            (rxt-eol)))
         (nested-1 (rxt-seq sequence))
         (nested-2 (rxt-seq nested-1)))
    (should (equal sequence nested-1))
    (should (equal sequence nested-2))))

(ert-deftest rxt-seq-remove-empty ()
  (let ((sequence-1 (rxt-seq (rxt-bow)
                             (rxt-string "lorem ipsum")
                             (rxt-anything)
                             (rxt-eow)))
        (sequence-2 (rxt-seq (rxt-empty-string)
                             (rxt-empty-string)
                             (rxt-bow)
                             (rxt-seq)
                             (rxt-string "lorem ipsum")
                             (rxt-seq)
                             (rxt-empty-string)
                             (rxt-anything)
                             (rxt-empty-string)
                             (rxt-eow))))
    (should (equal sequence-1 sequence-2))))

;;; Choice constructor
(ert-deftest rxt-choice ()
  ;; Singleton elements should be returned unchanged
  (let ((element (rxt-string "example")))
    (should (equal (rxt-choice element) element)))

  ;; Nested choices should be flattened
  (should (equal (rxt-choice
                  (rxt-choice
                   (rxt-string "first")
                   (rxt-string "second"))
                  (rxt-string "third"))
                 (rxt-choice
                  (rxt-string "first")
                  (rxt-string "second")
                  (rxt-string "third"))))

  ;; Char sets with the same case-folding behaviour should be folded together
  (let* ((char-set-1
          (make-rxt-char-set-union :chars '(?a ?q ?x)))
         (char-set-2
          (make-rxt-char-set-union :chars '(?1 ?9 ?5)))
         (choice
          (rxt-choice char-set-1 char-set-2)))
    (should (rxt-char-set-union-p choice))
    (should
     (rxt--char-set-equal
      choice
      (make-rxt-char-set-union :chars '(?a ?q ?x ?1 ?9 ?5)))))

  ;; Char-sets with different case-folding behaviour should NOT be
  ;; folded together
  (let* ((char-set-1
          (make-rxt-char-set-union :chars '(?a ?b ?c)
                                   :case-fold nil))
         (char-set-2
          (make-rxt-char-set-union :chars '(?1 ?2 ?3)
                                   :case-fold t))
         (choice
          (rxt-choice char-set-1 char-set-2)))
    (should (rxt-choice-p choice))))

;;; Repeat

;; FIXME

;;; Character sets and case-folding
(defun rxt--set-equal (a b)
  (null (cl-set-exclusive-or a b :test 'equal)))

(defun rxt--char-set-equal (a b)
  (and (rxt--set-equal (rxt-char-set-union-chars a)
                       (rxt-char-set-union-chars b))
       (rxt--set-equal (rxt-char-set-union-ranges a)
                       (rxt-char-set-union-ranges b))
       (rxt--set-equal (rxt-char-set-union-classes a)
                       (rxt-char-set-union-classes b))
       (eq (rxt-char-set-union-case-fold a)
           (rxt-char-set-union-case-fold b))))

(ert-deftest rxt--all-char-set-union-chars ()
  (should
   (rxt--set-equal
    (rxt--all-char-set-union-chars
     (make-rxt-char-set-union :chars '(?a ?x ?t)))
    '(?a ?x ?t)))

  (should
   (rxt--set-equal
    (rxt--all-char-set-union-chars
     (make-rxt-char-set-union :chars '(?a ?x ?t)
                              :ranges '((?0 . ?3) (?d . ?f))))
    '(?a ?x ?t ?0 ?1 ?2 ?3 ?d ?e ?f))))

(ert-deftest rxt--remove-redundant-chars ()
  (should
   (rxt--set-equal (rxt--remove-redundant-chars '(?a ?q ?t ?\n) nil)
                   '(?a ?q ?t ?\n)))

  (should
   (rxt--set-equal (rxt--remove-redundant-chars '(?a ?b ?c ?0 ?1 ?2) '(digit))
                   '(?a ?b ?c)))

  (should
   (rxt--set-equal (rxt--remove-redundant-chars '(?a ?b ?c ?0 ?1 ?2) '(letter))
                   '(?0 ?1 ?2)))

  (should
   (rxt--set-equal (rxt--remove-redundant-chars '(?a ?b ?c ?0 ?1 ?2) '(space))
                   '(?a ?b ?c ?0 ?1 ?2))))

(ert-deftest rxt--simplify-char-set ()
  ;; [abcdq-z[:digit:]] is unchanged
  (let ((char-set
         (rxt--simplify-char-set
          (make-rxt-char-set-union :chars '(?a ?b ?c ?d)
                                   :ranges '((?q . ?z))
                                   :classes '(digit)
                                   ))))
    (should
     (rxt--char-set-equal char-set
                          (rxt--simplify-char-set char-set))))

  ;; [abcd0-7[:alnum:]] => [[:alnum:]]
  (should
   (rxt--char-set-equal
    (rxt--simplify-char-set
     (make-rxt-char-set-union :chars '(?a ?b ?c ?d)
                              :ranges '((?0 . ?7))
                              :classes '(alnum)))
    (make-rxt-char-set-union :classes '(alnum))))

  ;; [abcda-z0-9] => [a-z0-9]
  (should
   (rxt--char-set-equal
    (rxt--simplify-char-set
     (make-rxt-char-set-union :chars '(?a ?b ?c ?d)
                              :ranges '((?a . ?z) (?0 . ?9))))
    (make-rxt-char-set-union :ranges '((?a . ?z) (?0 . ?9)))))

  ;; [g-za-f0-95-9] => [a-z0-9]
  (should
   (rxt--char-set-equal
    (rxt--simplify-char-set
     (make-rxt-char-set-union :ranges '((?g . ?z) (?a . ?f)
                                        (?0 . ?9) (?5 . ?9))))
    (make-rxt-char-set-union :ranges '((?a . ?z) (?0 . ?9)))))

  ;; Two-character ranges are unchanged
  (let ((char-set (make-rxt-char-set-union :chars '(?a ?b ?8 ?9))))
    (should
     (rxt--char-set-equal
      char-set
      (rxt--simplify-char-set char-set)))))

(ert-deftest rxt--simplify-char-set-case-fold ()
  ;; /[[:digit:][:space:]]/i => [[:digit:][:space:]]
  (let ((char-set (make-rxt-char-set-union :classes '(digit space))))
    (should (rxt--char-set-equal
             char-set
             (rxt--simplify-char-set char-set t))))

  ;; /[ad]/i => [ADad]
  (should (rxt--char-set-equal
           (rxt--simplify-char-set (make-rxt-char-set-union :chars '(?a ?d)) t)
           (make-rxt-char-set-union :chars '(?a ?d ?A ?D))))

  ;; /[abcd]/i => [A-Da-d]
  (should (rxt--char-set-equal
           (rxt--simplify-char-set
            (make-rxt-char-set-union :chars '(?a ?b ?c ?d)) t)
           (make-rxt-char-set-union :ranges '((?a . ?d) (?A . ?D)))))

  ;; /[W-c]/i => [A-CW-ca-c]
  (should (rxt--char-set-equal
           (rxt--simplify-char-set
            (make-rxt-char-set-union :ranges '((?W . ?c))) t)
           (make-rxt-char-set-union :ranges '((?W . ?c) (?A . ?C) (?w . ?z))))))

(ert-deftest rxt--extract-ranges ()
  (should (equal (rxt--extract-ranges '()) '()))
  (should (equal (rxt--extract-ranges '(1)) '((1 . 1))))
  (should (equal (rxt--extract-ranges '(1 1)) '((1 . 1))))
  (should (equal (rxt--extract-ranges '(1 1 1)) '((1 . 1))))
  (should (equal (rxt--extract-ranges '(1 2)) '((1 . 2))))
  (should (equal (rxt--extract-ranges '(1 2 3)) '((1 . 3))))
  (should (equal (rxt--extract-ranges '(1 2 3 4)) '((1 . 4))))
  (should (equal (rxt--extract-ranges '(1 2 3 4 5)) '((1 . 5))))
  (should (equal (rxt--extract-ranges '(0 1)) '((0 . 1))))
  (should (equal (rxt--extract-ranges '(0 0)) '((0 . 0))))
  (should (equal (rxt--extract-ranges '(0 0 0)) '((0 . 0))))
  (should (equal (rxt--extract-ranges '(-2 -1 0 1 2 3 4)) '((-2 . 4))))
  (should (equal (rxt--extract-ranges '(0 3 4 5)) '((0 . 0) (3 . 5))))
  (should (equal (rxt--extract-ranges '(0 0 0 3 3 4 5 0 3 4 5)) '((0 . 0) (3 . 5))))
  (should (equal (rxt--extract-ranges '(10 9 8 7 6 5)) '((5 . 10)))))

(ert-deftest rxt-char-set-union-case-fold-1 ()
  (should
   (rxt--char-set-equal
    (rxt-char-set-union
     (make-rxt-char-set-union :chars '(?a) :case-fold t)
     (make-rxt-char-set-union :case-fold t))
    (make-rxt-char-set-union :chars '(?a) :case-fold t)))

  (should
   (rxt--char-set-equal
    (rxt-char-set-union
     ?a
     (make-rxt-char-set-union :case-fold t))
    (make-rxt-char-set-union :chars '(?a) :case-fold t)))

  (should
   (rxt--char-set-equal
    (rxt-char-set-union
     "a"
     (make-rxt-char-set-union :case-fold t))
    (make-rxt-char-set-union :chars '(?a) :case-fold t)))

  (should
   (rxt--char-set-equal
    (rxt-char-set-union
     (make-rxt-char-set-union :case-fold t)
     (rxt-string "a"))
    (make-rxt-char-set-union :chars '(?a) :case-fold t))))


;;; PCRE parsing tests
(ert-deftest rxt-parse-pcre-simple-string ()
  (let* ((string "simple string")
         (parse (rxt-parse-pcre string)))
    (should (equal (rxt-string string) parse))
    (should (equal (rxt-source-text parse) string))))

(ert-deftest rxt-parse-pcre-quoted-string ()
  (cl-flet ((pcre-quote (string) (concat "\\Q" string "\\E")))
    (let* ((string "Simple string without metacharacters")
           (re (pcre-quote string))
           (parse (rxt-parse-pcre re)))
      (should (equal (rxt-string string) parse))
      (should (equal re (rxt-source-text parse))))

    (let* ((string "String $ with (( ) regexp \\ special [a-z] characters")
           (re (pcre-quote string))
           (parse (rxt-parse-pcre re)))
      (should (equal (rxt-string string) parse))
      (should (equal re (rxt-source-text parse))))))


;;; Simple pcre->elisp tests

;; Regexp quoting
(ert-deftest rxt-pcre-special-chars ()
  (let* ((string "String $ with (( ) regexp \\ special [a-z] characters")
         (re (pcre-to-elisp (concat "(\\Q" string "\\E)"))))
    (should (string-match re string))
    (should (equal (match-string 1 string) string))
    (should (equal (match-string 0 string) string))))

;; Grouping, alternation
(ert-deftest rxt-pcre-grouping ()
     (let ((re (pcre-to-elisp "(foo|bar)")))
       (should (string-match-p re "foo"))
       (should (string-match-p re "bar"))))

;; Grouping and character classes
(ert-deftest rxt-pcre-char-classes ()
  (let ((re (pcre-to-elisp "(\\D*):\\s*(\\d{3,5})$"))
        (string "Answer: 3501"))
    (should (string-match re string))
    (should (equal (match-string 1 string) "Answer"))
    (should (equal (match-string 2 string) "3501"))

    (should (not (string-match re "bad: 23")))
    (should (not (string-match re "also bad: 944732")))))

;;;; Weird rules for \digits
(ert-deftest rxt-pcre-digits ()
  ;; \040   is another way of writing a space
  (should (string-match-p (pcre-to-elisp "\\040") " "))
  
  ;; \40    is the same, provided there are fewer than 40 previous capturing subpatterns
  (should (string-match-p (pcre-to-elisp "\\40") " "))

  ;; \7     is always a back reference
  (let ((re
         (pcre-to-elisp
          "(.)(.)(.)(.)(.)(.)(.)\\s*\\7")))
    (should (string-match-p re "abcdefg g"))
    (should (not (string-match-p re "abcdefg\th"))))

  ;;\11    might be a back reference, or another way of writing a tab
  (should (string-match-p (pcre-to-elisp "\\11") "\t"))

  ;; Backreferences greater than 9 are unsupported in Emacs
  (should-error (pcre-to-elisp "(.)(.)(.)(.)(.)(.)(.)(.)(.)(.)(.)\\11"))

  ;; \011   is always a tab
  (should (string-match-p (pcre-to-elisp "\\011") "\t"))

  ;; \0113  is a tab followed by the character "3"
  (should (string-match-p (pcre-to-elisp "\\0113") "\t3"))

  ;; \113 might be a back reference, otherwise the character with octal
  ;; code 113
  (should (string-match-p (pcre-to-elisp "\\113") (char-to-string #o113)))

  ;;  \377 might be a back reference, otherwise the byte consisting
  ;;  entirely of 1 bits
  (should (string-match-p (pcre-to-elisp "\\377") (char-to-string 255)))

  ;; \81 is either a back reference, or a binary zero followed by the
  ;; two characters "8" and "1"
  (should (string-match-p (pcre-to-elisp "\\81") (concat (char-to-string 0) "81"))))

;; Character classes with special characters
(ert-deftest rxt-pcre-escapes-in-char-classes ()
  (let ((re (pcre-to-elisp "^[\\d\\w]*$")))
    (should (string-match-p re "012foo"))
    (should (not (string-match-p re "numbers 847 and 23 words"))))

  (let ((case-fold-search t))
    (should (string-match-p (pcre-to-elisp "^[\\dA-Z]*$")
                            "235711deadbeef"))))

;; Negated specials in character classes
(ert-deftest rxt-pcre-negated-char-class-escapes ()
  (let ((re (pcre-to-elisp "^[^\\d]*$")))
    (should (string-match-p re "words without numbers"))
    (should-not (string-match-p re "words 2 and 4 numbers 8"))))

;; Hexadecimal and octal escapes
(ert-deftest rxt-pcre-hex-octal ()
  (should (string-match-p (pcre-to-elisp "\\xab") (char-to-string #xab)))
  (should (string-match-p (pcre-to-elisp "[\\xab]") (char-to-string #xab)))
  (should (string-match-p (pcre-to-elisp "\\x{237}") (char-to-string #x237)))
  (should (string-match-p (pcre-to-elisp "[\\x{237}]") (char-to-string #x237)))
  (should (string-match-p (pcre-to-elisp "[\\177]") (char-to-string #o177)))
  (should (string-match-p (pcre-to-elisp "[\\7]") (char-to-string 7))))

;; Control characters
(ert-deftest rxt-pcre-control-chars ()
  (should (string-match-p (pcre-to-elisp "\\cx") (kbd "C-x")))
  (should (string-match-p (pcre-to-elisp "\\cC\\cn") (kbd "C-c C-n"))))

;; Double negation (intersection) in character classes - fixme?
(ert-deftest rxt-pcre-char-set-intersection ()
  (should (string-match-p (pcre-to-elisp "^[^\\W]*$") "foo")))

(ert-deftest rxt-quote-pcre ()
  (string=
   (rxt-quote-pcre ".*[]foo+")
   "\\.\\*\\[\\]foo\\+"))

;; String generation
(ert-deftest rxt-string-generation ()
  (let* ((strings '("caterpillar" "cat" "catatonic" "catamaran" "carthage"
                    "calloo" "callay"))
         (regexp (regexp-opt strings))
         (strings* (rxt-elisp-to-strings regexp)))
    (should (equal nil
                   (cl-set-exclusive-or strings strings*
                                        :test #'string=)))))


;;;; Elisp -> PCRE translation
(ert-deftest rxt-pcre-repetitions ()
  "Check that repetition and grouping have correct precedence in PCREs."
  (should
   (equal
    (rxt-elisp-to-pcre (rx (repeat 3 5 "c")))
    "c{3,5}"))

  (should
   (equal
    (rxt-elisp-to-pcre (rx (repeat 3 5 "string")))
    "(?:string){3,5}"))

  (should
   (equal
    (rxt-elisp-to-pcre (rx (* "c")))
    "c*"))

  (should
   (equal
    (rxt-elisp-to-pcre (rx (* "string")))
    "(?:string)*")))



;; Pretty-printing / explain tests

(ert-deftest rxt--print ()
  ;; Test that lists and dotted lists are printed correctly
  (cl-flet ((print-to-string (form)
              (with-temp-buffer
                (rxt-print form)
                (buffer-string))))
    (should (string= (print-to-string '(normal list))
                     "(normal list)"))
    (should (string= (print-to-string '(short-list))
                     "(short-list)"))
    (should (string= (print-to-string '(dotted . pair))
                     "(dotted . pair)"))
    (should (string= (print-to-string '(longer dotted . list))
                     "(longer dotted . list)"))

    ;; Test correct printing of some `rx' forms
    (should (string= (print-to-string '(? (any digit)))
                     "(? (any digit))"))
    (should (string= (print-to-string '(?? (any digit)))
                     "(?? (any digit))"))
    (should (string= (print-to-string '(*? "some regexp"))
                     "(*? \"some regexp\")"))
    (should (string= (print-to-string '(+? "some regexp"))
                     "(+? \"some regexp\")"))
    (should (string= (print-to-string '(any ?a ?q ?z))
                     "(any ?a ?q ?z)"))
    (should (string= (print-to-string '(any (?a . ?z) (?0 . ?3)))
                     "(any (?a . ?z) (?0 . ?3))"))
    (should (string= (print-to-string '(repeat 2 5 ?x))
                     "(repeat 2 5 ?x)"))
    (should (string= (print-to-string '(repeat 5 (any digit)))
                     "(repeat 5 (any digit))"))))

(ert-deftest rxt--propertize-whitespace ()
  (let ((string (rxt--propertize-whitespace "\n\t\f\r")))
    (should (equal (get-text-property 0 'display string) "\\n"))
    (should (equal (get-text-property 1 'display string) "\\t"))
    (should (equal (get-text-property 2 'display string) "\\f"))
    (should (equal (get-text-property 3 'display string) "\\r")))

  (let ((string (rxt--propertize-whitespace "String\n\twith\n\tnewlines and tabs")))
    (should (equal (get-text-property 6 'display string) "\\n"))
    (should (equal (get-text-property 7 'display string) "\\t"))
    (should (equal (get-text-property 12 'display string) "\\n"))
    (should (equal (get-text-property 13 'display string) "\\t"))))



;;;; Test PCRE reading

(ert-deftest rxt-read-delimited-pcre ()
  (cl-flet ((read-pcre-from-string (string)
              (with-temp-buffer
                (save-excursion (insert string))
                (rxt-read-delimited-pcre))))
    (should (string= (read-pcre-from-string "/[a-z]/")
                     "[a-z]"))
    (should (string= (read-pcre-from-string "  m/\\d+/")
                     "\\d+"))
    (should (string= (read-pcre-from-string "    qr/embedded\\/delimiters/")
                     "embedded\\/delimiters"))
    (should (string= (read-pcre-from-string
                      "    s/several\\/embedded\\/delimiters/replacement/")
                     "several\\/embedded\\/delimiters"))
    (should (string= (read-pcre-from-string
                      "    s/several\\/embedded\\/delimiters/replacement\\/with\\/delimiters/")
                     "several\\/embedded\\/delimiters"))

    (let ((pcre (read-pcre-from-string "/regexp/")))
      (should (string= pcre "regexp")))

    (let ((pcre (read-pcre-from-string "m/regexp/s")))
      (should (string= pcre "(?s)regexp")))

    (let ((pcre (read-pcre-from-string "s/regexp/replacement/sx")))
      (should (string= pcre "(?sx)regexp")))

    (let ((pcre (read-pcre-from-string "s/regexp/embedded\\/delimiters/x")))
      (should (string= pcre "(?x)regexp")))))

(ert-deftest rxt--read-pcre ()
  (when noninteractive (rxt-skip-test "Skipping interacive-only test"))
  (let* ((unread-command-events
          (string-to-list "regexp text\C-ci\C-cs\C-j"))
         (result
          (rxt--read-pcre "Test: ")))
    (should (string= result "(?is)regexp text")))

  (let* ((unread-command-events
          (string-to-list "\C-ciregexp text\C-ci\C-j"))
         (result
          (rxt--read-pcre "Test: ")))
    (should (string= result "regexp text"))))

(ert-deftest rxt--toggle-flag-string ()
  (cl-macrolet
      ((should-toggle (string flag result)
         `(should (string= (rxt--toggle-flag-string ,string ,flag) ,result))))
    (should-toggle "foo" ?x "(?x)foo")
    (should-toggle "(?x)foo" ?x "foo")
    (should-toggle "(?xi)foo" ?x "(?i)foo")
    (should-toggle "(?xi)foo" ?i "(?x)foo")
    (should-toggle "(?xi)foo" ?s "(?isx)foo")))


(defmacro rxt-with-minor-mode (mode &rest body)
  (declare (indent 1))
  (cl-assert (symbolp mode))
  (let ((saved-mode (make-symbol (concat "saved-" (symbol-name mode)))))
    `(let ((,saved-mode ,mode))
       (unwind-protect
            (progn
              (,mode +1)
              ,@body)
         (,mode (if ,saved-mode +1 0))))))

(defmacro rxt-with-minor-modes (modes &rest body)
  (declare (indent 1))
  (cl-assert (listp modes))
  (if (null modes)
      (macroexp-progn body)
    `(rxt-with-minor-modes ,(cdr modes)
       (rxt-with-minor-mode ,(car modes)
         ,@body))))

;;; Test for repeated searching in evil-mode (issue #19)
(ert-deftest rxt-pcre-mode-evil-search ()
  (when noninteractive
    (rxt-skip-test "Skipping interactive test `pcre-mode-evil-search'"))
  (unless (require 'evil nil t)
    (rxt-skip-test "Skipping `pcre-mode-evil-search' since `evil-mode' is not installed"))
  (cl-flet ((process-input (&rest keys)
              (let ((unread-command-events
                     (listify-key-sequence
                      (apply #'vconcat `(,@keys ,(kbd "C-M-c"))))))
                (recursive-edit))))
    (rxt-with-minor-modes (pcre-mode evil-mode)
      (save-window-excursion
        (with-temp-buffer
          (insert "\n\n(this) (that) (the other)")
          (goto-char (point-min))
          (set-window-buffer (selected-window) (current-buffer))

          (process-input "/\\(th" (kbd "RET"))
          (should (looking-at "(this)"))

          (process-input "n")
          (should (looking-at "(that)"))

          (process-input "n")
          (should (looking-at "(the other)"))

          (process-input "N")
          (should (looking-at "(that)"))

          (process-input "N")
          (should (looking-at "(this)")))))))


;; The following tests are adapted from the first set of tests
;; ("testinput1") in the PCRE library's test suite: see
;; http://www.pcre.org/ and the copyright notice at the beginning of
;; this file.

;; Each test converts a particular PCRE regexp to its (supposed) Elisp
;; equivalent, then compares the set of matches for the Elisp regexp
;; against the set of matches generated by Perl for a number of
;; subject strings. (The set of Perl matches to compare with was
;; statically generated by a script adapted from the PCRE test script
;; to create this file, so the tests don't actually call out to Perl).

;; Many of the tests currently fail -- a bit under half of them. This
;; obviously is not very good, but many of the failing tests are
;; features of PCRE which are not easily supported in Emacs, like the
;; (* ...) backtracking control verbs. Other failing tests are bugs
;; that might be worth fixing, so these are a good place to look for
;; anyone interested in improving the pcre->elisp code.

;; The failing tests are marked with the `:expected-result :failed'
;; property in their definitions, so the tests as a whole are still
;; useful to guard against regressions.
;; 

(defun rxt-all-matches
  (regexp input)
  (if (string-match regexp input)
      (let* ((match-count (- (/ (length (match-data)) 2) 1)))
        (cl-loop for i from 0 to match-count
                 collect (match-string i input)))
    nil))

(defmacro rxt-match-test
  (regexp input perl-matches)
  `(should
    (equal
     (rxt-all-matches ,regexp ,input)
     ,perl-matches)))

(ert-deftest rxt-pcre-test-00002 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "the quick brown fox" "")))
    (rxt-match-test regexp "the quick brown fox"
                    '("the quick brown fox"))
    (rxt-match-test regexp "The quick brown FOX" 'nil)
    (rxt-match-test regexp "What do you know about the quick brown fox?"
                    '("the quick brown fox"))
    (rxt-match-test regexp "What do you know about THE QUICK BROWN FOX?" 'nil)))


(ert-deftest rxt-pcre-test-00003 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "The quick brown fox" "i")))
    (rxt-match-test regexp "the quick brown fox"
                    '("the quick brown fox"))
    (rxt-match-test regexp "The quick brown FOX"
                    '("The quick brown FOX"))
    (rxt-match-test regexp "What do you know about the quick brown fox?"
                    '("the quick brown fox"))
    (rxt-match-test regexp "What do you know about THE QUICK BROWN FOX?"
                    '("THE QUICK BROWN FOX"))))

(ert-deftest rxt-pcre-test-00004 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "abcd\\t\\n\\r\\f\\a\\e\\071\\x3b\\$\\\\\\?caxyz" "")))
    (rxt-match-test regexp "abcd	\n\f9;$\\?caxyz"
                    '("abcd	\n\f9;$\\?caxyz"))))

(ert-deftest rxt-pcre-test-00005 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a*abc?xyz+pqr{3}ab{2,}xy{4,5}pq{0,6}AB{0,}zz" "")))
    (rxt-match-test regexp "abxyzpqrrrabbxyyyypqAzz"
                    '("abxyzpqrrrabbxyyyypqAzz"))
    (rxt-match-test regexp "abxyzpqrrrabbxyyyypqAzz"
                    '("abxyzpqrrrabbxyyyypqAzz"))
    (rxt-match-test regexp "aabxyzpqrrrabbxyyyypqAzz"
                    '("aabxyzpqrrrabbxyyyypqAzz"))
    (rxt-match-test regexp "aaabxyzpqrrrabbxyyyypqAzz"
                    '("aaabxyzpqrrrabbxyyyypqAzz"))
    (rxt-match-test regexp "aaaabxyzpqrrrabbxyyyypqAzz"
                    '("aaaabxyzpqrrrabbxyyyypqAzz"))
    (rxt-match-test regexp "abcxyzpqrrrabbxyyyypqAzz"
                    '("abcxyzpqrrrabbxyyyypqAzz"))
    (rxt-match-test regexp "aabcxyzpqrrrabbxyyyypqAzz"
                    '("aabcxyzpqrrrabbxyyyypqAzz"))
    (rxt-match-test regexp "aaabcxyzpqrrrabbxyyyypAzz"
                    '("aaabcxyzpqrrrabbxyyyypAzz"))
    (rxt-match-test regexp "aaabcxyzpqrrrabbxyyyypqAzz"
                    '("aaabcxyzpqrrrabbxyyyypqAzz"))
    (rxt-match-test regexp "aaabcxyzpqrrrabbxyyyypqqAzz"
                    '("aaabcxyzpqrrrabbxyyyypqqAzz"))
    (rxt-match-test regexp "aaabcxyzpqrrrabbxyyyypqqqAzz"
                    '("aaabcxyzpqrrrabbxyyyypqqqAzz"))
    (rxt-match-test regexp "aaabcxyzpqrrrabbxyyyypqqqqAzz"
                    '("aaabcxyzpqrrrabbxyyyypqqqqAzz"))
    (rxt-match-test regexp "aaabcxyzpqrrrabbxyyyypqqqqqAzz"
                    '("aaabcxyzpqrrrabbxyyyypqqqqqAzz"))
    (rxt-match-test regexp "aaabcxyzpqrrrabbxyyyypqqqqqqAzz"
                    '("aaabcxyzpqrrrabbxyyyypqqqqqqAzz"))
    (rxt-match-test regexp "aaaabcxyzpqrrrabbxyyyypqAzz"
                    '("aaaabcxyzpqrrrabbxyyyypqAzz"))
    (rxt-match-test regexp "abxyzzpqrrrabbxyyyypqAzz"
                    '("abxyzzpqrrrabbxyyyypqAzz"))
    (rxt-match-test regexp "aabxyzzzpqrrrabbxyyyypqAzz"
                    '("aabxyzzzpqrrrabbxyyyypqAzz"))
    (rxt-match-test regexp "aaabxyzzzzpqrrrabbxyyyypqAzz"
                    '("aaabxyzzzzpqrrrabbxyyyypqAzz"))
    (rxt-match-test regexp "aaaabxyzzzzpqrrrabbxyyyypqAzz"
                    '("aaaabxyzzzzpqrrrabbxyyyypqAzz"))
    (rxt-match-test regexp "abcxyzzpqrrrabbxyyyypqAzz"
                    '("abcxyzzpqrrrabbxyyyypqAzz"))
    (rxt-match-test regexp "aabcxyzzzpqrrrabbxyyyypqAzz"
                    '("aabcxyzzzpqrrrabbxyyyypqAzz"))
    (rxt-match-test regexp "aaabcxyzzzzpqrrrabbxyyyypqAzz"
                    '("aaabcxyzzzzpqrrrabbxyyyypqAzz"))
    (rxt-match-test regexp "aaaabcxyzzzzpqrrrabbxyyyypqAzz"
                    '("aaaabcxyzzzzpqrrrabbxyyyypqAzz"))
    (rxt-match-test regexp "aaaabcxyzzzzpqrrrabbbxyyyypqAzz"
                    '("aaaabcxyzzzzpqrrrabbbxyyyypqAzz"))
    (rxt-match-test regexp "aaaabcxyzzzzpqrrrabbbxyyyyypqAzz"
                    '("aaaabcxyzzzzpqrrrabbbxyyyyypqAzz"))
    (rxt-match-test regexp "aaabcxyzpqrrrabbxyyyypABzz"
                    '("aaabcxyzpqrrrabbxyyyypABzz"))
    (rxt-match-test regexp "aaabcxyzpqrrrabbxyyyypABBzz"
                    '("aaabcxyzpqrrrabbxyyyypABBzz"))
    (rxt-match-test regexp ">>>aaabxyzpqrrrabbxyyyypqAzz"
                    '("aaabxyzpqrrrabbxyyyypqAzz"))
    (rxt-match-test regexp ">aaaabxyzpqrrrabbxyyyypqAzz"
                    '("aaaabxyzpqrrrabbxyyyypqAzz"))
    (rxt-match-test regexp ">>>>abcxyzpqrrrabbxyyyypqAzz"
                    '("abcxyzpqrrrabbxyyyypqAzz"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "abxyzpqrrabbxyyyypqAzz" 'nil)
    (rxt-match-test regexp "abxyzpqrrrrabbxyyyypqAzz" 'nil)
    (rxt-match-test regexp "abxyzpqrrrabxyyyypqAzz" 'nil)
    (rxt-match-test regexp "aaaabcxyzzzzpqrrrabbbxyyyyyypqAzz" 'nil)
    (rxt-match-test regexp "aaaabcxyzzzzpqrrrabbbxyyypqAzz" 'nil)
    (rxt-match-test regexp "aaabcxyzpqrrrabbxyyyypqqqqqqqAzz" 'nil)))


(ert-deftest rxt-pcre-test-00006 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(abc){1,2}zz" "")))
    (rxt-match-test regexp "abczz"
                    '("abczz" "abc"))
    (rxt-match-test regexp "abcabczz"
                    '("abcabczz" "abc"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "zz" 'nil)
    (rxt-match-test regexp "abcabcabczz" 'nil)
    (rxt-match-test regexp ">>abczz" 'nil)))


(ert-deftest rxt-pcre-test-00007 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(b+?|a){1,2}?c" "")))
    (rxt-match-test regexp "bc"
                    '("bc" "b"))
    (rxt-match-test regexp "bbc"
                    '("bbc" "b"))
    (rxt-match-test regexp "bbbc"
                    '("bbbc" "bb"))
    (rxt-match-test regexp "bac"
                    '("bac" "a"))
    (rxt-match-test regexp "bbac"
                    '("bbac" "a"))
    (rxt-match-test regexp "aac"
                    '("aac" "a"))
    (rxt-match-test regexp "abbbbbbbbbbbc"
                    '("abbbbbbbbbbbc" "bbbbbbbbbbb"))
    (rxt-match-test regexp "bbbbbbbbbbbac"
                    '("bbbbbbbbbbbac" "a"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "aaac" 'nil)
    (rxt-match-test regexp "abbbbbbbbbbbac" 'nil)))


(ert-deftest rxt-pcre-test-00008 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(b+|a){1,2}c" "")))
    (rxt-match-test regexp "bc"
                    '("bc" "b"))
    (rxt-match-test regexp "bbc"
                    '("bbc" "bb"))
    (rxt-match-test regexp "bbbc"
                    '("bbbc" "bbb"))
    (rxt-match-test regexp "bac"
                    '("bac" "a"))
    (rxt-match-test regexp "bbac"
                    '("bbac" "a"))
    (rxt-match-test regexp "aac"
                    '("aac" "a"))
    (rxt-match-test regexp "abbbbbbbbbbbc"
                    '("abbbbbbbbbbbc" "bbbbbbbbbbb"))
    (rxt-match-test regexp "bbbbbbbbbbbac"
                    '("bbbbbbbbbbbac" "a"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "aaac" 'nil)
    (rxt-match-test regexp "abbbbbbbbbbbac" 'nil)))


(ert-deftest rxt-pcre-test-00009 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(b+|a){1,2}?bc" "")))
    (rxt-match-test regexp "bbc"
                    '("bbc" "b"))))


(ert-deftest rxt-pcre-test-00010 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(b*|ba){1,2}?bc" "")))
    (rxt-match-test regexp "babc"
                    '("babc" "ba"))
    (rxt-match-test regexp "bbabc"
                    '("bbabc" "ba"))
    (rxt-match-test regexp "bababc"
                    '("bababc" "ba"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "bababbc" 'nil)
    (rxt-match-test regexp "babababc" 'nil)))


(ert-deftest rxt-pcre-test-00011 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(ba|b*){1,2}?bc" "")))
    (rxt-match-test regexp "babc"
                    '("babc" "ba"))
    (rxt-match-test regexp "bbabc"
                    '("bbabc" "ba"))
    (rxt-match-test regexp "bababc"
                    '("bababc" "ba"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "bababbc" 'nil)
    (rxt-match-test regexp "babababc" 'nil)))


(ert-deftest rxt-pcre-test-00012 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^\\ca\\cA\\c[\\c{\\c:" "")))
    (rxt-match-test regexp ";z"
                    '(";z"))))


(ert-deftest rxt-pcre-test-00013 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^[ab\\]cde]" "")))
    (rxt-match-test regexp "athing"
                    '("a"))
    (rxt-match-test regexp "bthing"
                    '("b"))
    (rxt-match-test regexp "]thing"
                    '("]"))
    (rxt-match-test regexp "cthing"
                    '("c"))
    (rxt-match-test regexp "dthing"
                    '("d"))
    (rxt-match-test regexp "ething"
                    '("e"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "fthing" 'nil)
    (rxt-match-test regexp "[thing" 'nil)
    (rxt-match-test regexp "\\thing" 'nil)))


(ert-deftest rxt-pcre-test-00014 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^[]cde]" "")))
    (rxt-match-test regexp "]thing"
                    '("]"))
    (rxt-match-test regexp "cthing"
                    '("c"))
    (rxt-match-test regexp "dthing"
                    '("d"))
    (rxt-match-test regexp "ething"
                    '("e"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "athing" 'nil)
    (rxt-match-test regexp "fthing" 'nil)))


(ert-deftest rxt-pcre-test-00015 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^[^ab\\]cde]" "")))
    (rxt-match-test regexp "fthing"
                    '("f"))
    (rxt-match-test regexp "[thing"
                    '("["))
    (rxt-match-test regexp "\\thing"
                    '("\\"))
    (rxt-match-test regexp "*** Failers"
                    '("*"))
    (rxt-match-test regexp "athing" 'nil)
    (rxt-match-test regexp "bthing" 'nil)
    (rxt-match-test regexp "]thing" 'nil)
    (rxt-match-test regexp "cthing" 'nil)
    (rxt-match-test regexp "dthing" 'nil)
    (rxt-match-test regexp "ething" 'nil)))


(ert-deftest rxt-pcre-test-00016 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^[^]cde]" "")))
    (rxt-match-test regexp "athing"
                    '("a"))
    (rxt-match-test regexp "fthing"
                    '("f"))
    (rxt-match-test regexp "*** Failers"
                    '("*"))
    (rxt-match-test regexp "]thing" 'nil)
    (rxt-match-test regexp "cthing" 'nil)
    (rxt-match-test regexp "dthing" 'nil)
    (rxt-match-test regexp "ething" 'nil)))


(ert-deftest rxt-pcre-test-00017 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^\\\201" "")))
    (rxt-match-test regexp "\201"
                    '("\201"))))


(ert-deftest rxt-pcre-test-00018 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^\377" "")))
    (rxt-match-test regexp "\377"
                    '("\377"))))


(ert-deftest rxt-pcre-test-00019 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^[0-9]+$" "")))
    (rxt-match-test regexp "0"
                    '("0"))
    (rxt-match-test regexp "1"
                    '("1"))
    (rxt-match-test regexp "2"
                    '("2"))
    (rxt-match-test regexp "3"
                    '("3"))
    (rxt-match-test regexp "4"
                    '("4"))
    (rxt-match-test regexp "5"
                    '("5"))
    (rxt-match-test regexp "6"
                    '("6"))
    (rxt-match-test regexp "7"
                    '("7"))
    (rxt-match-test regexp "8"
                    '("8"))
    (rxt-match-test regexp "9"
                    '("9"))
    (rxt-match-test regexp "10"
                    '("10"))
    (rxt-match-test regexp "100"
                    '("100"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "abc" 'nil)))


(ert-deftest rxt-pcre-test-00020 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^.*nter" "")))
    (rxt-match-test regexp "enter"
                    '("enter"))
    (rxt-match-test regexp "inter"
                    '("inter"))
    (rxt-match-test regexp "uponter"
                    '("uponter"))))


(ert-deftest rxt-pcre-test-00021 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^xxx[0-9]+$" "")))
    (rxt-match-test regexp "xxx0"
                    '("xxx0"))
    (rxt-match-test regexp "xxx1234"
                    '("xxx1234"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "xxx" 'nil)))


(ert-deftest rxt-pcre-test-00022 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^.+[0-9][0-9][0-9]$" "")))
    (rxt-match-test regexp "x123"
                    '("x123"))
    (rxt-match-test regexp "xx123"
                    '("xx123"))
    (rxt-match-test regexp "123456"
                    '("123456"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "123" 'nil)
    (rxt-match-test regexp "x1234"
                    '("x1234"))))


(ert-deftest rxt-pcre-test-00023 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^.+?[0-9][0-9][0-9]$" "")))
    (rxt-match-test regexp "x123"
                    '("x123"))
    (rxt-match-test regexp "xx123"
                    '("xx123"))
    (rxt-match-test regexp "123456"
                    '("123456"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "123" 'nil)
    (rxt-match-test regexp "x1234"
                    '("x1234"))))


(ert-deftest rxt-pcre-test-00024 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^([^!]+)!(.+)=apquxz\\.ixr\\.zzz\\.ac\\.uk$" "")))
    (rxt-match-test regexp "abc!pqr=apquxz.ixr.zzz.ac.uk"
                    '("abc!pqr=apquxz.ixr.zzz.ac.uk" "abc" "pqr"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "!pqr=apquxz.ixr.zzz.ac.uk" 'nil)
    (rxt-match-test regexp "abc!=apquxz.ixr.zzz.ac.uk" 'nil)
    (rxt-match-test regexp "abc!pqr=apquxz:ixr.zzz.ac.uk" 'nil)
    (rxt-match-test regexp "abc!pqr=apquxz.ixr.zzz.ac.ukk" 'nil)))


(ert-deftest rxt-pcre-test-00025 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp ":" "")))
    (rxt-match-test regexp "Well, we need a colon: somewhere"
                    '(":"))
    (rxt-match-test regexp "*** Fail if we don't" 'nil)))


(ert-deftest rxt-pcre-test-00026 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "([\\da-f:]+)$" "i")))
    (rxt-match-test regexp "0abc"
                    '("0abc" "0abc"))
    (rxt-match-test regexp "abc"
                    '("abc" "abc"))
    (rxt-match-test regexp "fed"
                    '("fed" "fed"))
    (rxt-match-test regexp "E"
                    '("E" "E"))
    (rxt-match-test regexp "::"
                    '("::" "::"))
    (rxt-match-test regexp "5f03:12C0::932e"
                    '("5f03:12C0::932e" "5f03:12C0::932e"))
    (rxt-match-test regexp "fed def"
                    '("def" "def"))
    (rxt-match-test regexp "Any old stuff"
                    '("ff" "ff"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "0zzz" 'nil)
    (rxt-match-test regexp "gzzz" 'nil)
    (rxt-match-test regexp "fed " 'nil)
    (rxt-match-test regexp "Any old rubbish" 'nil)))


(ert-deftest rxt-pcre-test-00027 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^.*\\.(\\d{1,3})\\.(\\d{1,3})\\.(\\d{1,3})$" "")))
    (rxt-match-test regexp ".1.2.3"
                    '(".1.2.3" "1" "2" "3"))
    (rxt-match-test regexp "A.12.123.0"
                    '("A.12.123.0" "12" "123" "0"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp ".1.2.3333" 'nil)
    (rxt-match-test regexp "1.2.3" 'nil)
    (rxt-match-test regexp "1234.2.3" 'nil)))


(ert-deftest rxt-pcre-test-00028 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(\\d+)\\s+IN\\s+SOA\\s+(\\S+)\\s+(\\S+)\\s*\\(\\s*$" "")))
    (rxt-match-test regexp "1 IN SOA non-sp1 non-sp2("
                    '("1 IN SOA non-sp1 non-sp2(" "1" "non-sp1" "non-sp2"))
    (rxt-match-test regexp "1    IN    SOA    non-sp1    non-sp2   ("
                    '("1    IN    SOA    non-sp1    non-sp2   (" "1" "non-sp1" "non-sp2"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "1IN SOA non-sp1 non-sp2(" 'nil)))


(ert-deftest rxt-pcre-test-00029 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^[a-zA-Z\\d][a-zA-Z\\d\\-]*(\\.[a-zA-Z\\d][a-zA-z\\d\\-]*)*\\.$" "")))
    (rxt-match-test regexp "a."
                    '("a."))
    (rxt-match-test regexp "Z."
                    '("Z."))
    (rxt-match-test regexp "2."
                    '("2."))
    (rxt-match-test regexp "ab-c.pq-r."
                    '("ab-c.pq-r." ".pq-r"))
    (rxt-match-test regexp "sxk.zzz.ac.uk."
                    '("sxk.zzz.ac.uk." ".uk"))
    (rxt-match-test regexp "x-.y-."
                    '("x-.y-." ".y-"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "-abc.peq." 'nil)))


(ert-deftest rxt-pcre-test-00030 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^\\*\\.[a-z]([a-z\\-\\d]*[a-z\\d]+)?(\\.[a-z]([a-z\\-\\d]*[a-z\\d]+)?)*$" "")))
    (rxt-match-test regexp "*.a"
                    '("*.a"))
    (rxt-match-test regexp "*.b0-a"
                    '("*.b0-a" "0-a"))
    (rxt-match-test regexp "*.c3-b.c"
                    '("*.c3-b.c" "3-b" ".c"))
    (rxt-match-test regexp "*.c-a.b-c"
                    '("*.c-a.b-c" "-a" ".b-c" "-c"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "*.0" 'nil)
    (rxt-match-test regexp "*.a-" 'nil)
    (rxt-match-test regexp "*.a-b.c-" 'nil)
    (rxt-match-test regexp "*.c-a.0-c" 'nil)))


(ert-deftest rxt-pcre-test-00031 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?=ab(de))(abd)(e)" "")))
    (rxt-match-test regexp "abde"
                    '("abde" "de" "abd" "e"))))


(ert-deftest rxt-pcre-test-00032 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?!(ab)de|x)(abd)(f)" "")))
    (rxt-match-test regexp "abdf"
                    '("abdf" nil "abd" "f"))))


(ert-deftest rxt-pcre-test-00033 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?=(ab(cd)))(ab)" "")))
    (rxt-match-test regexp "abcd"
                    '("ab" "abcd" "cd" "ab"))))


(ert-deftest rxt-pcre-test-00034 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^[\\da-f](\\.[\\da-f])*$" "i")))
    (rxt-match-test regexp "a.b.c.d"
                    '("a.b.c.d" ".d"))
    (rxt-match-test regexp "A.B.C.D"
                    '("A.B.C.D" ".D"))
    (rxt-match-test regexp "a.b.c.1.2.3.C"
                    '("a.b.c.1.2.3.C" ".C"))))


(ert-deftest rxt-pcre-test-00035 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^\\\".*\\\"\\s*(;.*)?$" "")))
    (rxt-match-test regexp "\"1234\""
                    '("\"1234\""))
    (rxt-match-test regexp "\"abcd\" ;"
                    '("\"abcd\" ;" ";"))
    (rxt-match-test regexp "\"\" ; rhubarb"
                    '("\"\" ; rhubarb" "; rhubarb"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "\"1234\" : things" 'nil)))


(ert-deftest rxt-pcre-test-00036 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^$" "")))
    (rxt-match-test regexp ""
                    '(""))
    (rxt-match-test regexp "*** Failers" 'nil)))


(ert-deftest rxt-pcre-test-00037 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "   ^    a   (?# begins with a)  b\\sc (?# then b c) $ (?# then end)" "x")))
    (rxt-match-test regexp "ab c"
                    '("ab c"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "abc" 'nil)
    (rxt-match-test regexp "ab cde" 'nil)))


(ert-deftest rxt-pcre-test-00038 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?x)   ^    a   (?# begins with a)  b\\sc (?# then b c) $ (?# then end)" "")))
    (rxt-match-test regexp "ab c"
                    '("ab c"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "abc" 'nil)
    (rxt-match-test regexp "ab cde" 'nil)))


(ert-deftest rxt-pcre-test-00039 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^   a\\ b[c ]d       $" "x")))
    (rxt-match-test regexp "a bcd"
                    '("a bcd"))
    (rxt-match-test regexp "a b d"
                    '("a b d"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "abcd" 'nil)
    (rxt-match-test regexp "ab d" 'nil)))


(ert-deftest rxt-pcre-test-00040 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(a(b(c)))(d(e(f)))(h(i(j)))(k(l(m)))$" "")))
    (rxt-match-test regexp "abcdefhijklm"
                    '("abcdefhijklm" "abc" "bc" "c" "def" "ef" "f" "hij" "ij" "j" "klm" "lm" "m"))))


(ert-deftest rxt-pcre-test-00041 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?:a(b(c)))(?:d(e(f)))(?:h(i(j)))(?:k(l(m)))$" "")))
    (rxt-match-test regexp "abcdefhijklm"
                    '("abcdefhijklm" "bc" "c" "ef" "f" "ij" "j" "lm" "m"))))


(ert-deftest rxt-pcre-test-00042 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^[\\w][\\W][\\s][\\S][\\d][\\D][\\b][\\n][\\c]][\\022]" "")))
    (rxt-match-test regexp "a+ Z0+\n"
                    '("a+ Z0+\n"))))


(ert-deftest rxt-pcre-test-00043 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^[.^$|()*+?{,}]+" "")))
    (rxt-match-test regexp ".^$(*+)|{?,?}"
                    '(".^$(*+)|{?,?}"))))


(ert-deftest rxt-pcre-test-00044 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^a*\\w" "")))
    (rxt-match-test regexp "z"
                    '("z"))
    (rxt-match-test regexp "az"
                    '("az"))
    (rxt-match-test regexp "aaaz"
                    '("aaaz"))
    (rxt-match-test regexp "a"
                    '("a"))
    (rxt-match-test regexp "aa"
                    '("aa"))
    (rxt-match-test regexp "aaaa"
                    '("aaaa"))
    (rxt-match-test regexp "a+"
                    '("a"))
    (rxt-match-test regexp "aa+"
                    '("aa"))))


(ert-deftest rxt-pcre-test-00045 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^a*?\\w" "")))
    (rxt-match-test regexp "z"
                    '("z"))
    (rxt-match-test regexp "az"
                    '("a"))
    (rxt-match-test regexp "aaaz"
                    '("a"))
    (rxt-match-test regexp "a"
                    '("a"))
    (rxt-match-test regexp "aa"
                    '("a"))
    (rxt-match-test regexp "aaaa"
                    '("a"))
    (rxt-match-test regexp "a+"
                    '("a"))
    (rxt-match-test regexp "aa+"
                    '("a"))))


(ert-deftest rxt-pcre-test-00046 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^a+\\w" "")))
    (rxt-match-test regexp "az"
                    '("az"))
    (rxt-match-test regexp "aaaz"
                    '("aaaz"))
    (rxt-match-test regexp "aa"
                    '("aa"))
    (rxt-match-test regexp "aaaa"
                    '("aaaa"))
    (rxt-match-test regexp "aa+"
                    '("aa"))))


(ert-deftest rxt-pcre-test-00047 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^a+?\\w" "")))
    (rxt-match-test regexp "az"
                    '("az"))
    (rxt-match-test regexp "aaaz"
                    '("aa"))
    (rxt-match-test regexp "aa"
                    '("aa"))
    (rxt-match-test regexp "aaaa"
                    '("aa"))
    (rxt-match-test regexp "aa+"
                    '("aa"))))


(ert-deftest rxt-pcre-test-00048 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^\\d{8}\\w{2,}" "")))
    (rxt-match-test regexp "1234567890"
                    '("1234567890"))
    (rxt-match-test regexp "12345678ab"
                    '("12345678ab"))
    (rxt-match-test regexp "12345678__"
                    '("12345678__"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "1234567" 'nil)))


(ert-deftest rxt-pcre-test-00049 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^[aeiou\\d]{4,5}$" "")))
    (rxt-match-test regexp "uoie"
                    '("uoie"))
    (rxt-match-test regexp "1234"
                    '("1234"))
    (rxt-match-test regexp "12345"
                    '("12345"))
    (rxt-match-test regexp "aaaaa"
                    '("aaaaa"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "123456" 'nil)))


(ert-deftest rxt-pcre-test-00050 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^[aeiou\\d]{4,5}?" "")))
    (rxt-match-test regexp "uoie"
                    '("uoie"))
    (rxt-match-test regexp "1234"
                    '("1234"))
    (rxt-match-test regexp "12345"
                    '("1234"))
    (rxt-match-test regexp "aaaaa"
                    '("aaaa"))
    (rxt-match-test regexp "123456"
                    '("1234"))))


(ert-deftest rxt-pcre-test-00051 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\A(abc|def)=(\\1){2,3}\\Z" "")))
    (rxt-match-test regexp "abc=abcabc"
                    '("abc=abcabc" "abc" "abc"))
    (rxt-match-test regexp "def=defdefdef"
                    '("def=defdefdef" "def" "def"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "abc=defdef" 'nil)))


(ert-deftest rxt-pcre-test-00052 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(a)(b)(c)(d)(e)(f)(g)(h)(i)(j)(k)\\11*(\\3\\4)\\1(?#)2$" "")))
    (rxt-match-test regexp "abcdefghijkcda2"
                    '("abcdefghijkcda2" "a" "b" "c" "d" "e" "f" "g" "h" "i" "j" "k" "cd"))
    (rxt-match-test regexp "abcdefghijkkkkcda2"
                    '("abcdefghijkkkkcda2" "a" "b" "c" "d" "e" "f" "g" "h" "i" "j" "k" "cd"))))


(ert-deftest rxt-pcre-test-00053 nil 
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(cat(a(ract|tonic)|erpillar)) \\1()2(3)" "")))
    (rxt-match-test regexp "cataract cataract23"
                    '("cataract cataract23" "cataract" "aract" "ract" "" "3"))
    (rxt-match-test regexp "catatonic catatonic23"
                    '("catatonic catatonic23" "catatonic" "atonic" "tonic" "" "3"))
    (rxt-match-test regexp "caterpillar caterpillar23"
                    '("caterpillar caterpillar23" "caterpillar" "erpillar" nil "" "3"))))


(ert-deftest rxt-pcre-test-00054 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^From +([^ ]+) +[a-zA-Z][a-zA-Z][a-zA-Z] +[a-zA-Z][a-zA-Z][a-zA-Z] +[0-9]?[0-9] +[0-9][0-9]:[0-9][0-9]" "")))
    (rxt-match-test regexp "From abcd  Mon Sep 01 12:33:02 1997"
                    '("From abcd  Mon Sep 01 12:33" "abcd"))))


(ert-deftest rxt-pcre-test-00055 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^From\\s+\\S+\\s+([a-zA-Z]{3}\\s+){2}\\d{1,2}\\s+\\d\\d:\\d\\d" "")))
    (rxt-match-test regexp "From abcd  Mon Sep 01 12:33:02 1997"
                    '("From abcd  Mon Sep 01 12:33" "Sep "))
    (rxt-match-test regexp "From abcd  Mon Sep  1 12:33:02 1997"
                    '("From abcd  Mon Sep  1 12:33" "Sep  "))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "From abcd  Sep 01 12:33:02 1997" 'nil)))


(ert-deftest rxt-pcre-test-00056 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^12.34" "s")))
    (rxt-match-test regexp "12\n34"
                    '("12\n34"))
    (rxt-match-test regexp "1234"
                    '("1234"))))


(ert-deftest rxt-pcre-test-00057 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\w+(?=\\t)" "")))
    (rxt-match-test regexp "the quick brown	 fox"
                    '("brown"))))


(ert-deftest rxt-pcre-test-00058 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "foo(?!bar)(.*)" "")))
    (rxt-match-test regexp "foobar is foolish see?"
                    '("foolish see?" "lish see?"))))


(ert-deftest rxt-pcre-test-00059 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?:(?!foo)...|^.{0,2})bar(.*)" "")))
    (rxt-match-test regexp "foobar crowbar etc"
                    '("rowbar etc" " etc"))
    (rxt-match-test regexp "barrel"
                    '("barrel" "rel"))
    (rxt-match-test regexp "2barrel"
                    '("2barrel" "rel"))
    (rxt-match-test regexp "A barrel"
                    '("A barrel" "rel"))))


(ert-deftest rxt-pcre-test-00060 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(\\D*)(?=\\d)(?!123)" "")))
    (rxt-match-test regexp "abc456"
                    '("abc" "abc"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "abc123" 'nil)))


(ert-deftest rxt-pcre-test-00061 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^1234(?# test newlines\n  inside)" "")))
    (rxt-match-test regexp "1234"
                    '("1234"))))


(ert-deftest rxt-pcre-test-00062 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^1234 #comment in extended re\n  " "x")))
    (rxt-match-test regexp "1234"
                    '("1234"))))


(ert-deftest rxt-pcre-test-00063 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "#rhubarb\n  abcd" "x")))
    (rxt-match-test regexp "abcd"
                    '("abcd"))))


(ert-deftest rxt-pcre-test-00064 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^abcd#rhubarb" "x")))
    (rxt-match-test regexp "abcd"
                    '("abcd"))))


(ert-deftest rxt-pcre-test-00065 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(a)\\1{2,3}(.)" "")))
    (rxt-match-test regexp "aaab"
                    '("aaab" "a" "b"))
    (rxt-match-test regexp "aaaab"
                    '("aaaab" "a" "b"))
    (rxt-match-test regexp "aaaaab"
                    '("aaaaa" "a" "a"))
    (rxt-match-test regexp "aaaaaab"
                    '("aaaaa" "a" "a"))))


(ert-deftest rxt-pcre-test-00066 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?!^)abc" "")))
    (rxt-match-test regexp "the abc"
                    '("abc"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "abc" 'nil)))


(ert-deftest rxt-pcre-test-00067 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?=^)abc" "")))
    (rxt-match-test regexp "abc"
                    '("abc"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "the abc" 'nil)))


(ert-deftest rxt-pcre-test-00068 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^[ab]{1,3}(ab*|b)" "")))
    (rxt-match-test regexp "aabbbbb"
                    '("aabb" "b"))))


(ert-deftest rxt-pcre-test-00069 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^[ab]{1,3}?(ab*|b)" "")))
    (rxt-match-test regexp "aabbbbb"
                    '("aabbbbb" "abbbbb"))))


(ert-deftest rxt-pcre-test-00070 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^[ab]{1,3}?(ab*?|b)" "")))
    (rxt-match-test regexp "aabbbbb"
                    '("aa" "a"))))


(ert-deftest rxt-pcre-test-00071 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^[ab]{1,3}(ab*?|b)" "")))
    (rxt-match-test regexp "aabbbbb"
                    '("aabb" "b"))))


(ert-deftest rxt-pcre-test-00072 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "  (?: [\\040\\t] |  \\(\n(?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  |  \\( (?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  )* \\)  )*\n\\)  )*                          # optional leading comment\n(?:    (?:\n[^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]+    # some number of atom characters...\n(?![^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]) # ..not followed by something that could be part of an atom\n|\n\" (?:                      # opening quote...\n[^\\\\\\x80-\\xff\\n\\015\"]                #   Anything except backslash and quote\n|                     #    or\n\\\\ [^\\x80-\\xff]           #   Escaped something (something != CR)\n)* \"  # closing quote\n)                    # initial word\n(?:  (?: [\\040\\t] |  \\(\n(?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  |  \\( (?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  )* \\)  )*\n\\)  )*  \\.  (?: [\\040\\t] |  \\(\n(?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  |  \\( (?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  )* \\)  )*\n\\)  )*   (?:\n[^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]+    # some number of atom characters...\n(?![^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]) # ..not followed by something that could be part of an atom\n|\n\" (?:                      # opening quote...\n[^\\\\\\x80-\\xff\\n\\015\"]                #   Anything except backslash and quote\n|                     #    or\n\\\\ [^\\x80-\\xff]           #   Escaped something (something != CR)\n)* \"  # closing quote\n)  )* # further okay, if led by a period\n(?: [\\040\\t] |  \\(\n(?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  |  \\( (?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  )* \\)  )*\n\\)  )*  @  (?: [\\040\\t] |  \\(\n(?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  |  \\( (?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  )* \\)  )*\n\\)  )*    (?:\n[^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]+    # some number of atom characters...\n(?![^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]) # ..not followed by something that could be part of an atom\n|   \\[                         # [\n(?: [^\\\\\\x80-\\xff\\n\\015\\[\\]] |  \\\\ [^\\x80-\\xff]  )*    #    stuff\n\\]                        #           ]\n)                           # initial subdomain\n(?:                                  #\n(?: [\\040\\t] |  \\(\n(?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  |  \\( (?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  )* \\)  )*\n\\)  )*  \\.                        # if led by a period...\n(?: [\\040\\t] |  \\(\n(?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  |  \\( (?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  )* \\)  )*\n\\)  )*   (?:\n[^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]+    # some number of atom characters...\n(?![^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]) # ..not followed by something that could be part of an atom\n|   \\[                         # [\n(?: [^\\\\\\x80-\\xff\\n\\015\\[\\]] |  \\\\ [^\\x80-\\xff]  )*    #    stuff\n\\]                        #           ]\n)                     #   ...further okay\n)*\n# address\n|                     #  or\n(?:\n[^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]+    # some number of atom characters...\n(?![^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]) # ..not followed by something that could be part of an atom\n|\n\" (?:                      # opening quote...\n[^\\\\\\x80-\\xff\\n\\015\"]                #   Anything except backslash and quote\n|                     #    or\n\\\\ [^\\x80-\\xff]           #   Escaped something (something != CR)\n)* \"  # closing quote\n)             # one word, optionally followed by....\n(?:\n[^()<>@,;:\".\\\\\\[\\]\\x80-\\xff\\000-\\010\\012-\\037]  |  # atom and space parts, or...\n\\(\n(?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  |  \\( (?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  )* \\)  )*\n\\)       |  # comments, or...\n\n\" (?:                      # opening quote...\n[^\\\\\\x80-\\xff\\n\\015\"]                #   Anything except backslash and quote\n|                     #    or\n\\\\ [^\\x80-\\xff]           #   Escaped something (something != CR)\n)* \"  # closing quote\n# quoted strings\n)*\n<  (?: [\\040\\t] |  \\(\n(?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  |  \\( (?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  )* \\)  )*\n\\)  )*                     # leading <\n(?:  @  (?: [\\040\\t] |  \\(\n(?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  |  \\( (?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  )* \\)  )*\n\\)  )*    (?:\n[^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]+    # some number of atom characters...\n(?![^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]) # ..not followed by something that could be part of an atom\n|   \\[                         # [\n(?: [^\\\\\\x80-\\xff\\n\\015\\[\\]] |  \\\\ [^\\x80-\\xff]  )*    #    stuff\n\\]                        #           ]\n)                           # initial subdomain\n(?:                                  #\n(?: [\\040\\t] |  \\(\n(?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  |  \\( (?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  )* \\)  )*\n\\)  )*  \\.                        # if led by a period...\n(?: [\\040\\t] |  \\(\n(?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  |  \\( (?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  )* \\)  )*\n\\)  )*   (?:\n[^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]+    # some number of atom characters...\n(?![^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]) # ..not followed by something that could be part of an atom\n|   \\[                         # [\n(?: [^\\\\\\x80-\\xff\\n\\015\\[\\]] |  \\\\ [^\\x80-\\xff]  )*    #    stuff\n\\]                        #           ]\n)                     #   ...further okay\n)*\n\n(?:  (?: [\\040\\t] |  \\(\n(?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  |  \\( (?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  )* \\)  )*\n\\)  )*  ,  (?: [\\040\\t] |  \\(\n(?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  |  \\( (?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  )* \\)  )*\n\\)  )*  @  (?: [\\040\\t] |  \\(\n(?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  |  \\( (?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  )* \\)  )*\n\\)  )*    (?:\n[^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]+    # some number of atom characters...\n(?![^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]) # ..not followed by something that could be part of an atom\n|   \\[                         # [\n(?: [^\\\\\\x80-\\xff\\n\\015\\[\\]] |  \\\\ [^\\x80-\\xff]  )*    #    stuff\n\\]                        #           ]\n)                           # initial subdomain\n(?:                                  #\n(?: [\\040\\t] |  \\(\n(?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  |  \\( (?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  )* \\)  )*\n\\)  )*  \\.                        # if led by a period...\n(?: [\\040\\t] |  \\(\n(?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  |  \\( (?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  )* \\)  )*\n\\)  )*   (?:\n[^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]+    # some number of atom characters...\n(?![^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]) # ..not followed by something that could be part of an atom\n|   \\[                         # [\n(?: [^\\\\\\x80-\\xff\\n\\015\\[\\]] |  \\\\ [^\\x80-\\xff]  )*    #    stuff\n\\]                        #           ]\n)                     #   ...further okay\n)*\n)* # further okay, if led by comma\n:                                # closing colon\n(?: [\\040\\t] |  \\(\n(?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  |  \\( (?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  )* \\)  )*\n\\)  )*  )? #       optional route\n(?:\n[^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]+    # some number of atom characters...\n(?![^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]) # ..not followed by something that could be part of an atom\n|\n\" (?:                      # opening quote...\n[^\\\\\\x80-\\xff\\n\\015\"]                #   Anything except backslash and quote\n|                     #    or\n\\\\ [^\\x80-\\xff]           #   Escaped something (something != CR)\n)* \"  # closing quote\n)                    # initial word\n(?:  (?: [\\040\\t] |  \\(\n(?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  |  \\( (?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  )* \\)  )*\n\\)  )*  \\.  (?: [\\040\\t] |  \\(\n(?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  |  \\( (?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  )* \\)  )*\n\\)  )*   (?:\n[^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]+    # some number of atom characters...\n(?![^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]) # ..not followed by something that could be part of an atom\n|\n\" (?:                      # opening quote...\n[^\\\\\\x80-\\xff\\n\\015\"]                #   Anything except backslash and quote\n|                     #    or\n\\\\ [^\\x80-\\xff]           #   Escaped something (something != CR)\n)* \"  # closing quote\n)  )* # further okay, if led by a period\n(?: [\\040\\t] |  \\(\n(?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  |  \\( (?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  )* \\)  )*\n\\)  )*  @  (?: [\\040\\t] |  \\(\n(?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  |  \\( (?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  )* \\)  )*\n\\)  )*    (?:\n[^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]+    # some number of atom characters...\n(?![^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]) # ..not followed by something that could be part of an atom\n|   \\[                         # [\n(?: [^\\\\\\x80-\\xff\\n\\015\\[\\]] |  \\\\ [^\\x80-\\xff]  )*    #    stuff\n\\]                        #           ]\n)                           # initial subdomain\n(?:                                  #\n(?: [\\040\\t] |  \\(\n(?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  |  \\( (?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  )* \\)  )*\n\\)  )*  \\.                        # if led by a period...\n(?: [\\040\\t] |  \\(\n(?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  |  \\( (?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  )* \\)  )*\n\\)  )*   (?:\n[^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]+    # some number of atom characters...\n(?![^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]) # ..not followed by something that could be part of an atom\n|   \\[                         # [\n(?: [^\\\\\\x80-\\xff\\n\\015\\[\\]] |  \\\\ [^\\x80-\\xff]  )*    #    stuff\n\\]                        #           ]\n)                     #   ...further okay\n)*\n#       address spec\n(?: [\\040\\t] |  \\(\n(?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  |  \\( (?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  )* \\)  )*\n\\)  )*  > #                  trailing >\n# name and address\n)  (?: [\\040\\t] |  \\(\n(?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  |  \\( (?:  [^\\\\\\x80-\\xff\\n\\015()]  |  \\\\ [^\\x80-\\xff]  )* \\)  )*\n\\)  )*                       # optional trailing comment\n" "x")))
    (rxt-match-test regexp "Alan Other <user@dom.ain>"
                    '("Alan Other <user@dom.ain>"))
    (rxt-match-test regexp "<user@dom.ain>"
                    '("user@dom.ain"))
    (rxt-match-test regexp "user@dom.ain"
                    '("user@dom.ain"))
    (rxt-match-test regexp "\"A. Other\" <user.1234@dom.ain> (a comment)"
                    '("\"A. Other\" <user.1234@dom.ain> (a comment)"))
    (rxt-match-test regexp "A. Other <user.1234@dom.ain> (a comment)"
                    '(" Other <user.1234@dom.ain> (a comment)"))
    (rxt-match-test regexp "\"/s=user/ou=host/o=place/prmd=uu.yy/admd= /c=gb/\"@x400-re.lay"
                    '("\"/s=user/ou=host/o=place/prmd=uu.yy/admd= /c=gb/\"@x400-re.lay"))
    (rxt-match-test regexp "A missing angle <user@some.where"
                    '("user@some.where"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "The quick brown fox" 'nil)))


(ert-deftest rxt-pcre-test-00073 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[\\040\\t]*                    # Nab whitespace.\n(?:\n\\(                              #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                             #     normal*\n(?:                                 #       (\n(?:  \\\\ [^\\x80-\\xff]  |\n\\(                            #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                            #     normal*\n(?:  \\\\ [^\\x80-\\xff]   [^\\\\\\x80-\\xff\\n\\015()] * )*        #     (special normal*)*\n\\)                           #                       )\n)    #         special\n[^\\\\\\x80-\\xff\\n\\015()] *                         #         normal*\n)*                                  #            )*\n\\)                             #                )\n[\\040\\t]* )*    # If comment found, allow more spaces.\n# optional leading comment\n(?:\n(?:\n[^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]+    # some number of atom characters...\n(?![^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]) # ..not followed by something that could be part of an atom\n# Atom\n|                       #  or\n\"                                     # \"\n[^\\\\\\x80-\\xff\\n\\015\"] *                            #   normal\n(?:  \\\\ [^\\x80-\\xff]  [^\\\\\\x80-\\xff\\n\\015\"] * )*        #   ( special normal* )*\n\"                                     #        \"\n# Quoted string\n)\n[\\040\\t]*                    # Nab whitespace.\n(?:\n\\(                              #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                             #     normal*\n(?:                                 #       (\n(?:  \\\\ [^\\x80-\\xff]  |\n\\(                            #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                            #     normal*\n(?:  \\\\ [^\\x80-\\xff]   [^\\\\\\x80-\\xff\\n\\015()] * )*        #     (special normal*)*\n\\)                           #                       )\n)    #         special\n[^\\\\\\x80-\\xff\\n\\015()] *                         #         normal*\n)*                                  #            )*\n\\)                             #                )\n[\\040\\t]* )*    # If comment found, allow more spaces.\n(?:\n\\.\n[\\040\\t]*                    # Nab whitespace.\n(?:\n\\(                              #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                             #     normal*\n(?:                                 #       (\n(?:  \\\\ [^\\x80-\\xff]  |\n\\(                            #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                            #     normal*\n(?:  \\\\ [^\\x80-\\xff]   [^\\\\\\x80-\\xff\\n\\015()] * )*        #     (special normal*)*\n\\)                           #                       )\n)    #         special\n[^\\\\\\x80-\\xff\\n\\015()] *                         #         normal*\n)*                                  #            )*\n\\)                             #                )\n[\\040\\t]* )*    # If comment found, allow more spaces.\n(?:\n[^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]+    # some number of atom characters...\n(?![^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]) # ..not followed by something that could be part of an atom\n# Atom\n|                       #  or\n\"                                     # \"\n[^\\\\\\x80-\\xff\\n\\015\"] *                            #   normal\n(?:  \\\\ [^\\x80-\\xff]  [^\\\\\\x80-\\xff\\n\\015\"] * )*        #   ( special normal* )*\n\"                                     #        \"\n# Quoted string\n)\n[\\040\\t]*                    # Nab whitespace.\n(?:\n\\(                              #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                             #     normal*\n(?:                                 #       (\n(?:  \\\\ [^\\x80-\\xff]  |\n\\(                            #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                            #     normal*\n(?:  \\\\ [^\\x80-\\xff]   [^\\\\\\x80-\\xff\\n\\015()] * )*        #     (special normal*)*\n\\)                           #                       )\n)    #         special\n[^\\\\\\x80-\\xff\\n\\015()] *                         #         normal*\n)*                                  #            )*\n\\)                             #                )\n[\\040\\t]* )*    # If comment found, allow more spaces.\n# additional words\n)*\n@\n[\\040\\t]*                    # Nab whitespace.\n(?:\n\\(                              #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                             #     normal*\n(?:                                 #       (\n(?:  \\\\ [^\\x80-\\xff]  |\n\\(                            #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                            #     normal*\n(?:  \\\\ [^\\x80-\\xff]   [^\\\\\\x80-\\xff\\n\\015()] * )*        #     (special normal*)*\n\\)                           #                       )\n)    #         special\n[^\\\\\\x80-\\xff\\n\\015()] *                         #         normal*\n)*                                  #            )*\n\\)                             #                )\n[\\040\\t]* )*    # If comment found, allow more spaces.\n(?:\n[^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]+    # some number of atom characters...\n(?![^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]) # ..not followed by something that could be part of an atom\n|\n\\[                            # [\n(?: [^\\\\\\x80-\\xff\\n\\015\\[\\]] |  \\\\ [^\\x80-\\xff]  )*     #    stuff\n\\]                           #           ]\n)\n[\\040\\t]*                    # Nab whitespace.\n(?:\n\\(                              #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                             #     normal*\n(?:                                 #       (\n(?:  \\\\ [^\\x80-\\xff]  |\n\\(                            #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                            #     normal*\n(?:  \\\\ [^\\x80-\\xff]   [^\\\\\\x80-\\xff\\n\\015()] * )*        #     (special normal*)*\n\\)                           #                       )\n)    #         special\n[^\\\\\\x80-\\xff\\n\\015()] *                         #         normal*\n)*                                  #            )*\n\\)                             #                )\n[\\040\\t]* )*    # If comment found, allow more spaces.\n# optional trailing comments\n(?:\n\\.\n[\\040\\t]*                    # Nab whitespace.\n(?:\n\\(                              #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                             #     normal*\n(?:                                 #       (\n(?:  \\\\ [^\\x80-\\xff]  |\n\\(                            #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                            #     normal*\n(?:  \\\\ [^\\x80-\\xff]   [^\\\\\\x80-\\xff\\n\\015()] * )*        #     (special normal*)*\n\\)                           #                       )\n)    #         special\n[^\\\\\\x80-\\xff\\n\\015()] *                         #         normal*\n)*                                  #            )*\n\\)                             #                )\n[\\040\\t]* )*    # If comment found, allow more spaces.\n(?:\n[^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]+    # some number of atom characters...\n(?![^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]) # ..not followed by something that could be part of an atom\n|\n\\[                            # [\n(?: [^\\\\\\x80-\\xff\\n\\015\\[\\]] |  \\\\ [^\\x80-\\xff]  )*     #    stuff\n\\]                           #           ]\n)\n[\\040\\t]*                    # Nab whitespace.\n(?:\n\\(                              #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                             #     normal*\n(?:                                 #       (\n(?:  \\\\ [^\\x80-\\xff]  |\n\\(                            #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                            #     normal*\n(?:  \\\\ [^\\x80-\\xff]   [^\\\\\\x80-\\xff\\n\\015()] * )*        #     (special normal*)*\n\\)                           #                       )\n)    #         special\n[^\\\\\\x80-\\xff\\n\\015()] *                         #         normal*\n)*                                  #            )*\n\\)                             #                )\n[\\040\\t]* )*    # If comment found, allow more spaces.\n# optional trailing comments\n)*\n# address\n|                             #  or\n(?:\n[^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]+    # some number of atom characters...\n(?![^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]) # ..not followed by something that could be part of an atom\n# Atom\n|                       #  or\n\"                                     # \"\n[^\\\\\\x80-\\xff\\n\\015\"] *                            #   normal\n(?:  \\\\ [^\\x80-\\xff]  [^\\\\\\x80-\\xff\\n\\015\"] * )*        #   ( special normal* )*\n\"                                     #        \"\n# Quoted string\n)\n# leading word\n[^()<>@,;:\".\\\\\\[\\]\\x80-\\xff\\000-\\010\\012-\\037] *               # \"normal\" atoms and or spaces\n(?:\n(?:\n\\(                              #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                             #     normal*\n(?:                                 #       (\n(?:  \\\\ [^\\x80-\\xff]  |\n\\(                            #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                            #     normal*\n(?:  \\\\ [^\\x80-\\xff]   [^\\\\\\x80-\\xff\\n\\015()] * )*        #     (special normal*)*\n\\)                           #                       )\n)    #         special\n[^\\\\\\x80-\\xff\\n\\015()] *                         #         normal*\n)*                                  #            )*\n\\)                             #                )\n|\n\"                                     # \"\n[^\\\\\\x80-\\xff\\n\\015\"] *                            #   normal\n(?:  \\\\ [^\\x80-\\xff]  [^\\\\\\x80-\\xff\\n\\015\"] * )*        #   ( special normal* )*\n\"                                     #        \"\n) # \"special\" comment or quoted string\n[^()<>@,;:\".\\\\\\[\\]\\x80-\\xff\\000-\\010\\012-\\037] *            #  more \"normal\"\n)*\n<\n[\\040\\t]*                    # Nab whitespace.\n(?:\n\\(                              #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                             #     normal*\n(?:                                 #       (\n(?:  \\\\ [^\\x80-\\xff]  |\n\\(                            #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                            #     normal*\n(?:  \\\\ [^\\x80-\\xff]   [^\\\\\\x80-\\xff\\n\\015()] * )*        #     (special normal*)*\n\\)                           #                       )\n)    #         special\n[^\\\\\\x80-\\xff\\n\\015()] *                         #         normal*\n)*                                  #            )*\n\\)                             #                )\n[\\040\\t]* )*    # If comment found, allow more spaces.\n# <\n(?:\n@\n[\\040\\t]*                    # Nab whitespace.\n(?:\n\\(                              #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                             #     normal*\n(?:                                 #       (\n(?:  \\\\ [^\\x80-\\xff]  |\n\\(                            #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                            #     normal*\n(?:  \\\\ [^\\x80-\\xff]   [^\\\\\\x80-\\xff\\n\\015()] * )*        #     (special normal*)*\n\\)                           #                       )\n)    #         special\n[^\\\\\\x80-\\xff\\n\\015()] *                         #         normal*\n)*                                  #            )*\n\\)                             #                )\n[\\040\\t]* )*    # If comment found, allow more spaces.\n(?:\n[^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]+    # some number of atom characters...\n(?![^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]) # ..not followed by something that could be part of an atom\n|\n\\[                            # [\n(?: [^\\\\\\x80-\\xff\\n\\015\\[\\]] |  \\\\ [^\\x80-\\xff]  )*     #    stuff\n\\]                           #           ]\n)\n[\\040\\t]*                    # Nab whitespace.\n(?:\n\\(                              #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                             #     normal*\n(?:                                 #       (\n(?:  \\\\ [^\\x80-\\xff]  |\n\\(                            #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                            #     normal*\n(?:  \\\\ [^\\x80-\\xff]   [^\\\\\\x80-\\xff\\n\\015()] * )*        #     (special normal*)*\n\\)                           #                       )\n)    #         special\n[^\\\\\\x80-\\xff\\n\\015()] *                         #         normal*\n)*                                  #            )*\n\\)                             #                )\n[\\040\\t]* )*    # If comment found, allow more spaces.\n# optional trailing comments\n(?:\n\\.\n[\\040\\t]*                    # Nab whitespace.\n(?:\n\\(                              #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                             #     normal*\n(?:                                 #       (\n(?:  \\\\ [^\\x80-\\xff]  |\n\\(                            #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                            #     normal*\n(?:  \\\\ [^\\x80-\\xff]   [^\\\\\\x80-\\xff\\n\\015()] * )*        #     (special normal*)*\n\\)                           #                       )\n)    #         special\n[^\\\\\\x80-\\xff\\n\\015()] *                         #         normal*\n)*                                  #            )*\n\\)                             #                )\n[\\040\\t]* )*    # If comment found, allow more spaces.\n(?:\n[^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]+    # some number of atom characters...\n(?![^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]) # ..not followed by something that could be part of an atom\n|\n\\[                            # [\n(?: [^\\\\\\x80-\\xff\\n\\015\\[\\]] |  \\\\ [^\\x80-\\xff]  )*     #    stuff\n\\]                           #           ]\n)\n[\\040\\t]*                    # Nab whitespace.\n(?:\n\\(                              #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                             #     normal*\n(?:                                 #       (\n(?:  \\\\ [^\\x80-\\xff]  |\n\\(                            #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                            #     normal*\n(?:  \\\\ [^\\x80-\\xff]   [^\\\\\\x80-\\xff\\n\\015()] * )*        #     (special normal*)*\n\\)                           #                       )\n)    #         special\n[^\\\\\\x80-\\xff\\n\\015()] *                         #         normal*\n)*                                  #            )*\n\\)                             #                )\n[\\040\\t]* )*    # If comment found, allow more spaces.\n# optional trailing comments\n)*\n(?: ,\n[\\040\\t]*                    # Nab whitespace.\n(?:\n\\(                              #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                             #     normal*\n(?:                                 #       (\n(?:  \\\\ [^\\x80-\\xff]  |\n\\(                            #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                            #     normal*\n(?:  \\\\ [^\\x80-\\xff]   [^\\\\\\x80-\\xff\\n\\015()] * )*        #     (special normal*)*\n\\)                           #                       )\n)    #         special\n[^\\\\\\x80-\\xff\\n\\015()] *                         #         normal*\n)*                                  #            )*\n\\)                             #                )\n[\\040\\t]* )*    # If comment found, allow more spaces.\n@\n[\\040\\t]*                    # Nab whitespace.\n(?:\n\\(                              #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                             #     normal*\n(?:                                 #       (\n(?:  \\\\ [^\\x80-\\xff]  |\n\\(                            #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                            #     normal*\n(?:  \\\\ [^\\x80-\\xff]   [^\\\\\\x80-\\xff\\n\\015()] * )*        #     (special normal*)*\n\\)                           #                       )\n)    #         special\n[^\\\\\\x80-\\xff\\n\\015()] *                         #         normal*\n)*                                  #            )*\n\\)                             #                )\n[\\040\\t]* )*    # If comment found, allow more spaces.\n(?:\n[^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]+    # some number of atom characters...\n(?![^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]) # ..not followed by something that could be part of an atom\n|\n\\[                            # [\n(?: [^\\\\\\x80-\\xff\\n\\015\\[\\]] |  \\\\ [^\\x80-\\xff]  )*     #    stuff\n\\]                           #           ]\n)\n[\\040\\t]*                    # Nab whitespace.\n(?:\n\\(                              #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                             #     normal*\n(?:                                 #       (\n(?:  \\\\ [^\\x80-\\xff]  |\n\\(                            #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                            #     normal*\n(?:  \\\\ [^\\x80-\\xff]   [^\\\\\\x80-\\xff\\n\\015()] * )*        #     (special normal*)*\n\\)                           #                       )\n)    #         special\n[^\\\\\\x80-\\xff\\n\\015()] *                         #         normal*\n)*                                  #            )*\n\\)                             #                )\n[\\040\\t]* )*    # If comment found, allow more spaces.\n# optional trailing comments\n(?:\n\\.\n[\\040\\t]*                    # Nab whitespace.\n(?:\n\\(                              #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                             #     normal*\n(?:                                 #       (\n(?:  \\\\ [^\\x80-\\xff]  |\n\\(                            #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                            #     normal*\n(?:  \\\\ [^\\x80-\\xff]   [^\\\\\\x80-\\xff\\n\\015()] * )*        #     (special normal*)*\n\\)                           #                       )\n)    #         special\n[^\\\\\\x80-\\xff\\n\\015()] *                         #         normal*\n)*                                  #            )*\n\\)                             #                )\n[\\040\\t]* )*    # If comment found, allow more spaces.\n(?:\n[^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]+    # some number of atom characters...\n(?![^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]) # ..not followed by something that could be part of an atom\n|\n\\[                            # [\n(?: [^\\\\\\x80-\\xff\\n\\015\\[\\]] |  \\\\ [^\\x80-\\xff]  )*     #    stuff\n\\]                           #           ]\n)\n[\\040\\t]*                    # Nab whitespace.\n(?:\n\\(                              #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                             #     normal*\n(?:                                 #       (\n(?:  \\\\ [^\\x80-\\xff]  |\n\\(                            #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                            #     normal*\n(?:  \\\\ [^\\x80-\\xff]   [^\\\\\\x80-\\xff\\n\\015()] * )*        #     (special normal*)*\n\\)                           #                       )\n)    #         special\n[^\\\\\\x80-\\xff\\n\\015()] *                         #         normal*\n)*                                  #            )*\n\\)                             #                )\n[\\040\\t]* )*    # If comment found, allow more spaces.\n# optional trailing comments\n)*\n)*  # additional domains\n:\n[\\040\\t]*                    # Nab whitespace.\n(?:\n\\(                              #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                             #     normal*\n(?:                                 #       (\n(?:  \\\\ [^\\x80-\\xff]  |\n\\(                            #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                            #     normal*\n(?:  \\\\ [^\\x80-\\xff]   [^\\\\\\x80-\\xff\\n\\015()] * )*        #     (special normal*)*\n\\)                           #                       )\n)    #         special\n[^\\\\\\x80-\\xff\\n\\015()] *                         #         normal*\n)*                                  #            )*\n\\)                             #                )\n[\\040\\t]* )*    # If comment found, allow more spaces.\n# optional trailing comments\n)?     #       optional route\n(?:\n[^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]+    # some number of atom characters...\n(?![^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]) # ..not followed by something that could be part of an atom\n# Atom\n|                       #  or\n\"                                     # \"\n[^\\\\\\x80-\\xff\\n\\015\"] *                            #   normal\n(?:  \\\\ [^\\x80-\\xff]  [^\\\\\\x80-\\xff\\n\\015\"] * )*        #   ( special normal* )*\n\"                                     #        \"\n# Quoted string\n)\n[\\040\\t]*                    # Nab whitespace.\n(?:\n\\(                              #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                             #     normal*\n(?:                                 #       (\n(?:  \\\\ [^\\x80-\\xff]  |\n\\(                            #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                            #     normal*\n(?:  \\\\ [^\\x80-\\xff]   [^\\\\\\x80-\\xff\\n\\015()] * )*        #     (special normal*)*\n\\)                           #                       )\n)    #         special\n[^\\\\\\x80-\\xff\\n\\015()] *                         #         normal*\n)*                                  #            )*\n\\)                             #                )\n[\\040\\t]* )*    # If comment found, allow more spaces.\n(?:\n\\.\n[\\040\\t]*                    # Nab whitespace.\n(?:\n\\(                              #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                             #     normal*\n(?:                                 #       (\n(?:  \\\\ [^\\x80-\\xff]  |\n\\(                            #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                            #     normal*\n(?:  \\\\ [^\\x80-\\xff]   [^\\\\\\x80-\\xff\\n\\015()] * )*        #     (special normal*)*\n\\)                           #                       )\n)    #         special\n[^\\\\\\x80-\\xff\\n\\015()] *                         #         normal*\n)*                                  #            )*\n\\)                             #                )\n[\\040\\t]* )*    # If comment found, allow more spaces.\n(?:\n[^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]+    # some number of atom characters...\n(?![^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]) # ..not followed by something that could be part of an atom\n# Atom\n|                       #  or\n\"                                     # \"\n[^\\\\\\x80-\\xff\\n\\015\"] *                            #   normal\n(?:  \\\\ [^\\x80-\\xff]  [^\\\\\\x80-\\xff\\n\\015\"] * )*        #   ( special normal* )*\n\"                                     #        \"\n# Quoted string\n)\n[\\040\\t]*                    # Nab whitespace.\n(?:\n\\(                              #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                             #     normal*\n(?:                                 #       (\n(?:  \\\\ [^\\x80-\\xff]  |\n\\(                            #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                            #     normal*\n(?:  \\\\ [^\\x80-\\xff]   [^\\\\\\x80-\\xff\\n\\015()] * )*        #     (special normal*)*\n\\)                           #                       )\n)    #         special\n[^\\\\\\x80-\\xff\\n\\015()] *                         #         normal*\n)*                                  #            )*\n\\)                             #                )\n[\\040\\t]* )*    # If comment found, allow more spaces.\n# additional words\n)*\n@\n[\\040\\t]*                    # Nab whitespace.\n(?:\n\\(                              #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                             #     normal*\n(?:                                 #       (\n(?:  \\\\ [^\\x80-\\xff]  |\n\\(                            #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                            #     normal*\n(?:  \\\\ [^\\x80-\\xff]   [^\\\\\\x80-\\xff\\n\\015()] * )*        #     (special normal*)*\n\\)                           #                       )\n)    #         special\n[^\\\\\\x80-\\xff\\n\\015()] *                         #         normal*\n)*                                  #            )*\n\\)                             #                )\n[\\040\\t]* )*    # If comment found, allow more spaces.\n(?:\n[^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]+    # some number of atom characters...\n(?![^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]) # ..not followed by something that could be part of an atom\n|\n\\[                            # [\n(?: [^\\\\\\x80-\\xff\\n\\015\\[\\]] |  \\\\ [^\\x80-\\xff]  )*     #    stuff\n\\]                           #           ]\n)\n[\\040\\t]*                    # Nab whitespace.\n(?:\n\\(                              #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                             #     normal*\n(?:                                 #       (\n(?:  \\\\ [^\\x80-\\xff]  |\n\\(                            #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                            #     normal*\n(?:  \\\\ [^\\x80-\\xff]   [^\\\\\\x80-\\xff\\n\\015()] * )*        #     (special normal*)*\n\\)                           #                       )\n)    #         special\n[^\\\\\\x80-\\xff\\n\\015()] *                         #         normal*\n)*                                  #            )*\n\\)                             #                )\n[\\040\\t]* )*    # If comment found, allow more spaces.\n# optional trailing comments\n(?:\n\\.\n[\\040\\t]*                    # Nab whitespace.\n(?:\n\\(                              #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                             #     normal*\n(?:                                 #       (\n(?:  \\\\ [^\\x80-\\xff]  |\n\\(                            #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                            #     normal*\n(?:  \\\\ [^\\x80-\\xff]   [^\\\\\\x80-\\xff\\n\\015()] * )*        #     (special normal*)*\n\\)                           #                       )\n)    #         special\n[^\\\\\\x80-\\xff\\n\\015()] *                         #         normal*\n)*                                  #            )*\n\\)                             #                )\n[\\040\\t]* )*    # If comment found, allow more spaces.\n(?:\n[^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]+    # some number of atom characters...\n(?![^(\\040)<>@,;:\".\\\\\\[\\]\\000-\\037\\x80-\\xff]) # ..not followed by something that could be part of an atom\n|\n\\[                            # [\n(?: [^\\\\\\x80-\\xff\\n\\015\\[\\]] |  \\\\ [^\\x80-\\xff]  )*     #    stuff\n\\]                           #           ]\n)\n[\\040\\t]*                    # Nab whitespace.\n(?:\n\\(                              #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                             #     normal*\n(?:                                 #       (\n(?:  \\\\ [^\\x80-\\xff]  |\n\\(                            #  (\n[^\\\\\\x80-\\xff\\n\\015()] *                            #     normal*\n(?:  \\\\ [^\\x80-\\xff]   [^\\\\\\x80-\\xff\\n\\015()] * )*        #     (special normal*)*\n\\)                           #                       )\n)    #         special\n[^\\\\\\x80-\\xff\\n\\015()] *                         #         normal*\n)*                                  #            )*\n\\)                             #                )\n[\\040\\t]* )*    # If comment found, allow more spaces.\n# optional trailing comments\n)*\n#       address spec\n>                    #                 >\n# name and address\n)\n" "x")))
    (rxt-match-test regexp "Alan Other <user@dom.ain>"
                    '("Alan Other <user@dom.ain>"))
    (rxt-match-test regexp "<user@dom.ain>"
                    '("user@dom.ain"))
    (rxt-match-test regexp "user@dom.ain"
                    '("user@dom.ain"))
    (rxt-match-test regexp "\"A. Other\" <user.1234@dom.ain> (a comment)"
                    '("\"A. Other\" <user.1234@dom.ain>"))
    (rxt-match-test regexp "A. Other <user.1234@dom.ain> (a comment)"
                    '(" Other <user.1234@dom.ain>"))
    (rxt-match-test regexp "\"/s=user/ou=host/o=place/prmd=uu.yy/admd= /c=gb/\"@x400-re.lay"
                    '("\"/s=user/ou=host/o=place/prmd=uu.yy/admd= /c=gb/\"@x400-re.lay"))
    (rxt-match-test regexp "A missing angle <user@some.where"
                    '("user@some.where"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "The quick brown fox" 'nil)))


(ert-deftest rxt-pcre-test-00074 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "abc\\0def\\00pqr\\000xyz\\0000AB" "")))
    (rxt-match-test regexp "abc def pqr xyz 0AB"
                    '("abc def pqr xyz 0AB"))
    (rxt-match-test regexp "abc456 abc def pqr xyz 0ABCDE"
                    '("abc def pqr xyz 0AB"))))


(ert-deftest rxt-pcre-test-00075 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "abc\\x0def\\x00pqr\\x000xyz\\x0000AB" "")))
    (rxt-match-test regexp "abcef pqr 0xyz 00AB"
                    '("abcef pqr 0xyz 00AB"))
    (rxt-match-test regexp "abc456 abcef pqr 0xyz 00ABCDE"
                    '("abcef pqr 0xyz 00AB"))))


(ert-deftest rxt-pcre-test-00076 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^[\\000-\\037]" "")))
    (rxt-match-test regexp " A"
                    '(" "))
    (rxt-match-test regexp "B"
                    '(""))
    (rxt-match-test regexp "C"
                    '(""))))


(ert-deftest rxt-pcre-test-00077 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\0*" "")))
    (rxt-match-test regexp "    "
                    '("    "))))


(ert-deftest rxt-pcre-test-00078 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "A\\x0{2,3}Z" "")))
    (rxt-match-test regexp "The A  Z"
                    '("A  Z"))
    (rxt-match-test regexp "An A   Z"
                    '("A   Z"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "A Z" 'nil)
    (rxt-match-test regexp "A    Z" 'nil)))


(ert-deftest rxt-pcre-test-00079 nil 
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(cow|)\\1(bell)" "")))
    (rxt-match-test regexp "cowcowbell"
                    '("cowcowbell" "cow" "bell"))
    (rxt-match-test regexp "bell"
                    '("bell" "" "bell"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "cowbell" 'nil)))


(ert-deftest rxt-pcre-test-00080 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^\\s" "")))
    (rxt-match-test regexp " abc"
                    '(" "))
    (rxt-match-test regexp "\fabc"
                    '("\f"))
    (rxt-match-test regexp "\nabc"
                    '("\n"))
    (rxt-match-test regexp "abc"
                    '(""))
    (rxt-match-test regexp "	abc"
                    '("	"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "abc" 'nil)))


(ert-deftest rxt-pcre-test-00081 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^a	b\n    \f  c" "x")))
    (rxt-match-test regexp "abc"
                    '("abc"))))


(ert-deftest rxt-pcre-test-00082 nil 
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(a|)\\1*b" "")))
    (rxt-match-test regexp "ab"
                    '("ab" "a"))
    (rxt-match-test regexp "aaaab"
                    '("aaaab" "a"))
    (rxt-match-test regexp "b"
                    '("b" ""))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "acb" 'nil)))


(ert-deftest rxt-pcre-test-00083 nil 
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(a|)\\1+b" "")))
    (rxt-match-test regexp "aab"
                    '("aab" "a"))
    (rxt-match-test regexp "aaaab"
                    '("aaaab" "a"))
    (rxt-match-test regexp "b"
                    '("b" ""))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "ab" 'nil)))


(ert-deftest rxt-pcre-test-00084 nil 
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(a|)\\1?b" "")))
    (rxt-match-test regexp "ab"
                    '("ab" "a"))
    (rxt-match-test regexp "aab"
                    '("aab" "a"))
    (rxt-match-test regexp "b"
                    '("b" ""))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "acb" 'nil)))


(ert-deftest rxt-pcre-test-00085 nil 
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(a|)\\1{2}b" "")))
    (rxt-match-test regexp "aaab"
                    '("aaab" "a"))
    (rxt-match-test regexp "b"
                    '("b" ""))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "ab" 'nil)
    (rxt-match-test regexp "aab" 'nil)
    (rxt-match-test regexp "aaaab" 'nil)))


(ert-deftest rxt-pcre-test-00086 nil 
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(a|)\\1{2,3}b" "")))
    (rxt-match-test regexp "aaab"
                    '("aaab" "a"))
    (rxt-match-test regexp "aaaab"
                    '("aaaab" "a"))
    (rxt-match-test regexp "b"
                    '("b" ""))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "ab" 'nil)
    (rxt-match-test regexp "aab" 'nil)
    (rxt-match-test regexp "aaaaab" 'nil)))


(ert-deftest rxt-pcre-test-00087 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab{1,3}bc" "")))
    (rxt-match-test regexp "abbbbc"
                    '("abbbbc"))
    (rxt-match-test regexp "abbbc"
                    '("abbbc"))
    (rxt-match-test regexp "abbc"
                    '("abbc"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "abc" 'nil)
    (rxt-match-test regexp "abbbbbc" 'nil)))


(ert-deftest rxt-pcre-test-00088 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "([^.]*)\\.([^:]*):[T ]+(.*)" "")))
    (rxt-match-test regexp "track1.title:TBlah blah blah"
                    '("track1.title:TBlah blah blah" "track1" "title" "Blah blah blah"))))


(ert-deftest rxt-pcre-test-00089 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "([^.]*)\\.([^:]*):[T ]+(.*)" "i")))
    (rxt-match-test regexp "track1.title:TBlah blah blah"
                    '("track1.title:TBlah blah blah" "track1" "title" "Blah blah blah"))))


(ert-deftest rxt-pcre-test-00090 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "([^.]*)\\.([^:]*):[t ]+(.*)" "i")))
    (rxt-match-test regexp "track1.title:TBlah blah blah"
                    '("track1.title:TBlah blah blah" "track1" "title" "Blah blah blah"))))


(ert-deftest rxt-pcre-test-00091 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^[W-c]+$" "")))
    (rxt-match-test regexp "WXY_^abc"
                    '("WXY_^abc"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "wxy" 'nil)))


(ert-deftest rxt-pcre-test-00092 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^[W-c]+$" "i")))
    (rxt-match-test regexp "WXY_^abc"
                    '("WXY_^abc"))
    (rxt-match-test regexp "wxy_^ABC"
                    '("wxy_^ABC"))))


(ert-deftest rxt-pcre-test-00093 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^[\\x3f-\\x5F]+$" "i")))
    (rxt-match-test regexp "WXY_^abc"
                    '("WXY_^abc"))
    (rxt-match-test regexp "wxy_^ABC"
                    '("wxy_^ABC"))))


(ert-deftest rxt-pcre-test-00094 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^abc$" "m")))
    (rxt-match-test regexp "abc"
                    '("abc"))
    (rxt-match-test regexp "qqq\nabc"
                    '("abc"))
    (rxt-match-test regexp "abc\nzzz"
                    '("abc"))
    (rxt-match-test regexp "qqq\nabc\nzzz"
                    '("abc"))))


(ert-deftest rxt-pcre-test-00095 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^abc$" "")))
    (rxt-match-test regexp "abc"
                    '("abc"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "qqq\nabc" 'nil)
    (rxt-match-test regexp "abc\nzzz" 'nil)
    (rxt-match-test regexp "qqq\nabc\nzzz" 'nil)))


(ert-deftest rxt-pcre-test-00096 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\Aabc\\Z" "m")))
    (rxt-match-test regexp "abc"
                    '("abc"))
    (rxt-match-test regexp "abc\n"
                    '("abc"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "qqq\nabc" 'nil)
    (rxt-match-test regexp "abc\nzzz" 'nil)
    (rxt-match-test regexp "qqq\nabc\nzzz" 'nil)))


(ert-deftest rxt-pcre-test-00097 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\A(.)*\\Z" "s")))
    (rxt-match-test regexp "abc\ndef"
                    '("abc\ndef" "f"))))


(ert-deftest rxt-pcre-test-00098 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\A(.)*\\Z" "m")))
    (rxt-match-test regexp "*** Failers"
                    '("*** Failers" "s"))
    (rxt-match-test regexp "abc\ndef" 'nil)))


(ert-deftest rxt-pcre-test-00099 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?:b)|(?::+)" "")))
    (rxt-match-test regexp "b::c"
                    '("b"))
    (rxt-match-test regexp "c::b"
                    '("::"))))


(ert-deftest rxt-pcre-test-00100 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[-az]+" "")))
    (rxt-match-test regexp "az-"
                    '("az-"))
    (rxt-match-test regexp "*** Failers"
                    '("a"))
    (rxt-match-test regexp "b" 'nil)))


(ert-deftest rxt-pcre-test-00101 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[az-]+" "")))
    (rxt-match-test regexp "za-"
                    '("za-"))
    (rxt-match-test regexp "*** Failers"
                    '("a"))
    (rxt-match-test regexp "b" 'nil)))


(ert-deftest rxt-pcre-test-00102 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[a\\-z]+" "")))
    (rxt-match-test regexp "a-z"
                    '("a-z"))
    (rxt-match-test regexp "*** Failers"
                    '("a"))
    (rxt-match-test regexp "b" 'nil)))


(ert-deftest rxt-pcre-test-00103 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[a-z]+" "")))
    (rxt-match-test regexp "abcdxyz"
                    '("abcdxyz"))))


(ert-deftest rxt-pcre-test-00104 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[\\d-]+" "")))
    (rxt-match-test regexp "12-34"
                    '("12-34"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "aaa" 'nil)))


(ert-deftest rxt-pcre-test-00105 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[\\d-z]+" "")))
    (rxt-match-test regexp "12-34z"
                    '("12-34z"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "aaa" 'nil)))


(ert-deftest rxt-pcre-test-00106 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\x5c" "")))
    (rxt-match-test regexp "\\"
                    '("\\"))))


(ert-deftest rxt-pcre-test-00107 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\x20Z" "")))
    (rxt-match-test regexp "the Zoo"
                    '(" Z"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "Zulu" 'nil)))


(ert-deftest rxt-pcre-test-00108 nil
  :expected-result :failed
  ;; The current method of faking case-folding behavior cannot make
  ;; backreferences behave case-insensitively.
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(abc)\\1" "i")))
    (rxt-match-test regexp "abcabc"
                    '("abcabc" "abc"))
    (rxt-match-test regexp "ABCabc"
                    '("ABCabc" "ABC"))
    (rxt-match-test regexp "abcABC"
                    '("abcABC" "abc"))))


(ert-deftest rxt-pcre-test-00109 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab{3cd" "")))
    (rxt-match-test regexp "ab{3cd"
                    '("ab{3cd"))))


(ert-deftest rxt-pcre-test-00110 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab{3,cd" "")))
    (rxt-match-test regexp "ab{3,cd"
                    '("ab{3,cd"))))


(ert-deftest rxt-pcre-test-00111 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab{3,4a}cd" "")))
    (rxt-match-test regexp "ab{3,4a}cd"
                    '("ab{3,4a}cd"))))


(ert-deftest rxt-pcre-test-00112 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "{4,5a}bc" "")))
    (rxt-match-test regexp "{4,5a}bc"
                    '("{4,5a}bc"))))


(ert-deftest rxt-pcre-test-00113 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "abc$" "")))
    (rxt-match-test regexp "abc"
                    '("abc"))
    (rxt-match-test regexp "abc\n"
                    '("abc"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "abc\ndef" 'nil)))


(ert-deftest rxt-pcre-test-00114 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(abc)\\123" "")))
    (rxt-match-test regexp "abcS"
                    '("abcS" "abc"))))


(ert-deftest rxt-pcre-test-00115 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(abc)\\223" "")))
    (rxt-match-test regexp "abc\223"
                    '("abc\223" "abc"))))


(ert-deftest rxt-pcre-test-00116 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(abc)\\323" "")))
    (rxt-match-test regexp "abc\323"
                    '("abc\323" "abc"))))


(ert-deftest rxt-pcre-test-00117 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(abc)\\100" "")))
    (rxt-match-test regexp "abc@"
                    '("abc@" "abc"))
    (rxt-match-test regexp "abc@"
                    '("abc@" "abc"))))


(ert-deftest rxt-pcre-test-00118 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(abc)\\1000" "")))
    (rxt-match-test regexp "abc@0"
                    '("abc@0" "abc"))
    (rxt-match-test regexp "abc@0"
                    '("abc@0" "abc"))
    (rxt-match-test regexp "abc@0"
                    '("abc@0" "abc"))
    (rxt-match-test regexp "abc@0"
                    '("abc@0" "abc"))
    (rxt-match-test regexp "abc@0"
                    '("abc@0" "abc"))
    (rxt-match-test regexp "abc@0"
                    '("abc@0" "abc"))))


(ert-deftest rxt-pcre-test-00119 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "abc\\81" "")))
    (rxt-match-test regexp "abc 81"
                    '("abc 81"))
    (rxt-match-test regexp "abc 81"
                    '("abc 81"))))


(ert-deftest rxt-pcre-test-00120 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "abc\\91" "")))
    (rxt-match-test regexp "abc 91"
                    '("abc 91"))
    (rxt-match-test regexp "abc 91"
                    '("abc 91"))))


(ert-deftest rxt-pcre-test-00121 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(a)(b)(c)(d)(e)(f)(g)(h)(i)(j)(k)(l)\\12\\123" "")))
    (rxt-match-test regexp "abcdefghijkllS"
                    '("abcdefghijkllS" "a" "b" "c" "d" "e" "f" "g" "h" "i" "j" "k" "l"))))


(ert-deftest rxt-pcre-test-00122 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(a)(b)(c)(d)(e)(f)(g)(h)(i)(j)(k)\\12\\123" "")))
    (rxt-match-test regexp "abcdefghijk\nS"
                    '("abcdefghijk\nS" "a" "b" "c" "d" "e" "f" "g" "h" "i" "j" "k"))))


(ert-deftest rxt-pcre-test-00123 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab\\idef" "")))
    (rxt-match-test regexp "abidef"
                    '("abidef"))))


(ert-deftest rxt-pcre-test-00124 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a{0}bc" "")))
    (rxt-match-test regexp "bc"
                    '("bc"))))


(ert-deftest rxt-pcre-test-00125 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(a|(bc)){0,0}?xyz" "")))
    (rxt-match-test regexp "xyz"
                    '("xyz"))))


(ert-deftest rxt-pcre-test-00126 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "abc[\\10]de" "")))
    (rxt-match-test regexp "abcde"
                    '("abcde"))))


(ert-deftest rxt-pcre-test-00127 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "abc[\\1]de" "")))
    (rxt-match-test regexp "abcde"
                    '("abcde"))))


(ert-deftest rxt-pcre-test-00128 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(abc)[\\1]de" "")))
    (rxt-match-test regexp "abcde"
                    '("abcde" "abc"))))


(ert-deftest rxt-pcre-test-00129 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?s)a.b" "")))
    (rxt-match-test regexp "a\nb"
                    '("a\nb"))))


(ert-deftest rxt-pcre-test-00130 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^([^a])([^\\b])([^c]*)([^d]{3,4})" "")))
    (rxt-match-test regexp "baNOTccccd"
                    '("baNOTcccc" "b" "a" "NOT" "cccc"))
    (rxt-match-test regexp "baNOTcccd"
                    '("baNOTccc" "b" "a" "NOT" "ccc"))
    (rxt-match-test regexp "baNOTccd"
                    '("baNOTcc" "b" "a" "NO" "Tcc"))
    (rxt-match-test regexp "bacccd"
                    '("baccc" "b" "a" "" "ccc"))
    (rxt-match-test regexp "*** Failers"
                    '("*** Failers" "*" "*" "* Fail" "ers"))
    (rxt-match-test regexp "anything" 'nil)
    (rxt-match-test regexp "bc" 'nil)
    (rxt-match-test regexp "baccd" 'nil)))


(ert-deftest rxt-pcre-test-00131 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[^a]" "")))
    (rxt-match-test regexp "Abc"
                    '("A"))))


(ert-deftest rxt-pcre-test-00132 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[^a]" "i")))
    (rxt-match-test regexp "Abc"
                    '("b"))))


(ert-deftest rxt-pcre-test-00133 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[^a]+" "")))
    (rxt-match-test regexp "AAAaAbc"
                    '("AAA"))))


(ert-deftest rxt-pcre-test-00134 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[^a]+" "i")))
    (rxt-match-test regexp "AAAaAbc"
                    '("bc"))))


(ert-deftest rxt-pcre-test-00135 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[^a]+" "")))
    (rxt-match-test regexp "bbb\nccc"
                    '("bbb\nccc"))))


(ert-deftest rxt-pcre-test-00136 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[^k]$" "")))
    (rxt-match-test regexp "abc"
                    '("c"))
    (rxt-match-test regexp "*** Failers"
                    '("s"))
    (rxt-match-test regexp "abk" 'nil)))


(ert-deftest rxt-pcre-test-00137 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[^k]{2,3}$" "")))
    (rxt-match-test regexp "abc"
                    '("abc"))
    (rxt-match-test regexp "kbc"
                    '("bc"))
    (rxt-match-test regexp "kabc"
                    '("abc"))
    (rxt-match-test regexp "*** Failers"
                    '("ers"))
    (rxt-match-test regexp "abk" 'nil)
    (rxt-match-test regexp "akb" 'nil)
    (rxt-match-test regexp "akk" 'nil)))


(ert-deftest rxt-pcre-test-00138 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^\\d{8,}\\@.+[^k]$" "")))
    (rxt-match-test regexp "12345678@a.b.c.d"
                    '("12345678@a.b.c.d"))
    (rxt-match-test regexp "123456789@x.y.z"
                    '("123456789@x.y.z"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "12345678@x.y.uk" 'nil)
    (rxt-match-test regexp "1234567@a.b.c.d" 'nil)))


(ert-deftest rxt-pcre-test-00139 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(a)\\1{8,}" "")))
    (rxt-match-test regexp "aaaaaaaaa"
                    '("aaaaaaaaa" "a"))
    (rxt-match-test regexp "aaaaaaaaaa"
                    '("aaaaaaaaaa" "a"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "aaaaaaa" 'nil)))


(ert-deftest rxt-pcre-test-00140 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[^a]" "")))
    (rxt-match-test regexp "aaaabcd"
                    '("b"))
    (rxt-match-test regexp "aaAabcd"
                    '("A"))))


(ert-deftest rxt-pcre-test-00141 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[^a]" "i")))
    (rxt-match-test regexp "aaaabcd"
                    '("b"))
    (rxt-match-test regexp "aaAabcd"
                    '("b"))))


(ert-deftest rxt-pcre-test-00142 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[^az]" "")))
    (rxt-match-test regexp "aaaabcd"
                    '("b"))
    (rxt-match-test regexp "aaAabcd"
                    '("A"))))


(ert-deftest rxt-pcre-test-00143 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[^az]" "i")))
    (rxt-match-test regexp "aaaabcd"
                    '("b"))
    (rxt-match-test regexp "aaAabcd"
                    '("b"))))


(ert-deftest rxt-pcre-test-00144 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\000\\001\\002\\003\\004\\005\\006\\007\\010\\011\\012\\013\\014\\015\\016\\017\\020\\021\\022\\023\\024\\025\\026\\027\\030\\031\\032\\033\\034\\035\\036\\037\\040\\041\\042\\043\\044\\045\\046\\047\\050\\051\\052\\053\\054\\055\\056\\057\\060\\061\\062\\063\\064\\065\\066\\067\\070\\071\\072\\073\\074\\075\\076\\077\\100\\101\\102\\103\\104\\105\\106\\107\\110\\111\\112\\113\\114\\115\\116\\117\\120\\121\\122\\123\\124\\125\\126\\127\\130\\131\\132\\133\\134\\135\\136\\137\\140\\141\\142\\143\\144\\145\\146\\147\\150\\151\\152\\153\\154\\155\\156\\157\\160\\161\\162\\163\\164\\165\\166\\167\\170\\171\\172\\173\\174\\175\\176\\177\\200\\201\\202\\203\\204\\205\\206\\207\\210\\211\\212\\213\\214\\215\\216\\217\\220\\221\\222\\223\\224\\225\\226\\227\\230\\231\\232\\233\\234\\235\\236\\237\\240\\241\\242\\243\\244\\245\\246\\247\\250\\251\\252\\253\\254\\255\\256\\257\\260\\261\\262\\263\\264\\265\\266\\267\\270\\271\\272\\273\\274\\275\\276\\277\\300\\301\\302\\303\\304\\305\\306\\307\\310\\311\\312\\313\\314\\315\\316\\317\\320\\321\\322\\323\\324\\325\\326\\327\\330\\331\\332\\333\\334\\335\\336\\337\\340\\341\\342\\343\\344\\345\\346\\347\\350\\351\\352\\353\\354\\355\\356\\357\\360\\361\\362\\363\\364\\365\\366\\367\\370\\371\\372\\373\\374\\375\\376\\377" "")))
    (rxt-match-test regexp " 	\n\f !\"#$%&'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~\200\201\202\203\204\205\206\207\210\211\212\213\214\215\216\217\220\221\222\223\224\225\226\227\230\231\232\233\234\235\236\237\240\241\242\243\244\245\246\247\250\251\252\253\254\255\256\257\260\261\262\263\264\265\266\267\270\271\272\273\274\275\276\277\300\301\302\303\304\305\306\307\310\311\312\313\314\315\316\317\320\321\322\323\324\325\326\327\330\331\332\333\334\335\336\337\340\341\342\343\344\345\346\347\350\351\352\353\354\355\356\357\360\361\362\363\364\365\366\367\370\371\372\373\374\375\376\377"
                    '(" 	\n\f !\"#$%&'()*+,-./0123456789:;<=>?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~\200\201\202\203\204\205\206\207\210\211\212\213\214\215\216\217\220\221\222\223\224\225\226\227\230\231\232\233\234\235\236\237\240\241\242\243\244\245\246\247\250\251\252\253\254\255\256\257\260\261\262\263\264\265\266\267\270\271\272\273\274\275\276\277\300\301\302\303\304\305\306\307\310\311\312\313\314\315\316\317\320\321\322\323\324\325\326\327\330\331\332\333\334\335\336\337\340\341\342\343\344\345\346\347\350\351\352\353\354\355\356\357\360\361\362\363\364\365\366\367\370\371\372\373\374\375\376\377"))))


(ert-deftest rxt-pcre-test-00145 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "P[^*]TAIRE[^*]{1,6}?LL" "")))
    (rxt-match-test regexp "xxxxxxxxxxxPSTAIREISLLxxxxxxxxx"
                    '("PSTAIREISLL"))))


(ert-deftest rxt-pcre-test-00146 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "P[^*]TAIRE[^*]{1,}?LL" "")))
    (rxt-match-test regexp "xxxxxxxxxxxPSTAIREISLLxxxxxxxxx"
                    '("PSTAIREISLL"))))


(ert-deftest rxt-pcre-test-00147 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(\\.\\d\\d[1-9]?)\\d+" "")))
    (rxt-match-test regexp "1.230003938"
                    '(".230003938" ".23"))
    (rxt-match-test regexp "1.875000282"
                    '(".875000282" ".875"))
    (rxt-match-test regexp "1.235"
                    '(".235" ".23"))))


(ert-deftest rxt-pcre-test-00148 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(\\.\\d\\d((?=0)|\\d(?=\\d)))" "")))
    (rxt-match-test regexp "1.230003938"
                    '(".23" ".23" ""))
    (rxt-match-test regexp "1.875000282"
                    '(".875" ".875" "5"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "1.235" 'nil)))


(ert-deftest rxt-pcre-test-00149 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a(?)b" "")))
    (rxt-match-test regexp "ab"
                    '("ab"))))


(ert-deftest rxt-pcre-test-00150 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\b(foo)\\s+(\\w+)" "i")))
    (rxt-match-test regexp "Food is on the foo table"
                    '("foo table" "foo" "table"))))


(ert-deftest rxt-pcre-test-00151 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "foo(.*)bar" "")))
    (rxt-match-test regexp "The food is under the bar in the barn."
                    '("food is under the bar in the bar" "d is under the bar in the "))))


(ert-deftest rxt-pcre-test-00152 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "foo(.*?)bar" "")))
    (rxt-match-test regexp "The food is under the bar in the barn."
                    '("food is under the bar" "d is under the "))))


(ert-deftest rxt-pcre-test-00153 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(.*)(\\d*)" "")))
    (rxt-match-test regexp "I have 2 numbers: 53147"
                    '("I have 2 numbers: 53147" "I have 2 numbers: 53147" ""))))


(ert-deftest rxt-pcre-test-00154 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(.*)(\\d+)" "")))
    (rxt-match-test regexp "I have 2 numbers: 53147"
                    '("I have 2 numbers: 53147" "I have 2 numbers: 5314" "7"))))


(ert-deftest rxt-pcre-test-00155 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(.*?)(\\d*)" "")))
    (rxt-match-test regexp "I have 2 numbers: 53147"
                    '("" "" ""))))


(ert-deftest rxt-pcre-test-00156 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(.*?)(\\d+)" "")))
    (rxt-match-test regexp "I have 2 numbers: 53147"
                    '("I have 2" "I have " "2"))))


(ert-deftest rxt-pcre-test-00157 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(.*)(\\d+)$" "")))
    (rxt-match-test regexp "I have 2 numbers: 53147"
                    '("I have 2 numbers: 53147" "I have 2 numbers: 5314" "7"))))


(ert-deftest rxt-pcre-test-00158 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(.*?)(\\d+)$" "")))
    (rxt-match-test regexp "I have 2 numbers: 53147"
                    '("I have 2 numbers: 53147" "I have 2 numbers: " "53147"))))


(ert-deftest rxt-pcre-test-00159 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(.*)\\b(\\d+)$" "")))
    (rxt-match-test regexp "I have 2 numbers: 53147"
                    '("I have 2 numbers: 53147" "I have 2 numbers: " "53147"))))


(ert-deftest rxt-pcre-test-00160 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(.*\\D)(\\d+)$" "")))
    (rxt-match-test regexp "I have 2 numbers: 53147"
                    '("I have 2 numbers: 53147" "I have 2 numbers: " "53147"))))


(ert-deftest rxt-pcre-test-00161 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^\\D*(?!123)" "")))
    (rxt-match-test regexp "ABC123"
                    '("AB"))))


(ert-deftest rxt-pcre-test-00162 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(\\D*)(?=\\d)(?!123)" "")))
    (rxt-match-test regexp "ABC445"
                    '("ABC" "ABC"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "ABC123" 'nil)))


(ert-deftest rxt-pcre-test-00163 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^[W-]46]" "")))
    (rxt-match-test regexp "W46]789"
                    '("W46]"))
    (rxt-match-test regexp "-46]789"
                    '("-46]"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "Wall" 'nil)
    (rxt-match-test regexp "Zebra" 'nil)
    (rxt-match-test regexp "42" 'nil)
    (rxt-match-test regexp "[abcd]" 'nil)
    (rxt-match-test regexp "]abcd[" 'nil)))


(ert-deftest rxt-pcre-test-00164 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^[W-\\]46]" "")))
    (rxt-match-test regexp "W46]789"
                    '("W"))
    (rxt-match-test regexp "Wall"
                    '("W"))
    (rxt-match-test regexp "Zebra"
                    '("Z"))
    (rxt-match-test regexp "Xylophone"
                    '("X"))
    (rxt-match-test regexp "42"
                    '("4"))
    (rxt-match-test regexp "[abcd]"
                    '("["))
    (rxt-match-test regexp "]abcd["
                    '("]"))
    (rxt-match-test regexp "\\backslash"
                    '("\\"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "-46]789" 'nil)
    (rxt-match-test regexp "well" 'nil)))


(ert-deftest rxt-pcre-test-00165 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\d\\d\\/\\d\\d\\/\\d\\d\\d\\d" "")))
    (rxt-match-test regexp "01/01/2000"
                    '("01/01/2000"))))


(ert-deftest rxt-pcre-test-00166 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "word (?:[a-zA-Z0-9]+ ){0,10}otherword" "")))
    (rxt-match-test regexp "word cat dog elephant mussel cow horse canary baboon snake shark otherword"
                    '("word cat dog elephant mussel cow horse canary baboon snake shark otherword"))
    (rxt-match-test regexp "word cat dog elephant mussel cow horse canary baboon snake shark" 'nil)))


(ert-deftest rxt-pcre-test-00167 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "word (?:[a-zA-Z0-9]+ ){0,300}otherword" "")))
    (rxt-match-test regexp "word cat dog elephant mussel cow horse canary baboon snake shark the quick brown fox and the lazy dog and several other words getting close to thirty by now I hope" 'nil)))


(ert-deftest rxt-pcre-test-00168 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(a){0,0}" "")))
    (rxt-match-test regexp "bcd"
                    '(""))
    (rxt-match-test regexp "abc"
                    '(""))
    (rxt-match-test regexp "aab"
                    '(""))))


(ert-deftest rxt-pcre-test-00169 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(a){0,1}" "")))
    (rxt-match-test regexp "bcd"
                    '(""))
    (rxt-match-test regexp "abc"
                    '("a" "a"))
    (rxt-match-test regexp "aab"
                    '("a" "a"))))


(ert-deftest rxt-pcre-test-00170 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(a){0,2}" "")))
    (rxt-match-test regexp "bcd"
                    '(""))
    (rxt-match-test regexp "abc"
                    '("a" "a"))
    (rxt-match-test regexp "aab"
                    '("aa" "a"))))


(ert-deftest rxt-pcre-test-00171 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(a){0,3}" "")))
    (rxt-match-test regexp "bcd"
                    '(""))
    (rxt-match-test regexp "abc"
                    '("a" "a"))
    (rxt-match-test regexp "aab"
                    '("aa" "a"))
    (rxt-match-test regexp "aaa"
                    '("aaa" "a"))))


(ert-deftest rxt-pcre-test-00172 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(a){0,}" "")))
    (rxt-match-test regexp "bcd"
                    '(""))
    (rxt-match-test regexp "abc"
                    '("a" "a"))
    (rxt-match-test regexp "aab"
                    '("aa" "a"))
    (rxt-match-test regexp "aaa"
                    '("aaa" "a"))
    (rxt-match-test regexp "aaaaaaaa"
                    '("aaaaaaaa" "a"))))


(ert-deftest rxt-pcre-test-00173 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(a){1,1}" "")))
    (rxt-match-test regexp "bcd" 'nil)
    (rxt-match-test regexp "abc"
                    '("a" "a"))
    (rxt-match-test regexp "aab"
                    '("a" "a"))))


(ert-deftest rxt-pcre-test-00174 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(a){1,2}" "")))
    (rxt-match-test regexp "bcd" 'nil)
    (rxt-match-test regexp "abc"
                    '("a" "a"))
    (rxt-match-test regexp "aab"
                    '("aa" "a"))))


(ert-deftest rxt-pcre-test-00175 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(a){1,3}" "")))
    (rxt-match-test regexp "bcd" 'nil)
    (rxt-match-test regexp "abc"
                    '("a" "a"))
    (rxt-match-test regexp "aab"
                    '("aa" "a"))
    (rxt-match-test regexp "aaa"
                    '("aaa" "a"))))


(ert-deftest rxt-pcre-test-00176 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(a){1,}" "")))
    (rxt-match-test regexp "bcd" 'nil)
    (rxt-match-test regexp "abc"
                    '("a" "a"))
    (rxt-match-test regexp "aab"
                    '("aa" "a"))
    (rxt-match-test regexp "aaa"
                    '("aaa" "a"))
    (rxt-match-test regexp "aaaaaaaa"
                    '("aaaaaaaa" "a"))))


(ert-deftest rxt-pcre-test-00177 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp ".*\\.gif" "")))
    (rxt-match-test regexp "borfle\nbib.gif\nno"
                    '("bib.gif"))))


(ert-deftest rxt-pcre-test-00178 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp ".{0,}\\.gif" "")))
    (rxt-match-test regexp "borfle\nbib.gif\nno"
                    '("bib.gif"))))


(ert-deftest rxt-pcre-test-00179 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp ".*\\.gif" "m")))
    (rxt-match-test regexp "borfle\nbib.gif\nno"
                    '("bib.gif"))))


(ert-deftest rxt-pcre-test-00180 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp ".*\\.gif" "s")))
    (rxt-match-test regexp "borfle\nbib.gif\nno"
                    '("borfle\nbib.gif"))))


(ert-deftest rxt-pcre-test-00181 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp ".*\\.gif" "ms")))
    (rxt-match-test regexp "borfle\nbib.gif\nno"
                    '("borfle\nbib.gif"))))


(ert-deftest rxt-pcre-test-00182 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp ".*$" "")))
    (rxt-match-test regexp "borfle\nbib.gif\nno"
                    '("no"))))


(ert-deftest rxt-pcre-test-00183 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp ".*$" "m")))
    (rxt-match-test regexp "borfle\nbib.gif\nno"
                    '("borfle"))))


(ert-deftest rxt-pcre-test-00184 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp ".*$" "s")))
    (rxt-match-test regexp "borfle\nbib.gif\nno"
                    '("borfle\nbib.gif\nno"))))


(ert-deftest rxt-pcre-test-00185 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp ".*$" "ms")))
    (rxt-match-test regexp "borfle\nbib.gif\nno"
                    '("borfle\nbib.gif\nno"))))


(ert-deftest rxt-pcre-test-00186 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp ".*$" "")))
    (rxt-match-test regexp "borfle\nbib.gif\nno\n"
                    '("no"))))


(ert-deftest rxt-pcre-test-00187 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp ".*$" "m")))
    (rxt-match-test regexp "borfle\nbib.gif\nno\n"
                    '("borfle"))))


(ert-deftest rxt-pcre-test-00188 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp ".*$" "s")))
    (rxt-match-test regexp "borfle\nbib.gif\nno\n"
                    '("borfle\nbib.gif\nno\n"))))


(ert-deftest rxt-pcre-test-00189 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp ".*$" "ms")))
    (rxt-match-test regexp "borfle\nbib.gif\nno\n"
                    '("borfle\nbib.gif\nno\n"))))


(ert-deftest rxt-pcre-test-00190 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(.*X|^B)" "")))
    (rxt-match-test regexp "abcde\n1234Xyz"
                    '("1234X" "1234X"))
    (rxt-match-test regexp "BarFoo"
                    '("B" "B"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "abcde\nBar" 'nil)))


(ert-deftest rxt-pcre-test-00191 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(.*X|^B)" "m")))
    (rxt-match-test regexp "abcde\n1234Xyz"
                    '("1234X" "1234X"))
    (rxt-match-test regexp "BarFoo"
                    '("B" "B"))
    (rxt-match-test regexp "abcde\nBar"
                    '("B" "B"))))


(ert-deftest rxt-pcre-test-00192 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(.*X|^B)" "s")))
    (rxt-match-test regexp "abcde\n1234Xyz"
                    '("abcde\n1234X" "abcde\n1234X"))
    (rxt-match-test regexp "BarFoo"
                    '("B" "B"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "abcde\nBar" 'nil)))


(ert-deftest rxt-pcre-test-00193 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(.*X|^B)" "ms")))
    (rxt-match-test regexp "abcde\n1234Xyz"
                    '("abcde\n1234X" "abcde\n1234X"))
    (rxt-match-test regexp "BarFoo"
                    '("B" "B"))
    (rxt-match-test regexp "abcde\nBar"
                    '("B" "B"))))


(ert-deftest rxt-pcre-test-00194 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?s)(.*X|^B)" "")))
    (rxt-match-test regexp "abcde\n1234Xyz"
                    '("abcde\n1234X" "abcde\n1234X"))
    (rxt-match-test regexp "BarFoo"
                    '("B" "B"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "abcde\nBar" 'nil)))


(ert-deftest rxt-pcre-test-00195 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?s:.*X|^B)" "")))
    (rxt-match-test regexp "abcde\n1234Xyz"
                    '("abcde\n1234X"))
    (rxt-match-test regexp "BarFoo"
                    '("B"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "abcde\nBar" 'nil)))


(ert-deftest rxt-pcre-test-00196 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^.*B" "")))
    (rxt-match-test regexp "**** Failers" 'nil)
    (rxt-match-test regexp "abc\nB" 'nil)))


(ert-deftest rxt-pcre-test-00197 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?s)^.*B" "")))
    (rxt-match-test regexp "abc\nB"
                    '("abc\nB"))))


(ert-deftest rxt-pcre-test-00198 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?m)^.*B" "")))
    (rxt-match-test regexp "abc\nB"
                    '("B"))))


(ert-deftest rxt-pcre-test-00199 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?ms)^.*B" "")))
    (rxt-match-test regexp "abc\nB"
                    '("abc\nB"))))


(ert-deftest rxt-pcre-test-00200 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?ms)^B" "")))
    (rxt-match-test regexp "abc\nB"
                    '("B"))))


(ert-deftest rxt-pcre-test-00201 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?s)B$" "")))
    (rxt-match-test regexp "B\n"
                    '("B"))))


(ert-deftest rxt-pcre-test-00202 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^[0-9][0-9][0-9][0-9][0-9][0-9][0-9][0-9][0-9][0-9][0-9][0-9]" "")))
    (rxt-match-test regexp "123456654321"
                    '("123456654321"))))


(ert-deftest rxt-pcre-test-00203 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^\\d\\d\\d\\d\\d\\d\\d\\d\\d\\d\\d\\d" "")))
    (rxt-match-test regexp "123456654321"
                    '("123456654321"))))


(ert-deftest rxt-pcre-test-00204 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^[\\d][\\d][\\d][\\d][\\d][\\d][\\d][\\d][\\d][\\d][\\d][\\d]" "")))
    (rxt-match-test regexp "123456654321"
                    '("123456654321"))))


(ert-deftest rxt-pcre-test-00205 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^[abc]{12}" "")))
    (rxt-match-test regexp "abcabcabcabc"
                    '("abcabcabcabc"))))


(ert-deftest rxt-pcre-test-00206 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^[a-c]{12}" "")))
    (rxt-match-test regexp "abcabcabcabc"
                    '("abcabcabcabc"))))


(ert-deftest rxt-pcre-test-00207 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(a|b|c){12}" "")))
    (rxt-match-test regexp "abcabcabcabc"
                    '("abcabcabcabc" "c"))))


(ert-deftest rxt-pcre-test-00208 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^[abcdefghijklmnopqrstuvwxy0123456789]" "")))
    (rxt-match-test regexp "n"
                    '("n"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "z" 'nil)))


(ert-deftest rxt-pcre-test-00209 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "abcde{0,0}" "")))
    (rxt-match-test regexp "abcd"
                    '("abcd"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "abce" 'nil)))


(ert-deftest rxt-pcre-test-00210 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab[cd]{0,0}e" "")))
    (rxt-match-test regexp "abe"
                    '("abe"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "abcde" 'nil)))


(ert-deftest rxt-pcre-test-00211 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab(c){0,0}d" "")))
    (rxt-match-test regexp "abd"
                    '("abd"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "abcd" 'nil)))


(ert-deftest rxt-pcre-test-00212 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a(b*)" "")))
    (rxt-match-test regexp "a"
                    '("a" ""))
    (rxt-match-test regexp "ab"
                    '("ab" "b"))
    (rxt-match-test regexp "abbbb"
                    '("abbbb" "bbbb"))
    (rxt-match-test regexp "*** Failers"
                    '("a" ""))
    (rxt-match-test regexp "bbbbb" 'nil)))


(ert-deftest rxt-pcre-test-00213 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab\\d{0}e" "")))
    (rxt-match-test regexp "abe"
                    '("abe"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "ab1e" 'nil)))


(ert-deftest rxt-pcre-test-00214 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\"([^\\\\\"]+|\\\\.)*\"" "")))
    (rxt-match-test regexp "the \"quick\" brown fox"
                    '("\"quick\"" "quick"))
    (rxt-match-test regexp "\"the \\\"quick\\\" brown fox\""
                    '("\"the \\\"quick\\\" brown fox\"" " brown fox"))))


(ert-deftest rxt-pcre-test-00215 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp ".*?" "g")))
    (rxt-match-test regexp "abc"
                    '("" "a" "" "b" "" "c" ""))))


(ert-deftest rxt-pcre-test-00216 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\b" "g")))
    (rxt-match-test regexp "abc"
                    '("" ""))))


(ert-deftest rxt-pcre-test-00217 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\b" "g")))
    (rxt-match-test regexp "abc"
                    '("" ""))))


(ert-deftest rxt-pcre-test-00218 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "" "g")))
    (rxt-match-test regexp "abc"
                    '("" "" "" ""))))


(ert-deftest rxt-pcre-test-00219 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "<tr([\\w\\W\\s\\d][^<>]{0,})><TD([\\w\\W\\s\\d][^<>]{0,})>([\\d]{0,}\\.)(.*)((<BR>([\\w\\W\\s\\d][^<>]{0,})|[\\s]{0,}))<\\/a><\\/TD><TD([\\w\\W\\s\\d][^<>]{0,})>([\\w\\W\\s\\d][^<>]{0,})<\\/TD><TD([\\w\\W\\s\\d][^<>]{0,})>([\\w\\W\\s\\d][^<>]{0,})<\\/TD><\\/TR>" "is")))
    (rxt-match-test regexp "<TR BGCOLOR='#DBE9E9'><TD align=left valign=top>43.<a href='joblist.cfm?JobID=94 6735&Keyword='>Word Processor<BR>(N-1286)</a></TD><TD align=left valign=top>Lega lstaff.com</TD><TD align=left valign=top>CA - Statewide</TD></TR>"
                    '("<TR BGCOLOR='#DBE9E9'><TD align=left valign=top>43.<a href='joblist.cfm?JobID=94 6735&Keyword='>Word Processor<BR>(N-1286)</a></TD><TD align=left valign=top>Lega lstaff.com</TD><TD align=left valign=top>CA - Statewide</TD></TR>" " BGCOLOR='#DBE9E9'" " align=left valign=top" "43." "<a href='joblist.cfm?JobID=94 6735&Keyword='>Word Processor<BR>(N-1286)" "" "" nil " align=left valign=top" "Lega lstaff.com" " align=left valign=top" "CA - Statewide"))))


(ert-deftest rxt-pcre-test-00220 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a[^a]b" "")))
    (rxt-match-test regexp "acb"
                    '("acb"))
    (rxt-match-test regexp "a\nb"
                    '("a\nb"))))


(ert-deftest rxt-pcre-test-00221 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a.b" "")))
    (rxt-match-test regexp "acb"
                    '("acb"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "a\nb" 'nil)))


(ert-deftest rxt-pcre-test-00222 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a[^a]b" "s")))
    (rxt-match-test regexp "acb"
                    '("acb"))
    (rxt-match-test regexp "a\nb"
                    '("a\nb"))))


(ert-deftest rxt-pcre-test-00223 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a.b" "s")))
    (rxt-match-test regexp "acb"
                    '("acb"))
    (rxt-match-test regexp "a\nb"
                    '("a\nb"))))


(ert-deftest rxt-pcre-test-00224 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(b+?|a){1,2}?c" "")))
    (rxt-match-test regexp "bac"
                    '("bac" "a"))
    (rxt-match-test regexp "bbac"
                    '("bbac" "a"))
    (rxt-match-test regexp "bbbac"
                    '("bbbac" "a"))
    (rxt-match-test regexp "bbbbac"
                    '("bbbbac" "a"))
    (rxt-match-test regexp "bbbbbac"
                    '("bbbbbac" "a"))))


(ert-deftest rxt-pcre-test-00225 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(b+|a){1,2}?c" "")))
    (rxt-match-test regexp "bac"
                    '("bac" "a"))
    (rxt-match-test regexp "bbac"
                    '("bbac" "a"))
    (rxt-match-test regexp "bbbac"
                    '("bbbac" "a"))
    (rxt-match-test regexp "bbbbac"
                    '("bbbbac" "a"))
    (rxt-match-test regexp "bbbbbac"
                    '("bbbbbac" "a"))))


(ert-deftest rxt-pcre-test-00226 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?!\\A)x" "m")))
    (rxt-match-test regexp "x\nb\n" 'nil)
    (rxt-match-test regexp "ax\n"
                    '("x"))))


(ert-deftest rxt-pcre-test-00227 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\x0{ab}" "")))
    (rxt-match-test regexp " {ab}"
                    '(" {ab}"))))


(ert-deftest rxt-pcre-test-00228 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(A|B)*?CD" "")))
    (rxt-match-test regexp "CD"
                    '("CD"))))


(ert-deftest rxt-pcre-test-00229 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(A|B)*CD" "")))
    (rxt-match-test regexp "CD"
                    '("CD"))))


(ert-deftest rxt-pcre-test-00230 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(AB)*?\\1" "")))
    (rxt-match-test regexp "ABABAB"
                    '("ABAB" "AB"))))


(ert-deftest rxt-pcre-test-00231 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(AB)*\\1" "")))
    (rxt-match-test regexp "ABABAB"
                    '("ABABAB" "AB"))))


(ert-deftest rxt-pcre-test-00232 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?<!bar)foo" "")))
    (rxt-match-test regexp "foo"
                    '("foo"))
    (rxt-match-test regexp "catfood"
                    '("foo"))
    (rxt-match-test regexp "arfootle"
                    '("foo"))
    (rxt-match-test regexp "rfoosh"
                    '("foo"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "barfoo" 'nil)
    (rxt-match-test regexp "towbarfoo" 'nil)))


(ert-deftest rxt-pcre-test-00233 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\w{3}(?<!bar)foo" "")))
    (rxt-match-test regexp "catfood"
                    '("catfoo"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "foo" 'nil)
    (rxt-match-test regexp "barfoo" 'nil)
    (rxt-match-test regexp "towbarfoo" 'nil)))


(ert-deftest rxt-pcre-test-00234 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?<=(foo)a)bar" "")))
    (rxt-match-test regexp "fooabar"
                    '("bar" "foo"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "bar" 'nil)
    (rxt-match-test regexp "foobbar" 'nil)))


(ert-deftest rxt-pcre-test-00235 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\Aabc\\z" "m")))
    (rxt-match-test regexp "abc"
                    '("abc"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "abc\n" 'nil)
    (rxt-match-test regexp "qqq\nabc" 'nil)
    (rxt-match-test regexp "abc\nzzz" 'nil)
    (rxt-match-test regexp "qqq\nabc\nzzz" 'nil)))


(ert-deftest rxt-pcre-test-00236 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?>.*/)foo" "")))
    (rxt-match-test regexp "/this/is/a/very/long/line/in/deed/with/very/many/slashes/in/it/you/see/" 'nil)))


(ert-deftest rxt-pcre-test-00237 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?>.*/)foo" "")))
    (rxt-match-test regexp "/this/is/a/very/long/line/in/deed/with/very/many/slashes/in/and/foo"
                    '("/this/is/a/very/long/line/in/deed/with/very/many/slashes/in/and/foo"))))


(ert-deftest rxt-pcre-test-00238 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?>(\\.\\d\\d[1-9]?))\\d+" "")))
    (rxt-match-test regexp "1.230003938"
                    '(".230003938" ".23"))
    (rxt-match-test regexp "1.875000282"
                    '(".875000282" ".875"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "1.235" 'nil)))


(ert-deftest rxt-pcre-test-00239 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^((?>\\w+)|(?>\\s+))*$" "")))
    (rxt-match-test regexp "now is the time for all good men to come to the aid of the party"
                    '("now is the time for all good men to come to the aid of the party" "party"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "this is not a line with only words and spaces!" 'nil)))


(ert-deftest rxt-pcre-test-00240 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(\\d+)(\\w)" "")))
    (rxt-match-test regexp "12345a"
                    '("12345a" "12345" "a"))
    (rxt-match-test regexp "12345+"
                    '("12345" "1234" "5"))))


(ert-deftest rxt-pcre-test-00241 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((?>\\d+))(\\w)" "")))
    (rxt-match-test regexp "12345a"
                    '("12345a" "12345" "a"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "12345+" 'nil)))


(ert-deftest rxt-pcre-test-00242 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?>a+)b" "")))
    (rxt-match-test regexp "aaab"
                    '("aaab"))))


(ert-deftest rxt-pcre-test-00243 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((?>a+)b)" "")))
    (rxt-match-test regexp "aaab"
                    '("aaab" "aaab"))))


(ert-deftest rxt-pcre-test-00244 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?>(a+))b" "")))
    (rxt-match-test regexp "aaab"
                    '("aaab" "aaa"))))


(ert-deftest rxt-pcre-test-00245 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?>b)+" "")))
    (rxt-match-test regexp "aaabbbccc"
                    '("bbb"))))


(ert-deftest rxt-pcre-test-00246 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?>a+|b+|c+)*c" "")))
    (rxt-match-test regexp "aaabbbbccccd"
                    '("aaabbbbc"))))


(ert-deftest rxt-pcre-test-00247 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((?>[^()]+)|\\([^()]*\\))+" "")))
    (rxt-match-test regexp "((abc(ade)ufh()()x"
                    '("abc(ade)ufh()()x" "x"))))


(ert-deftest rxt-pcre-test-00248 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\(((?>[^()]+)|\\([^()]+\\))+\\)" "")))
    (rxt-match-test regexp "(abc)"
                    '("(abc)" "abc"))
    (rxt-match-test regexp "(abc(def)xyz)"
                    '("(abc(def)xyz)" "xyz"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "((()aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" 'nil)))


(ert-deftest rxt-pcre-test-00249 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a(?-i)b" "i")))
    (rxt-match-test regexp "ab"
                    '("ab"))
    (rxt-match-test regexp "Ab"
                    '("Ab"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "aB" 'nil)
    (rxt-match-test regexp "AB" 'nil)))


(ert-deftest rxt-pcre-test-00250 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(a (?x)b c)d e" "")))
    (rxt-match-test regexp "a bcd e"
                    '("a bcd e" "a bc"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "a b cd e" 'nil)
    (rxt-match-test regexp "abcd e" 'nil)
    (rxt-match-test regexp "a bcde" 'nil)))


(ert-deftest rxt-pcre-test-00251 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(a b(?x)c d (?-x)e f)" "")))
    (rxt-match-test regexp "a bcde f"
                    '("a bcde f" "a bcde f"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "abcdef" 'nil)))


(ert-deftest rxt-pcre-test-00252 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(a(?i)b)c" "")))
    (rxt-match-test regexp "abc"
                    '("abc" "ab"))
    (rxt-match-test regexp "aBc"
                    '("aBc" "aB"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "abC" 'nil)
    (rxt-match-test regexp "aBC" 'nil)
    (rxt-match-test regexp "Abc" 'nil)
    (rxt-match-test regexp "ABc" 'nil)
    (rxt-match-test regexp "ABC" 'nil)
    (rxt-match-test regexp "AbC" 'nil)))


(ert-deftest rxt-pcre-test-00253 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a(?i:b)c" "")))
    (rxt-match-test regexp "abc"
                    '("abc"))
    (rxt-match-test regexp "aBc"
                    '("aBc"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "ABC" 'nil)
    (rxt-match-test regexp "abC" 'nil)
    (rxt-match-test regexp "aBC" 'nil)))


(ert-deftest rxt-pcre-test-00254 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a(?i:b)*c" "")))
    (rxt-match-test regexp "aBc"
                    '("aBc"))
    (rxt-match-test regexp "aBBc"
                    '("aBBc"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "aBC" 'nil)
    (rxt-match-test regexp "aBBC" 'nil)))


(ert-deftest rxt-pcre-test-00255 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a(?=b(?i)c)\\w\\wd" "")))
    (rxt-match-test regexp "abcd"
                    '("abcd"))
    (rxt-match-test regexp "abCd"
                    '("abCd"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "aBCd" 'nil)
    (rxt-match-test regexp "abcD" 'nil)))


(ert-deftest rxt-pcre-test-00256 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?s-i:more.*than).*million" "i")))
    (rxt-match-test regexp "more than million"
                    '("more than million"))
    (rxt-match-test regexp "more than MILLION"
                    '("more than MILLION"))
    (rxt-match-test regexp "more \n than Million"
                    '("more \n than Million"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "MORE THAN MILLION" 'nil)
    (rxt-match-test regexp "more \n than \n million" 'nil)))


(ert-deftest rxt-pcre-test-00257 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?:(?s-i)more.*than).*million" "i")))
    (rxt-match-test regexp "more than million"
                    '("more than million"))
    (rxt-match-test regexp "more than MILLION"
                    '("more than MILLION"))
    (rxt-match-test regexp "more \n than Million"
                    '("more \n than Million"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "MORE THAN MILLION" 'nil)
    (rxt-match-test regexp "more \n than \n million" 'nil)))


(ert-deftest rxt-pcre-test-00258 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?>a(?i)b+)+c" "")))
    (rxt-match-test regexp "abc"
                    '("abc"))
    (rxt-match-test regexp "aBbc"
                    '("aBbc"))
    (rxt-match-test regexp "aBBc"
                    '("aBBc"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "Abc" 'nil)
    (rxt-match-test regexp "abAb" 'nil)
    (rxt-match-test regexp "abbC" 'nil)))


(ert-deftest rxt-pcre-test-00259 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?=a(?i)b)\\w\\wc" "")))
    (rxt-match-test regexp "abc"
                    '("abc"))
    (rxt-match-test regexp "aBc"
                    '("aBc"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "Ab" 'nil)
    (rxt-match-test regexp "abC" 'nil)
    (rxt-match-test regexp "aBC" 'nil)))


(ert-deftest rxt-pcre-test-00260 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?<=a(?i)b)(\\w\\w)c" "")))
    (rxt-match-test regexp "abxxc"
                    '("xxc" "xx"))
    (rxt-match-test regexp "aBxxc"
                    '("xxc" "xx"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "Abxxc" 'nil)
    (rxt-match-test regexp "ABxxc" 'nil)
    (rxt-match-test regexp "abxxC" 'nil)))


(ert-deftest rxt-pcre-test-00261 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?:(a)|b)(?(1)A|B)" "")))
    (rxt-match-test regexp "aA"
                    '("aA" "a"))
    (rxt-match-test regexp "bB"
                    '("bB"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "aB" 'nil)
    (rxt-match-test regexp "bA" 'nil)))


(ert-deftest rxt-pcre-test-00262 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(a)?(?(1)a|b)+$" "")))
    (rxt-match-test regexp "aa"
                    '("aa" "a"))
    (rxt-match-test regexp "b"
                    '("b"))
    (rxt-match-test regexp "bb"
                    '("bb"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "ab" 'nil)))


(ert-deftest rxt-pcre-test-00263 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?(?=abc)\\w{3}:|\\d\\d)$" "")))
    (rxt-match-test regexp "abc:"
                    '("abc:"))
    (rxt-match-test regexp "12"
                    '("12"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "123" 'nil)
    (rxt-match-test regexp "xyz" 'nil)))


(ert-deftest rxt-pcre-test-00264 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?(?!abc)\\d\\d|\\w{3}:)$" "")))
    (rxt-match-test regexp "abc:"
                    '("abc:"))
    (rxt-match-test regexp "12"
                    '("12"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "123" 'nil)
    (rxt-match-test regexp "xyz" 'nil)))


(ert-deftest rxt-pcre-test-00265 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?(?<=foo)bar|cat)" "")))
    (rxt-match-test regexp "foobar"
                    '("bar"))
    (rxt-match-test regexp "cat"
                    '("cat"))
    (rxt-match-test regexp "fcat"
                    '("cat"))
    (rxt-match-test regexp "focat"
                    '("cat"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "foocat" 'nil)))


(ert-deftest rxt-pcre-test-00266 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?(?<!foo)cat|bar)" "")))
    (rxt-match-test regexp "foobar"
                    '("bar"))
    (rxt-match-test regexp "cat"
                    '("cat"))
    (rxt-match-test regexp "fcat"
                    '("cat"))
    (rxt-match-test regexp "focat"
                    '("cat"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "foocat" 'nil)))


(ert-deftest rxt-pcre-test-00267 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "( \\( )? [^()]+ (?(1) \\) |) " "x")))
    (rxt-match-test regexp "abcd"
                    '("abcd"))
    (rxt-match-test regexp "(abcd)"
                    '("(abcd)" "("))
    (rxt-match-test regexp "the quick (abcd) fox"
                    '("the quick "))
    (rxt-match-test regexp "(abcd"
                    '("abcd"))))


(ert-deftest rxt-pcre-test-00268 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "( \\( )? [^()]+ (?(1) \\) ) " "x")))
    (rxt-match-test regexp "abcd"
                    '("abcd"))
    (rxt-match-test regexp "(abcd)"
                    '("(abcd)" "("))
    (rxt-match-test regexp "the quick (abcd) fox"
                    '("the quick "))
    (rxt-match-test regexp "(abcd"
                    '("abcd"))))


(ert-deftest rxt-pcre-test-00269 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?(2)a|(1)(2))+$" "")))
    (rxt-match-test regexp "12"
                    '("12" "1" "2"))
    (rxt-match-test regexp "12a"
                    '("12a" "1" "2"))
    (rxt-match-test regexp "12aa"
                    '("12aa" "1" "2"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "1234" 'nil)))


(ert-deftest rxt-pcre-test-00270 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((?i)blah)\\s+\\1" "")))
    (rxt-match-test regexp "blah blah"
                    '("blah blah" "blah"))
    (rxt-match-test regexp "BLAH BLAH"
                    '("BLAH BLAH" "BLAH"))
    (rxt-match-test regexp "Blah Blah"
                    '("Blah Blah" "Blah"))
    (rxt-match-test regexp "blaH blaH"
                    '("blaH blaH" "blaH"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "blah BLAH" 'nil)
    (rxt-match-test regexp "Blah blah" 'nil)
    (rxt-match-test regexp "blaH blah" 'nil)))


(ert-deftest rxt-pcre-test-00271 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((?i)blah)\\s+(?i:\\1)" "")))
    (rxt-match-test regexp "blah blah"
                    '("blah blah" "blah"))
    (rxt-match-test regexp "BLAH BLAH"
                    '("BLAH BLAH" "BLAH"))
    (rxt-match-test regexp "Blah Blah"
                    '("Blah Blah" "Blah"))
    (rxt-match-test regexp "blaH blaH"
                    '("blaH blaH" "blaH"))
    (rxt-match-test regexp "blah BLAH"
                    '("blah BLAH" "blah"))
    (rxt-match-test regexp "Blah blah"
                    '("Blah blah" "Blah"))
    (rxt-match-test regexp "blaH blah"
                    '("blaH blah" "blaH"))))


(ert-deftest rxt-pcre-test-00272 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?>a*)*" "")))
    (rxt-match-test regexp "a"
                    '("a"))
    (rxt-match-test regexp "aa"
                    '("aa"))
    (rxt-match-test regexp "aaaa"
                    '("aaaa"))))


(ert-deftest rxt-pcre-test-00273 nil 
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(abc|)+" "")))
    (rxt-match-test regexp "abc"
                    '("abc" ""))
    (rxt-match-test regexp "abcabc"
                    '("abcabc" ""))
    (rxt-match-test regexp "abcabcabc"
                    '("abcabcabc" ""))
    (rxt-match-test regexp "xyz"
                    '("" ""))))


(ert-deftest rxt-pcre-test-00274 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "([a]*)*" "")))
    (rxt-match-test regexp "a"
                    '("a" ""))
    (rxt-match-test regexp "aaaaa"
                    '("aaaaa" ""))))


(ert-deftest rxt-pcre-test-00275 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "([ab]*)*" "")))
    (rxt-match-test regexp "a"
                    '("a" ""))
    (rxt-match-test regexp "b"
                    '("b" ""))
    (rxt-match-test regexp "ababab"
                    '("ababab" ""))
    (rxt-match-test regexp "aaaabcde"
                    '("aaaab" ""))
    (rxt-match-test regexp "bbbb"
                    '("bbbb" ""))))


(ert-deftest rxt-pcre-test-00276 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "([^a]*)*" "")))
    (rxt-match-test regexp "b"
                    '("b" ""))
    (rxt-match-test regexp "bbbb"
                    '("bbbb" ""))
    (rxt-match-test regexp "aaa"
                    '("" ""))))


(ert-deftest rxt-pcre-test-00277 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "([^ab]*)*" "")))
    (rxt-match-test regexp "cccc"
                    '("cccc" ""))
    (rxt-match-test regexp "abab"
                    '("" ""))))


(ert-deftest rxt-pcre-test-00278 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "([a]*?)*" "")))
    (rxt-match-test regexp "a"
                    '("" ""))
    (rxt-match-test regexp "aaaa"
                    '("" ""))))


(ert-deftest rxt-pcre-test-00279 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "([ab]*?)*" "")))
    (rxt-match-test regexp "a"
                    '("" ""))
    (rxt-match-test regexp "b"
                    '("" ""))
    (rxt-match-test regexp "abab"
                    '("" ""))
    (rxt-match-test regexp "baba"
                    '("" ""))))


(ert-deftest rxt-pcre-test-00280 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "([^a]*?)*" "")))
    (rxt-match-test regexp "b"
                    '("" ""))
    (rxt-match-test regexp "bbbb"
                    '("" ""))
    (rxt-match-test regexp "aaa"
                    '("" ""))))


(ert-deftest rxt-pcre-test-00281 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "([^ab]*?)*" "")))
    (rxt-match-test regexp "c"
                    '("" ""))
    (rxt-match-test regexp "cccc"
                    '("" ""))
    (rxt-match-test regexp "baba"
                    '("" ""))))


(ert-deftest rxt-pcre-test-00282 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?>a*)*" "")))
    (rxt-match-test regexp "a"
                    '("a"))
    (rxt-match-test regexp "aaabcde"
                    '("aaa"))))


(ert-deftest rxt-pcre-test-00283 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((?>a*))*" "")))
    (rxt-match-test regexp "aaaaa"
                    '("aaaaa" ""))
    (rxt-match-test regexp "aabbaa"
                    '("aa" ""))))


(ert-deftest rxt-pcre-test-00284 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((?>a*?))*" "")))
    (rxt-match-test regexp "aaaaa"
                    '("" ""))
    (rxt-match-test regexp "aabbaa"
                    '("" ""))))


(ert-deftest rxt-pcre-test-00285 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?(?=[^a-z]+[a-z])  \\d{2}-[a-z]{3}-\\d{2}  |  \\d{2}-\\d{2}-\\d{2} ) " "x")))
    (rxt-match-test regexp "12-sep-98"
                    '("12-sep-98"))
    (rxt-match-test regexp "12-09-98"
                    '("12-09-98"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "sep-12-98" 'nil)))


(ert-deftest rxt-pcre-test-00286 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?<=(foo))bar\\1" "")))
    (rxt-match-test regexp "foobarfoo"
                    '("barfoo" "foo"))
    (rxt-match-test regexp "foobarfootling"
                    '("barfoo" "foo"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "foobar" 'nil)
    (rxt-match-test regexp "barfoo" 'nil)))


(ert-deftest rxt-pcre-test-00287 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?i:saturday|sunday)" "")))
    (rxt-match-test regexp "saturday"
                    '("saturday"))
    (rxt-match-test regexp "sunday"
                    '("sunday"))
    (rxt-match-test regexp "Saturday"
                    '("Saturday"))
    (rxt-match-test regexp "Sunday"
                    '("Sunday"))
    (rxt-match-test regexp "SATURDAY"
                    '("SATURDAY"))
    (rxt-match-test regexp "SUNDAY"
                    '("SUNDAY"))
    (rxt-match-test regexp "SunDay"
                    '("SunDay"))))


(ert-deftest rxt-pcre-test-00288 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(a(?i)bc|BB)x" "")))
    (rxt-match-test regexp "abcx"
                    '("abcx" "abc"))
    (rxt-match-test regexp "aBCx"
                    '("aBCx" "aBC"))
    (rxt-match-test regexp "bbx"
                    '("bbx" "bb"))
    (rxt-match-test regexp "BBx"
                    '("BBx" "BB"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "abcX" 'nil)
    (rxt-match-test regexp "aBCX" 'nil)
    (rxt-match-test regexp "bbX" 'nil)
    (rxt-match-test regexp "BBX" 'nil)))


(ert-deftest rxt-pcre-test-00289 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^([ab](?i)[cd]|[ef])" "")))
    (rxt-match-test regexp "ac"
                    '("ac" "ac"))
    (rxt-match-test regexp "aC"
                    '("aC" "aC"))
    (rxt-match-test regexp "bD"
                    '("bD" "bD"))
    (rxt-match-test regexp "elephant"
                    '("e" "e"))
    (rxt-match-test regexp "Europe"
                    '("E" "E"))
    (rxt-match-test regexp "frog"
                    '("f" "f"))
    (rxt-match-test regexp "France"
                    '("F" "F"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "Africa" 'nil)))


(ert-deftest rxt-pcre-test-00290 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(ab|a(?i)[b-c](?m-i)d|x(?i)y|z)" "")))
    (rxt-match-test regexp "ab"
                    '("ab" "ab"))
    (rxt-match-test regexp "aBd"
                    '("aBd" "aBd"))
    (rxt-match-test regexp "xy"
                    '("xy" "xy"))
    (rxt-match-test regexp "xY"
                    '("xY" "xY"))
    (rxt-match-test regexp "zebra"
                    '("z" "z"))
    (rxt-match-test regexp "Zambesi"
                    '("Z" "Z"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "aCD" 'nil)
    (rxt-match-test regexp "XY" 'nil)))


(ert-deftest rxt-pcre-test-00291 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?<=foo\\n)^bar" "m")))
    (rxt-match-test regexp "foo\nbar"
                    '("bar"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "bar" 'nil)
    (rxt-match-test regexp "baz\nbar" 'nil)))


(ert-deftest rxt-pcre-test-00292 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?<=(?<!foo)bar)baz" "")))
    (rxt-match-test regexp "barbaz"
                    '("baz"))
    (rxt-match-test regexp "barbarbaz"
                    '("baz"))
    (rxt-match-test regexp "koobarbaz"
                    '("baz"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "baz" 'nil)
    (rxt-match-test regexp "foobarbaz" 'nil)))


(ert-deftest rxt-pcre-test-00293 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "The cases of aaaa and aaaaaa are missed out below because Perl does things" "")))
    (rxt-match-test regexp "/differently. We know that odd, and maybe incorrect, things happen with/" 'nil)
    (rxt-match-test regexp "/recursive references in Perl, as far as 5.11.3 - see some stuff in test #2./" 'nil)))


(ert-deftest rxt-pcre-test-00294 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(a\\1?){4}$" "")))
    (rxt-match-test regexp "a" 'nil)
    (rxt-match-test regexp "aa" 'nil)
    (rxt-match-test regexp "aaa" 'nil)
    (rxt-match-test regexp "aaaaa"
                    '("aaaaa" "a"))
    (rxt-match-test regexp "aaaaaaa"
                    '("aaaaaaa" "a"))
    (rxt-match-test regexp "aaaaaaaa" 'nil)
    (rxt-match-test regexp "aaaaaaaaa" 'nil)
    (rxt-match-test regexp "aaaaaaaaaa"
                    '("aaaaaaaaaa" "aaaa"))
    (rxt-match-test regexp "aaaaaaaaaaa" 'nil)
    (rxt-match-test regexp "aaaaaaaaaaaa" 'nil)
    (rxt-match-test regexp "aaaaaaaaaaaaa" 'nil)
    (rxt-match-test regexp "aaaaaaaaaaaaaa" 'nil)
    (rxt-match-test regexp "aaaaaaaaaaaaaaa" 'nil)
    (rxt-match-test regexp "aaaaaaaaaaaaaaaa" 'nil)))


(ert-deftest rxt-pcre-test-00295 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(a\\1?)(a\\1?)(a\\2?)(a\\3?)$" "")))
    (rxt-match-test regexp "a" 'nil)
    (rxt-match-test regexp "aa" 'nil)
    (rxt-match-test regexp "aaa" 'nil)
    (rxt-match-test regexp "aaaa"
                    '("aaaa" "a" "a" "a" "a"))
    (rxt-match-test regexp "aaaaa"
                    '("aaaaa" "a" "aa" "a" "a"))
    (rxt-match-test regexp "aaaaaa"
                    '("aaaaaa" "a" "aa" "a" "aa"))
    (rxt-match-test regexp "aaaaaaa"
                    '("aaaaaaa" "a" "aa" "aaa" "a"))
    (rxt-match-test regexp "aaaaaaaa" 'nil)
    (rxt-match-test regexp "aaaaaaaaa" 'nil)
    (rxt-match-test regexp "aaaaaaaaaa"
                    '("aaaaaaaaaa" "a" "aa" "aaa" "aaaa"))
    (rxt-match-test regexp "aaaaaaaaaaa" 'nil)
    (rxt-match-test regexp "aaaaaaaaaaaa" 'nil)
    (rxt-match-test regexp "aaaaaaaaaaaaa" 'nil)
    (rxt-match-test regexp "aaaaaaaaaaaaaa" 'nil)
    (rxt-match-test regexp "aaaaaaaaaaaaaaa" 'nil)
    (rxt-match-test regexp "aaaaaaaaaaaaaaaa" 'nil)))


(ert-deftest rxt-pcre-test-00296 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "The following tests are taken from the Perl 5.005 test suite; some of them" "")))
    (rxt-match-test regexp "/are compatible with 5.004, but I'd rather not have to sort them out./" 'nil)))


(ert-deftest rxt-pcre-test-00297 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "abc" "")))
    (rxt-match-test regexp "abc"
                    '("abc"))
    (rxt-match-test regexp "xabcy"
                    '("abc"))
    (rxt-match-test regexp "ababc"
                    '("abc"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "xbc" 'nil)
    (rxt-match-test regexp "axc" 'nil)
    (rxt-match-test regexp "abx" 'nil)))


(ert-deftest rxt-pcre-test-00298 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab*c" "")))
    (rxt-match-test regexp "abc"
                    '("abc"))))


(ert-deftest rxt-pcre-test-00299 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab*bc" "")))
    (rxt-match-test regexp "abc"
                    '("abc"))
    (rxt-match-test regexp "abbc"
                    '("abbc"))
    (rxt-match-test regexp "abbbbc"
                    '("abbbbc"))))


(ert-deftest rxt-pcre-test-00300 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp ".{1}" "")))
    (rxt-match-test regexp "abbbbc"
                    '("a"))))


(ert-deftest rxt-pcre-test-00301 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp ".{3,4}" "")))
    (rxt-match-test regexp "abbbbc"
                    '("abbb"))))


(ert-deftest rxt-pcre-test-00302 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab{0,}bc" "")))
    (rxt-match-test regexp "abbbbc"
                    '("abbbbc"))))


(ert-deftest rxt-pcre-test-00303 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab+bc" "")))
    (rxt-match-test regexp "abbc"
                    '("abbc"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "abc" 'nil)
    (rxt-match-test regexp "abq" 'nil)))


(ert-deftest rxt-pcre-test-00304 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab{1,}bc" "")))))


(ert-deftest rxt-pcre-test-00305 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab+bc" "")))
    (rxt-match-test regexp "abbbbc"
                    '("abbbbc"))))


(ert-deftest rxt-pcre-test-00306 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab{1,}bc" "")))
    (rxt-match-test regexp "abbbbc"
                    '("abbbbc"))))


(ert-deftest rxt-pcre-test-00307 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab{1,3}bc" "")))
    (rxt-match-test regexp "abbbbc"
                    '("abbbbc"))))


(ert-deftest rxt-pcre-test-00308 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab{3,4}bc" "")))
    (rxt-match-test regexp "abbbbc"
                    '("abbbbc"))))


(ert-deftest rxt-pcre-test-00309 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab{4,5}bc" "")))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "abq" 'nil)
    (rxt-match-test regexp "abbbbc" 'nil)))


(ert-deftest rxt-pcre-test-00310 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab?bc" "")))
    (rxt-match-test regexp "abbc"
                    '("abbc"))
    (rxt-match-test regexp "abc"
                    '("abc"))))


(ert-deftest rxt-pcre-test-00311 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab{0,1}bc" "")))
    (rxt-match-test regexp "abc"
                    '("abc"))))


(ert-deftest rxt-pcre-test-00312 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab?bc" "")))))


(ert-deftest rxt-pcre-test-00313 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab?c" "")))
    (rxt-match-test regexp "abc"
                    '("abc"))))


(ert-deftest rxt-pcre-test-00314 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab{0,1}c" "")))
    (rxt-match-test regexp "abc"
                    '("abc"))))


(ert-deftest rxt-pcre-test-00315 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^abc$" "")))
    (rxt-match-test regexp "abc"
                    '("abc"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "abbbbc" 'nil)
    (rxt-match-test regexp "abcc" 'nil)))


(ert-deftest rxt-pcre-test-00316 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^abc" "")))
    (rxt-match-test regexp "abcc"
                    '("abc"))))


(ert-deftest rxt-pcre-test-00317 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^abc$" "")))))


(ert-deftest rxt-pcre-test-00318 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "abc$" "")))
    (rxt-match-test regexp "aabc"
                    '("abc"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "aabc"
                    '("abc"))
    (rxt-match-test regexp "aabcd" 'nil)))


(ert-deftest rxt-pcre-test-00319 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^" "")))
    (rxt-match-test regexp "abc"
                    '(""))))


(ert-deftest rxt-pcre-test-00320 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "$" "")))
    (rxt-match-test regexp "abc"
                    '(""))))


(ert-deftest rxt-pcre-test-00321 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a.c" "")))
    (rxt-match-test regexp "abc"
                    '("abc"))
    (rxt-match-test regexp "axc"
                    '("axc"))))


(ert-deftest rxt-pcre-test-00322 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a.*c" "")))
    (rxt-match-test regexp "axyzc"
                    '("axyzc"))))


(ert-deftest rxt-pcre-test-00323 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a[bc]d" "")))
    (rxt-match-test regexp "abd"
                    '("abd"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "axyzd" 'nil)
    (rxt-match-test regexp "abc" 'nil)))


(ert-deftest rxt-pcre-test-00324 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a[b-d]e" "")))
    (rxt-match-test regexp "ace"
                    '("ace"))))


(ert-deftest rxt-pcre-test-00325 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a[b-d]" "")))
    (rxt-match-test regexp "aac"
                    '("ac"))))


(ert-deftest rxt-pcre-test-00326 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a[-b]" "")))
    (rxt-match-test regexp "a-"
                    '("a-"))))


(ert-deftest rxt-pcre-test-00327 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a[b-]" "")))
    (rxt-match-test regexp "a-"
                    '("a-"))))


(ert-deftest rxt-pcre-test-00328 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a]" "")))
    (rxt-match-test regexp "a]"
                    '("a]"))))


(ert-deftest rxt-pcre-test-00329 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a[]]b" "")))
    (rxt-match-test regexp "a]b"
                    '("a]b"))))


(ert-deftest rxt-pcre-test-00330 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a[^bc]d" "")))
    (rxt-match-test regexp "aed"
                    '("aed"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "abd" 'nil)
    (rxt-match-test regexp "abd" 'nil)))


(ert-deftest rxt-pcre-test-00331 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a[^-b]c" "")))
    (rxt-match-test regexp "adc"
                    '("adc"))))


(ert-deftest rxt-pcre-test-00332 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a[^]b]c" "")))
    (rxt-match-test regexp "adc"
                    '("adc"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "a-c"
                    '("a-c"))
    (rxt-match-test regexp "a]c" 'nil)))


(ert-deftest rxt-pcre-test-00333 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\ba\\b" "")))
    (rxt-match-test regexp "a-"
                    '("a"))
    (rxt-match-test regexp "-a"
                    '("a"))
    (rxt-match-test regexp "-a-"
                    '("a"))))


(ert-deftest rxt-pcre-test-00334 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\by\\b" "")))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "xy" 'nil)
    (rxt-match-test regexp "yz" 'nil)
    (rxt-match-test regexp "xyz" 'nil)))


(ert-deftest rxt-pcre-test-00335 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\Ba\\B" "")))
    (rxt-match-test regexp "*** Failers"
                    '("a"))
    (rxt-match-test regexp "a-" 'nil)
    (rxt-match-test regexp "-a" 'nil)
    (rxt-match-test regexp "-a-" 'nil)))


(ert-deftest rxt-pcre-test-00336 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\By\\b" "")))
    (rxt-match-test regexp "xy"
                    '("y"))))


(ert-deftest rxt-pcre-test-00337 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\by\\B" "")))
    (rxt-match-test regexp "yz"
                    '("y"))))


(ert-deftest rxt-pcre-test-00338 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\By\\B" "")))
    (rxt-match-test regexp "xyz"
                    '("y"))))


(ert-deftest rxt-pcre-test-00339 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\w" "")))
    (rxt-match-test regexp "a"
                    '("a"))))


(ert-deftest rxt-pcre-test-00340 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\W" "")))
    (rxt-match-test regexp "-"
                    '("-"))
    (rxt-match-test regexp "*** Failers"
                    '("*"))
    (rxt-match-test regexp "-"
                    '("-"))
    (rxt-match-test regexp "a" 'nil)))


(ert-deftest rxt-pcre-test-00341 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a\\sb" "")))
    (rxt-match-test regexp "a b"
                    '("a b"))))


(ert-deftest rxt-pcre-test-00342 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a\\Sb" "")))
    (rxt-match-test regexp "a-b"
                    '("a-b"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "a-b"
                    '("a-b"))
    (rxt-match-test regexp "a b" 'nil)))


(ert-deftest rxt-pcre-test-00343 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\d" "")))
    (rxt-match-test regexp "1"
                    '("1"))))


(ert-deftest rxt-pcre-test-00344 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\D" "")))
    (rxt-match-test regexp "-"
                    '("-"))
    (rxt-match-test regexp "*** Failers"
                    '("*"))
    (rxt-match-test regexp "-"
                    '("-"))
    (rxt-match-test regexp "1" 'nil)))


(ert-deftest rxt-pcre-test-00345 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[\\w]" "")))
    (rxt-match-test regexp "a"
                    '("a"))))


(ert-deftest rxt-pcre-test-00346 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[\\W]" "")))
    (rxt-match-test regexp "-"
                    '("-"))
    (rxt-match-test regexp "*** Failers"
                    '("*"))
    (rxt-match-test regexp "-"
                    '("-"))
    (rxt-match-test regexp "a" 'nil)))


(ert-deftest rxt-pcre-test-00347 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a[\\s]b" "")))
    (rxt-match-test regexp "a b"
                    '("a b"))))


(ert-deftest rxt-pcre-test-00348 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a[\\S]b" "")))
    (rxt-match-test regexp "a-b"
                    '("a-b"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "a-b"
                    '("a-b"))
    (rxt-match-test regexp "a b" 'nil)))


(ert-deftest rxt-pcre-test-00349 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[\\d]" "")))
    (rxt-match-test regexp "1"
                    '("1"))))


(ert-deftest rxt-pcre-test-00350 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[\\D]" "")))
    (rxt-match-test regexp "-"
                    '("-"))
    (rxt-match-test regexp "*** Failers"
                    '("*"))
    (rxt-match-test regexp "-"
                    '("-"))
    (rxt-match-test regexp "1" 'nil)))


(ert-deftest rxt-pcre-test-00351 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab|cd" "")))
    (rxt-match-test regexp "abc"
                    '("ab"))
    (rxt-match-test regexp "abcd"
                    '("ab"))))


(ert-deftest rxt-pcre-test-00352 nil 
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "()ef" "")))
    (rxt-match-test regexp "def"
                    '("ef" ""))))


(ert-deftest rxt-pcre-test-00353 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "$b" "")))))


(ert-deftest rxt-pcre-test-00354 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a\\(b" "")))
    (rxt-match-test regexp "a(b"
                    '("a(b"))))


(ert-deftest rxt-pcre-test-00355 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a\\(*b" "")))
    (rxt-match-test regexp "ab"
                    '("ab"))
    (rxt-match-test regexp "a((b"
                    '("a((b"))))


(ert-deftest rxt-pcre-test-00356 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a\\\\b" "")))
    (rxt-match-test regexp "a" 'nil)))


(ert-deftest rxt-pcre-test-00357 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((a))" "")))
    (rxt-match-test regexp "abc"
                    '("a" "a" "a"))))


(ert-deftest rxt-pcre-test-00358 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(a)b(c)" "")))
    (rxt-match-test regexp "abc"
                    '("abc" "a" "c"))))


(ert-deftest rxt-pcre-test-00359 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a+b+c" "")))
    (rxt-match-test regexp "aabbabc"
                    '("abc"))))


(ert-deftest rxt-pcre-test-00360 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a{1,}b{1,}c" "")))
    (rxt-match-test regexp "aabbabc"
                    '("abc"))))


(ert-deftest rxt-pcre-test-00361 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a.+?c" "")))
    (rxt-match-test regexp "abcabc"
                    '("abc"))))


(ert-deftest rxt-pcre-test-00362 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(a+|b)*" "")))
    (rxt-match-test regexp "ab"
                    '("ab" "b"))))


(ert-deftest rxt-pcre-test-00363 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(a+|b){0,}" "")))
    (rxt-match-test regexp "ab"
                    '("ab" "b"))))


(ert-deftest rxt-pcre-test-00364 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(a+|b)+" "")))
    (rxt-match-test regexp "ab"
                    '("ab" "b"))))


(ert-deftest rxt-pcre-test-00365 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(a+|b){1,}" "")))
    (rxt-match-test regexp "ab"
                    '("ab" "b"))))


(ert-deftest rxt-pcre-test-00366 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(a+|b)?" "")))
    (rxt-match-test regexp "ab"
                    '("a" "a"))))


(ert-deftest rxt-pcre-test-00367 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(a+|b){0,1}" "")))
    (rxt-match-test regexp "ab"
                    '("a" "a"))))


(ert-deftest rxt-pcre-test-00368 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[^ab]*" "")))
    (rxt-match-test regexp "cde"
                    '("cde"))))


(ert-deftest rxt-pcre-test-00369 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "abc" "")))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "b" 'nil)))


(ert-deftest rxt-pcre-test-00370 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a*" "")))))


(ert-deftest rxt-pcre-test-00371 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "([abc])*d" "")))
    (rxt-match-test regexp "abbbcd"
                    '("abbbcd" "c"))))


(ert-deftest rxt-pcre-test-00372 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "([abc])*bcd" "")))
    (rxt-match-test regexp "abcd"
                    '("abcd" "a"))))


(ert-deftest rxt-pcre-test-00373 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a|b|c|d|e" "")))
    (rxt-match-test regexp "e"
                    '("e"))))


(ert-deftest rxt-pcre-test-00374 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(a|b|c|d|e)f" "")))
    (rxt-match-test regexp "ef"
                    '("ef" "e"))))


(ert-deftest rxt-pcre-test-00375 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "abcd*efg" "")))
    (rxt-match-test regexp "abcdefg"
                    '("abcdefg"))))


(ert-deftest rxt-pcre-test-00376 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab*" "")))
    (rxt-match-test regexp "xabyabbbz"
                    '("ab"))
    (rxt-match-test regexp "xayabbbz"
                    '("a"))))


(ert-deftest rxt-pcre-test-00377 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(ab|cd)e" "")))
    (rxt-match-test regexp "abcde"
                    '("cde" "cd"))))


(ert-deftest rxt-pcre-test-00378 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[abhgefdc]ij" "")))
    (rxt-match-test regexp "hij"
                    '("hij"))))


(ert-deftest rxt-pcre-test-00379 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(ab|cd)e" "")))))


(ert-deftest rxt-pcre-test-00380 nil 
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(abc|)ef" "")))
    (rxt-match-test regexp "abcdef"
                    '("ef" ""))))


(ert-deftest rxt-pcre-test-00381 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(a|b)c*d" "")))
    (rxt-match-test regexp "abcd"
                    '("bcd" "b"))))


(ert-deftest rxt-pcre-test-00382 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(ab|ab*)bc" "")))
    (rxt-match-test regexp "abc"
                    '("abc" "a"))))


(ert-deftest rxt-pcre-test-00383 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a([bc]*)c*" "")))
    (rxt-match-test regexp "abc"
                    '("abc" "bc"))))


(ert-deftest rxt-pcre-test-00384 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a([bc]*)(c*d)" "")))
    (rxt-match-test regexp "abcd"
                    '("abcd" "bc" "d"))))


(ert-deftest rxt-pcre-test-00385 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a([bc]+)(c*d)" "")))
    (rxt-match-test regexp "abcd"
                    '("abcd" "bc" "d"))))


(ert-deftest rxt-pcre-test-00386 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a([bc]*)(c+d)" "")))
    (rxt-match-test regexp "abcd"
                    '("abcd" "b" "cd"))))


(ert-deftest rxt-pcre-test-00387 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a[bcd]*dcdcde" "")))
    (rxt-match-test regexp "adcdcde"
                    '("adcdcde"))))


(ert-deftest rxt-pcre-test-00388 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a[bcd]+dcdcde" "")))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "abcde" 'nil)
    (rxt-match-test regexp "adcdcde" 'nil)))


(ert-deftest rxt-pcre-test-00389 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(ab|a)b*c" "")))
    (rxt-match-test regexp "abc"
                    '("abc" "ab"))))


(ert-deftest rxt-pcre-test-00390 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((a)(b)c)(d)" "")))
    (rxt-match-test regexp "abcd"
                    '("abcd" "abc" "a" "b" "d"))))


(ert-deftest rxt-pcre-test-00391 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[a-zA-Z_][a-zA-Z0-9_]*" "")))
    (rxt-match-test regexp "alpha"
                    '("alpha"))))


(ert-deftest rxt-pcre-test-00392 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^a(bc+|b[eh])g|.h$" "")))
    (rxt-match-test regexp "abh"
                    '("bh"))))


(ert-deftest rxt-pcre-test-00393 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(bc+d$|ef*g.|h?i(j|k))" "")))
    (rxt-match-test regexp "effgz"
                    '("effgz" "effgz"))
    (rxt-match-test regexp "ij"
                    '("ij" "ij" "j"))
    (rxt-match-test regexp "reffgz"
                    '("effgz" "effgz"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "effg" 'nil)
    (rxt-match-test regexp "bcdd" 'nil)))


(ert-deftest rxt-pcre-test-00394 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((((((((((a))))))))))" "")))
    (rxt-match-test regexp "a"
                    '("a" "a" "a" "a" "a" "a" "a" "a" "a" "a" "a"))))


(ert-deftest rxt-pcre-test-00395 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((((((((((a))))))))))\\10" "")))
    (rxt-match-test regexp "aa"
                    '("aa" "a" "a" "a" "a" "a" "a" "a" "a" "a" "a"))))


(ert-deftest rxt-pcre-test-00396 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(((((((((a)))))))))" "")))
    (rxt-match-test regexp "a"
                    '("a" "a" "a" "a" "a" "a" "a" "a" "a" "a"))))


(ert-deftest rxt-pcre-test-00397 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "multiple words of text" "")))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "aa" 'nil)
    (rxt-match-test regexp "uh-uh" 'nil)))


(ert-deftest rxt-pcre-test-00398 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "multiple words" "")))
    (rxt-match-test regexp "multiple words, yeah"
                    '("multiple words"))))


(ert-deftest rxt-pcre-test-00399 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(.*)c(.*)" "")))
    (rxt-match-test regexp "abcde"
                    '("abcde" "ab" "de"))))


(ert-deftest rxt-pcre-test-00400 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\((.*), (.*)\\)" "")))
    (rxt-match-test regexp "(a, b)"
                    '("(a, b)" "a" "b"))))


(ert-deftest rxt-pcre-test-00401 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[k]" "")))))


(ert-deftest rxt-pcre-test-00402 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "abcd" "")))
    (rxt-match-test regexp "abcd"
                    '("abcd"))))


(ert-deftest rxt-pcre-test-00403 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a(bc)d" "")))
    (rxt-match-test regexp "abcd"
                    '("abcd" "bc"))))


(ert-deftest rxt-pcre-test-00404 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a[-]?c" "")))
    (rxt-match-test regexp "ac"
                    '("ac"))))


(ert-deftest rxt-pcre-test-00405 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(abc)\\1" "")))
    (rxt-match-test regexp "abcabc"
                    '("abcabc" "abc"))))


(ert-deftest rxt-pcre-test-00406 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "([a-c]*)\\1" "")))
    (rxt-match-test regexp "abcabc"
                    '("abcabc" "abc"))))


(ert-deftest rxt-pcre-test-00407 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(a)|\\1" "")))
    (rxt-match-test regexp "a"
                    '("a" "a"))
    (rxt-match-test regexp "*** Failers"
                    '("a" "a"))
    (rxt-match-test regexp "ab"
                    '("a" "a"))
    (rxt-match-test regexp "x" 'nil)))


(ert-deftest rxt-pcre-test-00408 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(([a-c])b*?\\2)*" "")))
    (rxt-match-test regexp "ababbbcbc"
                    '("ababb" "bb" "b"))))


(ert-deftest rxt-pcre-test-00409 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(([a-c])b*?\\2){3}" "")))
    (rxt-match-test regexp "ababbbcbc"
                    '("ababbbcbc" "cbc" "c"))))


(ert-deftest rxt-pcre-test-00410 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((\\3|b)\\2(a)x)+" "")))
    (rxt-match-test regexp "aaaxabaxbaaxbbax"
                    '("bbax" "bbax" "b" "a"))))


(ert-deftest rxt-pcre-test-00411 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((\\3|b)\\2(a)){2,}" "")))
    (rxt-match-test regexp "bbaababbabaaaaabbaaaabba"
                    '("bbaaaabba" "bba" "b" "a"))))


(ert-deftest rxt-pcre-test-00412 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "abc" "i")))
    (rxt-match-test regexp "ABC"
                    '("ABC"))
    (rxt-match-test regexp "XABCY"
                    '("ABC"))
    (rxt-match-test regexp "ABABC"
                    '("ABC"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "aaxabxbaxbbx" 'nil)
    (rxt-match-test regexp "XBC" 'nil)
    (rxt-match-test regexp "AXC" 'nil)
    (rxt-match-test regexp "ABX" 'nil)))


(ert-deftest rxt-pcre-test-00413 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab*c" "i")))
    (rxt-match-test regexp "ABC"
                    '("ABC"))))


(ert-deftest rxt-pcre-test-00414 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab*bc" "i")))
    (rxt-match-test regexp "ABC"
                    '("ABC"))
    (rxt-match-test regexp "ABBC"
                    '("ABBC"))))


(ert-deftest rxt-pcre-test-00415 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab*?bc" "i")))
    (rxt-match-test regexp "ABBBBC"
                    '("ABBBBC"))))


(ert-deftest rxt-pcre-test-00416 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab{0,}?bc" "i")))
    (rxt-match-test regexp "ABBBBC"
                    '("ABBBBC"))))


(ert-deftest rxt-pcre-test-00417 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab+?bc" "i")))
    (rxt-match-test regexp "ABBC"
                    '("ABBC"))))


(ert-deftest rxt-pcre-test-00418 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab+bc" "i")))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "ABC" 'nil)
    (rxt-match-test regexp "ABQ" 'nil)))


(ert-deftest rxt-pcre-test-00419 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab{1,}bc" "i")))))


(ert-deftest rxt-pcre-test-00420 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab+bc" "i")))
    (rxt-match-test regexp "ABBBBC"
                    '("ABBBBC"))))


(ert-deftest rxt-pcre-test-00421 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab{1,}?bc" "i")))
    (rxt-match-test regexp "ABBBBC"
                    '("ABBBBC"))))


(ert-deftest rxt-pcre-test-00422 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab{1,3}?bc" "i")))
    (rxt-match-test regexp "ABBBBC"
                    '("ABBBBC"))))


(ert-deftest rxt-pcre-test-00423 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab{3,4}?bc" "i")))
    (rxt-match-test regexp "ABBBBC"
                    '("ABBBBC"))))


(ert-deftest rxt-pcre-test-00424 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab{4,5}?bc" "i")))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "ABQ" 'nil)
    (rxt-match-test regexp "ABBBBC" 'nil)))


(ert-deftest rxt-pcre-test-00425 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab??bc" "i")))
    (rxt-match-test regexp "ABBC"
                    '("ABBC"))
    (rxt-match-test regexp "ABC"
                    '("ABC"))))


(ert-deftest rxt-pcre-test-00426 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab{0,1}?bc" "i")))
    (rxt-match-test regexp "ABC"
                    '("ABC"))))


(ert-deftest rxt-pcre-test-00427 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab??bc" "i")))))


(ert-deftest rxt-pcre-test-00428 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab??c" "i")))
    (rxt-match-test regexp "ABC"
                    '("ABC"))))


(ert-deftest rxt-pcre-test-00429 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab{0,1}?c" "i")))
    (rxt-match-test regexp "ABC"
                    '("ABC"))))


(ert-deftest rxt-pcre-test-00430 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^abc$" "i")))
    (rxt-match-test regexp "ABC"
                    '("ABC"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "ABBBBC" 'nil)
    (rxt-match-test regexp "ABCC" 'nil)))


(ert-deftest rxt-pcre-test-00431 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^abc" "i")))
    (rxt-match-test regexp "ABCC"
                    '("ABC"))))


(ert-deftest rxt-pcre-test-00432 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^abc$" "i")))))


(ert-deftest rxt-pcre-test-00433 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "abc$" "i")))
    (rxt-match-test regexp "AABC"
                    '("ABC"))))


(ert-deftest rxt-pcre-test-00434 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^" "i")))
    (rxt-match-test regexp "ABC"
                    '(""))))


(ert-deftest rxt-pcre-test-00435 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "$" "i")))
    (rxt-match-test regexp "ABC"
                    '(""))))


(ert-deftest rxt-pcre-test-00436 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a.c" "i")))
    (rxt-match-test regexp "ABC"
                    '("ABC"))
    (rxt-match-test regexp "AXC"
                    '("AXC"))))


(ert-deftest rxt-pcre-test-00437 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a.*?c" "i")))
    (rxt-match-test regexp "AXYZC"
                    '("AXYZC"))))


(ert-deftest rxt-pcre-test-00438 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a.*c" "i")))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "AABC"
                    '("AABC"))
    (rxt-match-test regexp "AXYZD" 'nil)))


(ert-deftest rxt-pcre-test-00439 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a[bc]d" "i")))
    (rxt-match-test regexp "ABD"
                    '("ABD"))))


(ert-deftest rxt-pcre-test-00440 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a[b-d]e" "i")))
    (rxt-match-test regexp "ACE"
                    '("ACE"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "ABC" 'nil)
    (rxt-match-test regexp "ABD" 'nil)))


(ert-deftest rxt-pcre-test-00441 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a[b-d]" "i")))
    (rxt-match-test regexp "AAC"
                    '("AC"))))


(ert-deftest rxt-pcre-test-00442 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a[-b]" "i")))
    (rxt-match-test regexp "A-"
                    '("A-"))))


(ert-deftest rxt-pcre-test-00443 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a[b-]" "i")))
    (rxt-match-test regexp "A-"
                    '("A-"))))


(ert-deftest rxt-pcre-test-00444 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a]" "i")))
    (rxt-match-test regexp "A]"
                    '("A]"))))


(ert-deftest rxt-pcre-test-00445 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a[]]b" "i")))
    (rxt-match-test regexp "A]B"
                    '("A]B"))))


(ert-deftest rxt-pcre-test-00446 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a[^bc]d" "i")))
    (rxt-match-test regexp "AED"
                    '("AED"))))


(ert-deftest rxt-pcre-test-00447 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a[^-b]c" "i")))
    (rxt-match-test regexp "ADC"
                    '("ADC"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "ABD" 'nil)
    (rxt-match-test regexp "A-C" 'nil)))


(ert-deftest rxt-pcre-test-00448 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a[^]b]c" "i")))
    (rxt-match-test regexp "ADC"
                    '("ADC"))))


(ert-deftest rxt-pcre-test-00449 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab|cd" "i")))
    (rxt-match-test regexp "ABC"
                    '("AB"))
    (rxt-match-test regexp "ABCD"
                    '("AB"))))


(ert-deftest rxt-pcre-test-00450 nil 
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "()ef" "i")))
    (rxt-match-test regexp "DEF"
                    '("EF" ""))))


(ert-deftest rxt-pcre-test-00451 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "$b" "i")))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "A]C" 'nil)
    (rxt-match-test regexp "B" 'nil)))


(ert-deftest rxt-pcre-test-00452 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a\\(b" "i")))
    (rxt-match-test regexp "A(B"
                    '("A(B"))))


(ert-deftest rxt-pcre-test-00453 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a\\(*b" "i")))
    (rxt-match-test regexp "AB"
                    '("AB"))
    (rxt-match-test regexp "A((B"
                    '("A((B"))))


(ert-deftest rxt-pcre-test-00454 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a\\\\b" "i")))
    (rxt-match-test regexp "AB" 'nil)))


(ert-deftest rxt-pcre-test-00455 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((a))" "i")))
    (rxt-match-test regexp "ABC"
                    '("A" "A" "A"))))


(ert-deftest rxt-pcre-test-00456 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(a)b(c)" "i")))
    (rxt-match-test regexp "ABC"
                    '("ABC" "A" "C"))))


(ert-deftest rxt-pcre-test-00457 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a+b+c" "i")))
    (rxt-match-test regexp "AABBABC"
                    '("ABC"))))


(ert-deftest rxt-pcre-test-00458 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a{1,}b{1,}c" "i")))
    (rxt-match-test regexp "AABBABC"
                    '("ABC"))))


(ert-deftest rxt-pcre-test-00459 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a.+?c" "i")))
    (rxt-match-test regexp "ABCABC"
                    '("ABC"))))


(ert-deftest rxt-pcre-test-00460 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a.*?c" "i")))
    (rxt-match-test regexp "ABCABC"
                    '("ABC"))))


(ert-deftest rxt-pcre-test-00461 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a.{0,5}?c" "i")))
    (rxt-match-test regexp "ABCABC"
                    '("ABC"))))


(ert-deftest rxt-pcre-test-00462 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(a+|b)*" "i")))
    (rxt-match-test regexp "AB"
                    '("AB" "B"))))


(ert-deftest rxt-pcre-test-00463 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(a+|b){0,}" "i")))
    (rxt-match-test regexp "AB"
                    '("AB" "B"))))


(ert-deftest rxt-pcre-test-00464 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(a+|b)+" "i")))
    (rxt-match-test regexp "AB"
                    '("AB" "B"))))


(ert-deftest rxt-pcre-test-00465 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(a+|b){1,}" "i")))
    (rxt-match-test regexp "AB"
                    '("AB" "B"))))


(ert-deftest rxt-pcre-test-00466 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(a+|b)?" "i")))
    (rxt-match-test regexp "AB"
                    '("A" "A"))))


(ert-deftest rxt-pcre-test-00467 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(a+|b){0,1}" "i")))
    (rxt-match-test regexp "AB"
                    '("A" "A"))))


(ert-deftest rxt-pcre-test-00468 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(a+|b){0,1}?" "i")))
    (rxt-match-test regexp "AB"
                    '(""))))


(ert-deftest rxt-pcre-test-00469 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[^ab]*" "i")))
    (rxt-match-test regexp "CDE"
                    '("CDE"))))


(ert-deftest rxt-pcre-test-00470 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "abc" "i")))))


(ert-deftest rxt-pcre-test-00471 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a*" "i")))))


(ert-deftest rxt-pcre-test-00472 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "([abc])*d" "i")))
    (rxt-match-test regexp "ABBBCD"
                    '("ABBBCD" "C"))))


(ert-deftest rxt-pcre-test-00473 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "([abc])*bcd" "i")))
    (rxt-match-test regexp "ABCD"
                    '("ABCD" "A"))))


(ert-deftest rxt-pcre-test-00474 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a|b|c|d|e" "i")))
    (rxt-match-test regexp "E"
                    '("E"))))


(ert-deftest rxt-pcre-test-00475 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(a|b|c|d|e)f" "i")))
    (rxt-match-test regexp "EF"
                    '("EF" "E"))))


(ert-deftest rxt-pcre-test-00476 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "abcd*efg" "i")))
    (rxt-match-test regexp "ABCDEFG"
                    '("ABCDEFG"))))


(ert-deftest rxt-pcre-test-00477 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab*" "i")))
    (rxt-match-test regexp "XABYABBBZ"
                    '("AB"))
    (rxt-match-test regexp "XAYABBBZ"
                    '("A"))))


(ert-deftest rxt-pcre-test-00478 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(ab|cd)e" "i")))
    (rxt-match-test regexp "ABCDE"
                    '("CDE" "CD"))))


(ert-deftest rxt-pcre-test-00479 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[abhgefdc]ij" "i")))
    (rxt-match-test regexp "HIJ"
                    '("HIJ"))))


(ert-deftest rxt-pcre-test-00480 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(ab|cd)e" "i")))
    (rxt-match-test regexp "ABCDE" 'nil)))


(ert-deftest rxt-pcre-test-00481 nil 
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(abc|)ef" "i")))
    (rxt-match-test regexp "ABCDEF"
                    '("EF" ""))))


(ert-deftest rxt-pcre-test-00482 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(a|b)c*d" "i")))
    (rxt-match-test regexp "ABCD"
                    '("BCD" "B"))))


(ert-deftest rxt-pcre-test-00483 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(ab|ab*)bc" "i")))
    (rxt-match-test regexp "ABC"
                    '("ABC" "A"))))


(ert-deftest rxt-pcre-test-00484 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a([bc]*)c*" "i")))
    (rxt-match-test regexp "ABC"
                    '("ABC" "BC"))))


(ert-deftest rxt-pcre-test-00485 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a([bc]*)(c*d)" "i")))
    (rxt-match-test regexp "ABCD"
                    '("ABCD" "BC" "D"))))


(ert-deftest rxt-pcre-test-00486 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a([bc]+)(c*d)" "i")))
    (rxt-match-test regexp "ABCD"
                    '("ABCD" "BC" "D"))))


(ert-deftest rxt-pcre-test-00487 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a([bc]*)(c+d)" "i")))
    (rxt-match-test regexp "ABCD"
                    '("ABCD" "B" "CD"))))


(ert-deftest rxt-pcre-test-00488 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a[bcd]*dcdcde" "i")))
    (rxt-match-test regexp "ADCDCDE"
                    '("ADCDCDE"))))


(ert-deftest rxt-pcre-test-00489 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a[bcd]+dcdcde" "i")))))


(ert-deftest rxt-pcre-test-00490 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(ab|a)b*c" "i")))
    (rxt-match-test regexp "ABC"
                    '("ABC" "AB"))))


(ert-deftest rxt-pcre-test-00491 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((a)(b)c)(d)" "i")))
    (rxt-match-test regexp "ABCD"
                    '("ABCD" "ABC" "A" "B" "D"))))


(ert-deftest rxt-pcre-test-00492 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[a-zA-Z_][a-zA-Z0-9_]*" "i")))
    (rxt-match-test regexp "ALPHA"
                    '("ALPHA"))))


(ert-deftest rxt-pcre-test-00493 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^a(bc+|b[eh])g|.h$" "i")))
    (rxt-match-test regexp "ABH"
                    '("BH"))))


(ert-deftest rxt-pcre-test-00494 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(bc+d$|ef*g.|h?i(j|k))" "i")))
    (rxt-match-test regexp "EFFGZ"
                    '("EFFGZ" "EFFGZ"))
    (rxt-match-test regexp "IJ"
                    '("IJ" "IJ" "J"))
    (rxt-match-test regexp "REFFGZ"
                    '("EFFGZ" "EFFGZ"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "ADCDCDE" 'nil)
    (rxt-match-test regexp "EFFG" 'nil)
    (rxt-match-test regexp "BCDD" 'nil)))


(ert-deftest rxt-pcre-test-00495 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((((((((((a))))))))))" "i")))
    (rxt-match-test regexp "A"
                    '("A" "A" "A" "A" "A" "A" "A" "A" "A" "A" "A"))))


(ert-deftest rxt-pcre-test-00496 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((((((((((a))))))))))\\10" "i")))
    (rxt-match-test regexp "AA"
                    '("AA" "A" "A" "A" "A" "A" "A" "A" "A" "A" "A"))))


(ert-deftest rxt-pcre-test-00497 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(((((((((a)))))))))" "i")))
    (rxt-match-test regexp "A"
                    '("A" "A" "A" "A" "A" "A" "A" "A" "A" "A"))))


(ert-deftest rxt-pcre-test-00498 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?:(?:(?:(?:(?:(?:(?:(?:(?:(a))))))))))" "i")))
    (rxt-match-test regexp "A"
                    '("A" "A"))))


(ert-deftest rxt-pcre-test-00499 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?:(?:(?:(?:(?:(?:(?:(?:(?:(a|b|c))))))))))" "i")))
    (rxt-match-test regexp "C"
                    '("C" "C"))))


(ert-deftest rxt-pcre-test-00500 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "multiple words of text" "i")))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "AA" 'nil)
    (rxt-match-test regexp "UH-UH" 'nil)))


(ert-deftest rxt-pcre-test-00501 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "multiple words" "i")))
    (rxt-match-test regexp "MULTIPLE WORDS, YEAH"
                    '("MULTIPLE WORDS"))))


(ert-deftest rxt-pcre-test-00502 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(.*)c(.*)" "i")))
    (rxt-match-test regexp "ABCDE"
                    '("ABCDE" "AB" "DE"))))


(ert-deftest rxt-pcre-test-00503 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\((.*), (.*)\\)" "i")))
    (rxt-match-test regexp "(A, B)"
                    '("(A, B)" "A" "B"))))


(ert-deftest rxt-pcre-test-00504 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[k]" "i")))))


(ert-deftest rxt-pcre-test-00505 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "abcd" "i")))
    (rxt-match-test regexp "ABCD"
                    '("ABCD"))))


(ert-deftest rxt-pcre-test-00506 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a(bc)d" "i")))
    (rxt-match-test regexp "ABCD"
                    '("ABCD" "BC"))))


(ert-deftest rxt-pcre-test-00507 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a[-]?c" "i")))
    (rxt-match-test regexp "AC"
                    '("AC"))))


(ert-deftest rxt-pcre-test-00508 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(abc)\\1" "i")))
    (rxt-match-test regexp "ABCABC"
                    '("ABCABC" "ABC"))))


(ert-deftest rxt-pcre-test-00509 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "([a-c]*)\\1" "i")))
    (rxt-match-test regexp "ABCABC"
                    '("ABCABC" "ABC"))))


(ert-deftest rxt-pcre-test-00510 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a(?!b)." "")))
    (rxt-match-test regexp "abad"
                    '("ad"))))


(ert-deftest rxt-pcre-test-00511 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a(?=d)." "")))
    (rxt-match-test regexp "abad"
                    '("ad"))))


(ert-deftest rxt-pcre-test-00512 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a(?=c|d)." "")))
    (rxt-match-test regexp "abad"
                    '("ad"))))


(ert-deftest rxt-pcre-test-00513 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a(?:b|c|d)(.)" "")))
    (rxt-match-test regexp "ace"
                    '("ace" "e"))))


(ert-deftest rxt-pcre-test-00514 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a(?:b|c|d)*(.)" "")))
    (rxt-match-test regexp "ace"
                    '("ace" "e"))))


(ert-deftest rxt-pcre-test-00515 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a(?:b|c|d)+?(.)" "")))
    (rxt-match-test regexp "ace"
                    '("ace" "e"))
    (rxt-match-test regexp "acdbcdbe"
                    '("acd" "d"))))


(ert-deftest rxt-pcre-test-00516 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a(?:b|c|d)+(.)" "")))
    (rxt-match-test regexp "acdbcdbe"
                    '("acdbcdbe" "e"))))


(ert-deftest rxt-pcre-test-00517 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a(?:b|c|d){2}(.)" "")))
    (rxt-match-test regexp "acdbcdbe"
                    '("acdb" "b"))))


(ert-deftest rxt-pcre-test-00518 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a(?:b|c|d){4,5}(.)" "")))
    (rxt-match-test regexp "acdbcdbe"
                    '("acdbcdb" "b"))))


(ert-deftest rxt-pcre-test-00519 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a(?:b|c|d){4,5}?(.)" "")))
    (rxt-match-test regexp "acdbcdbe"
                    '("acdbcd" "d"))))


(ert-deftest rxt-pcre-test-00520 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((foo)|(bar))*" "")))
    (rxt-match-test regexp "foobar"
                    '("foobar" "bar" "foo" "bar"))))


(ert-deftest rxt-pcre-test-00521 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a(?:b|c|d){6,7}(.)" "")))
    (rxt-match-test regexp "acdbcdbe"
                    '("acdbcdbe" "e"))))


(ert-deftest rxt-pcre-test-00522 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a(?:b|c|d){6,7}?(.)" "")))
    (rxt-match-test regexp "acdbcdbe"
                    '("acdbcdbe" "e"))))


(ert-deftest rxt-pcre-test-00523 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a(?:b|c|d){5,6}(.)" "")))
    (rxt-match-test regexp "acdbcdbe"
                    '("acdbcdbe" "e"))))


(ert-deftest rxt-pcre-test-00524 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a(?:b|c|d){5,6}?(.)" "")))
    (rxt-match-test regexp "acdbcdbe"
                    '("acdbcdb" "b"))))


(ert-deftest rxt-pcre-test-00525 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a(?:b|c|d){5,7}(.)" "")))
    (rxt-match-test regexp "acdbcdbe"
                    '("acdbcdbe" "e"))))


(ert-deftest rxt-pcre-test-00526 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a(?:b|c|d){5,7}?(.)" "")))
    (rxt-match-test regexp "acdbcdbe"
                    '("acdbcdb" "b"))))


(ert-deftest rxt-pcre-test-00527 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a(?:b|(c|e){1,2}?|d)+?(.)" "")))
    (rxt-match-test regexp "ace"
                    '("ace" "c" "e"))))


(ert-deftest rxt-pcre-test-00528 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(.+)?B" "")))
    (rxt-match-test regexp "AB"
                    '("AB" "A"))))


(ert-deftest rxt-pcre-test-00529 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^([^a-z])|(\\^)$" "")))
    (rxt-match-test regexp "."
                    '("." "."))))


(ert-deftest rxt-pcre-test-00530 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^[<>]&" "")))
    (rxt-match-test regexp "<&OUT"
                    '("<&"))))


(ert-deftest rxt-pcre-test-00531 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(a\\1?){4}$" "")))
    (rxt-match-test regexp "aaaaaaaaaa"
                    '("aaaaaaaaaa" "aaaa"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "AB" 'nil)
    (rxt-match-test regexp "aaaaaaaaa" 'nil)
    (rxt-match-test regexp "aaaaaaaaaaa" 'nil)))


(ert-deftest rxt-pcre-test-00532 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(a(?(1)\\1)){4}$" "")))
    (rxt-match-test regexp "aaaaaaaaaa"
                    '("aaaaaaaaaa" "aaaa"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "aaaaaaaaa" 'nil)
    (rxt-match-test regexp "aaaaaaaaaaa" 'nil)))


(ert-deftest rxt-pcre-test-00533 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?:(f)(o)(o)|(b)(a)(r))*" "")))
    (rxt-match-test regexp "foobar"
                    '("foobar" "f" "o" "o" "b" "a" "r"))))


(ert-deftest rxt-pcre-test-00534 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?<=a)b" "")))
    (rxt-match-test regexp "ab"
                    '("b"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "cb" 'nil)
    (rxt-match-test regexp "b" 'nil)))


(ert-deftest rxt-pcre-test-00535 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?<!c)b" "")))
    (rxt-match-test regexp "ab"
                    '("b"))
    (rxt-match-test regexp "b"
                    '("b"))
    (rxt-match-test regexp "b"
                    '("b"))))


(ert-deftest rxt-pcre-test-00536 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?:..)*a" "")))
    (rxt-match-test regexp "aba"
                    '("aba"))))


(ert-deftest rxt-pcre-test-00537 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?:..)*?a" "")))
    (rxt-match-test regexp "aba"
                    '("a"))))


(ert-deftest rxt-pcre-test-00538 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?:b|a(?=(.)))*\\1" "")))
    (rxt-match-test regexp "abc"
                    '("ab" "b"))))


(ert-deftest rxt-pcre-test-00539 nil 
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(){3,5}" "")))
    (rxt-match-test regexp "abc"
                    '("" ""))))


(ert-deftest rxt-pcre-test-00540 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(a+)*ax" "")))
    (rxt-match-test regexp "aax"
                    '("aax" "a"))))


(ert-deftest rxt-pcre-test-00541 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^((a|b)+)*ax" "")))
    (rxt-match-test regexp "aax"
                    '("aax" "a" "a"))))


(ert-deftest rxt-pcre-test-00542 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^((a|bc)+)*ax" "")))
    (rxt-match-test regexp "aax"
                    '("aax" "a" "a"))))


(ert-deftest rxt-pcre-test-00543 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(a|x)*ab" "")))
    (rxt-match-test regexp "cab"
                    '("ab"))))


(ert-deftest rxt-pcre-test-00544 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(a)*ab" "")))
    (rxt-match-test regexp "cab"
                    '("ab"))))


(ert-deftest rxt-pcre-test-00545 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?:(?i)a)b" "")))
    (rxt-match-test regexp "ab"
                    '("ab"))))


(ert-deftest rxt-pcre-test-00546 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((?i)a)b" "")))
    (rxt-match-test regexp "ab"
                    '("ab" "a"))))


(ert-deftest rxt-pcre-test-00547 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?:(?i)a)b" "")))
    (rxt-match-test regexp "Ab"
                    '("Ab"))))


(ert-deftest rxt-pcre-test-00548 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((?i)a)b" "")))
    (rxt-match-test regexp "Ab"
                    '("Ab" "A"))))


(ert-deftest rxt-pcre-test-00549 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?:(?i)a)b" "")))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "cb" 'nil)
    (rxt-match-test regexp "aB" 'nil)))


(ert-deftest rxt-pcre-test-00550 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((?i)a)b" "")))))


(ert-deftest rxt-pcre-test-00551 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?i:a)b" "")))
    (rxt-match-test regexp "ab"
                    '("ab"))))


(ert-deftest rxt-pcre-test-00552 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((?i:a))b" "")))
    (rxt-match-test regexp "ab"
                    '("ab" "a"))))


(ert-deftest rxt-pcre-test-00553 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?i:a)b" "")))
    (rxt-match-test regexp "Ab"
                    '("Ab"))))


(ert-deftest rxt-pcre-test-00554 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((?i:a))b" "")))
    (rxt-match-test regexp "Ab"
                    '("Ab" "A"))))


(ert-deftest rxt-pcre-test-00555 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?i:a)b" "")))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "aB" 'nil)
    (rxt-match-test regexp "aB" 'nil)))


(ert-deftest rxt-pcre-test-00556 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((?i:a))b" "")))))


(ert-deftest rxt-pcre-test-00557 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?:(?-i)a)b" "i")))
    (rxt-match-test regexp "ab"
                    '("ab"))))


(ert-deftest rxt-pcre-test-00558 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((?-i)a)b" "i")))
    (rxt-match-test regexp "ab"
                    '("ab" "a"))))


(ert-deftest rxt-pcre-test-00559 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?:(?-i)a)b" "i")))
    (rxt-match-test regexp "aB"
                    '("aB"))))


(ert-deftest rxt-pcre-test-00560 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((?-i)a)b" "i")))
    (rxt-match-test regexp "aB"
                    '("aB" "a"))))


(ert-deftest rxt-pcre-test-00561 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?:(?-i)a)b" "i")))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "aB"
                    '("aB"))
    (rxt-match-test regexp "Ab" 'nil)))


(ert-deftest rxt-pcre-test-00562 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((?-i)a)b" "i")))))


(ert-deftest rxt-pcre-test-00563 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?:(?-i)a)b" "i")))
    (rxt-match-test regexp "aB"
                    '("aB"))))


(ert-deftest rxt-pcre-test-00564 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((?-i)a)b" "i")))
    (rxt-match-test regexp "aB"
                    '("aB" "a"))))


(ert-deftest rxt-pcre-test-00565 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?:(?-i)a)b" "i")))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "Ab" 'nil)
    (rxt-match-test regexp "AB" 'nil)))


(ert-deftest rxt-pcre-test-00566 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((?-i)a)b" "i")))))


(ert-deftest rxt-pcre-test-00567 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?-i:a)b" "i")))
    (rxt-match-test regexp "ab"
                    '("ab"))))


(ert-deftest rxt-pcre-test-00568 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((?-i:a))b" "i")))
    (rxt-match-test regexp "ab"
                    '("ab" "a"))))


(ert-deftest rxt-pcre-test-00569 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?-i:a)b" "i")))
    (rxt-match-test regexp "aB"
                    '("aB"))))


(ert-deftest rxt-pcre-test-00570 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((?-i:a))b" "i")))
    (rxt-match-test regexp "aB"
                    '("aB" "a"))))


(ert-deftest rxt-pcre-test-00571 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?-i:a)b" "i")))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "AB" 'nil)
    (rxt-match-test regexp "Ab" 'nil)))


(ert-deftest rxt-pcre-test-00572 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((?-i:a))b" "i")))))


(ert-deftest rxt-pcre-test-00573 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?-i:a)b" "i")))
    (rxt-match-test regexp "aB"
                    '("aB"))))


(ert-deftest rxt-pcre-test-00574 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((?-i:a))b" "i")))
    (rxt-match-test regexp "aB"
                    '("aB" "a"))))


(ert-deftest rxt-pcre-test-00575 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?-i:a)b" "i")))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "Ab" 'nil)
    (rxt-match-test regexp "AB" 'nil)))


(ert-deftest rxt-pcre-test-00576 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((?-i:a))b" "i")))))


(ert-deftest rxt-pcre-test-00577 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((?-i:a.))b" "i")))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "AB" 'nil)
    (rxt-match-test regexp "a\nB" 'nil)))


(ert-deftest rxt-pcre-test-00578 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((?s-i:a.))b" "i")))
    (rxt-match-test regexp "a\nB"
                    '("a\nB" "a\n"))))


(ert-deftest rxt-pcre-test-00579 nil 
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?:c|d)(?:)(?:a(?:)(?:b)(?:b(?:))(?:b(?:)(?:b)))" "")))
    (rxt-match-test regexp "cabbbb"
                    '("cabbbb"))))


(ert-deftest rxt-pcre-test-00580 nil 
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?:c|d)(?:)(?:aaaaaaaa(?:)(?:bbbbbbbb)(?:bbbbbbbb(?:))(?:bbbbbbbb(?:)(?:bbbbbbbb)))" "")))
    (rxt-match-test regexp "caaaaaaaabbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
                    '("caaaaaaaabbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"))))


(ert-deftest rxt-pcre-test-00581 nil
  :expected-result :failed
  ;; The current method of faking case-folding behavior cannot make
  ;; backreferences behave case-insensitively
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(ab)\\d\\1" "i")))
    (rxt-match-test regexp "Ab4ab"
                    '("Ab4ab" "Ab"))
    (rxt-match-test regexp "ab4Ab"
                    '("ab4Ab" "ab"))))


(ert-deftest rxt-pcre-test-00582 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "foo\\w*\\d{4}baz" "")))
    (rxt-match-test regexp "foobar1234baz"
                    '("foobar1234baz"))))


(ert-deftest rxt-pcre-test-00583 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "x(~~)*(?:(?:F)?)?" "")))
    (rxt-match-test regexp "x~~"
                    '("x~~" "~~"))))


(ert-deftest rxt-pcre-test-00584 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^a(?#xxx){3}c" "")))
    (rxt-match-test regexp "aaac"
                    '("aaac"))))


(ert-deftest rxt-pcre-test-00585 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^a (?#xxx) (?#yyy) {3}c" "x")))
    (rxt-match-test regexp "aaac"
                    '("aaac"))))


(ert-deftest rxt-pcre-test-00586 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?<![cd])b" "")))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "B\nB" 'nil)
    (rxt-match-test regexp "dbcb" 'nil)))


(ert-deftest rxt-pcre-test-00587 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?<![cd])[ab]" "")))
    (rxt-match-test regexp "dbaacb"
                    '("a"))))


(ert-deftest rxt-pcre-test-00588 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?<!(c|d))b" "")))))


(ert-deftest rxt-pcre-test-00589 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?<!(c|d))[ab]" "")))
    (rxt-match-test regexp "dbaacb"
                    '("a"))))


(ert-deftest rxt-pcre-test-00590 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?<!cd)[ab]" "")))
    (rxt-match-test regexp "cdaccb"
                    '("b"))))


(ert-deftest rxt-pcre-test-00591 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?:a?b?)*$" "")))
    (rxt-match-test regexp ""
                    '(""))
    (rxt-match-test regexp "a"
                    '("a"))
    (rxt-match-test regexp "ab"
                    '("ab"))
    (rxt-match-test regexp "aaa"
                    '("aaa"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "dbcb" 'nil)
    (rxt-match-test regexp "a--" 'nil)
    (rxt-match-test regexp "aa--" 'nil)))


(ert-deftest rxt-pcre-test-00592 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((?s)^a(.))((?m)^b$)" "")))
    (rxt-match-test regexp "a\nb\nc\n"
                    '("a\nb" "a\n" "\n" "b"))))


(ert-deftest rxt-pcre-test-00593 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((?m)^b$)" "")))
    (rxt-match-test regexp "a\nb\nc\n"
                    '("b" "b"))))


(ert-deftest rxt-pcre-test-00594 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?m)^b" "")))
    (rxt-match-test regexp "a\nb\n"
                    '("b"))))


(ert-deftest rxt-pcre-test-00595 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?m)^(b)" "")))
    (rxt-match-test regexp "a\nb\n"
                    '("b" "b"))))


(ert-deftest rxt-pcre-test-00596 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((?m)^b)" "")))
    (rxt-match-test regexp "a\nb\n"
                    '("b" "b"))))


(ert-deftest rxt-pcre-test-00597 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\n((?m)^b)" "")))
    (rxt-match-test regexp "a\nb\n"
                    '("\nb" "b"))))


(ert-deftest rxt-pcre-test-00598 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((?s).)c(?!.)" "")))
    (rxt-match-test regexp "a\nb\nc\n"
                    '("\nc" "\n"))
    (rxt-match-test regexp "a\nb\nc\n"
                    '("\nc" "\n"))))


(ert-deftest rxt-pcre-test-00599 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((?s)b.)c(?!.)" "")))
    (rxt-match-test regexp "a\nb\nc\n"
                    '("b\nc" "b\n"))
    (rxt-match-test regexp "a\nb\nc\n"
                    '("b\nc" "b\n"))))


(ert-deftest rxt-pcre-test-00600 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^b" "")))))


(ert-deftest rxt-pcre-test-00601 nil 
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "()^b" "")))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "a\nb\nc\n" 'nil)
    (rxt-match-test regexp "a\nb\nc\n" 'nil)))


(ert-deftest rxt-pcre-test-00602 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((?m)^b)" "")))
    (rxt-match-test regexp "a\nb\nc\n"
                    '("b" "b"))))


(ert-deftest rxt-pcre-test-00603 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(x)?(?(1)a|b)" "")))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "a" 'nil)
    (rxt-match-test regexp "a" 'nil)))


(ert-deftest rxt-pcre-test-00604 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(x)?(?(1)b|a)" "")))
    (rxt-match-test regexp "a"
                    '("a"))))


(ert-deftest rxt-pcre-test-00605 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "()?(?(1)b|a)" "")))
    (rxt-match-test regexp "a"
                    '("a"))))


(ert-deftest rxt-pcre-test-00606 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "()(?(1)b|a)" "")))))


(ert-deftest rxt-pcre-test-00607 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "()?(?(1)a|b)" "")))
    (rxt-match-test regexp "a"
                    '("a" ""))))


(ert-deftest rxt-pcre-test-00608 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(\\()?blah(?(1)(\\)))$" "")))
    (rxt-match-test regexp "(blah)"
                    '("(blah)" "(" ")"))
    (rxt-match-test regexp "blah"
                    '("blah"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "a" 'nil)
    (rxt-match-test regexp "blah)" 'nil)
    (rxt-match-test regexp "(blah" 'nil)))


(ert-deftest rxt-pcre-test-00609 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(\\(+)?blah(?(1)(\\)))$" "")))
    (rxt-match-test regexp "(blah)"
                    '("(blah)" "(" ")"))
    (rxt-match-test regexp "blah"
                    '("blah"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "blah)" 'nil)
    (rxt-match-test regexp "(blah" 'nil)))


(ert-deftest rxt-pcre-test-00610 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?(?!a)a|b)" "")))))


(ert-deftest rxt-pcre-test-00611 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?(?!a)b|a)" "")))
    (rxt-match-test regexp "a"
                    '("a"))))


(ert-deftest rxt-pcre-test-00612 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?(?=a)b|a)" "")))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "a" 'nil)
    (rxt-match-test regexp "a" 'nil)))


(ert-deftest rxt-pcre-test-00613 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?(?=a)a|b)" "")))
    (rxt-match-test regexp "a"
                    '("a"))))


(ert-deftest rxt-pcre-test-00614 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?=(a+?))(\\1ab)" "")))
    (rxt-match-test regexp "aaab"
                    '("aab" "a" "aab"))))


(ert-deftest rxt-pcre-test-00615 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?=(a+?))\\1ab" "")))))


(ert-deftest rxt-pcre-test-00616 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(\\w+:)+" "")))
    (rxt-match-test regexp "one:"
                    '("one:" "one:"))))


(ert-deftest rxt-pcre-test-00617 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "$(?<=^(a))" "")))
    (rxt-match-test regexp "a"
                    '("" "a"))))


(ert-deftest rxt-pcre-test-00618 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?=(a+?))(\\1ab)" "")))
    (rxt-match-test regexp "aaab"
                    '("aab" "a" "aab"))))


(ert-deftest rxt-pcre-test-00619 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?=(a+?))\\1ab" "")))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "aaab" 'nil)
    (rxt-match-test regexp "aaab" 'nil)))


(ert-deftest rxt-pcre-test-00620 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "([\\w:]+::)?(\\w+)$" "")))
    (rxt-match-test regexp "abcd"
                    '("abcd" nil "abcd"))
    (rxt-match-test regexp "xy:z:::abcd"
                    '("xy:z:::abcd" "xy:z:::" "abcd"))))


(ert-deftest rxt-pcre-test-00621 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^[^bcd]*(c+)" "")))
    (rxt-match-test regexp "aexycd"
                    '("aexyc" "c"))))


(ert-deftest rxt-pcre-test-00622 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(a*)b+" "")))
    (rxt-match-test regexp "caab"
                    '("aab" "aa"))))


(ert-deftest rxt-pcre-test-00623 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "([\\w:]+::)?(\\w+)$" "")))
    (rxt-match-test regexp "abcd"
                    '("abcd" nil "abcd"))
    (rxt-match-test regexp "xy:z:::abcd"
                    '("xy:z:::abcd" "xy:z:::" "abcd"))
    (rxt-match-test regexp "*** Failers"
                    '("Failers" nil "Failers"))
    (rxt-match-test regexp "abcd:" 'nil)
    (rxt-match-test regexp "abcd:" 'nil)))


(ert-deftest rxt-pcre-test-00624 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^[^bcd]*(c+)" "")))
    (rxt-match-test regexp "aexycd"
                    '("aexyc" "c"))))


(ert-deftest rxt-pcre-test-00625 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(>a+)ab" "")))))


(ert-deftest rxt-pcre-test-00626 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?>a+)b" "")))
    (rxt-match-test regexp "aaab"
                    '("aaab"))))


(ert-deftest rxt-pcre-test-00627 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "([[:]+)" "")))
    (rxt-match-test regexp "a:[b]:"
                    '(":[" ":["))))


(ert-deftest rxt-pcre-test-00628 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "([[=]+)" "")))
    (rxt-match-test regexp "a=[b]="
                    '("=[" "=["))))


(ert-deftest rxt-pcre-test-00629 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "([[.]+)" "")))
    (rxt-match-test regexp "a.[b]."
                    '(".[" ".["))))


(ert-deftest rxt-pcre-test-00630 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((?>a+)b)" "")))
    (rxt-match-test regexp "aaab"
                    '("aaab" "aaab"))))


(ert-deftest rxt-pcre-test-00631 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?>(a+))b" "")))
    (rxt-match-test regexp "aaab"
                    '("aaab" "aaa"))))


(ert-deftest rxt-pcre-test-00632 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((?>[^()]+)|\\([^()]*\\))+" "")))
    (rxt-match-test regexp "((abc(ade)ufh()()x"
                    '("abc(ade)ufh()()x" "x"))))


(ert-deftest rxt-pcre-test-00633 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a\\Z" "")))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "aaab" 'nil)
    (rxt-match-test regexp "a\nb\n" 'nil)))


(ert-deftest rxt-pcre-test-00634 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "b\\Z" "")))
    (rxt-match-test regexp "a\nb\n"
                    '("b"))))


(ert-deftest rxt-pcre-test-00635 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "b\\z" "")))))


(ert-deftest rxt-pcre-test-00636 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "b\\Z" "")))
    (rxt-match-test regexp "a\nb"
                    '("b"))))


(ert-deftest rxt-pcre-test-00637 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "b\\z" "")))
    (rxt-match-test regexp "a\nb"
                    '("b"))
    (rxt-match-test regexp "*** Failers" 'nil)))


(ert-deftest rxt-pcre-test-00638 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?>(?(1)\\.|())[^\\W_](?>[a-z0-9-]*[^\\W_])?)+$" "")))
    (rxt-match-test regexp "a"
                    '("a" ""))
    (rxt-match-test regexp "abc"
                    '("abc" ""))
    (rxt-match-test regexp "a-b"
                    '("a-b" ""))
    (rxt-match-test regexp "0-9"
                    '("0-9" ""))
    (rxt-match-test regexp "a.b"
                    '("a.b" ""))
    (rxt-match-test regexp "5.6.7"
                    '("5.6.7" ""))
    (rxt-match-test regexp "the.quick.brown.fox"
                    '("the.quick.brown.fox" ""))
    (rxt-match-test regexp "a100.b200.300c"
                    '("a100.b200.300c" ""))
    (rxt-match-test regexp "12-ab.1245"
                    '("12-ab.1245" ""))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "" 'nil)
    (rxt-match-test regexp ".a" 'nil)
    (rxt-match-test regexp "-a" 'nil)
    (rxt-match-test regexp "a-" 'nil)
    (rxt-match-test regexp "a." 'nil)
    (rxt-match-test regexp "a_b" 'nil)
    (rxt-match-test regexp "a.-" 'nil)
    (rxt-match-test regexp "a.." 'nil)
    (rxt-match-test regexp "ab..bc" 'nil)
    (rxt-match-test regexp "the.quick.brown.fox-" 'nil)
    (rxt-match-test regexp "the.quick.brown.fox." 'nil)
    (rxt-match-test regexp "the.quick.brown.fox_" 'nil)
    (rxt-match-test regexp "the.quick.brown.fox+" 'nil)))


(ert-deftest rxt-pcre-test-00639 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?>.*)(?<=(abcd|wxyz))" "")))
    (rxt-match-test regexp "alphabetabcd"
                    '("alphabetabcd" "abcd"))
    (rxt-match-test regexp "endingwxyz"
                    '("endingwxyz" "wxyz"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "a rather long string that doesn't end with one of them" 'nil)))


(ert-deftest rxt-pcre-test-00640 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "word (?>(?:(?!otherword)[a-zA-Z0-9]+ ){0,30})otherword" "")))
    (rxt-match-test regexp "word cat dog elephant mussel cow horse canary baboon snake shark otherword"
                    '("word cat dog elephant mussel cow horse canary baboon snake shark otherword"))
    (rxt-match-test regexp "word cat dog elephant mussel cow horse canary baboon snake shark" 'nil)))


(ert-deftest rxt-pcre-test-00641 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "word (?>[a-zA-Z0-9]+ ){0,30}otherword" "")))
    (rxt-match-test regexp "word cat dog elephant mussel cow horse canary baboon snake shark the quick brown fox and the lazy dog and several other words getting close to thirty by now I hope" 'nil)))


(ert-deftest rxt-pcre-test-00642 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?<=\\d{3}(?!999))foo" "")))
    (rxt-match-test regexp "999foo"
                    '("foo"))
    (rxt-match-test regexp "123999foo"
                    '("foo"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "123abcfoo" 'nil)))


(ert-deftest rxt-pcre-test-00643 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?<=(?!...999)\\d{3})foo" "")))
    (rxt-match-test regexp "999foo"
                    '("foo"))
    (rxt-match-test regexp "123999foo"
                    '("foo"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "123abcfoo" 'nil)))


(ert-deftest rxt-pcre-test-00644 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?<=\\d{3}(?!999)...)foo" "")))
    (rxt-match-test regexp "123abcfoo"
                    '("foo"))
    (rxt-match-test regexp "123456foo"
                    '("foo"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "123999foo" 'nil)))


(ert-deftest rxt-pcre-test-00645 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?<=\\d{3}...)(?<!999)foo" "")))
    (rxt-match-test regexp "123abcfoo"
                    '("foo"))
    (rxt-match-test regexp "123456foo"
                    '("foo"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "123999foo" 'nil)))


(ert-deftest rxt-pcre-test-00646 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "<a[\\s]+href[\\s]*=[\\s]*          # find <a href=\n ([\\\"\\'])?                       # find single or double quote\n (?(1) (.*?)\\1 | ([^\\s]+))       # if quote found, match up to next matching\n                                 # quote, otherwise match up to next space\n" "isx")))
    (rxt-match-test regexp "<a href=abcd xyz"
                    '("<a href=abcd" nil nil "abcd"))
    (rxt-match-test regexp "<a href=\"abcd xyz pqr\" cats"
                    '("<a href=\"abcd xyz pqr\"" "\"" "abcd xyz pqr"))
    (rxt-match-test regexp "<a href='abcd xyz pqr' cats"
                    '("<a href='abcd xyz pqr'" "'" "abcd xyz pqr"))))


(ert-deftest rxt-pcre-test-00647 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "<a\\s+href\\s*=\\s*                # find <a href=\n ([\"'])?                         # find single or double quote\n (?(1) (.*?)\\1 | (\\S+))          # if quote found, match up to next matching\n                                 # quote, otherwise match up to next space\n" "isx")))
    (rxt-match-test regexp "<a href=abcd xyz"
                    '("<a href=abcd" nil nil "abcd"))
    (rxt-match-test regexp "<a href=\"abcd xyz pqr\" cats"
                    '("<a href=\"abcd xyz pqr\"" "\"" "abcd xyz pqr"))
    (rxt-match-test regexp "<a href       =       'abcd xyz pqr' cats"
                    '("<a href       =       'abcd xyz pqr'" "'" "abcd xyz pqr"))))


(ert-deftest rxt-pcre-test-00648 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "<a\\s+href(?>\\s*)=(?>\\s*)        # find <a href=\n ([\"'])?                         # find single or double quote\n (?(1) (.*?)\\1 | (\\S+))          # if quote found, match up to next matching\n                                 # quote, otherwise match up to next space\n" "isx")))
    (rxt-match-test regexp "<a href=abcd xyz"
                    '("<a href=abcd" nil nil "abcd"))
    (rxt-match-test regexp "<a href=\"abcd xyz pqr\" cats"
                    '("<a href=\"abcd xyz pqr\"" "\"" "abcd xyz pqr"))
    (rxt-match-test regexp "<a href       =       'abcd xyz pqr' cats"
                    '("<a href       =       'abcd xyz pqr'" "'" "abcd xyz pqr"))))


(ert-deftest rxt-pcre-test-00649 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((Z)+|A)*" "")))
    (rxt-match-test regexp "ZABCDEFG"
                    '("ZA" "A" "Z"))))


(ert-deftest rxt-pcre-test-00650 nil 
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(Z()|A)*" "")))
    (rxt-match-test regexp "ZABCDEFG"
                    '("ZA" "A" ""))))


(ert-deftest rxt-pcre-test-00651 nil 
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(Z(())|A)*" "")))
    (rxt-match-test regexp "ZABCDEFG"
                    '("ZA" "A" "" ""))))


(ert-deftest rxt-pcre-test-00652 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((?>Z)+|A)*" "")))
    (rxt-match-test regexp "ZABCDEFG"
                    '("ZA" "A"))))


(ert-deftest rxt-pcre-test-00653 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((?>)+|A)*" "")))
    (rxt-match-test regexp "ZABCDEFG"
                    '("" ""))))


(ert-deftest rxt-pcre-test-00654 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a*" "g")))
    (rxt-match-test regexp "abbab"
                    '("a" "" "" "a" "" ""))))


(ert-deftest rxt-pcre-test-00655 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^[a-\\d]" "")))
    (rxt-match-test regexp "abcde"
                    '("a"))
    (rxt-match-test regexp "-things"
                    '("-"))
    (rxt-match-test regexp "0digit"
                    '("0"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "bcdef" 'nil)))


(ert-deftest rxt-pcre-test-00656 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^[\\d-a]" "")))
    (rxt-match-test regexp "abcde"
                    '("a"))
    (rxt-match-test regexp "-things"
                    '("-"))
    (rxt-match-test regexp "0digit"
                    '("0"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "bcdef" 'nil)))


(ert-deftest rxt-pcre-test-00657 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[[:space:]]+" "")))
    (rxt-match-test regexp "> 	\n\f<"
                    '(" 	\n\f"))))


(ert-deftest rxt-pcre-test-00658 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[[:blank:]]+" "")))
    (rxt-match-test regexp "> 	\n\f<"
                    '(" 	"))))


(ert-deftest rxt-pcre-test-00659 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[\\s]+" "")))
    (rxt-match-test regexp "> 	\n\f<"
                    '(" 	\n\f"))))


(ert-deftest rxt-pcre-test-00660 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\s+" "")))
    (rxt-match-test regexp "> 	\n\f<"
                    '(" 	\n\f"))))


(ert-deftest rxt-pcre-test-00661 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab" "x")))
    (rxt-match-test regexp "ab" 'nil)))


(ert-deftest rxt-pcre-test-00662 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?!\\A)x" "m")))
    (rxt-match-test regexp "a\nxb\n"
                    '("x"))))


(ert-deftest rxt-pcre-test-00663 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?!^)x" "m")))
    (rxt-match-test regexp "a\nxb\n" 'nil)))


(ert-deftest rxt-pcre-test-00664 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "abc\\Qabc\\Eabc" "")))
    (rxt-match-test regexp "abcabcabc"
                    '("abcabcabc"))))


(ert-deftest rxt-pcre-test-00665 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "abc\\Q(*+|\\Eabc" "")))
    (rxt-match-test regexp "abc(*+|abc"
                    '("abc(*+|abc"))))


(ert-deftest rxt-pcre-test-00666 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "   abc\\Q abc\\Eabc" "x")))
    (rxt-match-test regexp "abc abcabc"
                    '("abc abcabc"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "abcabcabc" 'nil)))


(ert-deftest rxt-pcre-test-00667 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "abc#comment\n    \\Q#not comment\n    literal\\E" "x")))
    (rxt-match-test regexp "abc#not comment\n    literal"
                    '("abc#not comment\n    literal"))))


(ert-deftest rxt-pcre-test-00668 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "abc#comment\n    \\Q#not comment\n    literal" "x")))
    (rxt-match-test regexp "abc#not comment\n    literal"
                    '("abc#not comment\n    literal"))))


(ert-deftest rxt-pcre-test-00669 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "abc#comment\n    \\Q#not comment\n    literal\\E #more comment\n    " "x")))
    (rxt-match-test regexp "abc#not comment\n    literal"
                    '("abc#not comment\n    literal"))))


(ert-deftest rxt-pcre-test-00670 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "abc#comment\n    \\Q#not comment\n    literal\\E #more comment" "x")))
    (rxt-match-test regexp "abc#not comment\n    literal"
                    '("abc#not comment\n    literal"))))


(ert-deftest rxt-pcre-test-00671 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\Qabc\\$xyz\\E" "")))
    (rxt-match-test regexp "abc\\$xyz"
                    '("abc\\$xyz"))))


(ert-deftest rxt-pcre-test-00672 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\Qabc\\E\\$\\Qxyz\\E" "")))
    (rxt-match-test regexp "abc$xyz"
                    '("abc$xyz"))))


(ert-deftest rxt-pcre-test-00673 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\Gabc" "")))
    (rxt-match-test regexp "abc"
                    '("abc"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "xyzabc" 'nil)))


(ert-deftest rxt-pcre-test-00674 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\Gabc." "g")))
    (rxt-match-test regexp "abc1abc2xyzabc3"
                    '("abc1" "abc2"))))


(ert-deftest rxt-pcre-test-00675 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "abc." "g")))
    (rxt-match-test regexp "abc1abc2xyzabc3"
                    '("abc1" "abc2" "abc3"))))


(ert-deftest rxt-pcre-test-00676 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a(?x: b c )d" "")))
    (rxt-match-test regexp "XabcdY"
                    '("abcd"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "Xa b c d Y" 'nil)))


(ert-deftest rxt-pcre-test-00677 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((?x)x y z | a b c)" "")))
    (rxt-match-test regexp "XabcY"
                    '("abc" "abc"))
    (rxt-match-test regexp "AxyzB"
                    '("xyz" "xyz"))))


(ert-deftest rxt-pcre-test-00678 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?i)AB(?-i)C" "")))
    (rxt-match-test regexp "XabCY"
                    '("abC"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "XabcY" 'nil)))


(ert-deftest rxt-pcre-test-00679 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((?i)AB(?-i)C|D)E" "")))
    (rxt-match-test regexp "abCE"
                    '("abCE" "abC"))
    (rxt-match-test regexp "DE"
                    '("DE" "D"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "abcE" 'nil)
    (rxt-match-test regexp "abCe" 'nil)
    (rxt-match-test regexp "dE" 'nil)
    (rxt-match-test regexp "De" 'nil)))


(ert-deftest rxt-pcre-test-00680 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(.*)\\d+\\1" "")))
    (rxt-match-test regexp "abc123abc"
                    '("abc123abc" "abc"))
    (rxt-match-test regexp "abc123bc"
                    '("bc123bc" "bc"))))


(ert-deftest rxt-pcre-test-00681 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(.*)\\d+\\1" "s")))
    (rxt-match-test regexp "abc123abc"
                    '("abc123abc" "abc"))
    (rxt-match-test regexp "abc123bc"
                    '("bc123bc" "bc"))))


(ert-deftest rxt-pcre-test-00682 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((.*))\\d+\\1" "")))
    (rxt-match-test regexp "abc123abc"
                    '("abc123abc" "abc" "abc"))
    (rxt-match-test regexp "abc123bc"
                    '("bc123bc" "bc" "bc"))))


(ert-deftest rxt-pcre-test-00683 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "-- This tests for an IPv6 address in the form where it can have up to --" "")))
    (rxt-match-test regexp "/-- eight components, one and only one of which is empty. This must be --/" 'nil)
    (rxt-match-test regexp "/-- an internal component. --/" 'nil)))


(ert-deftest rxt-pcre-test-00684 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?!:)                       # colon disallowed at start\n  (?:                         # start of item\n    (?: [0-9a-f]{1,4} |       # 1-4 hex digits or\n    (?(1)0 | () ) )           # if null previously matched, fail; else null\n    :                         # followed by colon\n  ){1,7}                      # end item; 1-7 of them required               \n  [0-9a-f]{1,4} $             # final hex number at end of string\n  (?(1)|.)                    # check that there was an empty component\n  " "xi")))
    (rxt-match-test regexp "a123::a123"
                    '("a123::a123" ""))
    (rxt-match-test regexp "a123:b342::abcd"
                    '("a123:b342::abcd" ""))
    (rxt-match-test regexp "a123:b342::324e:abcd"
                    '("a123:b342::324e:abcd" ""))
    (rxt-match-test regexp "a123:ddde:b342::324e:abcd"
                    '("a123:ddde:b342::324e:abcd" ""))
    (rxt-match-test regexp "a123:ddde:b342::324e:dcba:abcd"
                    '("a123:ddde:b342::324e:dcba:abcd" ""))
    (rxt-match-test regexp "a123:ddde:9999:b342::324e:dcba:abcd"
                    '("a123:ddde:9999:b342::324e:dcba:abcd" ""))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "1:2:3:4:5:6:7:8" 'nil)
    (rxt-match-test regexp "a123:bce:ddde:9999:b342::324e:dcba:abcd" 'nil)
    (rxt-match-test regexp "a123::9999:b342::324e:dcba:abcd" 'nil)
    (rxt-match-test regexp "abcde:2:3:4:5:6:7:8" 'nil)
    (rxt-match-test regexp "::1" 'nil)
    (rxt-match-test regexp "abcd:fee0:123::" 'nil)
    (rxt-match-test regexp ":1" 'nil)
    (rxt-match-test regexp "1:" 'nil)))


(ert-deftest rxt-pcre-test-00685 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[z\\Qa-d]\\E]" "")))
    (rxt-match-test regexp "z"
                    '("z"))
    (rxt-match-test regexp "a"
                    '("a"))
    (rxt-match-test regexp "-"
                    '("-"))
    (rxt-match-test regexp "d"
                    '("d"))
    (rxt-match-test regexp "]"
                    '("]"))
    (rxt-match-test regexp "*** Failers"
                    '("a"))
    (rxt-match-test regexp "b" 'nil)))


(ert-deftest rxt-pcre-test-00686 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[\\z\\C]" "")))
    (rxt-match-test regexp "z"
                    '("z"))
    (rxt-match-test regexp "C"
                    '("C"))))


(ert-deftest rxt-pcre-test-00687 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\M" "")))
    (rxt-match-test regexp "M"
                    '("M"))))


(ert-deftest rxt-pcre-test-00688 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(a+)*b" "")))
    (error "Skipping exponential blowup test %s" "(a+)*b")))


(ert-deftest rxt-pcre-test-00689 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?i)reg(?:ul(?:[a\344]|ae)r|ex)" "")))
    (rxt-match-test regexp "REGular"
                    '("REGular"))
    (rxt-match-test regexp "regulaer"
                    '("regulaer"))
    (rxt-match-test regexp "Regex"
                    '("Regex"))
    (rxt-match-test regexp "regul\344r"
                    '("regul\344r"))))


(ert-deftest rxt-pcre-test-00690 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\305\346\345\344[\340-\377\300-\337]+" "")))
    (rxt-match-test regexp "\305\346\345\344\340"
                    '("\305\346\345\344\340"))
    (rxt-match-test regexp "\305\346\345\344\377"
                    '("\305\346\345\344\377"))
    (rxt-match-test regexp "\305\346\345\344\300"
                    '("\305\346\345\344\300"))
    (rxt-match-test regexp "\305\346\345\344\337"
                    '("\305\346\345\344\337"))))


(ert-deftest rxt-pcre-test-00691 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?<=Z)X." "")))
    (rxt-match-test regexp "\204XAZXB"
                    '("XB"))))


(ert-deftest rxt-pcre-test-00692 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab cd (?x) de fg" "")))
    (rxt-match-test regexp "ab cd defg"
                    '("ab cd defg"))))


(ert-deftest rxt-pcre-test-00693 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab cd(?x) de fg" "")))
    (rxt-match-test regexp "ab cddefg"
                    '("ab cddefg"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "abcddefg" 'nil)))


(ert-deftest rxt-pcre-test-00694 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?<![^f]oo)(bar)" "")))
    (rxt-match-test regexp "foobarX"
                    '("bar" "bar"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "boobarX" 'nil)))


(ert-deftest rxt-pcre-test-00695 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?<![^f])X" "")))
    (rxt-match-test regexp "offX"
                    '("X"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "onyX" 'nil)))


(ert-deftest rxt-pcre-test-00696 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?<=[^f])X" "")))
    (rxt-match-test regexp "onyX"
                    '("X"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "offX" 'nil)))


(ert-deftest rxt-pcre-test-00697 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^" "mg")))
    (rxt-match-test regexp "a\nb\nc\n"
                    '("" "" ""))
    (rxt-match-test regexp ""
                    '(""))))


(ert-deftest rxt-pcre-test-00698 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?<=C\\n)^" "mg")))
    (rxt-match-test regexp "A\nC\nC\n"
                    '(""))))


(ert-deftest rxt-pcre-test-00699 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?:(?(1)a|b)(X))+" "")))
    (rxt-match-test regexp "bXaX"
                    '("bXaX" "X"))))


(ert-deftest rxt-pcre-test-00700 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?:(?(1)\\1a|b)(X|Y))+" "")))
    (rxt-match-test regexp "bXXaYYaY"
                    '("bXXaYYaY" "Y"))
    (rxt-match-test regexp "bXYaXXaX"
                    '("bX" "X"))))


(ert-deftest rxt-pcre-test-00701 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "()()()()()()()()()(?:(?(10)\\10a|b)(X|Y))+" "")))
    (rxt-match-test regexp "bXXaYYaY"
                    '("bX" "" "" "" "" "" "" "" "" "" "X"))))


(ert-deftest rxt-pcre-test-00702 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[[,abc,]+]" "")))
    (rxt-match-test regexp "abc]"
                    '("abc]"))
    (rxt-match-test regexp "a,b]"
                    '("a,b]"))
    (rxt-match-test regexp "[a,b,c]"
                    '("[a,b,c]"))))


(ert-deftest rxt-pcre-test-00703 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?-x: )" "x")))
    (rxt-match-test regexp "A B"
                    '(" "))))


(ert-deftest rxt-pcre-test-00704 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?x)(?-x: \\s*#\\s*)" "")))
    (rxt-match-test regexp "A # B"
                    '(" #"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "#" 'nil)))


(ert-deftest rxt-pcre-test-00705 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?x-is)(?:(?-ixs) \\s*#\\s*) include" "")))
    (rxt-match-test regexp "A #include"
                    '(" #include"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "A#include" 'nil)
    (rxt-match-test regexp "A #Include" 'nil)))


(ert-deftest rxt-pcre-test-00706 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a*b*\\w" "")))
    (rxt-match-test regexp "aaabbbb"
                    '("aaabbbb"))
    (rxt-match-test regexp "aaaa"
                    '("aaaa"))
    (rxt-match-test regexp "a"
                    '("a"))))


(ert-deftest rxt-pcre-test-00707 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a*b?\\w" "")))
    (rxt-match-test regexp "aaabbbb"
                    '("aaabb"))
    (rxt-match-test regexp "aaaa"
                    '("aaaa"))
    (rxt-match-test regexp "a"
                    '("a"))))


(ert-deftest rxt-pcre-test-00708 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a*b{0,4}\\w" "")))
    (rxt-match-test regexp "aaabbbb"
                    '("aaabbbb"))
    (rxt-match-test regexp "aaaa"
                    '("aaaa"))
    (rxt-match-test regexp "a"
                    '("a"))))


(ert-deftest rxt-pcre-test-00709 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a*b{0,}\\w" "")))
    (rxt-match-test regexp "aaabbbb"
                    '("aaabbbb"))
    (rxt-match-test regexp "aaaa"
                    '("aaaa"))
    (rxt-match-test regexp "a"
                    '("a"))))


(ert-deftest rxt-pcre-test-00710 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a*\\d*\\w" "")))
    (rxt-match-test regexp "0a"
                    '("0a"))
    (rxt-match-test regexp "a"
                    '("a"))))


(ert-deftest rxt-pcre-test-00711 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a*b *\\w" "x")))
    (rxt-match-test regexp "a"
                    '("a"))))


(ert-deftest rxt-pcre-test-00712 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a*b#comment\n  *\\w" "x")))
    (rxt-match-test regexp "a"
                    '("a"))))


(ert-deftest rxt-pcre-test-00713 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a* b *\\w" "x")))
    (rxt-match-test regexp "a"
                    '("a"))))


(ert-deftest rxt-pcre-test-00714 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^\\w+=.*(\\\\\\n.*)*" "")))
    (rxt-match-test regexp "abc=xyz\\\npqr"
                    '("abc=xyz\\"))))


(ert-deftest rxt-pcre-test-00715 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?=(\\w+))\\1:" "")))
    (rxt-match-test regexp "abcd:"
                    '("abcd:" "abcd"))))


(ert-deftest rxt-pcre-test-00716 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?=(\\w+))\\1:" "")))
    (rxt-match-test regexp "abcd:"
                    '("abcd:" "abcd"))))


(ert-deftest rxt-pcre-test-00717 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^\\Eabc" "")))
    (rxt-match-test regexp "abc"
                    '("abc"))))


(ert-deftest rxt-pcre-test-00718 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^[\\Eabc]" "")))
    (rxt-match-test regexp "a"
                    '("a"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "E" 'nil)))


(ert-deftest rxt-pcre-test-00719 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^[a-\\Ec]" "")))
    (rxt-match-test regexp "b"
                    '("b"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "-" 'nil)
    (rxt-match-test regexp "E" 'nil)))


(ert-deftest rxt-pcre-test-00720 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^[a\\E\\E-\\Ec]" "")))
    (rxt-match-test regexp "b"
                    '("b"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "-" 'nil)
    (rxt-match-test regexp "E" 'nil)))


(ert-deftest rxt-pcre-test-00721 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^[\\E\\Qa\\E-\\Qz\\E]+" "")))
    (rxt-match-test regexp "b"
                    '("b"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "-" 'nil)))


(ert-deftest rxt-pcre-test-00722 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^[a\\Q]bc\\E]" "")))
    (rxt-match-test regexp "a"
                    '("a"))
    (rxt-match-test regexp "]"
                    '("]"))
    (rxt-match-test regexp "c"
                    '("c"))))


(ert-deftest rxt-pcre-test-00723 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^[a-\\Q\\E]" "")))
    (rxt-match-test regexp "a"
                    '("a"))
    (rxt-match-test regexp "-"
                    '("-"))))


(ert-deftest rxt-pcre-test-00724 nil 
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(a()*)*" "")))
    (rxt-match-test regexp "aaaa"
                    '("aaaa" "a" ""))))


(ert-deftest rxt-pcre-test-00725 nil 
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?:a(?:(?:))*)*" "")))
    (rxt-match-test regexp "aaaa"
                    '("aaaa"))))


(ert-deftest rxt-pcre-test-00726 nil 
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(a()+)+" "")))
    (rxt-match-test regexp "aaaa"
                    '("aaaa" "a" ""))))


(ert-deftest rxt-pcre-test-00727 nil 
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?:a(?:(?:))+)+" "")))
    (rxt-match-test regexp "aaaa"
                    '("aaaa"))))


(ert-deftest rxt-pcre-test-00728 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(a){0,3}(?(1)b|(c|))*D" "")))
    (rxt-match-test regexp "abbD"
                    '("abbD" "a"))
    (rxt-match-test regexp "ccccD"
                    '("ccccD" nil ""))
    (rxt-match-test regexp "D"
                    '("D" nil ""))))


(ert-deftest rxt-pcre-test-00729 nil 
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(a|)*\\d" "")))
    (rxt-match-test regexp "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" 'nil)
    (rxt-match-test regexp "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa4"
                    '("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa4" ""))))


(ert-deftest rxt-pcre-test-00730 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?>a|)*\\d" "")))
    (rxt-match-test regexp "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" 'nil)
    (rxt-match-test regexp "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa4"
                    '("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa4"))))


(ert-deftest rxt-pcre-test-00731 nil 
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?:a|)*\\d" "")))
    (rxt-match-test regexp "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" 'nil)
    (rxt-match-test regexp "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa4"
                    '("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa4"))))


(ert-deftest rxt-pcre-test-00732 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\Z" "g")))
    (rxt-match-test regexp "abc\n"
                    '("" ""))))


(ert-deftest rxt-pcre-test-00733 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?s)(?>.*)(?<!\\n)" "")))
    (rxt-match-test regexp "abc"
                    '("abc"))
    (rxt-match-test regexp "abc\n" 'nil)))


(ert-deftest rxt-pcre-test-00734 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?![^\\n]*\\n\\z)" "")))
    (rxt-match-test regexp "abc"
                    '(""))
    (rxt-match-test regexp "abc\n" 'nil)))


(ert-deftest rxt-pcre-test-00735 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\z(?<!\\n)" "")))
    (rxt-match-test regexp "abc"
                    '(""))
    (rxt-match-test regexp "abc\n" 'nil)))


(ert-deftest rxt-pcre-test-00736 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(.*(.)?)*" "")))
    (rxt-match-test regexp "abcd"
                    '("abcd" ""))))


(ert-deftest rxt-pcre-test-00737 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "( (A | (?(1)0|) )*   )" "x")))
    (rxt-match-test regexp "abcd"
                    '("" "" ""))))


(ert-deftest rxt-pcre-test-00738 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "( ( (?(1)0|) )*   )" "x")))
    (rxt-match-test regexp "abcd"
                    '("" "" ""))))


(ert-deftest rxt-pcre-test-00739 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(  (?(1)0|)*   )" "x")))
    (rxt-match-test regexp "abcd"
                    '("" ""))))


(ert-deftest rxt-pcre-test-00740 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[[:abcd:xyz]]" "")))
    (rxt-match-test regexp "a]"
                    '("a]"))
    (rxt-match-test regexp ":]"
                    '(":]"))))


(ert-deftest rxt-pcre-test-00741 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[abc[:x\\]pqr]" "")))
    (rxt-match-test regexp "a"
                    '("a"))
    (rxt-match-test regexp "["
                    '("["))
    (rxt-match-test regexp ":"
                    '(":"))
    (rxt-match-test regexp "]"
                    '("]"))
    (rxt-match-test regexp "p"
                    '("p"))))


(ert-deftest rxt-pcre-test-00742 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp ".*[op][xyz]" "")))
    (rxt-match-test regexp "fooabcfoo" 'nil)))


(ert-deftest rxt-pcre-test-00743 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?(?=.*b)b|^)" "")))
    (rxt-match-test regexp "adc"
                    '(""))
    (rxt-match-test regexp "abc"
                    '("b"))))


(ert-deftest rxt-pcre-test-00744 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?(?=^.*b)b|^)" "")))
    (rxt-match-test regexp "adc"
                    '(""))
    (rxt-match-test regexp "abc" 'nil)))


(ert-deftest rxt-pcre-test-00745 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?(?=.*b)b|^)*" "")))
    (rxt-match-test regexp "adc"
                    '(""))
    (rxt-match-test regexp "abc"
                    '(""))))


(ert-deftest rxt-pcre-test-00746 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?(?=.*b)b|^)+" "")))
    (rxt-match-test regexp "adc"
                    '(""))
    (rxt-match-test regexp "abc"
                    '("b"))))


(ert-deftest rxt-pcre-test-00747 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?(?=b).*b|^d)" "")))
    (rxt-match-test regexp "abc"
                    '("b"))))


(ert-deftest rxt-pcre-test-00748 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?(?=.*b).*b|^d)" "")))
    (rxt-match-test regexp "abc"
                    '("ab"))))


(ert-deftest rxt-pcre-test-00749 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^%((?(?=[a])[^%])|b)*%$" "")))
    (rxt-match-test regexp "%ab%"
                    '("%ab%" ""))))


(ert-deftest rxt-pcre-test-00750 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?i)a(?-i)b|c" "")))
    (rxt-match-test regexp "XabX"
                    '("ab"))
    (rxt-match-test regexp "XAbX"
                    '("Ab"))
    (rxt-match-test regexp "CcC"
                    '("c"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "XABX" 'nil)))


(ert-deftest rxt-pcre-test-00751 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[\\x00-\\xff\\s]+" "")))
    (rxt-match-test regexp "\n\f"
                    '("\n\f"))))


(ert-deftest rxt-pcre-test-00752 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^\\c" "")))
    (rxt-match-test regexp "?"
                    '("?"))))


(ert-deftest rxt-pcre-test-00753 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(abc)\\1" "i")))
    (rxt-match-test regexp "abc" 'nil)))


(ert-deftest rxt-pcre-test-00754 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(abc)\\1" "")))
    (rxt-match-test regexp "abc" 'nil)))


(ert-deftest rxt-pcre-test-00755 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[^a]*" "i")))
    (rxt-match-test regexp "12abc"
                    '("12"))
    (rxt-match-test regexp "12ABC"
                    '("12"))))


(ert-deftest rxt-pcre-test-00756 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[^a]*+" "i")))
    (rxt-match-test regexp "12abc"
                    '("12"))
    (rxt-match-test regexp "12ABC"
                    '("12"))))


(ert-deftest rxt-pcre-test-00757 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[^a]*?X" "i")))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "12abc" 'nil)
    (rxt-match-test regexp "12ABC" 'nil)))


(ert-deftest rxt-pcre-test-00758 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[^a]+?X" "i")))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "12abc" 'nil)
    (rxt-match-test regexp "12ABC" 'nil)))


(ert-deftest rxt-pcre-test-00759 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[^a]?X" "i")))
    (rxt-match-test regexp "12aXbcX"
                    '("X"))
    (rxt-match-test regexp "12AXBCX"
                    '("X"))
    (rxt-match-test regexp "BCX"
                    '("CX"))))


(ert-deftest rxt-pcre-test-00760 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[^a]??X" "i")))
    (rxt-match-test regexp "12aXbcX"
                    '("X"))
    (rxt-match-test regexp "12AXBCX"
                    '("X"))
    (rxt-match-test regexp "BCX"
                    '("CX"))))


(ert-deftest rxt-pcre-test-00761 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[^a]?+X" "i")))
    (rxt-match-test regexp "12aXbcX"
                    '("cX"))
    (rxt-match-test regexp "12AXBCX"
                    '("CX"))
    (rxt-match-test regexp "BCX"
                    '("CX"))))


(ert-deftest rxt-pcre-test-00762 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[^a]{2,3}" "i")))
    (rxt-match-test regexp "abcdef"
                    '("bcd"))
    (rxt-match-test regexp "ABCDEF"
                    '("BCD"))))


(ert-deftest rxt-pcre-test-00763 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[^a]{2,3}?" "i")))
    (rxt-match-test regexp "abcdef"
                    '("bc"))
    (rxt-match-test regexp "ABCDEF"
                    '("BC"))))


(ert-deftest rxt-pcre-test-00764 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[^a]{2,3}+" "i")))
    (rxt-match-test regexp "abcdef"
                    '("bcd"))
    (rxt-match-test regexp "ABCDEF"
                    '("BCD"))))


(ert-deftest rxt-pcre-test-00765 nil 
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((a|)+)+Z" "")))
    (rxt-match-test regexp "Z"
                    '("Z" "" ""))))


(ert-deftest rxt-pcre-test-00766 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(a)b|(a)c" "")))
    (rxt-match-test regexp "ac"
                    '("ac" nil "a"))))


(ert-deftest rxt-pcre-test-00767 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?>(a))b|(a)c" "")))
    (rxt-match-test regexp "ac"
                    '("ac" nil "a"))))


(ert-deftest rxt-pcre-test-00768 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?=(a))ab|(a)c" "")))
    (rxt-match-test regexp "ac"
                    '("ac" nil "a"))))


(ert-deftest rxt-pcre-test-00769 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((?>(a))b|(a)c)" "")))
    (rxt-match-test regexp "ac"
                    '("ac" "ac" nil "a"))))


(ert-deftest rxt-pcre-test-00770 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((?>(a))b|(a)c)++" "")))
    (rxt-match-test regexp "ac"
                    '("ac" "ac" nil "a"))))


(ert-deftest rxt-pcre-test-00771 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?:(?>(a))b|(a)c)++" "")))
    (rxt-match-test regexp "ac"
                    '("ac" nil "a"))))


(ert-deftest rxt-pcre-test-00772 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?=(?>(a))b|(a)c)(..)" "")))
    (rxt-match-test regexp "ac"
                    '("ac" nil "a" "ac"))))


(ert-deftest rxt-pcre-test-00773 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?>(?>(a))b|(a)c)" "")))
    (rxt-match-test regexp "ac"
                    '("ac" nil "a"))))


(ert-deftest rxt-pcre-test-00774 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?:(?>([ab])))+a=" "")))
    (rxt-match-test regexp "=ba="
                    '("ba=" "b"))))


(ert-deftest rxt-pcre-test-00775 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?>([ab]))+a=" "")))
    (rxt-match-test regexp "=ba="
                    '("ba=" "b"))))


(ert-deftest rxt-pcre-test-00776 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((?>(a+)b)+(aabab))" "")))
    (rxt-match-test regexp "aaaabaaabaabab"
                    '("aaaabaaabaabab" "aaaabaaabaabab" "aaa" "aabab"))))


(ert-deftest rxt-pcre-test-00777 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?>a+|ab)+?c" "")))
    (rxt-match-test regexp "aabc" 'nil)))


(ert-deftest rxt-pcre-test-00778 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?>a+|ab)+c" "")))
    (rxt-match-test regexp "aabc" 'nil)))


(ert-deftest rxt-pcre-test-00779 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?:a+|ab)+c" "")))
    (rxt-match-test regexp "aabc"
                    '("aabc"))))


(ert-deftest rxt-pcre-test-00780 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?(?=(a))a)" "")))
    (rxt-match-test regexp "a"
                    '("a" "a"))))


(ert-deftest rxt-pcre-test-00781 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?(?=(a))a)(b)" "")))
    (rxt-match-test regexp "ab"
                    '("ab" "a" "b"))))


(ert-deftest rxt-pcre-test-00782 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?:a|ab)++c" "")))
    (rxt-match-test regexp "aaaabc" 'nil)))


(ert-deftest rxt-pcre-test-00783 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?>a|ab)++c" "")))
    (rxt-match-test regexp "aaaabc" 'nil)))


(ert-deftest rxt-pcre-test-00784 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?:a|ab)+c" "")))
    (rxt-match-test regexp "aaaabc"
                    '("aaaabc"))))


(ert-deftest rxt-pcre-test-00785 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?=abc){3}abc" "")))
    (rxt-match-test regexp "abcabcabc"
                    '("abc"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "xyz" 'nil)))


(ert-deftest rxt-pcre-test-00786 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?=abc)+abc" "")))
    (rxt-match-test regexp "abcabcabc"
                    '("abc"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "xyz" 'nil)))


(ert-deftest rxt-pcre-test-00787 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?=abc)++abc" "")))
    (rxt-match-test regexp "abcabcabc"
                    '("abc"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "xyz" 'nil)))


(ert-deftest rxt-pcre-test-00788 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?=abc){0}xyz" "")))
    (rxt-match-test regexp "xyz"
                    '("xyz"))))


(ert-deftest rxt-pcre-test-00789 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?=abc){1}xyz" "")))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "xyz" 'nil)))


(ert-deftest rxt-pcre-test-00790 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?=(a))?." "")))
    (rxt-match-test regexp "ab"
                    '("a" "a"))
    (rxt-match-test regexp "bc"
                    '("b"))))


(ert-deftest rxt-pcre-test-00791 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?=(a))??." "")))
    (rxt-match-test regexp "ab"
                    '("a"))
    (rxt-match-test regexp "bc"
                    '("b"))))


(ert-deftest rxt-pcre-test-00792 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?=(a)){0}b(?1)" "")))
    (rxt-match-test regexp "backgammon"
                    '("ba"))))


(ert-deftest rxt-pcre-test-00793 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?=(?1))?[az]([abc])d" "")))
    (rxt-match-test regexp "abd"
                    '("abd" "b"))
    (rxt-match-test regexp "zcdxx"
                    '("zcd" "c"))))


(ert-deftest rxt-pcre-test-00794 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?!a){0}\\w+" "")))
    (rxt-match-test regexp "aaaaa"
                    '("aaaaa"))))


(ert-deftest rxt-pcre-test-00795 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?<=(abc))?xyz" "")))
    (rxt-match-test regexp "abcxyz"
                    '("xyz" "abc"))
    (rxt-match-test regexp "pqrxyz"
                    '("xyz"))))


(ert-deftest rxt-pcre-test-00796 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^[\\g<a>]+" "")))
    (rxt-match-test regexp "ggg<<<aaa>>>"
                    '("ggg<<<aaa>>>"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "\\ga" 'nil)))


(ert-deftest rxt-pcre-test-00797 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^[\\ga]+" "")))
    (rxt-match-test regexp "gggagagaxyz"
                    '("gggagaga"))))


(ert-deftest rxt-pcre-test-00798 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^[:a[:digit:]]+" "")))
    (rxt-match-test regexp "aaaa444:::Z"
                    '("aaaa444:::"))))


(ert-deftest rxt-pcre-test-00799 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^[:a[:digit:]:b]+" "")))
    (rxt-match-test regexp "aaaa444:::bbbZ"
                    '("aaaa444:::bbb"))))


(ert-deftest rxt-pcre-test-00800 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "[:a]xxx[b:]" "")))
    (rxt-match-test regexp ":xxx:"
                    '(":xxx:"))))


(ert-deftest rxt-pcre-test-00801 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?<=a{2})b" "i")))
    (rxt-match-test regexp "xaabc"
                    '("b"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "xabc" 'nil)))


(ert-deftest rxt-pcre-test-00802 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?<!a{2})b" "i")))
    (rxt-match-test regexp "xabc"
                    '("b"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "xaabc" 'nil)))


(ert-deftest rxt-pcre-test-00803 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?<=a\\h)c" "")))
    (rxt-match-test regexp "xa c"
                    '("c"))))


(ert-deftest rxt-pcre-test-00804 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?<=[^a]{2})b" "")))
    (rxt-match-test regexp "axxbc"
                    '("b"))
    (rxt-match-test regexp "aAAbc"
                    '("b"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "xaabc" 'nil)))


(ert-deftest rxt-pcre-test-00805 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?<=[^a]{2})b" "i")))
    (rxt-match-test regexp "axxbc"
                    '("b"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "aAAbc" 'nil)
    (rxt-match-test regexp "xaabc" 'nil)))


(ert-deftest rxt-pcre-test-00806 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?<=a\\H)c" "")))
    (rxt-match-test regexp "abc"
                    '("c"))))


(ert-deftest rxt-pcre-test-00807 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?<=a\\V)c" "")))
    (rxt-match-test regexp "abc"
                    '("c"))))


(ert-deftest rxt-pcre-test-00808 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?<=a\\v)c" "")))
    (rxt-match-test regexp "a\nc"
                    '("c"))))


(ert-deftest rxt-pcre-test-00809 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?(?=c)c|d)++Y" "")))
    (rxt-match-test regexp "XcccddYX"
                    '("cccddY"))))


(ert-deftest rxt-pcre-test-00810 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?(?=c)c|d)*+Y" "")))
    (rxt-match-test regexp "XcccddYX"
                    '("cccddY"))))


(ert-deftest rxt-pcre-test-00811 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(a{2,3}){2,}+a" "")))
    (rxt-match-test regexp "aaaaaaa"
                    '("aaaaaaa" "aaa"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "aaaaaa" 'nil)
    (rxt-match-test regexp "aaaaaaaaa" 'nil)))


(ert-deftest rxt-pcre-test-00812 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(a{2,3})++a" "")))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "aaaaaa" 'nil)))


(ert-deftest rxt-pcre-test-00813 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(a{2,3})*+a" "")))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "aaaaaa" 'nil)))


(ert-deftest rxt-pcre-test-00814 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab\\Cde" "")))
    (rxt-match-test regexp "abXde"
                    '("abXde"))))


(ert-deftest rxt-pcre-test-00815 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?<=ab\\Cde)X" "")))
    (rxt-match-test regexp "abZdeX"
                    '("X"))))


(ert-deftest rxt-pcre-test-00816 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a[\\CD]b" "")))
    (rxt-match-test regexp "aCb"
                    '("aCb"))
    (rxt-match-test regexp "aDb"
                    '("aDb"))))


(ert-deftest rxt-pcre-test-00817 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a[\\C-X]b" "")))
    (rxt-match-test regexp "aJb"
                    '("aJb"))))


(ert-deftest rxt-pcre-test-00818 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\H\\h\\V\\v" "")))
    (rxt-match-test regexp "X X\n"
                    '("X X\n"))
    (rxt-match-test regexp "X	X"
                    '("X	X"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "\240 X\n" 'nil)))


(ert-deftest rxt-pcre-test-00819 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\H*\\h+\\V?\\v{3,4}" "")))
    (rxt-match-test regexp "	 \240X\n\f\n"
                    '("	 \240X\n\f"))
    (rxt-match-test regexp "	 \240\n\f\n"
                    '("	 \240\n\f"))
    (rxt-match-test regexp "	 \240\n\f"
                    '("	 \240\n\f"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "	 \240\n" 'nil)))


(ert-deftest rxt-pcre-test-00820 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\H{3,4}" "")))
    (rxt-match-test regexp "XY  ABCDE"
                    '("ABCD"))
    (rxt-match-test regexp "XY  PQR ST"
                    '("PQR"))))


(ert-deftest rxt-pcre-test-00821 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp ".\\h{3,4}." "")))
    (rxt-match-test regexp "XY  AB    PQRS"
                    '("B    P"))))


(ert-deftest rxt-pcre-test-00822 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\h*X\\h?\\H+Y\\H?Z" "")))
    (rxt-match-test regexp ">XNNNYZ"
                    '("XNNNYZ"))
    (rxt-match-test regexp ">  X NYQZ"
                    '("  X NYQZ"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp ">XYZ" 'nil)
    (rxt-match-test regexp ">  X NY Z" 'nil)))


(ert-deftest rxt-pcre-test-00823 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\v*X\\v?Y\\v+Z\\V*\\x0a\\V+\\x0b\\V{2,3}\\x0c" "")))
    (rxt-match-test regexp ">XY\nZ\nANN\f"
                    '("XY\nZ\nANN\f"))
    (rxt-match-test regexp ">\nX\nY\nZZZ\nAAANNN\f"
                    '("\nX\nY\nZZZ\nAAANNN\f"))))


(ert-deftest rxt-pcre-test-00824 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(foo)\\Kbar" "")))
    (rxt-match-test regexp "foobar"
                    '("bar" "foo"))))


(ert-deftest rxt-pcre-test-00825 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(foo)(\\Kbar|baz)" "")))
    (rxt-match-test regexp "foobar"
                    '("bar" "foo" "bar"))
    (rxt-match-test regexp "foobaz"
                    '("foobaz" "foo" "baz"))))


(ert-deftest rxt-pcre-test-00826 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(foo\\Kbar)baz" "")))
    (rxt-match-test regexp "foobarbaz"
                    '("barbaz" "foobar"))))


(ert-deftest rxt-pcre-test-00827 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "abc\\K|def\\K" "g")))
    (rxt-match-test regexp "Xabcdefghi"
                    '("" ""))))


(ert-deftest rxt-pcre-test-00828 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "ab\\Kc|de\\Kf" "g")))
    (rxt-match-test regexp "Xabcdefghi"
                    '("c" "f"))))


(ert-deftest rxt-pcre-test-00829 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?=C)" "g")))
    (rxt-match-test regexp "ABCDECBA"
                    '("" ""))))


(ert-deftest rxt-pcre-test-00830 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^abc\\K" "")))
    (rxt-match-test regexp "abcdef"
                    '(""))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "defabcxyz" 'nil)))


(ert-deftest rxt-pcre-test-00831 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(a(b))\\1\\g1\\g{1}\\g-1\\g{-1}\\g{-02}Z" "")))
    (rxt-match-test regexp "ababababbbabZXXXX"
                    '("ababababbbabZ" "ab" "b"))))


(ert-deftest rxt-pcre-test-00832 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?<A>tom|bon)-\\g{A}" "")))
    (rxt-match-test regexp "tom-tom"
                    '("tom-tom" "tom"))
    (rxt-match-test regexp "bon-bon"
                    '("bon-bon" "bon"))))


(ert-deftest rxt-pcre-test-00833 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(^(a|b\\g{-1}))" "")))
    (rxt-match-test regexp "bacxxx" 'nil)))


(ert-deftest rxt-pcre-test-00834 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?|(abc)|(xyz))\\1" "")))
    (rxt-match-test regexp "abcabc"
                    '("abcabc" "abc"))
    (rxt-match-test regexp "xyzxyz"
                    '("xyzxyz" "xyz"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "abcxyz" 'nil)
    (rxt-match-test regexp "xyzabc" 'nil)))


(ert-deftest rxt-pcre-test-00835 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?|(abc)|(xyz))(?1)" "")))
    (rxt-match-test regexp "abcabc"
                    '("abcabc" "abc"))
    (rxt-match-test regexp "xyzabc"
                    '("xyzabc" "xyz"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "xyzxyz" 'nil)))


(ert-deftest rxt-pcre-test-00836 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^X(?5)(a)(?|(b)|(q))(c)(d)(Y)" "")))
    (rxt-match-test regexp "XYabcdY"
                    '("XYabcdY" "a" "b" "c" "d" "Y"))))


(ert-deftest rxt-pcre-test-00837 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^X(?7)(a)(?|(b|(r)(s))|(q))(c)(d)(Y)" "")))
    (rxt-match-test regexp "XYabcdY"
                    '("XYabcdY" "a" "b" nil nil "c" "d" "Y"))))


(ert-deftest rxt-pcre-test-00838 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^X(?7)(a)(?|(b|(?|(r)|(t))(s))|(q))(c)(d)(Y)" "")))
    (rxt-match-test regexp "XYabcdY"
                    '("XYabcdY" "a" "b" nil nil "c" "d" "Y"))))


(ert-deftest rxt-pcre-test-00839 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?'abc'\\w+):\\k<abc>{2}" "")))
    (rxt-match-test regexp "a:aaxyz"
                    '("a:aa" "a"))
    (rxt-match-test regexp "ab:ababxyz"
                    '("ab:abab" "ab"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "a:axyz" 'nil)
    (rxt-match-test regexp "ab:abxyz" 'nil)))


(ert-deftest rxt-pcre-test-00840 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?'abc'\\w+):\\g{abc}{2}" "")))
    (rxt-match-test regexp "a:aaxyz"
                    '("a:aa" "a"))
    (rxt-match-test regexp "ab:ababxyz"
                    '("ab:abab" "ab"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "a:axyz" 'nil)
    (rxt-match-test regexp "ab:abxyz" 'nil)))


(ert-deftest rxt-pcre-test-00841 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?<ab>a)? (?(<ab>)b|c) (?('ab')d|e)" "x")))
    (rxt-match-test regexp "abd"
                    '("abd" "a"))
    (rxt-match-test regexp "ce"
                    '("ce"))))


(ert-deftest rxt-pcre-test-00842 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(a.)\\g-1Z" "")))
    (rxt-match-test regexp "aXaXZ"
                    '("aXaXZ" "aX"))))


(ert-deftest rxt-pcre-test-00843 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(a.)\\g{-1}Z" "")))
    (rxt-match-test regexp "aXaXZ"
                    '("aXaXZ" "aX"))))


(ert-deftest rxt-pcre-test-00844 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?(DEFINE) (?<A> a) (?<B> b) )  (?&A) (?&B) " "x")))
    (rxt-match-test regexp "abcd"
                    '("ab"))))


(ert-deftest rxt-pcre-test-00845 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?<NAME>(?&NAME_PAT))\\s+(?<ADDR>(?&ADDRESS_PAT))\n  (?(DEFINE)\n  (?<NAME_PAT>[a-z]+)\n  (?<ADDRESS_PAT>\\d+)\n  )" "x")))
    (rxt-match-test regexp "metcalfe 33"
                    '("metcalfe 33" "metcalfe" "33"))))


(ert-deftest rxt-pcre-test-00846 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?(DEFINE)(?<byte>2[0-4]\\d|25[0-5]|1\\d\\d|[1-9]?\\d))\\b(?&byte)(\\.(?&byte)){3}" "")))
    (rxt-match-test regexp "1.2.3.4"
                    '("1.2.3.4" nil ".4"))
    (rxt-match-test regexp "131.111.10.206"
                    '("131.111.10.206" nil ".206"))
    (rxt-match-test regexp "10.0.0.0"
                    '("10.0.0.0" nil ".0"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "10.6" 'nil)
    (rxt-match-test regexp "455.3.4.5" 'nil)))


(ert-deftest rxt-pcre-test-00847 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\b(?&byte)(\\.(?&byte)){3}(?(DEFINE)(?<byte>2[0-4]\\d|25[0-5]|1\\d\\d|[1-9]?\\d))" "")))
    (rxt-match-test regexp "1.2.3.4"
                    '("1.2.3.4" ".4"))
    (rxt-match-test regexp "131.111.10.206"
                    '("131.111.10.206" ".206"))
    (rxt-match-test regexp "10.0.0.0"
                    '("10.0.0.0" ".0"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "10.6" 'nil)
    (rxt-match-test regexp "455.3.4.5" 'nil)))


(ert-deftest rxt-pcre-test-00848 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(\\w++|\\s++)*$" "")))
    (error "Skipping exponential blowup test %s" "^(\\w++|\\s++)*$")))


(ert-deftest rxt-pcre-test-00849 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(\\d++)(\\w)" "")))
    (rxt-match-test regexp "12345a"
                    '("12345a" "12345" "a"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "12345+" 'nil)))


(ert-deftest rxt-pcre-test-00850 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a++b" "")))
    (rxt-match-test regexp "aaab"
                    '("aaab"))))


(ert-deftest rxt-pcre-test-00851 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(a++b)" "")))
    (rxt-match-test regexp "aaab"
                    '("aaab" "aaab"))))


(ert-deftest rxt-pcre-test-00852 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(a++)b" "")))
    (rxt-match-test regexp "aaab"
                    '("aaab" "aaa"))))


(ert-deftest rxt-pcre-test-00853 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "([^()]++|\\([^()]*\\))+" "")))
    (rxt-match-test regexp "((abc(ade)ufh()()x"
                    '("abc(ade)ufh()()x" "x"))))


(ert-deftest rxt-pcre-test-00854 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\(([^()]++|\\([^()]+\\))+\\)" "")))
    (rxt-match-test regexp "(abc)"
                    '("(abc)" "abc"))
    (rxt-match-test regexp "(abc(def)xyz)"
                    '("(abc(def)xyz)" "xyz"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "((()aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" 'nil)))


(ert-deftest rxt-pcre-test-00855 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^([^()]|\\((?1)*\\))*$" "")))
    (rxt-match-test regexp "abc"
                    '("abc" "c"))
    (rxt-match-test regexp "a(b)c"
                    '("a(b)c" "c"))
    (rxt-match-test regexp "a(b(c))d"
                    '("a(b(c))d" "d"))
    (rxt-match-test regexp "*** Failers)" 'nil)
    (rxt-match-test regexp "a(b(c)d" 'nil)))


(ert-deftest rxt-pcre-test-00856 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^>abc>([^()]|\\((?1)*\\))*<xyz<$" "")))
    (rxt-match-test regexp ">abc>123<xyz<"
                    '(">abc>123<xyz<" "3"))
    (rxt-match-test regexp ">abc>1(2)3<xyz<"
                    '(">abc>1(2)3<xyz<" "3"))
    (rxt-match-test regexp ">abc>(1(2)3)<xyz<"
                    '(">abc>(1(2)3)<xyz<" "(1(2)3)"))))


(ert-deftest rxt-pcre-test-00857 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?:((.)(?1)\\2|)|((.)(?3)\\4|.))$" "i")))
    (rxt-match-test regexp "1221"
                    '("1221" "1221" "1"))
    (rxt-match-test regexp "Satanoscillatemymetallicsonatas"
                    '("Satanoscillatemymetallicsonatas" nil nil "Satanoscillatemymetallicsonatas" "S"))
    (rxt-match-test regexp "AmanaplanacanalPanama"
                    '("AmanaplanacanalPanama" nil nil "AmanaplanacanalPanama" "A"))
    (rxt-match-test regexp "AblewasIereIsawElba"
                    '("AblewasIereIsawElba" nil nil "AblewasIereIsawElba" "A"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "Thequickbrownfox" 'nil)))


(ert-deftest rxt-pcre-test-00858 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(\\d+|\\((?1)([+*-])(?1)\\)|-(?1))$" "")))
    (rxt-match-test regexp "12"
                    '("12" "12"))
    (rxt-match-test regexp "(((2+2)*-3)-7)"
                    '("(((2+2)*-3)-7)" "(((2+2)*-3)-7)" "-"))
    (rxt-match-test regexp "-12"
                    '("-12" "-12"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "((2+2)*-3)-7)" 'nil)))


(ert-deftest rxt-pcre-test-00859 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(x(y|(?1){2})z)" "")))
    (rxt-match-test regexp "xyz"
                    '("xyz" "xyz" "y"))
    (rxt-match-test regexp "xxyzxyzz"
                    '("xxyzxyzz" "xxyzxyzz" "xyzxyz"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "xxyzz" 'nil)
    (rxt-match-test regexp "xxyzxyzxyzz" 'nil)))


(ert-deftest rxt-pcre-test-00860 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((< (?: (?(R) \\d++  | [^<>]*+) | (?2)) * >))" "x")))
    (rxt-match-test regexp "<>"
                    '("<>" "<>" "<>"))
    (rxt-match-test regexp "<abcd>"
                    '("<abcd>" "<abcd>" "<abcd>"))
    (rxt-match-test regexp "<abc <123> hij>"
                    '("<abc <123> hij>" "<abc <123> hij>" "<abc <123> hij>"))
    (rxt-match-test regexp "<abc <def> hij>"
                    '("<def>" "<def>" "<def>"))
    (rxt-match-test regexp "<abc<>def>"
                    '("<abc<>def>" "<abc<>def>" "<abc<>def>"))
    (rxt-match-test regexp "<abc<>"
                    '("<>" "<>" "<>"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "<abc" 'nil)))


(ert-deftest rxt-pcre-test-00861 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^a+(*FAIL)" "")))
    (rxt-match-test regexp "aaaaaa" 'nil)))


(ert-deftest rxt-pcre-test-00862 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a+b?c+(*FAIL)" "")))
    (rxt-match-test regexp "aaabccc" 'nil)))


(ert-deftest rxt-pcre-test-00863 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a+b?(*PRUNE)c+(*FAIL)" "")))
    (rxt-match-test regexp "aaabccc" 'nil)))


(ert-deftest rxt-pcre-test-00864 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a+b?(*COMMIT)c+(*FAIL)" "")))
    (rxt-match-test regexp "aaabccc" 'nil)))


(ert-deftest rxt-pcre-test-00865 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a+b?(*SKIP)c+(*FAIL)" "")))
    (rxt-match-test regexp "aaabcccaaabccc" 'nil)))


(ert-deftest rxt-pcre-test-00866 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?:aaa(*THEN)\\w{6}|bbb(*THEN)\\w{5}|ccc(*THEN)\\w{4}|\\w{3})" "")))
    (rxt-match-test regexp "aaaxxxxxx"
                    '("aaaxxxxxx"))
    (rxt-match-test regexp "aaa++++++"
                    '("aaa"))
    (rxt-match-test regexp "bbbxxxxx"
                    '("bbbxxxxx"))
    (rxt-match-test regexp "bbb+++++"
                    '("bbb"))
    (rxt-match-test regexp "cccxxxx"
                    '("cccxxxx"))
    (rxt-match-test regexp "ccc++++"
                    '("ccc"))
    (rxt-match-test regexp "dddddddd"
                    '("ddd"))))


(ert-deftest rxt-pcre-test-00867 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(aaa(*THEN)\\w{6}|bbb(*THEN)\\w{5}|ccc(*THEN)\\w{4}|\\w{3})" "")))
    (rxt-match-test regexp "aaaxxxxxx"
                    '("aaaxxxxxx" "aaaxxxxxx"))
    (rxt-match-test regexp "aaa++++++"
                    '("aaa" "aaa"))
    (rxt-match-test regexp "bbbxxxxx"
                    '("bbbxxxxx" "bbbxxxxx"))
    (rxt-match-test regexp "bbb+++++"
                    '("bbb" "bbb"))
    (rxt-match-test regexp "cccxxxx"
                    '("cccxxxx" "cccxxxx"))
    (rxt-match-test regexp "ccc++++"
                    '("ccc" "ccc"))
    (rxt-match-test regexp "dddddddd"
                    '("ddd" "ddd"))))


(ert-deftest rxt-pcre-test-00868 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a+b?(*THEN)c+(*FAIL)" "")))
    (rxt-match-test regexp "aaabccc" 'nil)))


(ert-deftest rxt-pcre-test-00869 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(A (A|B(*ACCEPT)|C) D)(E)" "x")))
    (rxt-match-test regexp "AB"
                    '("AB" "AB" "B"))
    (rxt-match-test regexp "ABX"
                    '("AB" "AB" "B"))
    (rxt-match-test regexp "AADE"
                    '("AADE" "AAD" "A" "E"))
    (rxt-match-test regexp "ACDE"
                    '("ACDE" "ACD" "C" "E"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "AD" 'nil)))


(ert-deftest rxt-pcre-test-00870 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^\\W*+(?:((.)\\W*+(?1)\\W*+\\2|)|((.)\\W*+(?3)\\W*+\\4|\\W*+.\\W*+))\\W*+$" "i")))
    (rxt-match-test regexp "1221"
                    '("1221" "1221" "1"))
    (rxt-match-test regexp "Satan, oscillate my metallic sonatas!"
                    '("Satan, oscillate my metallic sonatas!" nil nil "Satan, oscillate my metallic sonatas" "S"))
    (rxt-match-test regexp "A man, a plan, a canal: Panama!"
                    '("A man, a plan, a canal: Panama!" nil nil "A man, a plan, a canal: Panama" "A"))
    (rxt-match-test regexp "Able was I ere I saw Elba."
                    '("Able was I ere I saw Elba." nil nil "Able was I ere I saw Elba" "A"))
    (rxt-match-test regexp "*** Failers" 'nil)
    (rxt-match-test regexp "The quick brown fox" 'nil)))


(ert-deftest rxt-pcre-test-00871 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^((.)(?1)\\2|.)$" "")))
    (rxt-match-test regexp "a"
                    '("a" "a"))
    (rxt-match-test regexp "aba"
                    '("aba" "aba" "a"))
    (rxt-match-test regexp "aabaa"
                    '("aabaa" "aabaa" "a"))
    (rxt-match-test regexp "abcdcba"
                    '("abcdcba" "abcdcba" "a"))
    (rxt-match-test regexp "pqaabaaqp"
                    '("pqaabaaqp" "pqaabaaqp" "p"))
    (rxt-match-test regexp "ablewasiereisawelba"
                    '("ablewasiereisawelba" "ablewasiereisawelba" "a"))
    (rxt-match-test regexp "rhubarb" 'nil)
    (rxt-match-test regexp "the quick brown fox" 'nil)))


(ert-deftest rxt-pcre-test-00872 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(a)(?<=b(?1))" "")))
    (rxt-match-test regexp "baz"
                    '("a" "a"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "caz" 'nil)))


(ert-deftest rxt-pcre-test-00873 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?<=b(?1))(a)" "")))
    (rxt-match-test regexp "zbaaz"
                    '("a" "a"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "aaa" 'nil)))


(ert-deftest rxt-pcre-test-00874 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?<X>a)(?<=b(?&X))" "")))
    (rxt-match-test regexp "baz"
                    '("a" "a"))))


(ert-deftest rxt-pcre-test-00875 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?|(abc)|(def))\\1" "")))
    (rxt-match-test regexp "abcabc"
                    '("abcabc" "abc"))
    (rxt-match-test regexp "defdef"
                    '("defdef" "def"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "abcdef" 'nil)
    (rxt-match-test regexp "defabc" 'nil)))


(ert-deftest rxt-pcre-test-00876 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?|(abc)|(def))(?1)" "")))
    (rxt-match-test regexp "abcabc"
                    '("abcabc" "abc"))
    (rxt-match-test regexp "defabc"
                    '("defabc" "def"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "defdef" 'nil)
    (rxt-match-test regexp "abcdef" 'nil)))


(ert-deftest rxt-pcre-test-00877 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?:a(?<quote> (?<apostrophe>')|(?<realquote>\")) |b(?<quote> (?<apostrophe>')|(?<realquote>\")) ) (?('quote')[a-z]+|[0-9]+)" "x")))
    (rxt-match-test regexp "a\"aaaaa"
                    '("a\"aaaaa" "\"" nil "\""))
    (rxt-match-test regexp "b\"aaaaa"
                    '("b\"aaaaa" nil nil nil "\"" nil "\""))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "b\"11111" 'nil)))


(ert-deftest rxt-pcre-test-00878 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?:(?1)|B)(A(*F)|C)" "")))
    (rxt-match-test regexp "ABCD"
                    '("BC" "C"))
    (rxt-match-test regexp "CCD"
                    '("CC" "C"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "CAD" 'nil)))


(ert-deftest rxt-pcre-test-00879 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?:(?1)|B)(A(*F)|C)" "")))
    (rxt-match-test regexp "CCD"
                    '("CC" "C"))
    (rxt-match-test regexp "BCD"
                    '("BC" "C"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "ABCD" 'nil)
    (rxt-match-test regexp "CAD" 'nil)
    (rxt-match-test regexp "BAD" 'nil)))


(ert-deftest rxt-pcre-test-00880 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?:(?1)|B)(A(*ACCEPT)XX|C)D" "")))
    (rxt-match-test regexp "AAD"
                    '("AA" "A"))
    (rxt-match-test regexp "ACD"
                    '("ACD" "C"))
    (rxt-match-test regexp "BAD"
                    '("BA" "A"))
    (rxt-match-test regexp "BCD"
                    '("BCD" "C"))
    (rxt-match-test regexp "BAX"
                    '("BA" "A"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "ACX" 'nil)
    (rxt-match-test regexp "ABC" 'nil)))


(ert-deftest rxt-pcre-test-00881 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?(DEFINE)(A))B(?1)C" "")))
    (rxt-match-test regexp "BAC"
                    '("BAC"))))


(ert-deftest rxt-pcre-test-00882 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?(DEFINE)((A)\\2))B(?1)C" "")))
    (rxt-match-test regexp "BAAC"
                    '("BAAC"))))


(ert-deftest rxt-pcre-test-00883 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?<pn> \\( ( [^()]++ | (?&pn) )* \\) )" "x")))
    (rxt-match-test regexp "(ab(cd)ef)"
                    '("(ab(cd)ef)" "(ab(cd)ef)" "ef"))))


(ert-deftest rxt-pcre-test-00884 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?!a(*SKIP)b)" "")))
    (rxt-match-test regexp "ac"
                    '(""))))


(ert-deftest rxt-pcre-test-00885 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?=a(*SKIP)b|ac)" "")))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "ac" 'nil)))


(ert-deftest rxt-pcre-test-00886 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?=a(*THEN)b|ac)" "")))
    (rxt-match-test regexp "ac"
                    '(""))))


(ert-deftest rxt-pcre-test-00887 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?=a(*PRUNE)b)" "")))
    (rxt-match-test regexp "ab"
                    '(""))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "ac" 'nil)))


(ert-deftest rxt-pcre-test-00888 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?=a(*ACCEPT)b)" "")))
    (rxt-match-test regexp "ac"
                    '(""))))


(ert-deftest rxt-pcre-test-00889 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?(?!a(*SKIP)b))" "")))
    (rxt-match-test regexp "ac"
                    '(""))))


(ert-deftest rxt-pcre-test-00890 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?>a\\Kb)" "")))
    (rxt-match-test regexp "ab"
                    '("b"))))


(ert-deftest rxt-pcre-test-00891 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((?>a\\Kb))" "")))
    (rxt-match-test regexp "ab"
                    '("b" "ab"))))


(ert-deftest rxt-pcre-test-00892 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(a\\Kb)" "")))
    (rxt-match-test regexp "ab"
                    '("b" "ab"))))


(ert-deftest rxt-pcre-test-00893 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^a\\Kcz|ac" "")))
    (rxt-match-test regexp "ac"
                    '("ac"))))


(ert-deftest rxt-pcre-test-00894 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?>a\\Kbz|ab)" "")))
    (rxt-match-test regexp "ab"
                    '("ab"))))


(ert-deftest rxt-pcre-test-00895 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?&t)(?(DEFINE)(?<t>a\\Kb))$" "")))
    (rxt-match-test regexp "ab"
                    '("b"))))


(ert-deftest rxt-pcre-test-00896 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^([^()]|\\((?1)*\\))*$" "")))
    (rxt-match-test regexp "a(b)c"
                    '("a(b)c" "c"))
    (rxt-match-test regexp "a(b(c)d)e"
                    '("a(b(c)d)e" "e"))))


(ert-deftest rxt-pcre-test-00897 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?P<L1>(?P<L2>0)(?P>L1)|(?P>L2))" "")))
    (rxt-match-test regexp "0"
                    '("0" "0"))
    (rxt-match-test regexp "00"
                    '("00" "00" "0"))
    (rxt-match-test regexp "0000"
                    '("0000" "0000" "0"))))


(ert-deftest rxt-pcre-test-00898 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?P<L1>(?P<L2>0)|(?P>L2)(?P>L1))" "")))
    (rxt-match-test regexp "0"
                    '("0" "0" "0"))
    (rxt-match-test regexp "00"
                    '("0" "0" "0"))
    (rxt-match-test regexp "0000"
                    '("0" "0" "0"))))


(ert-deftest rxt-pcre-test-00899 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "--- This one does fail, as expected, in Perl. It needs the complex item at the\n     end of the pattern. A single letter instead of (B|D) makes it not fail,\n     which I think is a Perl bug. --- " "")))))


(ert-deftest rxt-pcre-test-00900 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "A(*COMMIT)(B|D)" "")))
    (rxt-match-test regexp "ACABX" 'nil)))


(ert-deftest rxt-pcre-test-00901 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "--- Check the use of names for failure ---" "")))))


(ert-deftest rxt-pcre-test-00902 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(A(*PRUNE:A)B|C(*PRUNE:B)D)" "")))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "AC" 'nil)
    (rxt-match-test regexp "CB" 'nil)))


(ert-deftest rxt-pcre-test-00903 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "--- Force no study, otherwise mark is not seen. The studied version is in\n     test 2 because it isn't Perl-compatible. ---" "")))))


(ert-deftest rxt-pcre-test-00904 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(*MARK:A)(*SKIP:B)(C|X)" "")))
    (rxt-match-test regexp "C"
                    '("C" "C"))
    (rxt-match-test regexp "D" 'nil)))


(ert-deftest rxt-pcre-test-00905 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(A(*THEN:A)B|C(*THEN:B)D)" "")))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "CB" 'nil)))


(ert-deftest rxt-pcre-test-00906 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?:A(*THEN:A)B|C(*THEN:B)D)" "")))
    (rxt-match-test regexp "CB" 'nil)))


(ert-deftest rxt-pcre-test-00907 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?>A(*THEN:A)B|C(*THEN:B)D)" "")))
    (rxt-match-test regexp "CB" 'nil)))


(ert-deftest rxt-pcre-test-00908 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "--- This should succeed, as the skip causes bump to offset 1 (the mark). Note\nthat we have to have something complicated such as (B|Z) at the end because,\nfor Perl, a simple character somehow causes an unwanted optimization to mess\nwith the handling of backtracking verbs. ---" "")))))


(ert-deftest rxt-pcre-test-00909 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "A(*MARK:A)A+(*SKIP:A)(B|Z) | AC" "x")))
    (rxt-match-test regexp "AAAC"
                    '("AC"))))


(ert-deftest rxt-pcre-test-00910 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "--- Test skipping over a non-matching mark. ---" "")))))


(ert-deftest rxt-pcre-test-00911 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "A(*MARK:A)A+(*MARK:B)(*SKIP:A)(B|Z) | AC" "x")))
    (rxt-match-test regexp "AAAC"
                    '("AC"))))


(ert-deftest rxt-pcre-test-00912 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "--- Check shorthand for MARK ---" "")))))


(ert-deftest rxt-pcre-test-00913 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "A(*:A)A+(*SKIP:A)(B|Z) | AC" "x")))
    (rxt-match-test regexp "AAAC"
                    '("AC"))))


(ert-deftest rxt-pcre-test-00914 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "--- Don't loop! Force no study, otherwise mark is not seen. ---" "")))))


(ert-deftest rxt-pcre-test-00915 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(*:A)A+(*SKIP:A)(B|Z)" "")))
    (rxt-match-test regexp "AAAC" 'nil)))


(ert-deftest rxt-pcre-test-00916 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "--- This should succeed, as a non-existent skip name disables the skip ---" "")))))


(ert-deftest rxt-pcre-test-00917 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "A(*MARK:A)A+(*SKIP:B)(B|Z) | AC" "x")))
    (rxt-match-test regexp "AAAC"
                    '("AC"))))


(ert-deftest rxt-pcre-test-00918 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "A(*MARK:A)A+(*SKIP:B)(B|Z) | AC(*:B)" "x")))
    (rxt-match-test regexp "AAAC"
                    '("AC"))))


(ert-deftest rxt-pcre-test-00919 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "--- COMMIT at the start of a pattern should act like an anchor. Again, \nhowever, we need the complication for Perl. ---" "")))))


(ert-deftest rxt-pcre-test-00920 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(*COMMIT)(A|P)(B|P)(C|P)" "")))
    (rxt-match-test regexp "ABCDEFG"
                    '("ABC" "A" "B" "C"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "DEFGABC" 'nil)))


(ert-deftest rxt-pcre-test-00921 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "--- COMMIT inside an atomic group can't stop backtracking over the group. ---" "")))))


(ert-deftest rxt-pcre-test-00922 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(\\w+)(?>b(*COMMIT))\\w{2}" "")))
    (rxt-match-test regexp "abbb"
                    '("abbb" "a"))))


(ert-deftest rxt-pcre-test-00923 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(\\w+)b(*COMMIT)\\w{2}" "")))
    (rxt-match-test regexp "abbb" 'nil)))


(ert-deftest rxt-pcre-test-00924 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "--- Check opening parens in comment when seeking forward reference. ---" "")))))


(ert-deftest rxt-pcre-test-00925 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?&t)(?#()(?(DEFINE)(?<t>a))" "")))
    (rxt-match-test regexp "bac"
                    '("a"))))


(ert-deftest rxt-pcre-test-00926 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "--- COMMIT should override THEN ---" "")))))


(ert-deftest rxt-pcre-test-00927 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?>(*COMMIT)(?>yes|no)(*THEN)(*F))?" "")))
    (rxt-match-test regexp "yes" 'nil)))


(ert-deftest rxt-pcre-test-00928 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?>(*COMMIT)(yes|no)(*THEN)(*F))?" "")))
    (rxt-match-test regexp "yes" 'nil)))


(ert-deftest rxt-pcre-test-00929 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "b?(*SKIP)c" "")))
    (rxt-match-test regexp "bc"
                    '("bc"))
    (rxt-match-test regexp "abc"
                    '("bc"))))


(ert-deftest rxt-pcre-test-00930 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(*SKIP)bc" "")))
    (rxt-match-test regexp "a" 'nil)))


(ert-deftest rxt-pcre-test-00931 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(*SKIP)b" "")))
    (rxt-match-test regexp "a" 'nil)))


(ert-deftest rxt-pcre-test-00932 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?P<abn>(?P=abn)xxx|)+" "")))
    (rxt-match-test regexp "xxx"
                    '("" ""))))


(ert-deftest rxt-pcre-test-00933 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?i:([^b]))(?1)" "")))
    (rxt-match-test regexp "aa"
                    '("aa" "a"))
    (rxt-match-test regexp "aA"
                    '("aA" "a"))
    (rxt-match-test regexp "** Failers"
                    '("**" "*"))
    (rxt-match-test regexp "ab" 'nil)
    (rxt-match-test regexp "aB" 'nil)
    (rxt-match-test regexp "Ba" 'nil)
    (rxt-match-test regexp "ba" 'nil)))


(ert-deftest rxt-pcre-test-00934 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?&t)*+(?(DEFINE)(?<t>a))\\w$" "")))
    (rxt-match-test regexp "aaaaaaX"
                    '("aaaaaaX"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "aaaaaa" 'nil)))


(ert-deftest rxt-pcre-test-00935 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?&t)*(?(DEFINE)(?<t>a))\\w$" "")))
    (rxt-match-test regexp "aaaaaaX"
                    '("aaaaaaX"))
    (rxt-match-test regexp "aaaaaa"
                    '("aaaaaa"))))


(ert-deftest rxt-pcre-test-00936 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(a)*+(\\w)" "")))
    (rxt-match-test regexp "aaaaX"
                    '("aaaaX" "a" "X"))
    (rxt-match-test regexp "YZ"
                    '("Y" nil "Y"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "aaaa" 'nil)))


(ert-deftest rxt-pcre-test-00937 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?:a)*+(\\w)" "")))
    (rxt-match-test regexp "aaaaX"
                    '("aaaaX" "X"))
    (rxt-match-test regexp "YZ"
                    '("Y" "Y"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "aaaa" 'nil)))


(ert-deftest rxt-pcre-test-00938 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(a)++(\\w)" "")))
    (rxt-match-test regexp "aaaaX"
                    '("aaaaX" "a" "X"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "aaaa" 'nil)
    (rxt-match-test regexp "YZ" 'nil)))


(ert-deftest rxt-pcre-test-00939 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?:a)++(\\w)" "")))
    (rxt-match-test regexp "aaaaX"
                    '("aaaaX" "X"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "aaaa" 'nil)
    (rxt-match-test regexp "YZ" 'nil)))


(ert-deftest rxt-pcre-test-00940 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(a)?+(\\w)" "")))
    (rxt-match-test regexp "aaaaX"
                    '("aa" "a" "a"))
    (rxt-match-test regexp "YZ"
                    '("Y" nil "Y"))))


(ert-deftest rxt-pcre-test-00941 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?:a)?+(\\w)" "")))
    (rxt-match-test regexp "aaaaX"
                    '("aa" "a"))
    (rxt-match-test regexp "YZ"
                    '("Y" "Y"))))


(ert-deftest rxt-pcre-test-00942 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(a){2,}+(\\w)" "")))
    (rxt-match-test regexp "aaaaX"
                    '("aaaaX" "a" "X"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "aaa" 'nil)
    (rxt-match-test regexp "YZ" 'nil)))


(ert-deftest rxt-pcre-test-00943 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?:a){2,}+(\\w)" "")))
    (rxt-match-test regexp "aaaaX"
                    '("aaaaX" "X"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "aaa" 'nil)
    (rxt-match-test regexp "YZ" 'nil)))


(ert-deftest rxt-pcre-test-00944 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(a|)*(?1)b" "")))
    (rxt-match-test regexp "b"
                    '("b" ""))
    (rxt-match-test regexp "ab"
                    '("ab" ""))
    (rxt-match-test regexp "aab"
                    '("aab" ""))))


(ert-deftest rxt-pcre-test-00945 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(a)++(?1)b" "")))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "ab" 'nil)
    (rxt-match-test regexp "aab" 'nil)))


(ert-deftest rxt-pcre-test-00946 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(a)*+(?1)b" "")))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "ab" 'nil)
    (rxt-match-test regexp "aab" 'nil)))


(ert-deftest rxt-pcre-test-00947 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?1)(?:(b)){0}" "")))
    (rxt-match-test regexp "b"
                    '("b"))))


(ert-deftest rxt-pcre-test-00948 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(foo ( \\( ((?:(?> [^()]+ )|(?2))*) \\) ) )" "x")))
    (rxt-match-test regexp "foo(bar(baz)+baz(bop))"
                    '("foo(bar(baz)+baz(bop))" "foo(bar(baz)+baz(bop))" "(bar(baz)+baz(bop))" "bar(baz)+baz(bop)"))))


(ert-deftest rxt-pcre-test-00949 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(A (A|B(*ACCEPT)|C) D)(E)" "x")))
    (rxt-match-test regexp "AB"
                    '("AB" "AB" "B"))))


(ert-deftest rxt-pcre-test-00950 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\A.*?(?:a|b(*THEN)c)" "")))
    (rxt-match-test regexp "ba"
                    '("ba"))))


(ert-deftest rxt-pcre-test-00951 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\A.*?(?:a|bc)" "")))
    (rxt-match-test regexp "ba"
                    '("ba"))))


(ert-deftest rxt-pcre-test-00952 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\A.*?(a|b(*THEN)c)" "")))
    (rxt-match-test regexp "ba"
                    '("ba" "a"))))


(ert-deftest rxt-pcre-test-00953 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\A.*?(a|bc)" "")))
    (rxt-match-test regexp "ba"
                    '("ba" "a"))))


(ert-deftest rxt-pcre-test-00954 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\A.*?(?:a|b(*THEN)c)++" "")))
    (rxt-match-test regexp "ba"
                    '("ba"))))


(ert-deftest rxt-pcre-test-00955 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\A.*?(?:a|bc)++" "")))
    (rxt-match-test regexp "ba"
                    '("ba"))))


(ert-deftest rxt-pcre-test-00956 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\A.*?(a|b(*THEN)c)++" "")))
    (rxt-match-test regexp "ba"
                    '("ba" "a"))))


(ert-deftest rxt-pcre-test-00957 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\A.*?(a|bc)++" "")))
    (rxt-match-test regexp "ba"
                    '("ba" "a"))))


(ert-deftest rxt-pcre-test-00958 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\A.*?(?:a|b(*THEN)c|d)" "")))
    (rxt-match-test regexp "ba"
                    '("ba"))))


(ert-deftest rxt-pcre-test-00959 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "\\A.*?(?:a|bc|d)" "")))
    (rxt-match-test regexp "ba"
                    '("ba"))))


(ert-deftest rxt-pcre-test-00960 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?:(b))++" "")))
    (rxt-match-test regexp "beetle"
                    '("b" "b"))))


(ert-deftest rxt-pcre-test-00961 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?(?=(a(*ACCEPT)z))a)" "")))
    (rxt-match-test regexp "a"
                    '("a" "a"))))


(ert-deftest rxt-pcre-test-00962 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(a)(?1)+ab" "")))
    (rxt-match-test regexp "aaaab"
                    '("aaaab" "a"))))


(ert-deftest rxt-pcre-test-00963 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(a)(?1)++ab" "")))
    (rxt-match-test regexp "aaaab" 'nil)))


(ert-deftest rxt-pcre-test-00964 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?=a(*:M))aZ" "")))
    (rxt-match-test regexp "aZbc"
                    '("aZ"))))


(ert-deftest rxt-pcre-test-00965 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?!(*:M)b)aZ" "")))
    (rxt-match-test regexp "aZbc"
                    '("aZ"))))


(ert-deftest rxt-pcre-test-00966 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?(DEFINE)(a))?b(?1)" "")))
    (rxt-match-test regexp "backgammon"
                    '("ba"))))


(ert-deftest rxt-pcre-test-00967 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^\\N+" "")))
    (rxt-match-test regexp "abc\ndef"
                    '("abc"))))


(ert-deftest rxt-pcre-test-00968 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^\\N{1,}" "")))
    (rxt-match-test regexp "abc\ndef"
                    '("abc"))))


(ert-deftest rxt-pcre-test-00969 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?(R)a+|(?R)b)" "")))
    (rxt-match-test regexp "aaaabcde"
                    '("aaaab"))))


(ert-deftest rxt-pcre-test-00970 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?(R)a+|((?R))b)" "")))
    (rxt-match-test regexp "aaaabcde"
                    '("aaaab" "aaaa"))))


(ert-deftest rxt-pcre-test-00971 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((?(R)a+|(?1)b))" "")))
    (rxt-match-test regexp "aaaabcde"
                    '("aaaab" "aaaab"))))


(ert-deftest rxt-pcre-test-00972 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "((?(R1)a+|(?1)b))" "")))
    (rxt-match-test regexp "aaaabcde"
                    '("aaaab" "aaaab"))))


(ert-deftest rxt-pcre-test-00973 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a(*:any \nname)" "")))
    (rxt-match-test regexp "abc"
                    '("a"))))


(ert-deftest rxt-pcre-test-00974 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?>(?&t)c|(?&t))(?(DEFINE)(?<t>a|b(*PRUNE)c))" "")))
    (rxt-match-test regexp "a"
                    '("a"))
    (rxt-match-test regexp "ba"
                    '("a"))
    (rxt-match-test regexp "bba"
                    '("a"))))


(ert-deftest rxt-pcre-test-00975 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "--- Checking revised (*THEN) handling ---" "")))))


(ert-deftest rxt-pcre-test-00976 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "--- Capture ---" "")))))


(ert-deftest rxt-pcre-test-00977 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^.*? (a(*THEN)b) c" "x")))
    (rxt-match-test regexp "aabc" 'nil)))


(ert-deftest rxt-pcre-test-00978 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^.*? (a(*THEN)b|(*F)) c" "x")))
    (rxt-match-test regexp "aabc"
                    '("aabc" "ab"))))


(ert-deftest rxt-pcre-test-00979 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^.*? ( (a(*THEN)b) | (*F) ) c" "x")))
    (rxt-match-test regexp "aabc"
                    '("aabc" "ab" "ab"))))


(ert-deftest rxt-pcre-test-00980 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^.*? ( (a(*THEN)b) ) c" "x")))
    (rxt-match-test regexp "aabc" 'nil)))


(ert-deftest rxt-pcre-test-00981 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "--- Non-capture ---" "")))))


(ert-deftest rxt-pcre-test-00982 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^.*? (?:a(*THEN)b) c" "x")))
    (rxt-match-test regexp "aabc" 'nil)))


(ert-deftest rxt-pcre-test-00983 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^.*? (?:a(*THEN)b|(*F)) c" "x")))
    (rxt-match-test regexp "aabc"
                    '("aabc"))))


(ert-deftest rxt-pcre-test-00984 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^.*? (?: (?:a(*THEN)b) | (*F) ) c" "x")))
    (rxt-match-test regexp "aabc"
                    '("aabc"))))


(ert-deftest rxt-pcre-test-00985 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^.*? (?: (?:a(*THEN)b) ) c" "x")))
    (rxt-match-test regexp "aabc" 'nil)))


(ert-deftest rxt-pcre-test-00986 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "--- Atomic ---" "")))))


(ert-deftest rxt-pcre-test-00987 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^.*? (?>a(*THEN)b) c" "x")))
    (rxt-match-test regexp "aabc" 'nil)))


(ert-deftest rxt-pcre-test-00988 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^.*? (?>a(*THEN)b|(*F)) c" "x")))
    (rxt-match-test regexp "aabc"
                    '("aabc"))))


(ert-deftest rxt-pcre-test-00989 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^.*? (?> (?>a(*THEN)b) | (*F) ) c" "x")))
    (rxt-match-test regexp "aabc"
                    '("aabc"))))


(ert-deftest rxt-pcre-test-00990 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^.*? (?> (?>a(*THEN)b) ) c" "x")))
    (rxt-match-test regexp "aabc" 'nil)))


(ert-deftest rxt-pcre-test-00991 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "--- Possessive capture ---" "")))))


(ert-deftest rxt-pcre-test-00992 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^.*? (a(*THEN)b)++ c" "x")))
    (rxt-match-test regexp "aabc" 'nil)))


(ert-deftest rxt-pcre-test-00993 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^.*? (a(*THEN)b|(*F))++ c" "x")))
    (rxt-match-test regexp "aabc"
                    '("aabc" "ab"))))


(ert-deftest rxt-pcre-test-00994 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^.*? ( (a(*THEN)b)++ | (*F) )++ c" "x")))
    (rxt-match-test regexp "aabc"
                    '("aabc" "ab" "ab"))))


(ert-deftest rxt-pcre-test-00995 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^.*? ( (a(*THEN)b)++ )++ c" "x")))
    (rxt-match-test regexp "aabc" 'nil)))


(ert-deftest rxt-pcre-test-00996 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "--- Possessive non-capture ---" "")))))


(ert-deftest rxt-pcre-test-00997 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^.*? (?:a(*THEN)b)++ c" "x")))
    (rxt-match-test regexp "aabc" 'nil)))


(ert-deftest rxt-pcre-test-00998 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^.*? (?:a(*THEN)b|(*F))++ c" "x")))
    (rxt-match-test regexp "aabc"
                    '("aabc"))))


(ert-deftest rxt-pcre-test-00999 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^.*? (?: (?:a(*THEN)b)++ | (*F) )++ c" "x")))
    (rxt-match-test regexp "aabc"
                    '("aabc"))))


(ert-deftest rxt-pcre-test-01000 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^.*? (?: (?:a(*THEN)b)++ )++ c" "x")))
    (rxt-match-test regexp "aabc" 'nil)))


(ert-deftest rxt-pcre-test-01001 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "--- Condition assertion ---" "")))))


(ert-deftest rxt-pcre-test-01002 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(?(?=a(*THEN)b)ab|ac)" "")))
    (rxt-match-test regexp "ac"
                    '("ac"))))


(ert-deftest rxt-pcre-test-01003 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "--- Condition ---" "")))))


(ert-deftest rxt-pcre-test-01004 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^.*?(?(?=a)a|b(*THEN)c)" "")))
    (rxt-match-test regexp "ba" 'nil)))


(ert-deftest rxt-pcre-test-01005 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^.*?(?:(?(?=a)a|b(*THEN)c)|d)" "")))
    (rxt-match-test regexp "ba"
                    '("ba"))))


(ert-deftest rxt-pcre-test-01006 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^.*?(?(?=a)a(*THEN)b|c)" "")))
    (rxt-match-test regexp "ac" 'nil)))


(ert-deftest rxt-pcre-test-01007 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "--- Assertion ---" "")))))


(ert-deftest rxt-pcre-test-01008 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^.*(?=a(*THEN)b)" "")))
    (rxt-match-test regexp "aabc"
                    '("a"))))


(ert-deftest rxt-pcre-test-01009 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "------------------------------" "")))))


(ert-deftest rxt-pcre-test-01010 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?>a(*:m))" "imsx")))
    (rxt-match-test regexp "a"
                    '("a"))))


(ert-deftest rxt-pcre-test-01011 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?>(a)(*:m))" "imsx")))
    (rxt-match-test regexp "a"
                    '("a" "a"))))


(ert-deftest rxt-pcre-test-01012 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?<=a(*ACCEPT)b)c" "")))
    (rxt-match-test regexp "xacd"
                    '("c"))))


(ert-deftest rxt-pcre-test-01013 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?<=(a(*ACCEPT)b))c" "")))
    (rxt-match-test regexp "xacd"
                    '("c" "a"))))


(ert-deftest rxt-pcre-test-01014 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?<=(a(*COMMIT)b))c" "")))
    (rxt-match-test regexp "xabcd"
                    '("c" "ab"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "xacd" 'nil)))


(ert-deftest rxt-pcre-test-01015 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?<!a(*FAIL)b)c" "")))
    (rxt-match-test regexp "xcd"
                    '("c"))
    (rxt-match-test regexp "acd"
                    '("c"))))


(ert-deftest rxt-pcre-test-01016 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?<=a(*:N)b)c" "")))
    (rxt-match-test regexp "xabcd"
                    '("c"))))


(ert-deftest rxt-pcre-test-01017 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?<=a(*PRUNE)b)c" "")))
    (rxt-match-test regexp "xabcd"
                    '("c"))))


(ert-deftest rxt-pcre-test-01018 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?<=a(*SKIP)b)c" "")))
    (rxt-match-test regexp "xabcd"
                    '("c"))))


(ert-deftest rxt-pcre-test-01019 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?<=a(*THEN)b)c" "")))
    (rxt-match-test regexp "xabcd"
                    '("c"))))


(ert-deftest rxt-pcre-test-01020 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(a)(?2){2}(.)" "")))
    (rxt-match-test regexp "abcd"
                    '("abcd" "a" "d"))))


(ert-deftest rxt-pcre-test-01021 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(*MARK:A)(*PRUNE:B)(C|X)" "")))
    (rxt-match-test regexp "C"
                    '("C" "C"))
    (rxt-match-test regexp "D" 'nil)))


(ert-deftest rxt-pcre-test-01022 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(*MARK:A)(*PRUNE:B)(C|X)" "")))
    (rxt-match-test regexp "C"
                    '("C" "C"))
    (rxt-match-test regexp "D" 'nil)))


(ert-deftest rxt-pcre-test-01023 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(*MARK:A)(*THEN:B)(C|X)" "")))
    (rxt-match-test regexp "C"
                    '("C" "C"))
    (rxt-match-test regexp "D" 'nil)))


(ert-deftest rxt-pcre-test-01024 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(*MARK:A)(*THEN:B)(C|X)" "")))
    (rxt-match-test regexp "C"
                    '("C" "C"))
    (rxt-match-test regexp "D" 'nil)))


(ert-deftest rxt-pcre-test-01025 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(*MARK:A)(*THEN:B)(C|X)" "")))
    (rxt-match-test regexp "C"
                    '("C" "C"))
    (rxt-match-test regexp "D" 'nil)))


(ert-deftest rxt-pcre-test-01026 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "--- This should fail, as the skip causes a bump to offset 3 (the skip) ---" "")))))


(ert-deftest rxt-pcre-test-01027 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "A(*MARK:A)A+(*SKIP)(B|Z) | AC" "x")))
    (rxt-match-test regexp "AAAC" 'nil)))


(ert-deftest rxt-pcre-test-01028 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "--- Same --" "")))))


(ert-deftest rxt-pcre-test-01029 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "A(*MARK:A)A+(*MARK:B)(*SKIP:B)(B|Z) | AC" "x")))
    (rxt-match-test regexp "AAAC" 'nil)))


(ert-deftest rxt-pcre-test-01030 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "A(*:A)A+(*SKIP)(B|Z) | AC" "x")))
    (rxt-match-test regexp "AAAC" 'nil)))


(ert-deftest rxt-pcre-test-01031 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "--- This should fail, as a null name is the same as no name ---" "")))))


(ert-deftest rxt-pcre-test-01032 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "A(*MARK:A)A+(*SKIP:)(B|Z) | AC" "x")))
    (rxt-match-test regexp "AAAC" 'nil)))


(ert-deftest rxt-pcre-test-01033 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "--- A check on what happens after hitting a mark and them bumping along to\nsomething that does not even start. Perl reports tags after the failures here, \nthough it does not when the individual letters are made into something \nmore complicated. ---" "")))))


(ert-deftest rxt-pcre-test-01034 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "A(*:A)B|XX(*:B)Y" "")))
    (rxt-match-test regexp "AABC"
                    '("AB"))
    (rxt-match-test regexp "XXYZ"
                    '("XXY"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "XAQQ" 'nil)
    (rxt-match-test regexp "XAQQXZZ" 'nil)
    (rxt-match-test regexp "AXQQQ" 'nil)
    (rxt-match-test regexp "AXXQQQ" 'nil)))


(ert-deftest rxt-pcre-test-01035 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(A(*THEN:A)B|C(*THEN:B)D)" "")))
    (rxt-match-test regexp "AB"
                    '("AB" "AB"))
    (rxt-match-test regexp "CD"
                    '("CD" "CD"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "AC" 'nil)
    (rxt-match-test regexp "CB" 'nil)))


(ert-deftest rxt-pcre-test-01036 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(A(*PRUNE:A)B|C(*PRUNE:B)D)" "")))
    (rxt-match-test regexp "AB"
                    '("AB" "AB"))
    (rxt-match-test regexp "CD"
                    '("CD" "CD"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "AC" 'nil)
    (rxt-match-test regexp "CB" 'nil)))


(ert-deftest rxt-pcre-test-01037 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "--- An empty name does not pass back an empty string. It is the same as if no\nname were given. ---" "")))))


(ert-deftest rxt-pcre-test-01038 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "^(A(*PRUNE:)B|C(*PRUNE:B)D)" "")))
    (rxt-match-test regexp "AB"
                    '("AB" "AB"))
    (rxt-match-test regexp "CD"
                    '("CD" "CD"))))


(ert-deftest rxt-pcre-test-01039 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "--- PRUNE goes to next bumpalong; COMMIT does not. ---" "")))))


(ert-deftest rxt-pcre-test-01040 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "A(*PRUNE:A)B" "")))
    (rxt-match-test regexp "ACAB"
                    '("AB"))))


(ert-deftest rxt-pcre-test-01041 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "--- Mark names can be duplicated ---" "")))))


(ert-deftest rxt-pcre-test-01042 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "A(*:A)B|X(*:A)Y" "")))
    (rxt-match-test regexp "AABC"
                    '("AB"))
    (rxt-match-test regexp "XXYZ"
                    '("XY"))))


(ert-deftest rxt-pcre-test-01043 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "b(*:m)f|a(*:n)w" "")))
    (rxt-match-test regexp "aw"
                    '("aw"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "abc" 'nil)))


(ert-deftest rxt-pcre-test-01044 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "b(*:m)f|aw" "")))
    (rxt-match-test regexp "abaw"
                    '("aw"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "abc" 'nil)
    (rxt-match-test regexp "abax" 'nil)))


(ert-deftest rxt-pcre-test-01045 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "A(*MARK:A)A+(*SKIP:B)(B|Z) | AAC" "x")))
    (rxt-match-test regexp "AAAC"
                    '("AAC"))))


(ert-deftest rxt-pcre-test-01046 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a(*PRUNE:X)bc|qq" "")))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "axy" 'nil)))


(ert-deftest rxt-pcre-test-01047 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "a(*THEN:X)bc|qq" "")))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "axy" 'nil)))


(ert-deftest rxt-pcre-test-01048 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?=a(*MARK:A)b)..x" "")))
    (rxt-match-test regexp "abxy"
                    '("abx"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "abpq" 'nil)))


(ert-deftest rxt-pcre-test-01049 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?=a(*MARK:A)b)..(*:Y)x" "")))
    (rxt-match-test regexp "abxy"
                    '("abx"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "abpq" 'nil)))


(ert-deftest rxt-pcre-test-01050 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?=a(*PRUNE:A)b)..x" "")))
    (rxt-match-test regexp "abxy"
                    '("abx"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "abpq" 'nil)))


(ert-deftest rxt-pcre-test-01051 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?=a(*PRUNE:A)b)..(*:Y)x" "")))
    (rxt-match-test regexp "abxy"
                    '("abx"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "abpq" 'nil)))


(ert-deftest rxt-pcre-test-01052 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?=a(*THEN:A)b)..x" "")))
    (rxt-match-test regexp "abxy"
                    '("abx"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "abpq" 'nil)))


(ert-deftest rxt-pcre-test-01053 nil
  :expected-result :failed
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(?=a(*THEN:A)b)..(*:Y)x" "")))
    (rxt-match-test regexp "abxy"
                    '("abx"))
    (rxt-match-test regexp "** Failers" 'nil)
    (rxt-match-test regexp "abpq" 'nil)))


(ert-deftest rxt-pcre-test-01054 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(another)?(\\1?)test" "")))
    (rxt-match-test regexp "hello world test"
                    '("test" nil ""))))


(ert-deftest rxt-pcre-test-01055 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "(another)?(\\1+)test" "")))
    (rxt-match-test regexp "hello world test" 'nil)))


(ert-deftest rxt-pcre-test-01056 nil
  (let*
      ((case-fold-search nil)
       (regexp
	(rxt-pcre-to-elisp "-- End of testinput1 --" "")))))

(ert-deftest rxt-pcre-test-01057 nil
  (should
   (equal (rxt-elisp-to-rx "\\(?3:test\\)")
          '(submatch-n 3 "test"))))



;;; Test runner script

(defun rxt-run-tests ()
  (let ((test-runner
         (if noninteractive
             #'ert-run-tests-batch
           #'ert-run-tests-interactively)))
    (let ((stats (funcall test-runner "^rxt-")))
      (kill-emacs (ert-stats-completed-unexpected stats)))))

;;; pcre2el.tests.el ends here
