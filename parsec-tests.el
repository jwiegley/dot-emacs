;;; parsec-tests.el --- Tests for parsec.el          -*- lexical-binding: t; -*-

;; Copyright (C) 2016  Free Software Foundation, Inc.

;; Author: Junpeng Qiu <qjpchmail@gmail.com>
;; Keywords:

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;;

;;; Code:

(require 'ert)
(require 'parsec)

(ert-deftest test-parsec-ch ()
  (should
   (equal
    (parsec-with-input "ab"
      (parsec-ch ?a)
      (parsec-ch ?b))
    "b"))
  (should
   (equal
    (parsec-with-input "ab"
      (parsec-query (parsec-ch ?a) :beg))
    1)))

(ert-deftest test-parsec-satisfy ()
  (should
   (equal
    (parsec-with-input "ab"
      (parsec-ch ?a)
      (parsec-satisfy (lambda (c) (char-equal c ?b))))
    "b"))
  (should
   (equal
    (parsec-with-input "ab"
      (parsec-ch ?a)
      (parsec-query (parsec-satisfy (lambda (c) (char-equal c ?b))) :end))
    3)))

(ert-deftest test-parsec-eol ()
  (should
   (equal
    (parsec-with-input "\na"
      (parsec-newline)
      (parsec-ch ?a))
    "a"))
  (should
   (equal
    (parsec-with-input "\r\na"
      (parsec-crlf)
      (parsec-ch ?a))
    "a"))
  (should
   (equal
    (parsec-with-input "\r\na"
      (parsec-eol)
      (parsec-ch ?a))
    "a"))
  (should
   (equal
    (parsec-with-input "\na"
      (parsec-eol)
      (parsec-ch ?a))
    "a"))
  (should
   (equal
    (parsec-with-input "\ra"
      (parsec-eol)
      (parsech-ch ?a))
    (parsec-error-new-2 "\n" "a"))))

(ert-deftest test-parsec-eof ()
  (should
   (equal
    (parsec-with-input "\r\na"
      (parsec-eol)
      (parsec-ch ?a)
      (parsec-eof))
    nil)))

(ert-deftest test-parsec-re ()
  (should
   (equal
    (parsec-with-input "abc"
      (parsec-query
       (parsec-re "\\(a\\)\\(bc\\)")
       :group 2))
    "bc")))

(ert-deftest test-parsec-make-alternatives ()
  (should
   (equal
    (parsec-make-alternatives '(?-))
    "-"))
  (should
   (equal
    (parsec-make-alternatives '(?- ?\] ?a ?^))
    "]a^-"))
  (should
   (equal
    (parsec-make-alternatives '(?- ?^))
    "-^"))
  (should
   (equal
    (parsec-make-alternatives '(?^ ?\"))
    "\"^")))

(ert-deftest test-parsec-one-of ()
  (should
   (equal
    (parsec-with-input "^]-"
      (parsec-many-as-string (parsec-one-of ?^ ?\] ?-)))
    "^]-"))
  (should
   (equal
    (parsec-with-input "^-"
      (parsec-many-as-string (parsec-one-of ?^ ?-)))
    "^-")))

(ert-deftest test-parsec-none-of ()
  (should
   (equal
    (parsec-with-input "-[]"
      (parsec-none-of ?\] ?^)
      (parsec-one-of ?\[ ?\])
      (parsec-none-of ?- ?^))
    "]")))

(ert-deftest test-parsec-str ()
  (should
   (equal
    (parsec-with-input "abc"
      (parsec-str "abc"))
    "abc"))
  (should
   (equal
    (parsec-with-input "abc"
      (parsec-or (parsec-str "ac")
                 (parsec-ch ?a)))
    "a")))

(ert-deftest test-parsec-string ()
  (should
   (equal
    (parsec-with-input "abc"
      (parsec-string "abc"))
    "abc"))
  (should
   (equal
    (parsec-with-input "abc"
      (parsec-or (parsec-string "ac")
                 (parsec-ch ?a)))
    (parsec-error-new-2 "c" "b")))
  (should
   (equal
    (parsec-with-input "abc"
      (parsec-or (parsec-try (parsec-string "ac"))
                 (parsec-ch ?a)))
    "a")))

(ert-deftest test-parsec-or ()
  (should
   (equal
    (parsec-with-input "1"
      (parsec-or (parsec-letter)
                 (parsec-digit)))
    "1"))
  (should
   (equal
    (parsec-with-input "124"
      (parsec-or (parsec-string "13")
                 (parsec-ch ?1)))
    (parsec-error-new-2 "3" "2")))
  (should
   (equal
    (parsec-with-input "124"
      (parsec-or (parsec-str "13")
                 (parsec-ch ?1)))
    "1")))

(ert-deftest test-parsec-collect-optional ()
  (should
   (equal
    (parsec-with-input "abc-def"
      (parsec-collect-as-string
       (parsec-and
         (parsec-ch ?a)
         (parsec-str "bc"))
       (parsec-optional (parsec-ch ?-))
       (parsec-and
         (parsec-return (parsec-str "de")
           (parsec-ch ?f)))))
    "bc-de"))
  (should
   (equal
    (parsec-with-input "abcdef"
      (parsec-collect-as-string
       (parsec-and
         (parsec-ch ?a)
         (parsec-str "bc"))
       (parsec-optional (parsec-ch ?-))
       (parsec-and
         (parsec-return (parsec-str "de")
           (parsec-ch ?f)))))
    "bcde")))

(ert-deftest test-parsec-try ()
  (should
   (equal
    (parsec-with-input "abc"
      (parsec-or (parsec-try (parsec-string "abd"))
                 (parsec-str "abc")))
    "abc")))

(ert-deftest test-parsec-lookahead ()
  (should
   (equal
    (parsec-with-input "abc"
      (parsec-lookahead (parsec-str "abc"))
      (point))
    (point-min)))
  (should
   (equal
    (parsec-with-input "abc"
      (parsec-start
       (parsec-lookahead
        (parsec-and
          (parsec-ch ?a)
          (parsec-ch ?c))))
      (point))
    (1+ (point-min))))
  (should
   (equal
    (parsec-with-input "abc"
      (parsec-start
       (parsec-try
        (parsec-lookahead
         (parsec-and
           (parsec-ch ?a)
           (parsec-ch ?c)))))
      (point))
    (point-min))))

(ert-deftest test-parsec-error-handles ()
  (should
   (equal
    (parsec-with-input "abc"
      (parsec-with-error-message "foo"
        (parsec-str "abd")))
    (parsec-error-new "foo")))
  (should
   (equal
    (parsec-with-input "abc"
      (parsec-with-error-message "foo"
        (parsec-str "abc")))
    "abc"))
  (should
   (equal
    (condition-case err
        (parsec-with-input "abc"
          (parsec-ensure-with-error-message "foo"
            (parsec-str "abd")))
      (error (cdr err)))
    '("foo")))
  (should
   (equal
    (condition-case err
        (parsec-with-input "abc"
          (parsec-ensure-with-error-message "foo"
            (parsec-str "abc")))
      (error (cdr err)))
    "abc")))

(ert-deftest test-parsec-many ()
  (should
   (equal
    (parsec-with-input "aaaaab"
      (parsec-collect-as-string
       (parsec-many-as-string (parsec-ch ?a))
       (parsec-many-as-string (parsec-ch ?c))
       (parsec-many1-as-string (parsec-ch ?b))))
    "aaaaab"))
  (should
   (equal
    (parsec-with-input "aaaaab"
      (parsec-collect-as-string
       (parsec-many-as-string (parsec-ch ?a))
       (parsec-many-as-string (parsec-ch ?c))
       (parsec-many1-as-string (parsec-ch ?b))
       (parsec-many1-as-string (parsec-ch ?c))))
    (parsec-error-new-2 "c" "`EOF'")))
  (should
   (equal
    (parsec-with-input "abababaa"
      (parsec-many1-as-string (parsec-string "ab")))
    (parsec-error-new-2 "b" "a")))
  (should
   (equal
    (parsec-with-input "abababaa"
      (parsec-many1-as-string (parsec-try (parsec-string "ab")))
      (parsec-str "aa"))
    "aa"))
  (should
   (equal
    (parsec-with-input "abababaa"
      (parsec-many1-as-string (parsec-str "ab"))
      (parsec-str "aa"))
    "aa")))


(ert-deftest test-parsec-till ()
  (should
   (equal
    (parsec-with-input "abcd"
      (parsec-many-till-as-string (parsec-any-ch) (parsec-ch ?d)))
    "abc"))
  (should
   (equal
    (parsec-with-input "abcd"
      (parsec-many-till-as-string (parsec-any-ch) (parsec-ch ?d) :both))
    '("abc" . "d")))
  (should
   (equal
    (parsec-with-input "abcd"
      (parsec-many-till-as-string (parsec-any-ch) (parsec-ch ?d) :end))
    "d"))
  (should
   (equal
    (parsec-with-input "abcd"
      (parsec-with-error-message "eof"
        (parsec-many-till-as-string (parsec-any-ch) (parsec-ch ?e))))
    (parsec-error-new "eof")))
  (should
   (equal
    (parsec-with-input "abc"
      (parsec-until-as-string (parsec-ch ?c)))
    "ab"))
  (should
   (equal
    (parsec-with-input "abc"
      (parsec-until-as-string (parsec-ch ?c) :end))
    "c"))
  (should
   (equal
    (parsec-with-input "abc"
      (parsec-query (parsec-until-as-string (parsec-ch ?c)) :beg))
    1)))

(ert-deftest test-parsec-not-followed-by ()
  (should
   (equal
    (parsec-with-input "abd"
      (parsec-collect*
       (parsec-str "ab")
       (parsec-not-followed-by (parsec-ch ?c))
       (parsec-ch ?d)))
    '("ab" "d")))
  (should
   (equal
    (parsec-with-input "abd"
      (parsec-collect*
       (parsec-str "ab")
       (parsec-or (parsec-not-followed-by (parsec-ch ?d))
                  (parsec-not-followed-by (parsec-ch ?c)))
       (parsec-ch ?d)))
    '("ab" "d"))))

(ert-deftest test-parsec-endby ()
  (should
   (equal
    (parsec-with-input "abc\ndef"
      (parsec-endby (parsec-many-as-string (parsec-letter))
                    (parsec-eol-or-eof)))
    '("abc" "def"))))

(ert-deftest test-parsec-sepby ()
  (should
   (equal
    (parsec-with-input "ab,cd,ef"
      (parsec-sepby (parsec-many-as-string (parsec-re "[^,]"))
                    (parsec-ch ?,)))
    '("ab" "cd" "ef"))))

(ert-deftest test-parsec-between ()
  (should
   (equal
    (parsec-with-input "{abc}"
      (parsec-between
       (parsec-ch ?\{) (parsec-ch ?\})
       (parsec-or
        (parsec-str "ac")
        (parsec-many-as-string (parsec-letter)))))
    "abc"))
  (should
   (equal
    (parsec-with-input "{abc}"
      (parsec-between
       (parsec-ch ?\{) (parsec-ch ?\})
       (parsec-or
        (parsec-string "ac")
        (parsec-many-as-string (parsec-letter)))))
    (parsec-error-new-2 "c" "b"))))

(ert-deftest test-parsec-count ()
  (should
   (equal
    (parsec-with-input "aaaab"
      (parsec-return (parsec-count-as-string 3 (parsec-ch ?a))
        (parsec-many1 (parsec-one-of ?a ?b))))
    "aaa")))

(ert-deftest test-parsec-option ()
  (should
   (equal
    (parsec-with-input "ab"
      (parsec-option "opt" (parsec-string "ac")))
    (parsec-error-new-2 "c" "b")))
  (should
   (equal
    (parsec-with-input "ab"
      (parsec-option "opt" (parsec-str "ac")))
    "opt"))
  (should
   (equal
    (parsec-with-input "ab"
      (parsec-option "opt" (parsec-string "ab")))
    "ab")))

(ert-deftest test-parsec-optional ()
  (should
   (equal
    (parsec-with-input "abcdef"
      (parsec-collect-as-string
       (parsec-str "abc")
       (parsec-optional (parsec-ch ?-))
       (parsec-str "def")))
    "abcdef"))
  (should
   (equal
    (parsec-with-input "abc-def"
      (parsec-collect-as-string
       (parsec-str "abc")
       (parsec-optional (parsec-ch ?-))
       (parsec-str "def")))
    "abc-def"))
  (should
   (equal
    (parsec-with-input "abcdef"
      (parsec-collect-as-string
       (parsec-str "abc")
       (parsec-from-maybe (parsec-optional-maybe (parsec-ch ?-)))
       (parsec-str "def")))
    "abcdef"))
  (should
   (equal
    (parsec-with-input "abc-def"
      (parsec-collect-as-string
       (parsec-str "abc")
       (parsec-from-maybe (parsec-optional-maybe (parsec-ch ?-)))
       (parsec-str "def")))
    "abc-def")))

(provide 'parsec-tests)
;;; parsec-tests.el ends here
