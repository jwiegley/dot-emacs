;;; eval-in-repl-test.el ---                         -*- lexical-binding: t; -*-

;; Copyright (C) 2014  Kazuki Yoshida

;; Author: Kazuki YOSHIDA <kazukiyoshida@mail.harvard.edu>
;; Keywords: tools, convenience
;; URL: https://github.com/kaz-yos/eval-in-repl
;; Version: 0.9.4

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
(require 'eval-in-repl)

(ert-deftest eir--matching-elements-test ()
  "Testing regexp matching filter"
  (should (equal (eir--matching-elements "mystr" '()) nil))
  (should (equal (eir--matching-elements "mystr" '("a" "b" "c")) nil))
  (should (equal (eir--matching-elements "mystr" '("a" "mystr_b" "c"))
                 '("mystr_b")))
  (should (equal (eir--matching-elements "mystr" '("a" "mystr_b" "c_mystr"))
                 '("mystr_b" "c_mystr")))
  (should (equal (eir--matching-elements "*ielm*" '("*ielm*" "ielm" " ielm "))
                 '("*ielm*")))
  (should (equal (eir--matching-elements "\\*nrepl-.*\\*$"
                                         '("nrepl-test" "*nrepl-test"
                                           "nrepl-test*" "*nrepl-test*"
                                           "*nrepl-test2*" "*nrepl-test3*"))
                 '("*nrepl-test*" "*nrepl-test2*" "*nrepl-test3*"))))


;; (provide 'eval-in-repl-test)
;;; eval-in-repl-test.el ends here

