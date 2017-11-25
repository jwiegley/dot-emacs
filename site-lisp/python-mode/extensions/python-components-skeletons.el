;;; python-components-skeletons.el --- python-mode skeletons

;; Maintainer: Andreas Roehler <andreas.roehler@online.de>
;; Keywords: languages

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

;;; Commentary: Derived from GNU python.el, where it's instrumented as abbrev; errors are mine

;;; Code:
(define-skeleton py-else
  "Auxiliary skeleton."
  nil
  (unless (eq ?y (read-char "Add `else' clause? (y for yes or RET for no) "))
    (signal 'quit t))
  < "else:" \n)

(define-skeleton py-if
    "If condition "
  "if " "if " str ":" \n
  _ \n
  ("other condition, %s: "
  < "elif " str ":" \n
   > _ \n nil)
  '(py-else) | ^)

(define-skeleton py-while
    "Condition: "
  "while " "while " str ":" \n
  > -1 _ \n
  '(py-else) | ^)

(define-skeleton py-for
    "Target, %s: "
  "for " "for " str " in " (skeleton-read "Expression, %s: ") ":" \n
  > -1 _ \n
  '(py-else) | ^)

(define-skeleton py-try/except
    "Py-try/except skeleton "
  "try:" "try:" \n
  > -1 _ \n
  ("Exception, %s: "
   < "except " str '(python-target) ":" \n
   > _ \n nil)
  < "except:" \n
  > _ \n
  '(py-else) | ^)

(define-skeleton py-target
  "Auxiliary skeleton."
  "Target, %s: " ", " str | -2)

(define-skeleton py-try/finally
    "Py-try/finally skeleton "
  "try:" \n
  > -1 _ \n
  < "finally:" \n
  > _ \n)

(define-skeleton py-def
    "Name: "
  "def " str " (" ("Parameter, %s: " (unless (equal ?\( (char-before)) ", ")
                   str) "):" \n
                   "\"\"\"" - "\"\"\"" \n     ; Fixme:  extra space inserted -- why?).
                   > _ \n)

(define-skeleton py-class
    "Name: "
  "class " str " (" ("Inheritance, %s: "
		     (unless (equal ?\( (char-before)) ", ")
		     str)
  & ")" | -2				; close list or remove opening
  ":" \n
  "\"\"\"" - "\"\"\"" \n
  > _ \n)

;;;

(provide 'python-components-skeletons)
;;; python-components-skeletons.el ends here
