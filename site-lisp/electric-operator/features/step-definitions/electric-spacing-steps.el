;; This file contains your project specific step definitions. All
;; files in this directory whose names end with "-steps.el" will be
;; loaded automatically by Ecukes.

(Then "^electric-operator-mode is on$"
      (lambda ()
        (cl-assert electric-operator-mode)
        ))

;; C/C++ stuff
(When "^I'm inside C main"
      (lambda ()
        (When "The buffer is empty")
        (insert "int main() {\n")
        (insert "\n")
        (insert "}\n")
        (When "I go to line \"2\"")))


;; Rust stuff
(When "^inside a rust function$"
      (lambda ()
        (insert "fn foo() -> i32 {\n")
        (insert "\n")
        (insert "}\n")
        (When "I go to line \"2\"")
        ))

(When "^inside a rust pattern matching statement$"
      (lambda ()
        (insert "match x {\n")
        (insert "\n")
        (insert "}\n")
        (When "I go to line \"2\"")
        ))

;; TODO: when ecukes merges this use the ecukes version instead
(When "^I turn off minor mode \\(.+\\)$"
      "Turns off some minor mode (to turn off a major mode you have to turn on another one)."
      (lambda (mode)
        (let ((v (vconcat [?\C-u ?- ?\M-x] (string-to-vector mode))))
          (execute-kbd-macro v))))

(When "^I let js2-mode reparse$"
      (lambda ()
        (js2-reparse)))

;; TODO: Figure out why this fails with call-interactively
;; It works correct with ert but seems to be problematic when used with ecukes
(When "^I go to end of line$"
      "Places the cursor at the end of the line."
      (lambda ()
        (funcall #'move-end-of-line nil)))

(When "^I execute newline-and-indent$"
      (lambda ()
        (newline-and-indent)))
