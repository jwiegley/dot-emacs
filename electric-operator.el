;;; electric-operator.el --- Automatically add spaces around operators -*- lexical-binding: t; -*-

;; Copyright (C) 2015 Free Software Foundation, Inc.

;; Author: David Shepherd <davidshepherd7@gmail.com>
;; Version: 1.0.0
;; Package-Requires: ((dash "2.10.0") (names "20150618.0") (emacs "24.4"))
;; Keywords: electric
;; URL: https://github.com/davidshepherd7/electric-operator

;;; Commentary:

;; An emacs minor-mode to automatically add spacing around operators. For
;; example typing `a=10*5+2' results in `a = 10 * 5 + 2'.

;;; Code:

(require 'cc-mode)
(require 'thingatpt)
(require 'subr-x)

(require 'dash)
(require 'names)

;; namespacing using names.el:
;;;###autoload
(define-namespace electric-operator-

;; Tell names that it's ok to expand things inside these threading macros.
:functionlike-macros (-->)



;;; Customisable variables

(defcustom double-space-docs nil
  "Enable double spacing of . in document lines - e,g, type '.' => get '.  '."
  :type 'boolean
  :group 'electricity)

(defcustom enable-in-docs nil
  "Enable electric-operator in strings and comments."
  :type 'boolean
  :group 'electricity)

(defcustom c-pointer-type-style 'variable
  "Defines how C/C++ mode pointer and reference types are spaced.

If set to 'variable' then the operator is touching the variable
name, as in `int *x'.

If set to 'type' then the operator is touching the type name , as
in `int* x'."
  :group 'electricity
  :type 'symbol
  :options '(variable type))

(defcustom R-named-argument-style 'unspaced
  "Defines whether = in R named function arguments should be
spaced.

Setting the value to 'spaced' results in f(foo = 1), 'unspaced'
results in f(foo=1)."
  :group 'electricity
  :type 'symbol
  :options '(spaced unspaced))



;;; Other variables

(defvar -mode-rules-table
  (make-hash-table)
  "A hash table of replacement rule lists for specific major modes")



;;; Rule list helper functions

(defun -add-rule (initial new-rule)
  "Replace or append a new rule

Returns a modified copy of the rule list."
  (let* ((op (car new-rule))
         (existing-rule (assoc op initial)))
    (if existing-rule
        (-replace existing-rule new-rule initial)
      (-snoc initial new-rule))))

(defun -add-rule-list (initial new-rules)
  "Replace or append a list of rules

Returns a modified copy of the rule list."
  (-reduce #'-add-rule (-concat (list initial) new-rules)))

(defun add-rules (initial &rest new-rules)
  "Replace or append multiple rules

Returns a modified copy of the rule list."
  (-add-rule-list initial new-rules))


;; All rule manipulation should be done through these functions and not by
;; using puthash/gethash directly because it's plausible that the
;; underlying data structure could be changed (e.g. to an alist).

(defun get-rules-for-mode (major-mode-symbol)
  "Get the spacing rules for major mode"
  (gethash major-mode-symbol -mode-rules-table))

(defun add-rules-for-mode (major-mode-symbol &rest new-rules)
  "Replace or add spacing rules for major mode

Destructively modifies `electric-operator--mode-rules-table' to use the new rules for
the given major mode."
  (puthash major-mode-symbol
           (-add-rule-list (get-rules-for-mode major-mode-symbol)
                           new-rules)
           -mode-rules-table))



;;; Default rule lists

(defvar prog-mode-rules
  (list (cons "=" " = ")
        (cons "<" " < ")
        (cons ">" " > ")
        (cons "%" " % ")
        (cons "+" " + ")
        (cons "-" #'prog-mode--)
        (cons "*" " * ")
        (cons "/" #'prog-mode-/)
        (cons "&" " & ")
        (cons "|" " | ")
        (cons "?" "? ")
        (cons "," ", ")
        (cons "^" " ^ ")

        (cons "==" " == ")
        (cons "!=" " != ")
        (cons "<=" " <= ")
        (cons ">=" " >= ")

        (cons "*=" " *= ")
        (cons "+=" " += ")
        (cons "/=" " /= ")
        (cons "-=" " -= ")

        (cons "&&" " && ")
        (cons "||" " || ")
        )
  "Default spacing rules for programming modes")

(defvar prose-rules
  (add-rules '()
             (cons "." #'docs-.)
             (cons "," ", ")
             )
  "Rules to use in comments, strings and text modes.")



;;; Core functions

(defun get-rules-list ()
  "Pick which rule list is appropriate for spacing just before point"
  (save-excursion
    ;; We want to look one character before point because this is called
    ;; via post-self-insert-hook (there is no pre-self-insert-hook). This
    ;; allows us to correctly handle cases where the just-inserted
    ;; character ended a comment/string/...
    (forward-char -1)

    (cond
     ;; In comment or string?
     ((in-docs?) (if enable-in-docs prose-rules (list)))

     ;; Try to find an entry for this mode in the table
     ((get-rules-for-mode major-mode))

     ;; Default modes
     ((derived-mode-p 'prog-mode) prog-mode-rules)
     (t prose-rules))))

(defun rule-regex-with-whitespace (op)
  "Construct regex matching operator and any whitespace before/inside/after.

For example for the operator '+=' we allow '+=', ' +=', '+ ='. etc.

Whitespace before the operator is captured for possible use later.
"
  (concat "\\(\s*\\)"
          (mapconcat #'regexp-quote (split-string op "" t) "\s*")
          "\\(\s*\\)"))

(defun longest-matching-rule (rule-list)
  "Return the rule with the most characters that applies to text before point"
  (--> rule-list
       (-filter (lambda (rule) (looking-back-locally (rule-regex-with-whitespace (car rule)))) it)
       (-sort (lambda (p1 p2) (> (length (car p1)) (length (car p2)))) it)
       (car it)))

(defun eval-action (action point)
  (cond
   ((functionp action)
    (save-excursion (goto-char point) (funcall action)))
   ((stringp action) action)
   (t (error "Unrecognised action: %s" action))))

(defun post-self-insert-function ()
  "Check for a matching rule and apply it"
  (-let* ((rule (longest-matching-rule (get-rules-list)))
          ((operator . action) rule)
          (operator-just-inserted nil))
    (when (and rule action)

      ;; Find point where operator starts
      (looking-back-locally (rule-regex-with-whitespace operator) t)

      ;; Capture operator include all leading and *trailing* whitespace
      (save-excursion
        (goto-char (match-beginning 0))
        (looking-at (rule-regex-with-whitespace operator)))

      (let* ((pre-whitespace (match-string 1))
             (op-match-beginning (match-beginning 0))
             (op-match-end (match-end 0))
             (spaced-string (eval-action action op-match-beginning)))

        ;; If action was a function which eval-d to nil then we do nothing.
        (when spaced-string

          ;; Record the fact we are inserting something for passing to fixup
          ;; functions
          (setq operator-just-inserted t)

          ;; Set an undo boundary for easy undo-ing of the automatic insertion
          (undo-boundary)

          ;; Delete the characters matching this rule before point
          (delete-region op-match-beginning op-match-end)

          ;; If this is the first thing in a line then restore the
          ;; indentation.
          (when (looking-back-locally "^\s*")
            (insert pre-whitespace))

          ;; Insert correctly spaced operator
          (insert spaced-string))))

    (when (derived-mode-p 'haskell-mode)
      (haskell-mode-fixup-partial-operator-parens operator-just-inserted))))

:autoload
(define-minor-mode mode
  "Toggle automatic insertion of spaces around operators (Electric Spacing mode).

With a prefix argument ARG, enable Electric Spacing mode if ARG is
positive, and disable it otherwise.  If called from Lisp, enable
the mode if ARG is omitted or nil.

This is a local minor mode.  When enabled, typing an operator automatically
inserts surrounding spaces, e.g., `=' becomes ` = ',`+=' becomes ` += '."
  :global nil
  :group 'electricity
  :lighter " _+_"

  ;; body
  (if mode
      (add-hook 'post-self-insert-hook
                #'post-self-insert-function nil t)
    (remove-hook 'post-self-insert-hook
                 #'post-self-insert-function t)))



;;; Helper functions

(defun in-docs? ()
  "Check if we are inside a string or comment"
  (nth 8 (syntax-ppss)))

(defun hashbang-line? ()
  "Does the current line contain a UNIX hashbang?"
  (and (eq 1 (line-number-at-pos))
       (save-excursion
         (move-beginning-of-line nil)
         (looking-at "#!"))))

(defun enclosing-paren ()
  "Return the opening parenthesis of the enclosing parens, or nil
if not inside any parens."
  (interactive)
  (let ((ppss (syntax-ppss)))
    (when (nth 1 ppss)
      (char-after (nth 1 ppss)))))

(defun probably-unary-operator? ()
  "Try to guess if the operator we are about to insert will be unary

(i.e. takes one argument). This is a bit of a fudge based on C-like syntax."
  (or
   (looking-back-locally "^\\s-*")
   (looking-back-locally "[=,:\*\+-/><&^{;]\\s-*")
   (looking-back-locally "\\(return\\)\\s-*")))

(defun just-inside-bracket ()
  (looking-back-locally "[([{]"))

(defun looking-back-locally (string &optional greedy)
  "A wrapper for looking-back limited to the two previous lines

Apparently looking-back can be slow without a limit, and calling
it without a limit is deprecated.

Any better ideas would be welcomed."
  (let ((two-lines-up (save-excursion
                        (forward-line -2)
                        (beginning-of-line)
                        (point))))
    (looking-back string two-lines-up greedy)))




;;; General tweaks

(defun docs-. ()
  "Double space if setting tells us to"
  (if double-space-docs
      ".  "
    ". "))

(defun prog-mode-- ()
  "Handle exponent and negative number notation"
  (cond
   ;; Exponent notation, e.g. 1e-10: don't space
   ((looking-back-locally "[0-9.]+[eE]") "-")

   ;; Space negative numbers as e.g. a = -1 (but don't space f(-1) or -1
   ;; alone at all). This will proabaly need to be major mode specific
   ;; eventually.
   ((probably-unary-operator?) " -")
   ((just-inside-bracket) "-")

   (t " - ")))

(defun prog-mode-/ ()
  "Handle path separator in UNIX hashbangs"
  ;; First / needs a space before it, rest don't need any spaces
  (cond ((and (hashbang-line?) (looking-back-locally "#!")) " /")
        ((hashbang-line?) "/")
        (t " / ")))


(defun handle-c-style-comments-start ()
  "Handle / being (probably) the start of a full-line comment"
  (when (looking-back-locally "^\\s-*")
    "/")
  ;; else return nil so that it passes to the next cond in blocks
  )


;; Functions to handle comments in C-like languages
(defun c-like-mode-/ ()
  "Handle / being the first character of a comment"
  (cond
   ((handle-c-style-comments-start))
   (t (prog-mode-/))))

(defun c-like-mode-// ()
  "Handle // comments on (non-)empty lines."
  (if (looking-back-locally "^\s*") "// " " // "))

(defun c-like-mode-/* ()
  "Handle /* comments on (non-)empty lines."
  (if (looking-back-locally "^\s*") "/* " " /* "))




;;; C/C++ mode tweaks

(apply #'add-rules-for-mode 'c-mode prog-mode-rules)
(add-rules-for-mode 'c-mode
                    (cons "->" "->")

                    (cons "/" #'c-mode-/)

                    ;; ternary operator
                    (cons "?" " ? ")
                    (cons ":" #'c-mode-:) ; (or case label)

                    ;; pointers
                    (cons "*" #'c-mode-*)
                    (cons "&" #'c-mode-&)
                    (cons "**" #'c-mode-**) ; pointer-to-pointer type

                    ;; increment/decrement
                    (cons "++" #'c-mode-++)
                    (cons "--" #'c-mode---)

                    ;; #include statements
                    (cons "<" #'c-mode-<)
                    (cons ">" #'c-mode->)

                    ;; bitshift operators
                    (cons "<<" " << ")
                    (cons ">>" " >> ")

                    ;; Comments
                    (cons "/*" #'c-like-mode-/*)
                    (cons "//" #'c-like-mode-//)

                    ;; End of statement inc/decrement, handled separately
                    ;; because there is no space after the ++/--.
                    (cons "++;" "++;")
                    (cons "--;" "--;")

                    ;; Weirder assignment operators
                    (cons "%=" " %= ")
                    (cons "^=" " ^= ")
                    (cons "&=" " &= ")
                    (cons "|=" " |= ")
                    (cons "<<=" " <<= ")
                    (cons ">>=" " >>= ")

                    )


;; Use the same rules for c++
(apply #'add-rules-for-mode 'c++-mode (get-rules-for-mode 'c-mode))

;; And some extra rules
(add-rules-for-mode 'c++-mode

                    ;; Move constructor or `and' operator
                    (cons "&&" #'c++-mode-&&)

                    ;; Nested templates
                    (cons ">>" #'c++-mode->>)

                    ;; Handle for-each loops, public/private as well
                    (cons ":" #'c++-mode-:)

                    ;; Namespaces
                    (cons "::" "::")

                    ;; Lambdas
                    (cons "->" #'c++-mode-->)
                    (cons "=" #'c++-mode-=)

                    ;; Templates are hard to deal with sensibly
                    (cons "<" nil)
                    (cons ">" nil)
                    )

;; Construct and add null rules for operator=, operator<< etc.
(--> (get-rules-for-mode 'c++-mode)
     (-map (lambda (p) (cons (concat "operator" (car p)) nil)) it)
     (apply #'add-rules-for-mode 'c++-mode it))

;; Use the c rules for arduino mode
(apply #'add-rules-for-mode 'arduino-mode (get-rules-for-mode 'c-mode))


(defvar c-user-types-regex
  "_t"
  "Regex used in looking-back-locally to check for C types

For now we just assume that anything ending in '_t' is a type.
I'm not sure if we can do any better by default.

You could add your own type names to this if needed. Send pull
requests/bug reports if you find any widely used type names that
could be added here.")

(defun c-after-type? ()
  (or
   ;; Check for built-in types
   (looking-back-locally (concat c-primitive-type-key "?"))

   ;; Check if previous word is struct/union/enum keyword
   (looking-back-locally "\\b\\(struct\\|union\\|enum\\|const\\)[[:space:]]+[[:alnum:]\\|_\\|:]+")

   (looking-back-locally "auto")

   ;; Check for any user-defined types
   (looking-back-locally c-user-types-regex)))

(defvar c-function-definition-syntax-list
  '(topmost-intro
    topmost-intro-cont
    arglist-intro
    arglist-cont-nonempty)
  "syntax symbols for lines which contain a function definition

See `c-guess-basic-syntax'.")

(defun c-is-function-or-class-definition? ()
  "Try to guess if we are in function definition/declaration

Using `cc-mode''s syntactic analysis."
  ;; There are similar but different symbols for objective-C, but I'm not
  ;; going to try to support that now.

  (--> (c-guess-basic-syntax)
       (-map #'car it)
       (-intersection c-function-definition-syntax-list it)))

(defun c-mode-include-line? ()
  (looking-back-locally "#\s*include.*"))

(defun c-mode-probably-ternary ()
  (looking-back-locally "\\?.+"))

(defun c-mode-: ()
  "Handle the : part of ternary operator"
  (if (c-mode-probably-ternary)
      " : "
    ":"))

(defun c++-mode-: ()
  "Handle ternary, case, or for each"
  (cond
   ;; Public/private class methods
   ((looking-back-locally "private\\|public\\|protected") ":")

   ;; The colon in `class Foo : public Bar`
   ((c-is-function-or-class-definition?) " : ")

   ((c-mode-probably-ternary) " : ")

   ;; probably a for-each loop
   ((equal (enclosing-paren) ?\() " : ")

   ;; probably a case statement
   (t ":" )))


(defun c-mode-++ ()
  "Handle ++ operator pre/postfix"
  (if (looking-back-locally "[a-zA-Z0-9_]\s*")
      "++ "
    " ++"))

(defun c-mode--- ()
  "Handle -- operator pre/postfix"
  (if (looking-back-locally "[a-zA-Z0-9_]\s*")
      "-- "
    " --"))

(defun c-mode-< ()
  "Handle #include brackets and templates"
  (cond ((c-mode-include-line?) " <")
        ((c-is-function-or-class-definition?) "<")
        (t " < ")))

(defun c-mode-> ()
  "Handle #include brackets and templates"
  (cond ((c-mode-include-line?) ">")
        ((c-is-function-or-class-definition?) "> ")
        (t " > ")))

(defun c++-mode->> ()
  "Handle nested templates"
  (cond ((c-is-function-or-class-definition?) ">> ")
        (t " >> ")))

(defun c-space-pointer-type (op)
  "Space a C pointer types operator as specified by
  `c-pointer-type-style'.

 For example `int* x'  or `int *x'."
  (cond ((eq c-pointer-type-style  'variable) (concat " " op))
        ((eq c-pointer-type-style 'type) (concat op " "))
        (t (error "Unrecognised value for c-pointer-type-style."))))

(defun c-mode-& ()
  "Handle C address-of operator and reference types"
  (cond
   ;; Reference types
   ((or (c-after-type?) (c-is-function-or-class-definition?))
    (c-space-pointer-type "&"))

   ;; Address-of operator or lambda pass-by-reference specifier
   ((just-inside-bracket) "&")
   ((probably-unary-operator?) " &")

   (t " & ")))

(defun c-mode-* ()
  "Handle C dereference operator and pointer types

Also handles C++ lambda capture by reference."
  (cond
   ;; Pointer types
   ((or (c-after-type?) (c-is-function-or-class-definition?))
    (c-space-pointer-type "*"))

   ;; Pointer dereference
   ((just-inside-bracket) "*")
   ((probably-unary-operator?) " *")

   (t " * ")))

(defun c-mode-** ()
  "C pointer to pointer or multiplication by pointer dereference.
  e.g. `res = a * *b;`'"
  (if (c-after-type?)
      (c-space-pointer-type "**")
    " * *"))

(defun c++-mode-&& ()
  "Handle move constructor"
  (if (c-is-function-or-class-definition?)
      (c-space-pointer-type "&&")
    " && "))

(defun c-mode-/ ()
  "Handle / in #include <a/b> and start of full-line comment"
  (cond
   ((c-mode-include-line?) "/")
   ((handle-c-style-comments-start))
   (t (prog-mode-/))))

(defun c++-probably-lambda-arrow ()
  "Try to guess if we are writing a lambda statement"
  (looking-back-locally "\\[[^]]*\\]\\s-*([^)]*)\\s-*\\(mutable\\)?"))

(defun c++-mode--> ()
  "Handle lambda arrows"
  (if (c++-probably-lambda-arrow)
      " -> "
    "->"))

(defun c++-mode-= ()
  "Handle capture-by-value in lamdas"
  (cond
   ((probably-unary-operator?) " =")
   ((just-inside-bracket) "=")
   (t " = ")))



;;; Python mode tweaks

(apply #'add-rules-for-mode 'python-mode prog-mode-rules)
(add-rules-for-mode 'python-mode
                    (cons "**" #'python-mode-**)
                    (cons "*" #'python-mode-*)
                    (cons ":" #'python-mode-:)
                    (cons "//" " // ") ; integer division
                    (cons "=" #'python-mode-kwargs-=)
                    (cons "-" #'python-mode-negative-slices)
                    (cons "->" " -> ") ; function return types
                    )

(defun python-mode-in-lambda-args? ()
  "Are we inside the arguments statement of a lambda?"
  (looking-back-locally "lambda[^:]*"))

(defun python-mode-: ()
  "Handle python dict assignment"
  (cond
   ((python-mode-in-lambda-args?) ": ")
   ((eq (enclosing-paren) ?\{) ": ")
   ((and (eq (enclosing-paren) ?\() (looking-back-locally "def .*")) ": ") ; type definitions

   ;; Probably a variable type definition or an end of a keyword line, leave it
   ;; alone for now (possible TODO: variable type definitions properly by
   ;; checking if this line matches any keywords, and if not treating it as a
   ;; type definition).
   (t nil)))

(defun python-mode-* ()
  "Handle python *args"
  (cond
   ;; After a ',' we need a space before
   ((looking-back-locally ",")  " *")
   ;; After a '(' or a newline we don't
   ((looking-back-locally "\\((\\|^\\)")  "*")
   ;; Othewise act as normal
   (t  " * ")))

(defun python-mode-** ()
  "Handle python **kwargs"
  (cond
   ;; After a ',' we need a space before
   ((looking-back-locally ",")  " **")
   ;; After a '(' or a newline we don't
   ((looking-back-locally "\\((\\|^\\)")  "**")
   (t " ** ")))

(defun python-mode-kwargs-= ()
  (cond
   ((python-mode-in-lambda-args?) "=")
   ((eq (enclosing-paren) ?\() "=")
   (t " = ")))

(defun python-mode-negative-slices ()
  "Handle cases like a[1:-1], see issue #2."
  (if (and (eq (enclosing-paren) ?\[)
           (looking-back-locally ":"))
      "-"
    (prog-mode--)))



;;; Javascript mode tweaks

(defun js-mode-: ()
  "Handle object assignment and ternary"
  (if (eq (enclosing-paren) ?\{)
      ": "
    " : "))

(defun js-mode-/ ()
  "Handle regex literals and division"
  ;; Closing / counts as being inside a string so we don't need to do anything.
  (cond
   ;; Probably starting a comment or regex
   ((handle-c-style-comments-start))
   ;; Probably starting a regex
   ((probably-unary-operator?) nil)
   (t (prog-mode-/))))

(apply #'add-rules-for-mode 'js-mode prog-mode-rules)
(add-rules-for-mode 'js-mode
                    (cons "%=" " %= ")
                    (cons "++" "++ ")
                    (cons "--" "-- ")
                    (cons "===" " === ")
                    (cons "!==" " !== ")
                    (cons "<<" " << ")
                    (cons ">>" " >> ")
                    (cons ":" #'js-mode-:)
                    (cons "?" " ? ")
                    (cons "/" #'js-mode-/)
                    (cons "//" #'c-like-mode-//)
                    (cons "/*" #'c-like-mode-/*)
                    (cons "=>" " => ") ; ES6 arrow functions
                    )

(apply #'add-rules-for-mode 'js2-mode (get-rules-for-mode 'js-mode))

(apply #'add-rules-for-mode 'typescript-mode (get-rules-for-mode 'js-mode))
(add-rules-for-mode 'typescript-mode
                    (cons ":" nil)
                    ;; Generics ruin everything
                    (cons ">>" nil)
                    (cons "<" nil)
                    (cons ">" nil)
                    (cons ">=" nil))



;;; Rust mode tweaks

(apply #'add-rules-for-mode 'rust-mode prog-mode-rules)
(add-rules-for-mode 'rust-mode
                    ;; templates are hard
                    (cons "<" nil)
                    (cons ">" nil)

                    ;; mut vs. bitwise and
                    (cons "&" nil)

                    ;; pointer deref vs multiplication
                    (cons "*" nil)

                    (cons "/" #'c-like-mode-/)
                    (cons "/*" #'c-like-mode-/*)
                    (cons "//" #'c-like-mode-//)

                    ;; Extra operators
                    (cons "<<" " << ")
                    (cons ">>" " >> ")
                    (cons "->" " -> ")
                    (cons "=>" " => ")

                    )



;; R tweaks (ess mode)

(defun ess-mode-keyword-args-= ()
  (if (and (eq R-named-argument-style 'unspaced)
           (eq (enclosing-paren) ?\())
      "="
    " = "))

(apply #'add-rules-for-mode 'ess-mode prog-mode-rules)
(add-rules-for-mode 'ess-mode
                    (cons "." nil) ; word separator
                    (cons "<-" " <- ") ; assignment
                    (cons "->" " -> ") ; Right assignment
                    (cons "%%" " %% ") ; Modulus
                    (cons "%/%" " %/% ") ; Integer divide
                    (cons "%*%" " %*% ") ; Matrix product
                    (cons "%o%" " %o% ") ; Outer product
                    (cons "%x%" " %x% ") ; Kronecker product
                    (cons "%in%" " %in% ") ; Matching operator
                    (cons "~" " ~ ") ; "is modeled by"
                    (cons "%>%" " %>% ") ; Pipe (magrittr)
                    (cons "%<>%" " %<>% ") ; Assignment pipe (magrittr)
                    (cons "%$%" " %$% ") ; Exposition pipe (magrittr)
                    (cons "%T>%" " %T>% ") ; Tee operator (magrittr)
                    (cons "=" #'ess-mode-keyword-args-=)
                    )

(defun ess-comma-post-self-insert-function ()
  (when mode
    (post-self-insert-function)))

;; ess-mode binds comma to a function, so we need to advise that function
;; to also run our code:
(with-eval-after-load 'ess-mode
  (advice-add 'ess-smart-comma :after #'ess-comma-post-self-insert-function))



;;; Other major mode tweaks

(apply #'add-rules-for-mode 'ruby-mode prog-mode-rules)
(add-rules-for-mode 'ruby-mode
                    (cons "=~" " =~ ") ; regex equality
                    )

(apply #'add-rules-for-mode 'perl-mode prog-mode-rules)
(add-rules-for-mode 'perl-mode
                    (cons "=~" " =~ ") ; regex equality
                    )

;; cperl mode is another perl mode, copy the rules
(apply #'add-rules-for-mode 'cperl-mode (get-rules-for-mode 'cperl-mode))

;; This is based on a syntax guide and hasn't been tested.
(apply #'add-rules-for-mode 'java-mode prog-mode-rules)
(add-rules-for-mode 'java-mode

                    ;; ternary operator
                    (cons "?" " ? ")
                    (cons ":" #'c-mode-:) ; (or case label)

                    ;; increment/decrement
                    (cons "++" #'c-mode-++)
                    (cons "--" #'c-mode---)

                    ;; bitshift operators
                    (cons "<<" " << ")
                    (cons ">>" " >> ")
                    (cons ">>>" " >>> ")

                    ;; Weirder assignment operators
                    (cons "%=" " %= ")
                    (cons "^=" " ^= ")
                    (cons "&=" " &= ")
                    (cons "|=" " |= ")
                    (cons "<<=" " <<= ")
                    (cons ">>=" " >>= ")

                    ;; Comments
                    (cons "/" #'c-like-mode-/)
                    (cons "/*" #'c-like-mode-/*)
                    (cons "//" #'c-like-mode-//)

                    ;; Generics are hard
                    (cons "<" nil)
                    (cons ">" nil)
                    )



;; Haskell mode

(defconst haskell-mode-infix-binary-operators
  (list "=" "<" ">" "%" "+" "*" "&" "|" "==" "<=" ">=" "&&" "||"

        "++" ; list concat
        "!!"  ; indexing
        ".|." ; bitwise OR
        ".&." ; bitwise AND
        "$" ; delay evaluation

        ;; Monads or something like that
        ">>" ">>=" "<$>" "<*>"

        ;; Exponents, for some reason there are three of
        ;; them!
        "^" "**" "^^"
        ))

(defconst haskell-mode-special-infix-binary-operators
  (list "/" "-"))

(defun haskell-mode-infix-action (op)
  (lambda ()
    (let ((after-paren (looking-back-locally "(\\s-*"))
          (before-paren (looking-at (concat (rule-regex-with-whitespace op) ")"))))
      (cond
       ;; only thing in the parens: no spaces
       ((and after-paren before-paren) op)

       (before-paren (concat " " op))
       (after-paren (concat op " "))
       (t (concat " " op " "))))))

(defun haskell-mode-fixup-partial-operator-parens (operator-just-inserted)
  (when (not operator-just-inserted)
    (-each (-concat haskell-mode-infix-binary-operators haskell-mode-special-infix-binary-operators)
      (lambda (op)
        ;; If another character was typed between an operator and `)', make sure
        ;; these's a single space there.
        (when (and (looking-at "\\s-*)")
                   (looking-back-locally (concat (rule-regex-with-whitespace op) "[^\\s-]")))
          (save-excursion (replace-match " " nil nil nil 2)))

        ;; When inserting a ) delete any whitespace between it and the operator
        (when (looking-back-locally (concat "\\s-" op ")"))
          (save-excursion (replace-match ")" nil nil nil 0)))))))

(defun haskell-mode-/ ()
  (let ((base (funcall (haskell-mode-infix-action "/"))))
    (if (equal base " / ")
        (prog-mode-/)
      base)))

(defun haskell-mode-- ()
  (let ((base (funcall (haskell-mode-infix-action "-"))))
    (if (equal base " - ")
        (prog-mode--)
      base)))

(apply #'add-rules-for-mode 'haskell-mode prog-mode-rules)

;; Make rules for partially evaluated binary operators inside parens
(apply #'add-rules-for-mode 'haskell-mode
       (-map (lambda (op) (cons op (haskell-mode-infix-action op)))
             haskell-mode-infix-binary-operators))

(add-rules-for-mode 'haskell-mode

                    ;; More complex infix operators
                    (cons "-" #'haskell-mode--)
                    (cons "/" #'haskell-mode-/)
                    (cons ":" nil)  ; list constructor: no spaces needed in either

                    (cons "--" "-- ") ; comment
                    (cons "<-" " <- ") ; assignment
                    (cons "->" " -> ") ; lambdas and function types
                    (cons "=>" " => ") ; typeclasses
                    (cons "::" " :: ") ; type specification
                    (cons "!=" nil) ; unused
                    (cons "~" " ~") ; lazy pattern match

                    ;; Comments?
                    (cons "{-" "{- ")
                    (cons "-}" " -}")

                    ;; Either function composition or function qualification,
                    ;; can't tell so disable it
                    (cons "." nil)
                    )



(apply #'add-rules-for-mode 'php-mode prog-mode-rules)
(add-rules-for-mode 'php-mode
                    (cons "**" " ** ")
                    (cons "%=" " %= ")
                    (cons "===" " === ")
                    (cons "<>" " <> ") ; not-equal
                    (cons "!==" " !== ")
                    (cons "++" #'c-mode-++)
                    (cons "--" #'c-mode---)
                    (cons "." " . ")   ; string concat
                    (cons ".=" " .= ")
                    (cons "->" "->")
                    (cons "=>" " => ")
                    (cons "<?" "<?")

                    (cons "/" #'c-like-mode-/)
                    (cons "/*" #'c-like-mode-/*)
                    (cons "//" #'c-like-mode-//)
                    )


;; Coffee script support based on http://coffeescript.org/#operators
(apply #'add-rules-for-mode 'coffee-mode prog-mode-rules)
(add-rules-for-mode 'coffee-mode
                    (cons "**" " ** ")
                    (cons "//" " // ")
                    (cons "///" " /// ")
                    (cons "%%" " %% ")
                    (cons "?" "? ")
                    (cons "?=" " ?= ")
                    (cons "?." "?.")
                    (cons "->" " -> ")
                    (cons "=>" " => ")
                    )

(apply #'add-rules-for-mode 'sql-mode prog-mode-rules)
(add-rules-for-mode 'sql-mode
                    (cons "-" nil)
                    (cons "=" nil)
                    (cons "%" nil)
                    (cons "*" nil))

;; Don't use either prog or text mode defaults, css is too different
(add-rules-for-mode 'css-mode
                    (cons ":" ": ")
                    (cons "," ", "))

(add-rules-for-mode 'scss-mode
                    (cons ":" ": ")
                    (cons "," ", "))




;;; Julia mode

(defun julia-mode-kwargs-= ()
  (cond
   ((eq (enclosing-paren) ?\() "=")
   (t " = ")))

(apply #'add-rules-for-mode 'julia-mode prog-mode-rules)
(add-rules-for-mode 'julia-mode

                    (cons "=" #'julia-mode-kwargs-=)
                    (cons ";" "; ")

                    ;; Subtype comparison
                    (cons "<:" " <: ")

                    ;; Cool! Unicode!
                    (cons "÷" " ÷ ")
                    (cons "≠" " ≠ ")
                    (cons "≤" " ≤ ")
                    (cons "≥" " ≥ ")

                    ;; something about fractions
                    (cons "//" " // ")
                    (cons ".//" " .// ")
                    (cons "//=" " //= ")

                    ;; pipe
                    (cons "|>" " |> ")

                    (cons "*" " * ")
                    (cons "/" " / ")
                    (cons "%" " % ")
                    (cons "&" " & ")

                    ;; \ (escaped), for solving matrix multiplies
                    (cons "\\" " \\ ")
                    (cons "\\=" " \\= ")
                    (cons ".\\" " .\\ ")

                    ;; XOR
                    (cons "$" " $ ")

                    ;; Even more equal!
                    (cons "===" " === ")
                    (cons "!==" " !== ")

                    ;; vector operations and assign-operators
                    (cons ".^" " .^ ")
                    (cons ".*" " .* ")
                    (cons "./" " ./ ")
                    (cons ".%" " .% ")
                    (cons "<<" " << ")
                    (cons ">>" " >> ")
                    (cons ">>>" " >>> ")
                    (cons ".<<" " .<< ")
                    (cons ".>>" " .>> ")
                    (cons ".>>>" " .>>> ")
                    (cons ".+" " .+ ")
                    (cons ".-" " .- ")
                    (cons ".>" " .> ")
                    (cons ".<" " .< ")
                    (cons ".>=" " .>= ")
                    (cons ".<=" " .<= ")
                    (cons ".==" " .== ")
                    (cons ".!=" " .!= ")
                    (cons "^=" " ^= ")
                    (cons "÷=" " ÷= ")
                    (cons "%=" " %= ")
                    (cons "|=" " |= ")
                    (cons "&=" " &= ")
                    (cons "$=" " $= ")
                    (cons "<<=" " <<= ")
                    (cons ">>=" " >>= ")
                    (cons ">>>=" " >>>= ")
                    (cons ".+=" " .+= ")
                    (cons ".-=" " .-= ")
                    (cons ".*=" " .*= ")
                    (cons "./=" " ./= ")
                    (cons ".//=" " .//= ")
                    (cons ".\\=" " .\\= ")
                    (cons ".^=" " .^= ")
                    (cons ".÷=" " .÷= ")
                    (cons ".%=" " .%= "))


) ; end of namespace

(provide 'electric-operator)

;;; electric-operator.el ends here
