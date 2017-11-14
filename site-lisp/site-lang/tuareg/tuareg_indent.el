;;; tuareg_indent.el --- Old (pre-SMIE) indentation code for tuarge-mode

;; This software is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This software is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;;; Code:

(eval-when-compile (require 'cl))
(require 'tuareg)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                       User customizable variables

;; Comments

(defcustom tuareg-indent-leading-comments t
  "*If true, indent leading comment lines (starting with `(*') like others."
  :group 'tuareg :type 'boolean)

(defcustom tuareg-indent-comments t
  "*If true, automatically align multi-line comments."
  :group 'tuareg :type 'boolean)

(defcustom tuareg-comment-end-extra-indent 0
  "*How many spaces to indent a leading comment end `*)'.
If you expect comments to be indented like
        (*
          ...
         *)
even without leading `*', use `tuareg-comment-end-extra-indent' = 1."
  :group 'tuareg
  :type '(radio :extra-offset 8
                :format "%{Comment End Extra Indent%}:
   Comment alignment:\n%v"
                (const :tag "align with `(' in comment opening" 0)
                (const :tag "align with `*' in comment opening" 1)
                (integer :tag "custom alignment" 0)))


;; Comments

(defcustom tuareg-leading-star-in-doc nil
  "*Enable automatic intentation of documentation comments of the form
        (**
         * ...
         *)"
  :group 'tuareg :type 'boolean)

(defcustom tuareg-support-leading-star-comments t
  "*Enable automatic intentation of comments of the form
        (*
         * ...
         *)
Documentation comments (** *) are not concerned by this variable
unless `tuareg-leading-star-in-doc' is also set.

If you do not set this variable and still expect comments to be
indented like
        (*
          ...
         *)
\(without leading `*'), set `tuareg-comment-end-extra-indent' to 1."
  :group 'tuareg :type 'boolean)

;; Indentation defaults

(defcustom tuareg-let-always-indent t
  "*If true, enforce indentation is at least `tuareg-let-indent' after a `let'.

As an example, set it to nil when you have `tuareg-with-indent' set to 0,
and you want `let x = match ... with' and `match ... with' indent the
same way."
  :group 'tuareg :type 'boolean)

(defcustom tuareg-pipe-extra-unindent tuareg-default-indent
  "*Extra backward indent for OCaml lines starting with the `|' operator.

It is NOT the variable controlling the indentation of the `|' itself:
this value is automatically added to `function', `with', `parse' and
some cases of `type' keywords to leave enough space for `|' backward
indentation.

For example, setting this variable to 0 leads to the following indentation:
  match ... with
    X -> ...
    | Y -> ...
    | Z -> ...

To modify the indentation of lines lead by `|' you need to modify the
indentation variables for `with', `function', and possibly
for `type' as well.  For example, setting them to 0 (and leaving
`tuareg-pipe-extra-unindent' to its default value) yields:
  match ... with
    X -> ...
  | Y -> ...
  | Z -> ..."
  :group 'tuareg :type 'integer)

(defcustom tuareg-class-indent tuareg-default-indent
  "*How many spaces to indent from a `class' keyword."
  :group 'tuareg :type 'integer)

(defcustom tuareg-sig-struct-align t
  "*Align `sig' and `struct' keywords with `module'."
  :group 'tuareg :type 'boolean)

(defcustom tuareg-sig-struct-indent tuareg-default-indent
  "*How many spaces to indent from a `sig' or `struct' keyword."
  :group 'tuareg :type 'integer)

(defcustom tuareg-method-indent tuareg-default-indent
  "*How many spaces to indent from a `method' keyword."
  :group 'tuareg :type 'integer)

(defcustom tuareg-begin-indent tuareg-default-indent
  "*How many spaces to indent from a `begin' keyword."
  :group 'tuareg :type 'integer)

(defcustom tuareg-for-while-indent tuareg-default-indent
  "*How many spaces to indent from a `for' or `while' keyword."
  :group 'tuareg :type 'integer)

(defcustom tuareg-do-indent tuareg-default-indent
  "*How many spaces to indent from a `do' keyword."
  :group 'tuareg :type 'integer)

(defcustom tuareg-fun-indent tuareg-default-indent
  "*How many spaces to indent from a `fun' keyword."
  :group 'tuareg :type 'integer)

(defcustom tuareg-function-indent 0 ;tuareg-default-indent
  "*How many spaces to indent from a `function' keyword."
  :group 'tuareg :type 'integer)

(defcustom tuareg-if-then-else-indent tuareg-default-indent
  "*How many spaces to indent from an `if', `then' or `else' keyword."
  :group 'tuareg :type 'integer)

(defcustom tuareg-let-indent tuareg-default-indent
  "*How many spaces to indent from a `let' keyword."
  :group 'tuareg :type 'integer)

(defcustom tuareg-match-indent tuareg-default-indent
  "*How many spaces to indent from a `match' keyword."
  :group 'tuareg :type 'integer)

(defcustom tuareg-try-indent tuareg-default-indent
  "*How many spaces to indent from a `try' keyword."
  :group 'tuareg :type 'integer)

(defcustom tuareg-type-indent tuareg-default-indent
  "*How many spaces to indent from a `type' keyword."
  :group 'tuareg :type 'integer)

(defcustom tuareg-val-indent tuareg-default-indent
  "*How many spaces to indent from a `val' keyword."
  :group 'tuareg :type 'integer)

;; Tuareg-Interactive



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun tuareg-ro (&rest words) (concat "\\<" (regexp-opt words t) "\\>"))

(eval-and-compile
  (defconst tuareg-no-more-code-this-line-regexp "[ \t]*\\((\\*\\|$\\)"
    "Regexp matching lines which have no more code:
 blanks + (maybe) comment start."))

(defmacro tuareg-no-code-after (rex)
  `(eval-when-compile (concat ,rex tuareg-no-more-code-this-line-regexp)))

(defconst tuareg-no-code-this-line-regexp
  (concat "^" tuareg-no-more-code-this-line-regexp))

(defconst tuareg-extra-unindent-regexp
  (concat "\\(" (tuareg-ro "with" "fun" "function")
          "\\|\\[" tuareg-no-more-code-this-line-regexp "\\)")
  "Regexp for keywords needing extra indentation to compensate for case matches.")

(defconst tuareg-ls3-extras (concat "\\|" (tuareg-ro "automaton" "present")))

(defconst tuareg-extra-unindent-regexp-ls3
  (concat tuareg-extra-unindent-regexp tuareg-ls3-extras)
  "Regexp for keywords needing extra indentation to compensate for case matches.")

(defun tuareg-give-extra-unindent-regexp ()
  (if (tuareg-editing-ls3)
      tuareg-extra-unindent-regexp-ls3
    tuareg-extra-unindent-regexp))

(defconst tuareg-keyword-regexp
  (concat (tuareg-ro "object" "initializer" "and" "constraint" "class"
                     "match" "module" "method" "mutable" "sig" "struct" "begin"
                     "else" "exception" "external" "to" "then" "try" "type"
                     "virtual" "val" "while" "when" "with" "if" "in" "inherit"
                     "for" "fun" "functor" "function" "let" "do" "downto"
                     "of")
          "\\|->\\|[;,|]")
  "Regexp for all recognized keywords.")

(defconst tuareg-keyword-regexp-ls3
  (concat tuareg-keyword-regexp "\\|"
          (tuareg-ro "where" "automaton" "present" "fby" "pre" "last" "merge"
                     "when" "reset" "every" "emit" "until" "unless" "period"
                     "at"))
  "Regexp for all recognized keywords.
For synchronous programming.")

(defun tuareg-give-keyword-regexp ()
  (if (tuareg-editing-ls3)
      tuareg-keyword-regexp-ls3
    tuareg-keyword-regexp))

(defconst tuareg-match-pipe-kwop-regexp
  (concat (tuareg-ro "and" "function" "type" "with")
          "\\|[[({=]\\||[^!]")
  "Regexp for keywords supporting case match.")

(defconst tuareg-match-pipe-kwop-regexp-ls3
  (concat tuareg-match-pipe-kwop-regexp tuareg-ls3-extras)
  "Regexp for keywords supporting case match.
For synchronous programming.")

(defun tuareg-give-match-pipe-kwop-regexp ()
  (if (tuareg-editing-ls3)
      tuareg-match-pipe-kwop-regexp-ls3
    tuareg-match-pipe-kwop-regexp))

(defconst tuareg-operator-regexp "[-+*/=<>@^&|]\\|:>\\|::\\|\\<\\(or\\|l\\(and\\|x?or\\|s[lr]\\)\\|as[lr]\\|mod\\)\\>"
  "Regexp for all operators.")

(defconst tuareg-matching-keyword-regexp
  (tuareg-ro "and" "do" "done" "then" "else" "end" "in" "downto")
  "Regexp matching OCaml keywords which act as end block delimiters.")

(defconst tuareg-extra-ls3-keyword-regexp
  (tuareg-ro "where" "unless" "until" "every")
  "Additional Lucid Synchrone keywords.")

(defconst tuareg-matching-keyword-regexp-ls3
  (concat tuareg-matching-keyword-regexp "\\|" tuareg-extra-ls3-keyword-regexp)
  "Regexp matching OCaml keywords which act as end block delimiters
For synchronous programming.")

(defun tuareg-give-matching-keyword-regexp ()
  (let ((rxp (if (tuareg-editing-ls3)
                 tuareg-matching-keyword-regexp-ls3
               tuareg-matching-keyword-regexp)))
    (if tuareg-support-metaocaml
        (concat rxp "\\|>\\.")
      rxp)))

(defconst tuareg-matching-kwop-regexp
  (concat tuareg-matching-keyword-regexp
          "\\|\\<with\\>\\|[|>]?\\]\\|>?}\\|[|)]\\|;;")
  ;; FIXME: what about \\|\\<end\\> ?
  "Regexp matching OCaml keywords or operators which act as end block
delimiters.")

(defconst tuareg-matching-kwop-regexp-ls3
  (concat tuareg-matching-kwop-regexp "\\|" tuareg-extra-ls3-keyword-regexp)
  "Regexp matching OCaml keywords or operators which act as end block
delimiters.  For synchronous programming.")

(defun tuareg-give-matching-kwop-regexp ()
  (if (tuareg-editing-ls3)
      tuareg-matching-kwop-regexp-ls3
    tuareg-matching-kwop-regexp))

(defconst tuareg-block-regexp
  (concat (tuareg-ro "for" "while" "do" "if" "begin" "sig" "struct" "object")
          "\\|[][(){}]\\|\\*)"))

(defconst tuareg-find-kwop-regexp
  (concat tuareg-matching-keyword-regexp "\\|" tuareg-block-regexp))

(defconst tuareg-find-kwop-regexp-ls3
  (concat tuareg-find-kwop-regexp "\\|"
          (tuareg-ro "where" "automaton" "present" "match")))

(defun tuareg-give-find-kwop-regexp ()
  (if (tuareg-editing-ls3)
      tuareg-find-kwop-regexp-ls3
    tuareg-find-kwop-regexp))

(defconst tuareg-governing-phrase-regexp
  (tuareg-ro "val" "type" "method" "module" "constraint" "class" "inherit"
             "initializer" "external" "exception" "open" "let" "object"
             "include")
  "Regexp matching tuareg phrase delimitors.")

(defconst tuareg-keyword-alist
  '(("module" . tuareg-default-indent)
    ("class" . tuareg-class-indent)
    ("sig" . tuareg-sig-struct-indent)
    ("struct" . tuareg-sig-struct-indent)
    ("method" . tuareg-method-indent)
    ("object" . tuareg-begin-indent)
    ("begin" . tuareg-begin-indent)
    (".<" . tuareg-begin-indent)
    ("for" . tuareg-for-while-indent)
    ("while" . tuareg-for-while-indent)
    ("do" . tuareg-do-indent)
    ("val" . tuareg-val-indent)
    ("fun" . tuareg-fun-indent)
    ("if" . tuareg-if-then-else-indent)
    ("then" . tuareg-if-then-else-indent)
    ("else" . tuareg-if-then-else-indent)
    ("let" . tuareg-let-indent)
    ("match" . tuareg-match-indent)
    ("try" . tuareg-try-indent)

    ;; Case match keywords
    ("function" . tuareg-function-indent)
    ("with" . tuareg-with-indent)
    ("automaton" . tuareg-with-indent)
    ("present" . tuareg-with-indent)
    ("type" . tuareg-type-indent) ; sometimes, `type' acts like a case match

    ;; Assume default indentation for other keywords and operators
    )
  "Association list of indentation values based on governing keywords.")

(defconst tuareg-leading-kwop-alist
  '(("|" . tuareg-find-pipe-match)
    ("}" . tuareg-find-match)
    (">}" . tuareg-find-match)
    (">." . tuareg-find-match)
    (")" . tuareg-find-match)
    ("]" . tuareg-find-match)
    ("|]" . tuareg-find-match)
    (">]" . tuareg-find-match)
    ("end" . tuareg-find-match)
    ("done" . tuareg-find-done-match)
    ("unless" . tuareg-find-done-match)
    ("until" . tuareg-find-done-match)
    ("every" . tuareg-find-done-match)
    ("in" . tuareg-find-in-match)
    ("where" . tuareg-find-in-match)
    ("with" . tuareg-find-with-match)
    ("else" . tuareg-find-else-match)
    ("then" . tuareg-find-then-match)
    ("do" . tuareg-find-do-match)
    ("to" . tuareg-find-match)
    ("downto" . tuareg-find-match)
    ("and" . tuareg-find-and-match))
  "Association list used in Tuareg mode for skipping back over nested blocks.")

(defun tuareg-find-leading-kwop-match (kwop)
  (funcall (cdr (assoc kwop tuareg-leading-kwop-alist))))

(defconst tuareg-binding-regexp "\\(\\<and\\>\\|(*\\<let\\>\\)")

(defun tuareg-assoc-indent (kwop &optional look-for-let-or-and)
  "Return relative indentation of the keyword given in argument."
  (let ((ind (or (symbol-value (cdr (assoc kwop tuareg-keyword-alist)))
                 tuareg-default-indent))
        (looking-let-or-and (and look-for-let-or-and
                                 (looking-at tuareg-binding-regexp))))
    (if (string-match (tuareg-give-extra-unindent-regexp) kwop)
        (- (if (and tuareg-let-always-indent
                    looking-let-or-and (< ind tuareg-let-indent))
               tuareg-let-indent ind)
           tuareg-pipe-extra-unindent)
      ind)))

(defun tuareg-in-monadic-op-p (&optional pos)
  (unless pos (setq pos (point)))
  (and (char-equal ?> (char-before pos))
       (char-equal ?> (char-before (1- pos)))))

(defun tuareg-in-literal-p ()
  "Return non-nil if point is inside an OCaml literal."
  (eq (nth 3 (syntax-ppss)) 34))

(defun tuareg-in-comment-p ()
  "Return non-nil if point is inside or right before an OCaml comment."
  (or (nth 4 (syntax-ppss))
      (looking-at "[ \t]*(\\*")))

(defun tuareg-beginning-of-literal-or-comment ()
  "Skips to the beginning of the current literal or comment (or buffer)."
  (interactive)
  (goto-char (or (nth 8 (syntax-ppss)) (point))))

(defun tuareg-beginning-of-literal-or-comment-fast ()
  ;; FIXME: Rename this function, since it's not a faster version of
  ;; tuareg-beginning-of-literal-or-comment.
  (goto-char (or (nth 8 (syntax-ppss)) (point-min))))

(defconst tuareg-meaningful-word-regexp
  "[^ \t\n_[:alnum:]]\\|\\<\\(\\w\\|_\\)+\\>\\|\\*)")
(defun tuareg-find-meaningful-word ()
  "Look back for a word, skipping comments and blanks.
Returns the actual text of the word, if found."
  (let ((found nil) (kwop nil) (pt (point)))
    (while (and (not found)
                (re-search-backward tuareg-meaningful-word-regexp
                                    (point-min) t))
      (setq kwop (tuareg-match-string 0))
      (cond ((and (or (string= kwop "|") (string= kwop "=") (string= kwop ">"))
                  (tuareg-in-monadic-op-p))
             (backward-char 2)
             (setq kwop (concat ">>" kwop)))
            ((and (string= kwop ">") (char-equal ?- (char-before)))
             (backward-char)
             (setq kwop "->")))
      (when (= pt (point))
        (error "tuareg-find-meaningful-word: inf loop at %d, kwop=%s" pt kwop))
      (setq pt (point))
      (if kwop
          (if (tuareg-in-comment-p)
              (tuareg-beginning-of-literal-or-comment-fast)
            (setq found t))
        (setq found t)))
    (if found kwop (goto-char (point-min)) nil)))

(defun tuareg-make-find-kwop-regexp (kwop-regexp)
  "Make a custom indentation regexp."
  (concat (tuareg-give-find-kwop-regexp) "\\|" kwop-regexp))

;; Dynamic regexps (for language changes, see `tuareg-editing-ls3')
(defvar tuareg-find-comma-match-regexp nil)
(defvar tuareg-find-with-match-regexp nil)
(defvar tuareg-find-in-match-regexp nil)
(defvar tuareg-find-else-match-regexp nil)
(defvar tuareg-find-do-match-regexp nil)
(defvar tuareg-find-=-match-regexp nil)
(defvar tuareg-find-pipe-match-regexp nil)
(defvar tuareg-find-arrow-match-regexp nil)
(defvar tuareg-find-semicolon-match-regexp nil)
(defvar tuareg-find-phrase-indentation-regexp nil)
(defvar tuareg-find-phrase-indentation-break-regexp nil)
(defvar tuareg-find-phrase-indentation-class-regexp nil)
(defvar tuareg-compute-argument-indent-regexp nil)
(defvar tuareg-compute-normal-indent-regexp nil)
(defvar tuareg-find-module-regexp nil)
(defvar tuareg-find-pipe-bang-match-regexp nil)
(defvar tuareg-find-monadic-match-regexp nil)

;; Static regexps
(defconst tuareg-find-and-match-regexp
  (concat (tuareg-ro "do" "done" "else" "end" "in" "then" "downto"
                     "for" "while" "do" "if" "begin" "sig" "struct" "class"
                     "exception" "let" "in" "type" "val" "module")
          "\\|[][(){}]\\|\\*)"))
(defconst tuareg-find-phrase-beginning-regexp
  (concat (tuareg-ro "end" "type" "module" "sig" "struct" "class"
                     "exception" "open" "let")
          "\\|^#[ \t]*[a-z][_a-z]*\\>\\|;;"))
(defconst tuareg-find-phrase-beginning-and-regexp
  (concat "\\<\\(and\\)\\>\\|" tuareg-find-phrase-beginning-regexp))
(defconst tuareg-back-to-paren-or-indentation-regexp
  "[][(){}]\\|\\.<\\|>\\.\\|\\*)\\|^[ \t]*\\(.\\|\n\\)")

;; Specific regexps for module/class detection
(defconst tuareg-inside-module-or-class-opening
  (tuareg-ro "struct" "sig" "object"))
(defconst tuareg-inside-module-or-class-opening-full
  (concat tuareg-inside-module-or-class-opening "\\|"
          (tuareg-ro "module" "class")))
(defconst tuareg-inside-module-or-class-regexp
  (concat (tuareg-give-matching-keyword-regexp) "\\|"
          tuareg-inside-module-or-class-opening))

(defun tuareg-make-indentation-regexps ()
  "Initialisation of specific indentation regexp.
Gathered here for memoization and dynamic reconfiguration purposes."
  (setq
   tuareg-find-comma-match-regexp
    (tuareg-make-find-kwop-regexp
     (concat (tuareg-ro "and" "match" "begin" "else" "exception" "then" "try"
                        "with" "or" "fun" "function" "let" "do")
             "\\|->\\|[[{(]"))
   tuareg-find-with-match-regexp
    (tuareg-make-find-kwop-regexp
     (concat (tuareg-ro "match" "try" "module" "begin" "with" "type")
             "\\|[[{(]"))
   tuareg-find-in-match-regexp
;;    (tuareg-make-find-kwop-regexp (tuareg-ro "let" "open"))
    (tuareg-make-find-kwop-regexp (tuareg-ro "let"))
   tuareg-find-else-match-regexp
    (tuareg-make-find-kwop-regexp ";")
   tuareg-find-do-match-regexp
    (tuareg-make-find-kwop-regexp "->")
   tuareg-find-=-match-regexp
    (tuareg-make-find-kwop-regexp
     (concat (tuareg-ro "val" "let" "method" "module" "type" "class" "when"
                        "if" "in" "do")
             "\\|="))
   tuareg-find-pipe-match-regexp
    (tuareg-make-find-kwop-regexp (tuareg-give-match-pipe-kwop-regexp))
   tuareg-find-arrow-match-regexp
    (tuareg-make-find-kwop-regexp
     (concat (tuareg-ro "external" "type" "val" "method" "let" "with" "fun"
                        "function" "functor" "class")
             "\\|[|;]"))
   tuareg-find-semicolon-match-regexp
    (tuareg-make-find-kwop-regexp
     (concat ";" tuareg-no-more-code-this-line-regexp "\\|->\\|"
             (tuareg-ro "let" "method" "with" "try" "initializer")))
   tuareg-find-phrase-indentation-regexp
    (tuareg-make-find-kwop-regexp
     (concat tuareg-governing-phrase-regexp "\\|" (tuareg-ro "and" "every")))
   tuareg-find-phrase-indentation-break-regexp
    (concat tuareg-find-phrase-indentation-regexp "\\|;;")
   tuareg-find-phrase-indentation-class-regexp
    (concat (tuareg-give-matching-keyword-regexp) "\\|\\<class\\>")
   tuareg-compute-argument-indent-regexp
    (tuareg-make-find-kwop-regexp
     (concat (tuareg-give-keyword-regexp) "\\|="))
   tuareg-compute-normal-indent-regexp
    (concat tuareg-compute-argument-indent-regexp "\\|^.[ \t]*")
   tuareg-find-module-regexp
    (tuareg-make-find-kwop-regexp "\\<module\\>")
   tuareg-find-pipe-bang-match-regexp
    (concat tuareg-find-comma-match-regexp "\\|=")
   tuareg-find-monadic-match-regexp
    (concat tuareg-block-regexp "\\|\\([;=]\\)\\|\\(->\\)\\|"
            (tuareg-ro "val" "let" "method" "module" "type" "class" "when"
                       "if" "in" "do" "done" "end"))))

(defun tuareg-strip-trailing-whitespace (string)
  (if (string-match "[ \t]*\\'" string)
      (substring string 0 (match-beginning 0))
    string))

(defun tuareg-find-kwop-pos (kr do-not-skip-regexp may-terminate-early)
  "Look back for a keyword or operator matching KR (short for kwop regexp).
Skips blocks etc...

Ignore occurences inside literals and comments.
If found, return the actual text of the keyword or operator."
  (let ((found nil)
        (kwop nil) pos
        (kwop-regexp (if tuareg-support-metaocaml
                         (concat kr "\\|\\.<\\|>\\.")
                       kr)))
    (while (and (not found)
                (setq pos (re-search-backward kwop-regexp (point-min) t))
                (setq kwop (tuareg-strip-trailing-whitespace
                            ;; for trailing blanks after a semicolon
                            (tuareg-match-string 0))))
      (cond
       ((tuareg-in-literal-or-comment-p)
        (tuareg-beginning-of-literal-or-comment-fast))
       ((looking-at "[]})]")
        (tuareg-backward-up-list))
       ((tuareg-at-phrase-break-p)
        (setq found t))
       ((and do-not-skip-regexp (looking-at do-not-skip-regexp))
        (if (and (string= kwop "|") (char-equal ?| (preceding-char)))
            (backward-char)
          (setq found t)))
       ((looking-at (tuareg-give-matching-keyword-regexp))
        (let ((mkwop (tuareg-find-leading-kwop-match (tuareg-match-string 0))))
          (when (and may-terminate-early (string-match kwop-regexp mkwop))
            (setq found t))))
       (t
        (setq found t))))
    (if found (list kwop pos) (goto-char (point-min)) nil)))

(defun tuareg-find-kwop (kr &optional do-not-skip-regexp)
  (car (tuareg-find-kwop-pos kr do-not-skip-regexp nil)))

(defun tuareg-find-match ()
  (let ((kwop (tuareg-find-kwop (tuareg-give-find-kwop-regexp))))
    (when (string= kwop "then")
      (tuareg-find-then-match)
      (tuareg-find-match))
    kwop))

(defun tuareg-find-comma-match ()
  (car (tuareg-find-kwop-pos tuareg-find-comma-match-regexp nil t)))

(defun tuareg-find-pipe-bang-match ()
  (destructuring-bind (kwop pos)
      (tuareg-find-kwop-pos tuareg-find-pipe-bang-match-regexp nil t)
    ;; when matched "if ... then", kwop is "then" but point is at "if"
    (goto-char pos)   ; go back to kwop for tuareg-indent-to-code
    (if (looking-at "\\[|") "[|" kwop)))

(defun tuareg-monadic-operator-p (word)
  (and (or (string= ">>=" word) (string= ">>|" word) (string= ">>>" word))
       word))

(defun tuareg-ignorable-arrow-p ()
  (save-excursion
    (or (tuareg-monadic-operator-p (tuareg-find-arrow-match))
        (looking-at (tuareg-give-extra-unindent-regexp)))))

(defun tuareg-find-monadic-match ()
  (let (kwop)
    (while (or (null kwop)
               (and (string= kwop "=") (tuareg-in-monadic-op-p)))
      (when kwop (tuareg-backward-char 2))
      (setq kwop (tuareg-find-kwop tuareg-find-monadic-match-regexp))
      (when (and (string= kwop "->") (tuareg-ignorable-arrow-p))
        (setq kwop nil)))
    kwop))

(defun tuareg-find-with-match ()
  (tuareg-find-kwop tuareg-find-with-match-regexp))

(defun tuareg-find-in-match ()
  (let ((kwop (tuareg-find-kwop tuareg-find-in-match-regexp "\\<and\\>")))
    (cond
     ((string= kwop "and")
      (tuareg-find-in-match))
     (t
      kwop))))

(defconst tuareg-find-arrow-match-regexp-ls3
  (concat tuareg-find-arrow-match-regexp tuareg-ls3-extras))
(defun tuareg-give-find-arrow-match-regexp ()
  (if (tuareg-editing-ls3)
      tuareg-find-arrow-match-regexp-ls3
    tuareg-find-arrow-match-regexp))

(defconst tuareg-find-then-match-skip-regexp-ls3
  (regexp-opt '("->" "unless" "until") t))
(defconst tuareg-find-then-match-regexp-ls3
  (tuareg-make-find-kwop-regexp tuareg-find-then-match-skip-regexp-ls3))
(defconst tuareg-find-then-match-regexp
  (tuareg-make-find-kwop-regexp "\\(->\\)"))
(defun tuareg-find-then-kwop ()
  (let ((ls3 (tuareg-editing-ls3)))
    (tuareg-find-kwop
     (if ls3 tuareg-find-then-match-regexp-ls3 tuareg-find-then-match-regexp)
     (if ls3 tuareg-find-then-match-regexp-ls3 "\\(->\\)"))))
(defun tuareg-find-then-match ()
  (let ((kwop (tuareg-find-then-kwop)))
    (cond ((string= kwop "if")
           (let ((back (point)))
             (tuareg-back-to-paren-or-indentation)
             (if (looking-at "else[ \t]*\\((\\*.*\\*)\\)*[ \t]*if")
                 "else if"
               (goto-char back)
               kwop)))
          (t kwop))))

(defun tuareg-find-then-else-match ()
  (let ((kwop (tuareg-find-then-kwop)))
    (cond
     ((string= kwop "if")
      (let ((pos (point)))
        (if (and (not (tuareg-in-indentation-p))
                 (string= "else" (tuareg-find-meaningful-word)))
            "else"
          (goto-char pos)
          kwop)))
     (t
      kwop))))

(defun tuareg-find-else-match ()
  (let ((kwop (tuareg-find-kwop tuareg-find-else-match-regexp
                                "\\<then\\>")))
    (cond
     ((string= kwop "then")
      (tuareg-find-then-else-match))
     ((string= kwop ";")
      (tuareg-find-semicolon-match)
      (tuareg-find-else-match)))))

(defconst tuareg-do-match-stop-regexp (tuareg-ro "downto"))
(defun tuareg-find-do-match ()
  (let ((kwop (tuareg-find-kwop tuareg-find-do-match-regexp
                                tuareg-do-match-stop-regexp)))
    (if (or (string= kwop "to") (string= kwop "downto"))
        (tuareg-find-match)
      kwop)))

(defconst tuareg-done-match-stop-regexp (tuareg-ro "and" "do"))
(defun tuareg-find-done-match ()
  (let ((kwop (tuareg-find-kwop (tuareg-give-find-kwop-regexp)
                                tuareg-done-match-stop-regexp)))
    (cond
     ((string= kwop "and")
      (tuareg-find-and-match))
     ((string= kwop "done")
      (tuareg-find-done-match)
      (tuareg-find-done-match))
     ((string= kwop "do")
      (tuareg-find-do-match))
     (t
      kwop))))

(defconst tuareg-and-stop-regexp-ls3 (tuareg-ro "and" "do" "where"))
(defun tuareg-give-and-stop-regexp ()
  (if (tuareg-editing-ls3)
      tuareg-and-stop-regexp-ls3
    "\\<and\\>"))

(defun tuareg-find-and-match ()
  (let* ((kwop (tuareg-find-kwop
                tuareg-find-and-match-regexp
                (tuareg-give-and-stop-regexp)))
         (old-point (point)))
    (cond
     ((or (string= kwop "type") (string= kwop "module"))
      (let ((kwop2 (tuareg-find-meaningful-word)))
        (cond ((string= kwop2 "with")
               kwop2)
              ((string= kwop2 "and")
               (tuareg-find-and-match))
              ((and (string= kwop "module")
                    (string= kwop2 "let"))
               kwop2)
              (t (goto-char old-point) kwop))))
     (t kwop))))

(defconst tuareg-=-stop-regexp-ls3
  (concat (tuareg-ro "and" "do" "in" "where") "\\|="))
(defconst tuareg-=-stop-regexp (concat (tuareg-ro "and" "in") "\\|="))
(defun tuareg-give-=-stop-regexp ()
  (if (tuareg-editing-ls3)
      tuareg-=-stop-regexp-ls3
    tuareg-=-stop-regexp))

(defun tuareg-false-=-p ()
  "Is the underlying `=' the first/second letter of an operator?"
  (or (memq (preceding-char) '(?: ?> ?< ?=))
      (char-equal ?= (char-after (1+ (point))))))

(defun tuareg-at-phrase-break-p ()
  "Is the underlying `;' a phrase break?"
  (and (char-equal ?\; (following-char))
       (or (and (not (eobp))
                (char-equal ?\; (char-after (1+ (point)))))
           (char-equal ?\; (preceding-char)))))

(defun tuareg-find-=-match ()
  (let ((kwop (tuareg-find-kwop
               tuareg-find-=-match-regexp
               (tuareg-give-=-stop-regexp))))
    (cond
     ((string= kwop "and")
      (tuareg-find-and-match))
     ((and (string= kwop "=")
           (not (tuareg-false-=-p)))
      (while (and (string= kwop "=")
                  (not (tuareg-false-=-p)))
        (setq kwop (tuareg-find-=-match)))
      kwop)
     (t kwop))))

(defconst tuareg-if-when-regexp (tuareg-ro "if" "when"))
(defun tuareg-if-when-= ()
  (save-excursion
    (tuareg-find-=-match)
    (looking-at tuareg-if-when-regexp)))

(defconst tuareg-captive-regexp
  (tuareg-ro "let" "if" "when" "module" "type" "class"))
(defun tuareg-captive-= ()
  (save-excursion
    (tuareg-find-=-match)
    (looking-at tuareg-captive-regexp)))

(defconst tuareg-pipe-stop-regexp
  (concat (tuareg-ro "and" "with") "\\||"))
(defconst tuareg-pipe-stop-regexp-ls3
  (concat tuareg-pipe-stop-regexp tuareg-ls3-extras))
(defun tuareg-give-pipe-stop-regexp ()
  (if (tuareg-editing-ls3)
      tuareg-pipe-stop-regexp-ls3
    tuareg-pipe-stop-regexp))

(defun tuareg-find-pipe-match ()
  (let ((kwop
         (let ((k (tuareg-find-kwop
                   tuareg-find-pipe-match-regexp
                   (tuareg-give-pipe-stop-regexp))))
           (if (and k (string-match "|[^!]" k))
               "|" k)))
        (old-point (point)))
    (cond
     ((string= kwop "and")
      (setq old-point (point))
      (setq kwop (tuareg-find-and-match))
      (if (not (string= kwop "do"))
          (goto-char old-point)
        (setq kwop (tuareg-find-arrow-match)))
      kwop)
     ((and (string= kwop "|")
           (looking-at "|[^|]")
           (tuareg-in-indentation-p))
      kwop)
     ((string= kwop "|") (tuareg-find-pipe-match))
     ((and (string= kwop "=")
           (or (looking-at (tuareg-no-code-after "="))
               (tuareg-false-=-p)
               (not (string= (save-excursion (tuareg-find-=-match))
                             "type"))))
      (tuareg-find-pipe-match))
     (t
      kwop))))

(defun tuareg-find-arrow-match ()
  (let ((kwop (tuareg-find-kwop (tuareg-give-find-arrow-match-regexp)
                                "\\<with\\>")))
    (cond
     ((string= kwop "|")
      (if (tuareg-in-indentation-p)
          kwop
        (progn (forward-char -1) (tuareg-find-arrow-match))))
     ((string= kwop "fun")
      (let ((pos (point)))
        (or (tuareg-monadic-operator-p (tuareg-find-meaningful-word))
            (progn (goto-char pos) kwop))))
     ((not (string= kwop ":"))
      kwop)
     ;; If we get this far, we know we're looking at a colon.
     ((or (char-equal (char-before) ?:)
          (char-equal (char-after (1+ (point))) ?:)
          (char-equal (char-after (1+ (point))) ?>))
      (tuareg-find-arrow-match))
     ;; Patch by T. Freeman
     (t
      (let ((oldpoint (point))
            (match (tuareg-find-arrow-match)))
        (if (looking-at ":")
            match
          (progn
            ;; Go back to where we were before the recursive call.
            (goto-char oldpoint)
            kwop)))))))

(defconst tuareg-semicolon-match-stop-regexp
  (tuareg-ro "and" "do" "end" "in" "with"))
(defconst tuareg-no-code-after-paren-regexp
  (tuareg-no-code-after "[[{(][|<]?"))
(defun tuareg-semicolon-indent-kwop-point (&optional leading-semi-colon)
  ;; return (kwop kwop-point indentation)
  (let ((kwop (tuareg-find-kwop tuareg-find-semicolon-match-regexp
                                tuareg-semicolon-match-stop-regexp))
        (point (point)))
    ;; We don't need to find the keyword matching `and' since we know
    ;; it's `let'!
    (list
     (cond
       ((string= kwop ";")
        (forward-line 1)
        (while (or (tuareg-in-comment-p)
                   (looking-at tuareg-no-code-this-line-regexp))
          (forward-line 1))
        (back-to-indentation)
        (current-column))
       ((and leading-semi-colon
             (looking-at "\\((\\|\\[[<|]?\\|{<?\\)[ \t]*[^ \t\n]")
             (not (looking-at tuareg-no-code-after-paren-regexp)))
        (current-column))
       ;; ((looking-at (tuareg-no-code-after "\\((\\|\\[[<|]?\\|{<?\\)"))
       ;;  (+ (current-column) tuareg-default-indent))
       ((looking-at (tuareg-no-code-after
                     "\\<begin\\>\\|\\((\\|\\[[<|]?\\|{<?\\)"))
        (if (tuareg-in-indentation-p)
            (+ (current-column) tuareg-default-indent)
          (tuareg-indent-from-previous-kwop)))
       ((looking-at "\\(\\.<\\|(\\|\\[[<|]?\\|{<?\\)") ; paren with subsequent text
        (tuareg-search-forward-paren)
        (current-column))
       ((string= kwop "method")
        (+ (tuareg-paren-or-indentation-column) tuareg-method-indent))
       ((string= kwop "->")
        (if (save-excursion
              (tuareg-find-arrow-match)
              (or (looking-at "\\<fun\\>\\||")
                  (looking-at (tuareg-give-extra-unindent-regexp))))
            (tuareg-paren-or-indentation-indent)
          (tuareg-find-semicolon-match)))
       ((string= kwop "end")
        (tuareg-find-match)
        (tuareg-find-semicolon-match))
       ((string= kwop "in")
        (tuareg-find-in-match)
        (+ (current-column) tuareg-in-indent))
       ((string= kwop "where")
        (tuareg-find-in-match)
        (+ (tuareg-paren-or-indentation-column) tuareg-in-indent))
       ((string= kwop "let")
        (+ (current-column) tuareg-let-indent))
       ((string= kwop "try")
        (forward-char 3) (skip-syntax-forward " ")
        (current-column))
       (t (tuareg-paren-or-indentation-indent)))
     kwop point)))

(defun tuareg-find-semicolon-match (&optional leading-semi-colon)
  (car (tuareg-semicolon-indent-kwop-point leading-semi-colon)))

(defconst tuareg-phrase-regexp-1 (tuareg-ro "module" "type"))
(defconst tuareg-phrase-regexp-2 (tuareg-ro "and" "let" "module" "with"))
(defconst tuareg-phrase-regexp-3
  (tuareg-ro "and" "end" "every" "in" "with"))
(defun tuareg-find-phrase-indentation (&optional phrase-break)
  (if (and (looking-at tuareg-phrase-regexp-1) (> (point) (point-min))
           (save-excursion
             (tuareg-find-meaningful-word)
             (looking-at tuareg-phrase-regexp-2)))
      (progn
        (tuareg-find-meaningful-word)
        (+ (current-column) tuareg-default-indent))
    (let ((looking-at-and (looking-at "\\<and\\>"))
          (kwop (tuareg-find-kwop
                 (if phrase-break
                     tuareg-find-phrase-indentation-break-regexp
                   tuareg-find-phrase-indentation-regexp)
                 tuareg-phrase-regexp-3))
          (tmpkwop nil) (curr nil))
      (tuareg-reset-and-kwop kwop)
      (cond ((not kwop) (current-column))
            ((string= kwop "every")
             (if (tuareg-editing-ls3)
                 (progn
                   (tuareg-find-done-match)
                   (tuareg-find-phrase-indentation phrase-break)
                   (current-column))
               (tuareg-find-phrase-indentation phrase-break)))
            ((string= kwop "end")
             (if (not (save-excursion
                        (setq tmpkwop (tuareg-find-match))
                        (setq curr (point))
                        (string= tmpkwop "object")))
                 (progn
                   (tuareg-find-match)
                   (tuareg-find-phrase-indentation phrase-break))
               (tuareg-find-kwop tuareg-find-phrase-indentation-class-regexp)
               (current-column)))
            ((and (string= kwop "with")
                  (not (save-excursion
                         (setq tmpkwop (tuareg-find-with-match))
                         (setq curr (point))
                         (string= tmpkwop "module"))))
             (goto-char curr)
             (tuareg-find-phrase-indentation phrase-break))
            ((and (string= kwop "in")
                  (not (save-excursion
                         (setq tmpkwop (tuareg-find-in-match))
                         (tuareg-reset-and-kwop tmpkwop)
                         (setq curr (point))
                         (and (string= tmpkwop "let")
                              (not (tuareg-looking-at-internal-let))))))
             (goto-char curr)
             (tuareg-find-phrase-indentation phrase-break))
            ((tuareg-at-phrase-break-p)
             (end-of-line)
             (tuareg-skip-blank-and-comments)
             (current-column))
            ((string= kwop "let")
             (if (tuareg-looking-at-internal-let)
                 (tuareg-find-phrase-indentation phrase-break)
                 (current-column)))
            ((string= kwop "with")
             (current-column))
            ((string= kwop "end")
             (current-column))
            ((or (string= kwop "in") (string= kwop "where"))
             (tuareg-find-in-match)
             (current-column))
            ((string= kwop "class")
             (tuareg-paren-or-indentation-column))
            ((looking-at tuareg-inside-module-or-class-opening)
             (+ (tuareg-paren-or-indentation-column)
                (tuareg-assoc-indent kwop)))
            ((or (string= kwop "type") (string= kwop "module"))
             (if (or (tuareg-looking-at-false-type)
                     (tuareg-looking-at-false-module))
                 (if looking-at-and
                     (current-column)
                   (if (string= "and" (tuareg-find-meaningful-word))
                       (progn
                         (tuareg-find-and-match)
                         (tuareg-find-phrase-indentation phrase-break))
                     (tuareg-find-phrase-indentation phrase-break)))
               (current-column)))
            ((looking-at "\\(\\.<\\|(\\|\\[[<|]?\\|{<?\\)[ \t]*[^ \t\n]")
             (tuareg-search-forward-paren)
             (current-column))
            ((string= kwop "open") ; compatible with Caml Light `#open'
             (tuareg-paren-or-indentation-column))
            (t (current-column))))))

(defconst tuareg-paren-or-indentation-stop-regexp
  (tuareg-ro "and" "do" "in" "with"))
(defun tuareg-back-to-paren-or-indentation ()
  "Search backwards for the first open paren in line, or skip to indentation.
Returns t iff skipped to indentation."
  (if (or (bolp) (tuareg-in-indentation-p))
      (progn (back-to-indentation) t)
    (let ((kwop (tuareg-find-kwop
                 tuareg-back-to-paren-or-indentation-regexp
                 tuareg-paren-or-indentation-stop-regexp))
          (retval))
      (when (string= kwop "with")
        (let ((with-point (point)))
          (setq kwop (tuareg-find-with-match))
          (if (or (string= kwop "match") (string= kwop "try"))
              (tuareg-find-kwop tuareg-back-to-paren-or-indentation-regexp
                                "\\<and\\>")
            (setq kwop "with") (goto-char with-point))))
      (setq retval
            (cond
             ((string= kwop "with") nil)
             ((or (string= kwop "in") (string= kwop "do"))
              (tuareg-in-indentation-p))
             ;; ((looking-at "[[{(]") (tuareg-search-forward-paren) nil)
             ;; ((looking-at "\\.<")
             ;;  (if tuareg-support-metaocaml
             ;;      (progn
             ;;        (tuareg-search-forward-paren) nil)
             ;;    (tuareg-back-to-paren-or-indentation)))
             (t (back-to-indentation) t)))
      (cond
       ;; ((looking-at "|[^|]")
       ;;  (re-search-forward "|[^|][ \t]*") nil)
       ((or (string= kwop "in") (string= kwop "do"))
        (tuareg-find-in-match)
        (tuareg-back-to-paren-or-indentation)
        (if (looking-at "\\<\\(let\\|and\\)\\>")
            (forward-char tuareg-in-indent)) nil)
       (t retval)))))

(defun tuareg-paren-or-indentation-column ()
  (tuareg-back-to-paren-or-indentation)
  (current-column))

(defun tuareg-paren-or-indentation-indent ()
  (+ (tuareg-paren-or-indentation-column) tuareg-default-indent))

(defun tuareg-search-forward-paren ()
  (re-search-forward "\\(\\.<\\|(\\|\\[[<|]?\\|{<?\\)[ \t]*"))

(defun tuareg-add-default-indent (leading-operator)
  (if leading-operator 0 tuareg-default-indent))

(defconst tuareg-internal-let-regexp
  (concat "[[({;=]\\|"
           (tuareg-ro "begin" "open" "if" "in" "do" "try" "then" "else"
                      "match" "while" "when")))
(defun tuareg-looking-at-internal-let ()
  (save-excursion
    (tuareg-find-meaningful-word)
    (and (not (tuareg-at-phrase-break-p))
         (not (and tuareg-support-metaocaml
                   (char-equal ?. (following-char))
                   (char-equal ?> (preceding-char))))
         (or (looking-at tuareg-internal-let-regexp)
             (looking-at tuareg-operator-regexp)))))

(defconst tuareg-false-module-regexp (tuareg-ro "and" "let" "with"))
(defun tuareg-looking-at-false-module ()
  (save-excursion
    (tuareg-find-meaningful-word)
    (looking-at tuareg-false-module-regexp)))

(defun tuareg-looking-at-false-sig-struct ()
  (save-excursion
    (tuareg-find-module)
    (looking-at "\\<module\\>\\|(")))

(defconst tuareg-false-type-regexp (tuareg-ro "and" "class" "module" "with"))
(defun tuareg-looking-at-false-type ()
  (save-excursion
    (tuareg-find-meaningful-word)
    (looking-at tuareg-false-type-regexp)))

(defun tuareg-looking-at-in-let ()
  (save-excursion
    (string= (tuareg-find-meaningful-word) "in")))

(defun tuareg-find-module ()
  (tuareg-find-kwop tuareg-find-module-regexp))

(defun tuareg-indent-from-previous-kwop ()
  (let* ((start-pos (point))
         (kwop (tuareg-find-argument-kwop-non-blank t))
         (captive= (and (string= kwop "=") (tuareg-captive-=)))
         (kwop-pos (point)))
    (forward-char (length kwop))
    (tuareg-skip-blank-and-comments)
    (cond ((or (not captive=)
               (/= (point) start-pos)) ; code between paren and kwop
           (goto-char start-pos)
           (tuareg-paren-or-indentation-indent))
          (t
           (goto-char kwop-pos)
           (when (string= kwop "=")
             (setq kwop (tuareg-find-=-match)))
           (+ tuareg-default-indent
              (if (assoc kwop tuareg-leading-kwop-alist)
                  (tuareg-compute-kwop-indent kwop)
                  (current-column)))))))

(defun tuareg-find-colon-typespec (start-pos)
  (let* ((old-pos (point))
         (new-pos (search-forward ":" start-pos t)))
    (when new-pos
      (backward-char 1)
      (skip-syntax-backward " ")
      (skip-syntax-backward "w")
      (skip-syntax-backward " ")
      (let ((char (char-before)))
        (cond ((or (char-equal char ??) (char-equal char ?~))
               (goto-char old-pos) nil)
              (t (goto-char new-pos) t))))))

(defun tuareg-indent-from-paren (leading-operator start-pos)
  (cond
   ((looking-at (tuareg-no-code-after "\\(\\(\\.<\\|(\\|\\[[<|]?\\|{<?\\)\\)"))
    (cond ((tuareg-in-indentation-p)
           (+ tuareg-default-indent
              (current-column)))
          ((tuareg-find-colon-typespec start-pos)
           (if (looking-at tuareg-no-code-this-line-regexp)
               (tuareg-paren-or-indentation-indent)
             (tuareg-skip-blank-and-comments)
             (current-column)))
          (t (tuareg-indent-from-previous-kwop))))
   ((looking-at "\\<begin\\>")
    (tuareg-paren-or-indentation-indent))
   ((looking-at "([ \t]*\\(\\w\\)")
    (goto-char (match-beginning 1))
    (current-column))
   (t
    (+ (tuareg-add-default-indent leading-operator)
       (current-column)))))

(defun tuareg-skip-to-next-form (old-point)
  (while (and (not (looking-at tuareg-no-more-code-this-line-regexp))
              (< (point) old-point)) ; do not go beyond old-point
    (forward-sexp 1))
  (tuareg-skip-blank-and-comments)
  (tuareg-back-to-paren-or-indentation))

(defun tuareg-find-argument-kwop (leading-operator)
  (tuareg-find-kwop (if leading-operator
                      tuareg-compute-argument-indent-regexp
                      tuareg-compute-normal-indent-regexp)
                    (tuareg-give-keyword-regexp)))

(defun tuareg-find-argument-kwop-clean (leading-operator)
  (let (kwop)
    (while (or (progn (setq kwop (tuareg-find-argument-kwop leading-operator))
                      (tuareg-reset-and-kwop kwop)
                      nil)
               (and (string= kwop "=") (tuareg-false-=-p))
               (and (looking-at tuareg-no-code-this-line-regexp)
                    (not (= (point) (point-min))))))
    kwop))

(defun tuareg-find-argument-kwop-non-blank (leading-operator)
  (let ((kwop "") (point (1+ (point))))
    (while (and (> point (point)) (string= "" kwop))
      (setq point (point)
            kwop (tuareg-find-argument-kwop-clean leading-operator)))
    kwop))

(defun tuareg-compute-argument-indent (leading-operator)
  (let* ((old-point (line-beginning-position))
         (kwop (tuareg-find-argument-kwop-non-blank leading-operator))
         (match-end-point (+ (point) (length kwop)))) ; match-end is invalid!
    (cond
     ((and (string= kwop "->")
           (not (looking-at (tuareg-no-code-after "->"))))
      (let (matching-kwop matching-pos)
        (save-excursion
          (setq matching-kwop (tuareg-find-arrow-match))
          (setq matching-pos (point)))
        (cond
         ((string= matching-kwop ":")
          (goto-char matching-pos)
          (tuareg-find-arrow-match) ; matching `val' or `let'
          (+ (current-column) tuareg-val-indent))
         ((or (string= matching-kwop "val") (string= matching-kwop "let"))
          (+ (current-column) tuareg-val-indent))
         ((string= matching-kwop "|")
          (goto-char matching-pos)
          (+ (tuareg-add-default-indent leading-operator)
             (current-column)
             (- tuareg-pipe-extra-unindent)
             tuareg-match-clause-indent
             tuareg-default-indent))
         (t
          (+ (tuareg-paren-or-indentation-column)
             (tuareg-add-default-indent leading-operator))))))
     ((string= kwop "fun")
      (+ (tuareg-paren-or-indentation-column)
         (tuareg-add-default-indent leading-operator)
         (tuareg-assoc-indent kwop)))
     ((<= old-point (point))
      (+ (tuareg-add-default-indent leading-operator)
         (current-column)))
     (t
      (goto-char match-end-point) ; skip kwop == (forward-char (length kwop))
      (tuareg-skip-to-next-form old-point)
      (+ (tuareg-add-default-indent
          (if (save-excursion (goto-char match-end-point)
                              (looking-at tuareg-no-more-code-this-line-regexp))
              (or leading-operator (string= kwop "{")
                  (looking-at (tuareg-no-code-after "[[:upper:]].*\\.")))
            (not (looking-at tuareg-operator-regexp))))
         (current-column))))))

(defun tuareg-compute-arrow-indent ()
  (let (kwop pos)
    (save-excursion (setq kwop (tuareg-find-arrow-match) pos (point)))
    (cond ((string= kwop "|")
           (tuareg-find-arrow-match)
           (+ (current-column)
              tuareg-default-indent
              tuareg-match-clause-indent))
          ((or (string= kwop "val")
               (string= kwop "let"))
           (goto-char pos)
           (+ (current-column) tuareg-val-indent))
          ((string= kwop "type")
           (goto-char pos)
           (+ (current-column) tuareg-type-indent
              tuareg-default-indent))
          ((string= kwop "(")
           (goto-char pos)
           (tuareg-indent-after-next-char))
          ((or (string= kwop "{")
               (string= kwop ";"))
           (if (and (looking-at "->")
                    (search-backward ":" pos t))
               (tuareg-indent-after-next-char)
             (tuareg-back-to-paren-or-indentation)
             (current-column)))
          ((tuareg-monadic-operator-p kwop)
           ;; find the last ">>=" or ">>>"
           ;; (goto-char pos)
           ;; (let ((back (point)))
           ;;   (while (tuareg-monadic-operator-p (tuareg-find-arrow-match))
           ;;     (setq back (point)))
           ;;   (goto-char back))
           ;; (if (not (re-search-backward
           ;;           (concat "(\\|" (tuareg-give-keyword-regexp))
           ;;           (point-min) t))
           ;;     0
           ;;   (goto-char (match-end 0))
           ;;   (tuareg-skip-blank-and-comments)
           ;;   (tuareg-compute-indent))

           ;; this is not perfect, in particular, inside match.
           ;; (see example in sample.ml)
           ;; the problem is that we cannot skip an expression backwards.
           ;; workaround: wrap code in parens
           (destructuring-bind (indent kwop _point)
               (tuareg-semicolon-indent-kwop-point)
             (- indent
                (if (string= kwop "in")
                    tuareg-in-indent 0))))
          (t (tuareg-paren-or-indentation-indent)))))

(defun tuareg-compute-keyword-indent (kwop leading-operator start-pos)
  (cond ((string= kwop ";")
         (if (looking-at (tuareg-no-code-after ";"))
             (let* ((pos (point)) (indent (tuareg-find-semicolon-match)))
               (if (looking-at tuareg-phrase-regexp-1)
                   (progn
                     (goto-char start-pos)
                     (if (search-backward ":" pos t)
                         (tuareg-indent-after-next-char)
                       indent))
                 indent))
           (tuareg-paren-or-indentation-indent)))
        ((string= kwop ",")
         (if (looking-at (tuareg-no-code-after ","))
             (let ((mkwop (tuareg-find-comma-match)))
               (cond ((or (string= mkwop "[")
                          (string= mkwop "{")
                          (string= mkwop "("))
                      (forward-char 1) (skip-syntax-forward " ")
                      (current-column))
                     ((looking-at "[[{(]\\|\\.<")
                      (tuareg-indent-from-paren t start-pos))
                     ((or (and (looking-at "[<|]")
                               (char-equal ?\[ (preceding-char)))
                          (and (looking-at "<")
                               (char-equal ?\{ (preceding-char))))
                      (tuareg-backward-char)
                      (tuareg-indent-from-paren t start-pos))
                     ((and (looking-at "\\<let\\>") (string= mkwop "in"))
                      (+ (current-column) tuareg-in-indent))
                     (t (+ (tuareg-paren-or-indentation-column)
                           (tuareg-assoc-indent mkwop)))))
           (tuareg-paren-or-indentation-indent)))
        ((looking-at "\\<begin\\>\\|->")
         (if (looking-at (tuareg-no-code-after "\\(\\<begin\\>\\|->\\)"))
             (tuareg-indent-from-paren leading-operator start-pos)
           (+ tuareg-default-indent
              (tuareg-indent-from-paren leading-operator start-pos))))
        ((or (string= kwop "let") (string= kwop "and"))
         (tuareg-back-to-paren-or-indentation)
         (+ (tuareg-paren-or-indentation-indent)
            (tuareg-assoc-indent kwop t)))
        ((string= kwop "with")
         (if (save-excursion
               (let ((tmpkwop (tuareg-find-with-match)))
                 (or (string= tmpkwop "module")
                     (string= tmpkwop "{"))))
             (tuareg-paren-or-indentation-indent)
           (+ (tuareg-paren-or-indentation-column)
              (* 2 tuareg-default-indent) ; assume a missing first "|"
              (tuareg-assoc-indent kwop t))))
        ((string-match "\\<\\(fun\\|of\\)\\>" kwop)
         (+ (tuareg-paren-or-indentation-column)
            (tuareg-add-default-indent leading-operator)
            (tuareg-assoc-indent kwop t)))
        ((string-match (tuareg-give-extra-unindent-regexp) kwop)
         (+ (tuareg-paren-or-indentation-column)
            (tuareg-assoc-indent kwop t)))
        ((string= kwop "in")
         (when (looking-at (tuareg-no-code-after "\\<in\\>"))
           (tuareg-find-in-match))
         (+ (current-column)
            tuareg-in-indent))
        ((string-match (tuareg-give-matching-kwop-regexp) kwop)
         (tuareg-find-leading-kwop-match kwop)
         (if (tuareg-in-indentation-p)
             (+ (current-column)
                (tuareg-assoc-indent kwop t))
           (tuareg-back-to-paren-or-indentation)
           (+ (tuareg-paren-or-indentation-indent)
              (tuareg-assoc-indent kwop t))))
        ((string= kwop "try")
         (forward-char 3)
         (if (looking-at tuareg-no-more-code-this-line-regexp)
             (+ (current-column) -3 tuareg-default-indent)
           (skip-syntax-forward " ")
           (+ (current-column) tuareg-default-indent)))
        (t (+ (if (tuareg-in-indentation-p)
                  (current-column)
                (tuareg-paren-or-indentation-indent))
              (tuareg-assoc-indent kwop t)))))

(defconst tuareg-=-indent-regexp-1
  (tuareg-ro "val" "let" "method" "module" "class" "when" "for" "if" "do"))

(defun tuareg-compute-=-indent (start-pos)
  (let ((current-column-module-type nil) (kwop1 (tuareg-find-=-match))
        (next-pos (point)))
    (+ (save-excursion
         (tuareg-reset-and-kwop kwop1)
         (cond ((string= kwop1 "type")
                (tuareg-find-meaningful-word)
                (cond ((looking-at "\\<module\\>")
                       (setq current-column-module-type (current-column))
                       tuareg-default-indent)
                      ((looking-at "\\<\\(with\\|and\\)\\>")
                       (tuareg-find-with-match)
                       (setq current-column-module-type (current-column))
                       tuareg-default-indent)
                      (t (goto-char start-pos)
                         (beginning-of-line)
                         ;; A first sum constructor without a preceding `|'
                         ;; needs extra indentation to be aligned with the other
                         ;; constructors.
                         (+ (if (looking-at "[ \t]*[A-Z]") 2 0)
                            tuareg-type-indent))))
               ((looking-at tuareg-=-indent-regexp-1)
                (let ((matched-string (tuareg-match-string 0)))
                  (setq current-column-module-type (current-column))
                  (tuareg-assoc-indent matched-string)))
               ((looking-at "\\<object\\>")
                (tuareg-back-to-paren-or-indentation)
                (setq current-column-module-type (current-column))
                (+ (tuareg-assoc-indent "object")
                   tuareg-default-indent))
               ((looking-at tuareg-no-code-after-paren-regexp)
                (setq current-column-module-type
                      (tuareg-indent-from-paren nil next-pos))
                tuareg-default-indent)
               (t (setq current-column-module-type
                        (tuareg-paren-or-indentation-indent))
                  tuareg-default-indent)))
       (or current-column-module-type
           (current-column)))))

(defun tuareg-indent-after-next-char ()
  (forward-char 1)
  (tuareg-skip-blank-and-comments)
  (current-column))

(defun tuareg-compute-normal-indent ()
  (let ((leading-operator (looking-at tuareg-operator-regexp)))
    (beginning-of-line)
    (save-excursion
      (let ((start-pos (point))
            (kwop (tuareg-find-argument-kwop-clean leading-operator)))
        (cond
          ((not kwop) (current-column))
          ((tuareg-at-phrase-break-p)
           (tuareg-find-phrase-indentation t))
          ((and (string= kwop "|") (not (char-equal ?\[ (preceding-char))))
           (tuareg-backward-char)
           (+ (tuareg-paren-or-indentation-indent)
              (tuareg-add-default-indent leading-operator)))
          ((or (looking-at "[[{(]")
               (and (looking-at "[<|]")
                    (char-equal ?\[ (preceding-char))
                    (progn (tuareg-backward-char) t))
               (and (looking-at "<")
                    (char-equal ?\{ (preceding-char))
                    (progn (tuareg-backward-char) t)))
           (cond ((looking-at "{ *[A-Z]")
                  (forward-char 1) (skip-syntax-forward " ")
                  (current-column))
                 ((looking-at (tuareg-no-code-after "[[{(][<|]?"))
                  (tuareg-indent-from-paren leading-operator start-pos))
                 ((and leading-operator (string= kwop "("))
                  (tuareg-indent-after-next-char))
                 (t (+ tuareg-default-indent
                       (tuareg-indent-from-paren leading-operator
                                                 start-pos)))))
          ((looking-at "\\.<")
           (if (looking-at (tuareg-no-code-after "\\.<"))
               (tuareg-indent-from-paren leading-operator start-pos)
             (+ tuareg-default-indent
                (tuareg-indent-from-paren leading-operator start-pos))))
          ((looking-at "->")
           (tuareg-compute-arrow-indent))
          ((looking-at (tuareg-give-keyword-regexp))
           (tuareg-compute-keyword-indent kwop leading-operator start-pos))
          ((and (string= kwop "=") (not (tuareg-false-=-p))
                (or (null leading-operator)
                    ;; defining "=", not testing for equality
                    (string-match tuareg-definitions-regexp
                                  (save-excursion
                                    (tuareg-find-argument-kwop-clean t)))))
           (tuareg-compute-=-indent start-pos))
          (nil 0)
          (t (tuareg-compute-argument-indent leading-operator)))))))

(defun tuareg-compute-pipe-indent (matching-kwop old-point)
  (cond
    ((or (string= matching-kwop "|")
         (string= matching-kwop "["))
     (tuareg-back-to-paren-or-indentation)
     (current-column))
    ((and (string= matching-kwop "=")
          (not (tuareg-false-=-p)))
     (re-search-forward "=[ \t]*")
     (current-column))
    ((and matching-kwop
          (looking-at (tuareg-give-match-pipe-kwop-regexp)))
     (when (looking-at (tuareg-give-extra-unindent-regexp))
       (tuareg-back-to-paren-or-indentation))
     (+ (tuareg-assoc-indent matching-kwop t)
        (tuareg-add-default-indent (not (looking-at "|")))
        (current-column)
        (if (or (string= matching-kwop "type")
                (string= matching-kwop "["))
            0
            tuareg-pipe-extra-unindent)))
    (t
     (goto-char old-point)
     (tuareg-compute-normal-indent))))

(defun tuareg-compute-paren-indent (paren-match-p old-point)
  (unless paren-match-p
    (tuareg-search-forward-paren))
  (let ((looking-at-paren (char-equal ?\( (char-after))) (start-pos (point)))
    (when (or looking-at-paren
              (looking-at (tuareg-no-code-after "\\(\{\\(.*with[ \t]*\\([[:upper:]].*\\.\\)?\\)?\\|\\[\\)")))
      (if (or (tuareg-in-indentation-p)
              (save-excursion (string= ":" (tuareg-find-meaningful-word))))
          (tuareg-back-to-paren-or-indentation)
        (tuareg-indent-from-previous-kwop))
      (when looking-at-paren
        (skip-chars-forward "( \t" start-pos))
      (while (and (looking-at "[([{]")
                  (> (scan-sexps (point) 1)
                     (save-excursion (goto-char old-point)
                                     (line-end-position))))
        (forward-char 1)
        (skip-syntax-forward " "))))
  (current-column))

(defun tuareg-compute-kwop-indent-general (kwop matching-kwop)
  (let* ((looking-at-matching (looking-at matching-kwop))
         (extra-unindent        ; non-paren code before matching-kwop
          (unless (save-excursion
                    (skip-chars-backward "( \t" (line-beginning-position))
                    (bolp))
            (tuareg-back-to-paren-or-indentation)
            t)))
    (+ (current-column)
       (tuareg-add-default-indent
        (if extra-unindent
            (or (string= matching-kwop "struct")
                (string= matching-kwop "object")
                (string= matching-kwop "with")
                (string= kwop "end"))
            (or (not (string= kwop "then"))
                looking-at-matching))))))

(defun tuareg-compute-kwop-indent (kwop)
  (when (string= kwop "rec")
    (setq kwop "and"))
  (let* ((old-point (point))
         (paren-match-p (looking-at "[|>]?[]})]\\|>\\."))
         (real-pipe (looking-at "|\\([^|]\\|$\\)"))
         (matching-kwop (tuareg-find-leading-kwop-match kwop)))
    (cond ((string= kwop "|")
           (if real-pipe
               (tuareg-compute-pipe-indent matching-kwop old-point)
             (goto-char old-point)
             (tuareg-compute-normal-indent)))
          ((looking-at "[[{(][<|]?\\|\\.<")
           (tuareg-compute-paren-indent paren-match-p old-point))
          ((string= kwop "with")
           (when (string= matching-kwop "type")
             (setq old-point (point)
                   matching-kwop (tuareg-find-meaningful-word)))
           (while (string= matching-kwop "with")
             (tuareg-find-with-match)
             (setq matching-kwop (tuareg-find-leading-kwop-match kwop)))
           (cond ((or (string= matching-kwop "module")
                      (string= matching-kwop "struct"))
                  (tuareg-paren-or-indentation-indent))
                 ((or (string= matching-kwop "try")
                      (string= matching-kwop "match"))
                  (tuareg-compute-kwop-indent-general kwop matching-kwop))
                 (t (goto-char old-point)
                    (tuareg-compute-kwop-indent-general kwop matching-kwop))))
          ((and (tuareg-editing-ls3)
                (or (string= kwop "do")
                    (string= kwop "done")
                    (string= kwop "reset")
                    (string= kwop "unless")
                    (string= kwop "until")))
           (tuareg-back-to-paren-or-indentation)
           (if (string= matching-kwop "->")
               (+ (current-column) tuareg-default-indent)
             (current-column)))
          ((or (and (string= kwop "and")
                    (string= matching-kwop "reset"))
               (and (string= kwop "end")
                    (tuareg-editing-ls3)
                    (or (string= matching-kwop "match")
                        (string= matching-kwop "automaton")
                        (string= matching-kwop "present"))))
           (if (tuareg-in-indentation-p)
               (current-column)
             (tuareg-paren-or-indentation-column)))
          ((string= kwop "in")
           (+ (current-column)
              (tuareg-add-default-indent (string= matching-kwop "let"))))
          ((not (string= kwop "and")) ; pretty general case
           (tuareg-compute-kwop-indent-general kwop matching-kwop))
          ((string= matching-kwop "with")
           (current-column))
          (t (tuareg-paren-or-indentation-column)))))

(defun tuareg-indent-to-code (beg-pos match)
  (unless (and (string= match "(")
               (search-forward "->" beg-pos t))
    (forward-char (length match)))
  (tuareg-skip-blank-and-comments)
  (current-column))

(defmacro tuareg-with-internal-syntax (&rest body)
  `(progn
     ;; Switch to a modified internal syntax.
     (modify-syntax-entry ?. "w" tuareg-mode-syntax-table)
     (modify-syntax-entry ?' "w" tuareg-mode-syntax-table)
     (modify-syntax-entry ?_ "w" tuareg-mode-syntax-table)
     (unwind-protect (progn ,@body)
       ;; Switch back to the interactive syntax.
       (modify-syntax-entry ?. "'" tuareg-mode-syntax-table)
       (modify-syntax-entry ?' "_" tuareg-mode-syntax-table)
       (modify-syntax-entry ?_ "_" tuareg-mode-syntax-table))))

(defun tuareg-leading-star-p ()
  (and tuareg-support-leading-star-comments
       (save-excursion ; this function does not make sense outside of a comment
         (tuareg-beginning-of-literal-or-comment)
         (and (or tuareg-leading-star-in-doc
                  (not (looking-at "(\\*[Tt][Ee][Xx]\\|(\\*\\*")))
              (progn
                (forward-line 1)
                (back-to-indentation)
                (looking-at "\\*[^)]"))))))

(defun tuareg-auto-fill-insert-leading-star (&optional leading-star)
  (let ((point-leading-comment (looking-at "(\\*")) (return-leading nil))
    (save-excursion
      (back-to-indentation)
      (when tuareg-electric-indent
        (when (and (tuareg-in-comment-p)
                   (or leading-star
                       (tuareg-leading-star-p)))
          (unless (looking-at "(?\\*")
            (insert-before-markers "* "))
          (setq return-leading t))
        (unless point-leading-comment
          ;; Use optional argument to break recursion
          (tuareg-indent-command t))))
    return-leading))

(unless (fboundp 'comment-normalize-vars) ;I.e. Only Emacs<21 (or XEmacs?).
  (defun tuareg-auto-fill-function ()
    (unless (tuareg-in-literal-p)
      (let ((leading-star
             (and (not (char-equal ?\n last-command-event))
                  (tuareg-auto-fill-insert-leading-star))))
        (do-auto-fill)
        (unless (char-equal ?\n last-command-event)
          (tuareg-auto-fill-insert-leading-star leading-star))))))

(defun tuareg-indent-command (&optional from-leading-star)
  "Indent the current line in Tuareg mode.

Compute new indentation based on OCaml syntax."
  (interactive "*")
  (unless from-leading-star
    (tuareg-auto-fill-insert-leading-star))
  (let ((case-fold-search nil))
   (tuareg-with-internal-syntax
    (save-excursion
      (back-to-indentation)
      (indent-line-to (max 0 (tuareg-compute-indent))))
    (when (tuareg-in-indentation-p) (back-to-indentation)))))

(defconst tuareg-sig-struct-regexp (tuareg-ro "sig" "struct"))
(defconst tuareg-top-level-command-regexp
  (concat "#" (tuareg-ro "open" "load" "use")))
(defun tuareg-compute-indent ()
  (save-excursion
    (cond
     ((tuareg-in-comment-p)
      (cond
       ((looking-at "(\\*")
        (if tuareg-indent-leading-comments
            (save-excursion
              (tuareg-skip-blank-and-comments)
              (back-to-indentation)
              (current-column))
          (current-column)))
       ((looking-at "\\*\\**)")
        (tuareg-beginning-of-literal-or-comment-fast)
        (if (tuareg-leading-star-p)
            (+ (current-column)
               (if (save-excursion
                     (forward-line 1)
                     (back-to-indentation)
                     (looking-at "*"))
                   1
                 tuareg-comment-end-extra-indent))
          (+ (current-column) tuareg-comment-end-extra-indent)))
       (tuareg-indent-comments
        (let ((star (and (tuareg-leading-star-p)
                         (looking-at "\\*"))))
          (tuareg-beginning-of-literal-or-comment-fast)
          (if star (re-search-forward "(") (re-search-forward "(\\*+[ \t]*"))
          (current-column)))
       (t (current-column))))
     ((tuareg-in-literal-p)
      (current-column))
     ((or (looking-at "\\<let\\>") (looking-at "\\<open\\>"))
      (if (tuareg-looking-at-internal-let)
          (if (tuareg-looking-at-in-let)
              (progn
                (tuareg-find-meaningful-word)
                (tuareg-find-in-match)
                (current-column))
            (tuareg-compute-normal-indent))
        (tuareg-find-phrase-indentation)))
     ((or (looking-at tuareg-governing-phrase-regexp)
          (looking-at ";;"))
      (tuareg-find-phrase-indentation))
     ((and tuareg-sig-struct-align (looking-at tuareg-sig-struct-regexp))
      (if (string= (tuareg-find-module) "module") (current-column)
        (tuareg-paren-or-indentation-indent)))
     ((looking-at ";")
      (tuareg-find-semicolon-match t))
     ((looking-at "|!")
      (tuareg-indent-to-code (line-beginning-position)
                             (tuareg-find-pipe-bang-match)))
     ((looking-at ">>[=>|]")
      (tuareg-indent-to-code (line-beginning-position)
                             (tuareg-find-monadic-match)))
     ((or (looking-at "%\\|;;")
          (and tuareg-support-camllight (looking-at "#"))
          (looking-at tuareg-top-level-command-regexp))
      0)
     ((or (looking-at (tuareg-give-matching-kwop-regexp))
          (looking-at "\\<rec\\>")
          (and tuareg-support-metaocaml
               (looking-at ">\\.")))
      (tuareg-compute-kwop-indent (tuareg-match-string 0)))
     (t (tuareg-compute-normal-indent)))))

(defun tuareg-split-string ()
  "Called whenever a line is broken inside an OCaml string literal."
  (insert-before-markers "\\ ")
  (tuareg-backward-char))

(defun tuareg-newline-and-indent ()
  "Like `newline-and-indent' but handles OCaml's multi-line strings."
  (interactive)
  (let ((hooked (tuareg-in-literal-p))
        (split-mark))
    (when hooked
      (setq split-mark (set-marker (make-marker) (point)))
      (tuareg-split-string))
    (newline-and-indent)
    (when hooked
      (goto-char (max (point) split-mark))
      (set-marker split-mark nil))))

(defun tuareg-abbrev-hook ()
  "If inserting a leading keyword at beginning of line, reindent the line."
  (unless (or (and (boundp 'electric-indent-mode) electric-indent-mode)
              (tuareg-in-literal-or-comment-p))
    (let* ((bol (line-beginning-position))
           (kw (save-excursion
                 (and (re-search-backward "^[ \t]*\\(\\w\\|_\\)+\\=" bol t)
                      (tuareg-match-string 1)))))
      (when kw
        (insert " ")
        (indent-according-to-mode)
        (backward-delete-char-untabify 1)))))

(defun tuareg-skip-to-end-of-phrase ()
  (let ((old-point (point)))
    (when (and (string= (tuareg-find-meaningful-word) ";")
               (char-equal (preceding-char) ?\;))
      (setq old-point (1- (point))))
    (goto-char old-point)
    (let ((kwop (tuareg-find-meaningful-word)))
      (goto-char (+ (point) (length kwop))))))

(defun tuareg-skip-back-blank-and-comments ()
  (skip-syntax-backward " ")
  (while (save-excursion (tuareg-backward-char)
                         (and (> (point) (point-min)) (tuareg-in-comment-p)))
    (tuareg-backward-char)
    (tuareg-beginning-of-literal-or-comment) (skip-syntax-backward " ")))

(defun tuareg-find-phrase-beginning (&optional stop-at-and)
  "Find `real' phrase beginning and return point."
  (beginning-of-line)
  (tuareg-skip-blank-and-comments)
  (end-of-line)
  (tuareg-skip-to-end-of-phrase)
  (let ((old-point (point)) (pt (point)))
    (if stop-at-and
        (tuareg-find-kwop tuareg-find-phrase-beginning-and-regexp "and")
      (tuareg-find-kwop tuareg-find-phrase-beginning-regexp))
    (while (and (> (point) (point-min)) (< (point) old-point)
                (or (not (looking-at tuareg-find-phrase-beginning-and-regexp))
                    (and (looking-at "\\<let\\>")
                         (tuareg-looking-at-internal-let))
                    (and (looking-at "\\<and\\>")
                         (save-excursion
                           (tuareg-find-and-match)
                           (tuareg-looking-at-internal-let)))
                    (and (looking-at "\\<module\\>")
                         (tuareg-looking-at-false-module))
                    (and (looking-at tuareg-sig-struct-regexp)
                         (tuareg-looking-at-false-sig-struct))
                    (and (looking-at "\\<type\\>")
                         (tuareg-looking-at-false-type))))
      (when (= pt (point))
        (error "tuareg-find-phrase-beginning: inf loop at %d" pt))
      (setq pt (point))
      (if (looking-at "\\<end\\>")
          (tuareg-find-match)
        (unless (bolp) (tuareg-backward-char))
        (setq old-point (point))
        (if stop-at-and
            (tuareg-find-kwop tuareg-find-phrase-beginning-and-regexp "and")
          (tuareg-find-kwop tuareg-find-phrase-beginning-regexp))))
    (when (tuareg-at-phrase-break-p)
      (end-of-line) (tuareg-skip-blank-and-comments))
    (back-to-indentation)
    (point)))


(defun tuareg-search-forward-end ()
  (let ((begin (point)) (current -1) (found) (move t))
    (while (and move (> (point) current))
      (if (re-search-forward "\\<end\\>" (point-max) t)
          (let ((stop (point)) (kwop))
            (unless (tuareg-in-literal-or-comment-p)
              (save-excursion
                (tuareg-backward-char 3)
                (setq kwop (tuareg-find-match))
                (cond
                 ((string= kwop "object")
                  (tuareg-find-phrase-beginning))
                 ((and (looking-at tuareg-sig-struct-regexp)
                       (tuareg-looking-at-false-sig-struct))
                  (tuareg-find-phrase-beginning)))
                (cond
                 ((or
                   (> (point) begin)
                   (and
                    (string= kwop "sig")
                    (looking-at
                     "[ \t\n]*\\(\\<with\\>[ \t\n]*\\<type\\>\\|=\\)")))
                  (if (> (point) current)
                      (progn
                        (setq current (point))
                        (goto-char stop))
                    (setq found nil move nil)))
                 (t (setq found t move nil))))))
        (setq found nil move nil)))
    found))

(defun tuareg-inside-module-or-class-find-kwop ()
  (let ((kwop (tuareg-find-kwop tuareg-inside-module-or-class-regexp
                                "\\<\\(and\\|end\\)\\>")))
    (tuareg-reset-and-kwop kwop)
    (when (string= kwop "with") (setq kwop nil))
    (if (string= kwop "end")
        (progn
          (tuareg-find-match)
          (tuareg-find-kwop tuareg-inside-module-or-class-regexp)
          (tuareg-inside-module-or-class-find-kwop))
      kwop)))

(defun tuareg-inside-module-or-class-p ()
  (let ((begin) (end) (and-end) (and-iter t) (kwop t))
    (save-excursion
      (when (looking-at "\\<and\\>")
        (tuareg-find-and-match))
      (setq begin (point))
      (unless (or (and (looking-at "\\<class\\>")
                       (save-excursion
                         (re-search-forward "\\<object\\>"
                                            (point-max) t)
                         (tuareg-find-phrase-beginning)
                         (> (point) begin)))
                  (and (looking-at "\\<module\\>")
                       (save-excursion
                         (re-search-forward tuareg-sig-struct-regexp
                                            (point-max) t)
                         (tuareg-find-phrase-beginning)
                         (> (point) begin))))
        (unless (looking-at tuareg-inside-module-or-class-opening-full)
          (setq kwop (tuareg-inside-module-or-class-find-kwop)))
        (when kwop
          (setq begin (point))
          (when (tuareg-search-forward-end)
            (tuareg-backward-char 3)
            (when (looking-at "\\<end\\>")
              (forward-char 3)
              (setq end (point))
              (setq and-end (point))
              (tuareg-skip-blank-and-comments)
              (while (and and-iter (looking-at "\\<and\\>"))
                (setq and-end (point))
                (when (tuareg-search-forward-end)
                  (tuareg-backward-char 3)
                  (when (looking-at "\\<end\\>")
                    (forward-char 3)
                    (setq and-end (point))
                    (tuareg-skip-blank-and-comments)))
                (when (<= (point) and-end)
                  (setq and-iter nil)))
              (list begin end and-end))))))))

(defun tuareg-move-inside-module-or-class-opening ()
  "Go to the beginning of the enclosing module or class.

Notice that white-lines (or comments) located immediately before a
module/class are considered enclosed in this module/class."
  (interactive)
  (let* ((old-point (point))
         (kwop (tuareg-inside-module-or-class-find-kwop)))
    (unless kwop
      (goto-char old-point))
    (tuareg-find-phrase-beginning)))

(unless tuareg-use-smie
  (defun tuareg-discover-phrase (&optional quiet stop-at-and)
    (end-of-line)
    (let ((end (point)) (case-fold-search nil))
      (tuareg-with-internal-syntax
       (tuareg-find-phrase-beginning stop-at-and)
       (when (> (point) end) (setq end (point)))
       (save-excursion
         (let ((begin (point)) (cpt 0) (lines-left 0) (stop)
               (inside-module-or-class (tuareg-inside-module-or-class-p))
               (looking-block
                (looking-at tuareg-inside-module-or-class-opening-full)))
           (if (and looking-block inside-module-or-class)
               (progn
                 (setq begin (nth 0 inside-module-or-class))
                 (setq end (nth 2 inside-module-or-class))
                 (goto-char end))
             (if inside-module-or-class
                 (progn
                   (setq stop (save-excursion
                                (goto-char (nth 1 inside-module-or-class))
                                (line-beginning-position)))
                   (if (< stop end) (setq stop (point-max))))
               (setq stop (point-max)))
             (save-restriction
               (goto-char end)
               (while (and (= lines-left 0)
                           (or (not inside-module-or-class) (< (point) stop))
                           (<= (save-excursion
                                 (tuareg-find-phrase-beginning stop-at-and))
                               end))
                 (unless quiet
                   (setq cpt (1+ cpt))
                   (when (= 8 cpt)
                     (message "Looking for enclosing phrase...")))
                 (setq end (point))
                 (tuareg-skip-to-end-of-phrase)
                 (narrow-to-region (line-beginning-position) (point-max))
                 (goto-char end)
                 (setq lines-left (forward-line 1)))))
           (when (>= cpt 8) (message "Looking for enclosing phrase... done."))
           (save-excursion (tuareg-skip-blank-and-comments) (setq end (point)))
           (tuareg-skip-back-blank-and-comments)
           (list begin (point) end)))))))

(defun tuareg-mark-phrase ()
  "Put mark at end of this OCaml phrase, point at beginning.
The OCaml phrase is the phrase just before the point."
  (interactive)
  (let ((pair (tuareg-discover-phrase)))
    (goto-char (nth 1 pair)) (push-mark (nth 0 pair) t t)))

(defun tuareg-next-phrase (&optional quiet stop-at-and)
  "Skip to the beginning of the next phrase."
  (interactive "i")
  (goto-char (save-excursion
               (nth 2 (tuareg-discover-phrase quiet stop-at-and))))
  (cond
   ((looking-at "\\<end\\>")
    (tuareg-next-phrase quiet stop-at-and))
   ((looking-at ")")
    (forward-char 1)
    (tuareg-skip-blank-and-comments))
   ((looking-at ";;")
    (forward-char 2)
    (tuareg-skip-blank-and-comments))))

(defun tuareg-previous-phrase ()
  "Skip to the beginning of the previous phrase."
  (interactive)
  (beginning-of-line)
  (tuareg-skip-to-end-of-phrase)
  (tuareg-discover-phrase))

(unless tuareg-use-smie
  (defun tuareg-indent-phrase ()
    "Depending of the context: justify and indent a comment,
or indent all lines in the current phrase."
    (interactive)
    (save-excursion
      (back-to-indentation)
      (if (tuareg-in-comment-p)
          (let* ((cobpoint (save-excursion
                             (tuareg-beginning-of-literal-or-comment)
                             (point)))
                 (begpoint (save-excursion
                             (while (and (> (point) cobpoint)
                                         (tuareg-in-comment-p)
                                         (not (looking-at "^[ \t]*$")))
                               (forward-line -1))
                             (max cobpoint (point))))
                 (coepoint (save-excursion
                             (while (and (tuareg-in-comment-p)
                                         (< (point) (point-max)))
                               (re-search-forward "\\*)" nil 'end))
                             (point)))
                 (endpoint (save-excursion
                             (re-search-forward "^[ \t]*$" coepoint 'end)
                             (line-beginning-position 2)))
                 (leading-star (tuareg-leading-star-p)))
            (goto-char begpoint)
            (while (and leading-star
                        (< (point) endpoint)
                        (not (looking-at "^[ \t]*$")))
              (forward-line 1)
              (back-to-indentation)
              (when (looking-at "\\*\\**\\([^)]\\|$\\)")
                (delete-char 1)
                (setq endpoint (1- endpoint))))
            (goto-char (min (point) endpoint))
            (fill-region begpoint endpoint)
            (re-search-forward "\\*)" nil 'end)
            (setq endpoint (point))
            (when leading-star
              (goto-char begpoint)
              (forward-line 1)
              (if (< (point) endpoint)
                  (tuareg-auto-fill-insert-leading-star t)))
            (indent-region begpoint endpoint nil))
        (let ((pair (tuareg-discover-phrase)))
          (indent-region (nth 0 pair) (nth 1 pair) nil))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(unless tuareg-use-smie
  (defun tuareg-interactive-end-of-phrase ()
    (save-excursion
      (end-of-line)
      (tuareg-find-meaningful-word)
      (tuareg-find-meaningful-word)
      (looking-at ";;")))

  (defun tuareg-interactive-send-input ()
    "Process if the current line ends with `;;' then send the
current phrase else insert a newline."
    (if (tuareg-interactive-end-of-phrase)
        (progn
          (comint-send-input)
          (goto-char (point-max)))
      (insert "\n")
      (message tuareg-interactive--send-warning)))

  (defun tuareg-interactive-send-input-end-of-phrase ()
    (interactive)
    (goto-char (point-max))
    (unless (tuareg-interactive-end-of-phrase)
      (insert ";;"))
    (comint-send-input))
  )


(provide 'tuareg_indent)

;;; tuareg_indent.el ends here
