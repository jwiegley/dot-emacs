;;; js3-vars.el -- byte-compiler support for js3-mode

;;; Code:

(eval-when-compile
  (require 'cl))
(require 'thingatpt)                    ; forward-symbol etc

(eval-and-compile
  (require 'cc-mode)     ; (only) for `c-populate-syntax-table'
  (require 'cc-langs)    ; it's here in Emacs 21...
  (require 'cc-engine))  ; for `c-paragraph-start' et. al.

(defvar js3-emacs22 (>= emacs-major-version 22))

(defun js3-mark-safe-local (name pred)
  "Make the variable NAME buffer-local and mark it as safe file-local
variable with predicate PRED."
  (make-variable-buffer-local name)
  (put name 'safe-local-variable pred))

(defcustom js3-highlight-level 2
  "Amount of syntax highlighting to perform.
nil, zero or negative means none.
1 adds basic syntax highlighting.
2 adds highlighting of some Ecma built-in properties.
3 adds highlighting of many Ecma built-in functions."
  :group 'js3-mode
  :type '(choice (const :tag "None" nil)
                 (const :tag "Basic" 1)
                 (const :tag "Include Properties" 2)
                 (const :tag "Include Functions" 3)))

(defgroup js3-mode nil
  "An improved JavaScript mode."
  :group 'languages)

(defcustom js3-mode-dev-mode-p nil
  "Non-nil if running in development mode.  Normally nil."
  :group 'js3-mode
  :type 'boolean)

(defcustom js3-compact t
  "Printing variable.
If set to t, try to shorten as much as possible onto one line.
Overrides other compact settings."
  :group 'js3-mode
  :type 'boolean)

(defcustom js3-compact-while nil
  "Printing variable.
If set to t, try to shorten while statements onto one line."
  :group 'js3-mode
  :type 'boolean)

(defcustom js3-compact-for nil
  "Printing variable.
If set to t, try to shorten for statements onto one line."
  :group 'js3-mode
  :type 'boolean)

(defcustom js3-compact-if nil
  "Printing variable.
If set to t, try to shorten if statements onto one line."
  :group 'js3-mode
  :type 'boolean)

(defcustom js3-compact-infix nil
  "Printing variable.
If set to t, try to shorten infix expressions onto one line."
  :group 'js3-mode
  :type 'boolean)

(defcustom js3-compact-expr nil
  "Printing variable.
If set to t, try to shorten expressions onto one line."
  :group 'js3-mode
  :type 'boolean)

(defcustom js3-compact-list nil
  "Printing variable.
If set to t, try to shorten lists onto one line."
  :group 'js3-mode
  :type 'boolean)

(defcustom js3-compact-case nil
  "Printing variable.
If set to t, try to shorten case statements onto one line."
  :group 'js3-mode
  :type 'boolean)

(defcustom js3-max-columns 72
  "Printing variable.
Max number of columns per line."
  :group 'js3-mode
  :type 'integer)

(defcustom js3-indent-tabs-mode nil
  "Default setting for indent-tabs-mode for js3-mode."
  :group 'js3-mode
  :type 'boolean)
(js3-mark-safe-local 'js3-indent-tabs-mode 'booleanp)

(defcustom js3-continued-expr-mult 2
  "Number of tabs to indent continued expressions."
  :group 'js3-mode
  :type 'integer)

(defcustom js3-pretty-vars t
  "Non-nil to try to indent comma-last continued var statements in a pretty way.
Does not affect comma-first continued var statements.

Note that this forces a reparse so should be turned off if not being used"
  :group 'js3-mode
  :type 'boolean)
(js3-mark-safe-local 'js3-pretty-vars 'booleanp)

(defcustom js3-pretty-vars-spaces 4
  "Number of spaces to indent when `js3-pretty-vars' is enabled."

  :group 'js3-mode
  :type 'integer)
(js3-mark-safe-local 'js3-pretty-vars-spaces 'integerp)

(defcustom js3-pretty-lazy-vars t
  "Non-nil to try to indent comma-first continued var statements correctly
when `js3-lazy-commas' is t"
  :group 'js3-mode
  :type 'boolean)
(js3-mark-safe-local 'js3-pretty-lazy-vars 'booleanp)

(defcustom js3-move-point-on-right-click t
  "Non-nil to move insertion point when you right-click.
This makes right-click context menu behavior a bit more intuitive,
since menu operations generally apply to the point.  The exception
is if there is a region selection, in which case the point does -not-
move, so cut/copy/paste etc. can work properly.

Note that IntelliJ moves the point, and Eclipse leaves it alone,
so this behavior is customizable."
  :group 'js3-mode
  :type 'boolean)

(defcustom js3-mirror-mode nil
  "Non-nil to insert closing brackets, parens, etc. automatically."
  :group 'js3-mode
  :type 'boolean)

(defcustom js3-auto-indent-p nil
  "Automatic indentation with punctuation characters. If non-nil, the
current line is indented when certain punctuations are inserted."
  :group 'js3-mode
  :type 'boolean)
(js3-mark-safe-local 'js3-auto-indent-p 'booleanp)

(defcustom js3-consistent-level-indent-inner-bracket nil
  "Non-nil to make indentation level inner bracket consistent,
regardless of the beginning bracket position."
  :group 'js3-mode
  :type 'boolean)
(js3-mark-safe-local 'js3-consistent-level-indent-inner-bracket 'booleanp)

(defcustom js3-boring-indentation nil
  "Non-nil to indent various sorts of continued expressions standardly."
  :group 'js3-mode
  :type 'boolean)
(js3-mark-safe-local 'js3-boring-indentation 'booleanp)

(defcustom js3-manual-indentation nil
  "Non-nil to override all other indentation behavior and indent manually."
  :group 'js3-mode
  :type 'boolean)
(js3-mark-safe-local 'js3-manual-indentation 'booleanp)

(defcustom js3-indent-on-enter-key nil
  "Non-nil to have Enter/Return key indent the line.
This is unusual for Emacs modes but common in IDEs like Eclipse."
  :type 'boolean
  :group 'js3-mode)
(js3-mark-safe-local 'js3-indent-on-enter-key 'booleanp)

(defcustom js3-enter-indents-newline nil
  "Non-nil to have Enter/Return key indent the newly-inserted line.
This is unusual for Emacs modes but common in IDEs like Eclipse."
  :type 'boolean
  :group 'js3-mode)
(js3-mark-safe-local 'js3-enter-indents-newline 'booleanp)

(defcustom js3-rebind-eol-bol-keys nil
  "Non-nil to rebind beginning-of-line and end-of-line keys.
If non-nil, bounce between bol/eol and first/last non-whitespace char."
  :group 'js3-mode
  :type 'boolean)

(defcustom js3-electric-keys '("{" "}" "(" ")" "[" "]" ":" ";" "," "*")
  "Keys that auto-indent when `js3-auto-indent-p' is non-nil.
Each value in the list is passed to `define-key'."
  :type 'list
  :group 'js3-mode)

(defcustom js3-idle-timer-delay 0.2
  "Delay in secs before re-parsing after user makes changes.
Multiplied by `js3-dynamic-idle-timer-adjust', which see."
  :type 'number
  :group 'js3-mode)
(make-variable-buffer-local 'js3-idle-timer-delay)

(defcustom js3-dynamic-idle-timer-adjust 0
  "Positive to adjust `js3-idle-timer-delay' based on file size.
The idea is that for short files, parsing is faster so we can be
more responsive to user edits without interfering with editing.
The buffer length in characters (typically bytes) is divided by
this value and used to multiply `js3-idle-timer-delay' for the
buffer.  For example, a 21k file and 10k adjust yields 21k/10k
== 2, so js3-idle-timer-delay is multiplied by 2.
If `js3-dynamic-idle-timer-adjust' is 0 or negative,
`js3-idle-timer-delay' is not dependent on the file size."
  :type 'number
  :group 'js3-mode)

(defcustom js3-mode-escape-quotes t
  "Non-nil to disable automatic quote-escaping inside strings."
  :type 'boolean
  :group 'js3-mode)

(defcustom js3-mode-squeeze-spaces t
  "Non-nil to normalize whitespace when filling in comments.
Multiple runs of spaces are converted to a single space."
  :type 'boolean
  :group 'js3-mode)

(defcustom js3-mode-show-parse-errors t
  "True to highlight parse errors."
  :type 'boolean
  :group 'js3-mode)

(defcustom js3-mode-show-strict-warnings t
  "Non-nil to emit Ecma strict-mode warnings.
Some of the warnings can be individually disabled by other flags,
even if this flag is non-nil."
  :type 'boolean
  :group 'js3-mode)

(defcustom js3-strict-trailing-comma-warning t
  "Non-nil to warn about trailing commas in array literals.
Ecma-262 forbids them, but many browsers permit them.  IE is the
big exception, and can produce bugs if you have trailing commas."
  :type 'boolean
  :group 'js3-mode)

(defcustom js3-strict-missing-semi-warning nil
  "Non-nil to warn about semicolon auto-insertion after statement.
Technically this is legal per Ecma-262, but some style guides disallow
depending on it."
  :type 'boolean
  :group 'js3-mode)

(defcustom js3-missing-semi-one-line-override nil
  "Non-nil to permit missing semicolons in one-line functions.
In one-liner functions such as `function identity(x) {return x}'
people often omit the semicolon for a cleaner look.  If you are
such a person, you can suppress the missing-semicolon warning
by setting this variable to t."
  :type 'boolean
  :group 'js3-mode)

(defcustom js3-strict-inconsistent-return-warning t
  "Non-nil to warn about mixing returns with value-returns.
It's perfectly legal to have a `return' and a `return foo' in the
same function, but it's often an indicator of a bug, and it also
interferes with type inference (in systems that support it.)"
  :type 'boolean
  :group 'js3-mode)

(defcustom js3-strict-cond-assign-warning t
  "Non-nil to warn about expressions like if (a = b).
This often should have been '==' instead of '='.  If the warning
is enabled, you can suppress it on a per-expression basis by
parenthesizing the expression, e.g. if ((a = b)) ..."
  :type 'boolean
  :group 'js3-mode)

(defcustom js3-strict-var-redeclaration-warning t
  "Non-nil to warn about redeclaring variables in a script or function."
  :type 'boolean
  :group 'js3-mode)

(defcustom js3-strict-var-hides-function-arg-warning t
  "Non-nil to warn about a var decl hiding a function argument."
  :type 'boolean
  :group 'js3-mode)

(defcustom js3-skip-preprocessor-directives nil
  "Non-nil to treat lines beginning with # as comments.
Useful for viewing Mozilla JavaScript source code."
  :type 'boolean
  :group 'js3-mode)

(defcustom js3-language-version 180
  "Configures what JavaScript language version to recognize.
Currently versions 150, 160, 170 and 180 are supported, corresponding
to JavaScript 1.5, 1.6, 1.7 and 1.8, respectively.  In a nutshell,
1.6 adds E4X support, 1.7 adds let, yield, and Array comprehensions,
and 1.8 adds function closures."
  :type 'integer
  :group 'js3-mode)

(defcustom js3-allow-keywords-as-property-names t
  "If non-nil, you can use JavaScript keywords as object property names.
Examples:

var foo = {int: 5, while: 6, continue: 7};
foo.return = 8;

Ecma-262 forbids this syntax, but many browsers support it."
  :type 'boolean
  :group 'js3-mode)

(defcustom js3-instanceof-has-side-effects nil
  "If non-nil, treats the instanceof operator as having side effects.
This is useful for xulrunner apps."
  :type 'boolean
  :group 'js3-mode)

(defcustom js3-allow-rhino-new-expr-initializer nil
  "Non-nil to support a Rhino's experimental syntactic construct.

Rhino supports the ability to follow a `new' expression with an object
literal, which is used to set additional properties on the new object
after calling its constructor.  Syntax:

new <expr> [ ( arglist ) ] [initializer]

Hence, this expression:

new Object {a: 1, b: 2}

results in an Object with properties a=1 and b=2.  This syntax is
apparently not configurable in Rhino - it's currently always enabled,
as of Rhino version 1.7R2."
  :type 'boolean
  :group 'js3-mode)

(defcustom js3-allow-member-expr-as-function-name nil
  "Non-nil to support experimental Rhino syntax for function names.

Rhino supports an experimental syntax configured via the Rhino Context
setting `allowMemberExprAsFunctionName'.  The experimental syntax is:

function <member-expr> ( [ arg-list ] ) { <body> }

Where member-expr is a non-parenthesized 'member expression', which
is anything at the grammar level of a new-expression or lower, meaning
any expression that does not involve infix or unary operators.

When <member-expr> is not a simple identifier, then it is syntactic
sugar for assigning the anonymous function to the <member-expr>.  Hence,
this code:

function a.b().c[2] (x, y) { ... }

is rewritten as:

a.b().c[2] = function(x, y) {...}

which doesn't seem particularly useful, but Rhino permits it."
  :type 'boolean
  :group 'js3-mode)

(defvar js3-mode-version 20110809
  "Release number for `js3-mode'.")

;; scanner variables

(defmacro deflocal (name value &optional comment)
  `(progn
     (defvar ,name ,value ,comment)
     (make-variable-buffer-local ',name)))

;; We record the start and end position of each token.
(deflocal js3-token-beg 1)
(deflocal js3-token-end -1)

(defvar js3-EOF_CHAR -1
  "Represents end of stream.  Distinct from js3-EOF token type.")

;; I originally used symbols to represent tokens, but Rhino uses
;; ints and then sets various flag bits in them, so ints it is.
;; The upshot is that we need a `js3-' prefix in front of each name.
(defvar js3-ERROR -1)
(defvar js3-EOF 0)
(defvar js3-EOL 1)
(defvar js3-ENTERWITH 2)       ; begin interpreter bytecodes
(defvar js3-LEAVEWITH 3)
(defvar js3-RETURN 4)
(defvar js3-GOTO 5)
(defvar js3-IFEQ 6)
(defvar js3-IFNE 7)
(defvar js3-SETNAME 8)
(defvar js3-BITOR 9)
(defvar js3-BITXOR 10)
(defvar js3-BITAND 11)
(defvar js3-ADD 12)            ; infix plus
(defvar js3-SUB 13)            ; infix minus
(defvar js3-MUL 14)
(defvar js3-DIV 15)
(defvar js3-MOD 16)
(defvar js3-LT 17)
(defvar js3-GT 18)
(defvar js3-EQ 19)
(defvar js3-NE 20)
(defvar js3-LE 21)
(defvar js3-GE 22)
(defvar js3-LSH 23)
(defvar js3-RSH 24)
(defvar js3-URSH 25)
(defvar js3-NOT 26)
(defvar js3-BITNOT 27)
(defvar js3-POS 28)            ; unary plus
(defvar js3-NEG 29)            ; unary minus
(defvar js3-NEW 30)
(defvar js3-DELPROP 31)
(defvar js3-TYPEOF 32)
(defvar js3-GETPROP 33)
(defvar js3-GETPROPNOWARN 34)
(defvar js3-SETPROP 35)
(defvar js3-GETELEM 36)
(defvar js3-SETELEM 37)
(defvar js3-CALL 38)
(defvar js3-NAME 39)           ; an identifier
(defvar js3-NUMBER 40)
(defvar js3-STRING 41)
(defvar js3-NULL 42)
(defvar js3-THIS 43)
(defvar js3-FALSE 44)
(defvar js3-TRUE 45)
(defvar js3-SHEQ 46)           ; shallow equality (===)
(defvar js3-SHNE 47)           ; shallow inequality (!==)
(defvar js3-REGEXP 48)
(defvar js3-BINDNAME 49)
(defvar js3-THROW 50)
(defvar js3-RETHROW 51)        ; rethrow caught exception: catch (e if ) uses it
(defvar js3-IN 52)
(defvar js3-INSTANCEOF 53)
(defvar js3-LOCAL_LOAD 54)
(defvar js3-GETVAR 55)
(defvar js3-SETVAR 56)
(defvar js3-CATCH_SCOPE 57)
(defvar js3-ENUM_INIT_KEYS 58)
(defvar js3-ENUM_INIT_VALUES 59)
(defvar js3-ENUM_INIT_ARRAY 60)
(defvar js3-ENUM_NEXT 61)
(defvar js3-ENUM_ID 62)
(defvar js3-THISFN 63)
(defvar js3-RETURN_RESULT 64)  ; to return previously stored return result
(defvar js3-ARRAYLIT 65)       ; array literal
(defvar js3-OBJECTLIT 66)      ; object literal
(defvar js3-GET_REF 67)        ; *reference
(defvar js3-SET_REF 68)        ; *reference = something
(defvar js3-DEL_REF 69)        ; delete reference
(defvar js3-REF_CALL 70)       ; f(args) = something or f(args)++
(defvar js3-REF_SPECIAL 71)    ; reference for special properties like __proto
(defvar js3-YIELD 72)          ; JS 1.7 yield pseudo keyword

;; deprecated
(defvar js3-DEPRECATED-A 73)
(defvar js3-DEPRECATED-B 74)
(defvar js3-DEPRECATED-C 75)
(defvar js3-DEPRECATED-D 76)
(defvar js3-DEPRECATED-E 77)
(defvar js3-DEPRECATED-F 78)
(defvar js3-DEPRECATED-G 79)

(defvar js3-TRY 80)
(defvar js3-SEMI 81)           ; semicolon
(defvar js3-LB 82)             ; left and right brackets
(defvar js3-RB 83)
(defvar js3-LC 84)             ; left and right curly-braces
(defvar js3-RC 85)
(defvar js3-LP 86)             ; left and right parens
(defvar js3-RP 87)
(defvar js3-COMMA 88)          ; comma operator

(defvar js3-ASSIGN 89)         ; simple assignment (=)
(defvar js3-ASSIGN_BITOR 90)   ; |=
(defvar js3-ASSIGN_BITXOR 91)  ; ^=
(defvar js3-ASSIGN_BITAND 92)  ; &=
(defvar js3-ASSIGN_ADD 93)     ; +=
(defvar js3-ASSIGN_SUB 94)     ; -=
(defvar js3-ASSIGN_MUL 95)     ; *=
(defvar js3-ASSIGN_DIV 96)     ; /=
(defvar js3-ASSIGN_MOD 97)     ; %=
(defvar js3-ASSIGN_LSH 98)     ; <<=
(defvar js3-ASSIGN_RSH 99)     ; >>=
(defvar js3-ASSIGN_URSH 100)   ; >>>=

(defvar js3-first-assign js3-ASSIGN)
(defvar js3-last-assign js3-ASSIGN_MOD)

(defvar js3-HOOK 101)          ; conditional (?:)
(defvar js3-COLON 102)
(defvar js3-OR 103)            ; logical or (||)
(defvar js3-AND 104)           ; logical and (&&)
(defvar js3-INC 105)           ; increment/decrement (++ --)
(defvar js3-DEC 106)
(defvar js3-DOT 107)           ; member operator (.)
(defvar js3-FUNCTION 108)      ; function keyword
(defvar js3-EXPORT 109)        ; export keyword
(defvar js3-IMPORT 110)        ; import keyword
(defvar js3-IF 111)            ; if keyword
(defvar js3-ELSE 112)          ; else keyword
(defvar js3-SWITCH 113)        ; switch keyword
(defvar js3-CASE 114)          ; case keyword
(defvar js3-DEFAULT 115)       ; default keyword
(defvar js3-WHILE 116)         ; while keyword
(defvar js3-DO 117)            ; do keyword
(defvar js3-FOR 118)           ; for keyword
(defvar js3-BREAK 119)         ; break keyword
(defvar js3-CONTINUE 120)      ; continue keyword
(defvar js3-VAR 121)           ; var keyword
(defvar js3-WITH 122)          ; with keyword
(defvar js3-CATCH 123)         ; catch keyword
(defvar js3-FINALLY 124)       ; finally keyword
(defvar js3-VOID 125)          ; void keyword
(defvar js3-RESERVED 126)      ; reserved keywords

(defvar js3-EMPTY 127)

;; Types used for the parse tree - never returned by scanner.

(defvar js3-BLOCK 128)         ; statement block
(defvar js3-LABEL 129)         ; label
(defvar js3-TARGET 130)
(defvar js3-LOOP 131)
(defvar js3-EXPR_VOID 132)     ; expression statement in functions
(defvar js3-EXPR_RESULT 133)   ; expression statement in scripts
(defvar js3-JSR 134)
(defvar js3-SCRIPT 135)        ; top-level node for entire script
(defvar js3-TYPEOFNAME 136)    ; for typeof(simple-name)
(defvar js3-USE_STACK 137)
(defvar js3-SETPROP_OP 138)    ; x.y op= something
(defvar js3-SETELEM_OP 139)    ; x[y] op= something
(defvar js3-LOCAL_BLOCK 140)
(defvar js3-SET_REF_OP 141)    ; *reference op= something

;; deprecated
(defvar js3-DEPRECATED-H 142)
(defvar js3-DEPRECATED-I 143)
(defvar js3-DEPRECATED-J 144)
(defvar js3-DEPRECATED-K 145)
(defvar js3-DEPRECATED-L 146)
(defvar js3-DEPRECATED-M 147)

;; Optimizer-only tokens
(defvar js3-TO_OBJECT 148)
(defvar js3-TO_DOUBLE 149)

(defvar js3-GET 150)           ; JS 1.5 get pseudo keyword
(defvar js3-SET 151)           ; JS 1.5 set pseudo keyword
(defvar js3-LET 152)           ; JS 1.7 let pseudo keyword
(defvar js3-CONST 153)
(defvar js3-SETCONST 154)
(defvar js3-SETCONSTVAR 155)
(defvar js3-ARRAYCOMP 156)
(defvar js3-LETEXPR 157)
(defvar js3-WITHEXPR 158)
(defvar js3-DEBUGGER 159)

(defvar js3-COMMENT 160)
(defvar js3-ENUM 161)  ; for "enum" reserved word

(defconst js3-num-tokens (1+ js3-ENUM))

(defconst js3-debug-print-trees nil)

;; Rhino accepts any string or stream as input.
;; Emacs character processing works best in buffers, so we'll
;; assume the input is a buffer.  JavaScript strings can be
;; copied into temp buffers before scanning them.

;; Buffer-local variables yield much cleaner code than using `defstruct'.
;; They're the Emacs equivalent of instance variables, more or less.

(deflocal js3-ts-dirty-line nil
  "Token stream buffer-local variable.
Indicates stuff other than whitespace since start of line.")

(deflocal js3-ts-regexp-flags nil
  "Token stream buffer-local variable.")

(deflocal js3-ts-string ""
  "Token stream buffer-local variable.
Last string scanned.")

(deflocal js3-ts-number nil
  "Token stream buffer-local variable.
Last literal number scanned.")

(deflocal js3-ts-hit-eof nil
  "Token stream buffer-local variable.")

(deflocal js3-ts-line-start 0
  "Token stream buffer-local variable.")

(deflocal js3-ts-lineno 1
  "Token stream buffer-local variable.")

(deflocal js3-ts-line-end-char -1
  "Token stream buffer-local variable.")

(deflocal js3-ts-cursor 1  ; emacs buffers are 1-indexed
  "Token stream buffer-local variable.
Current scan position.")

(deflocal js3-ts-string-buffer nil
  "Token stream buffer-local variable.
List of chars built up while scanning various tokens.")

(deflocal js3-ts-comment-type nil
  "Token stream buffer-local variable.")

;;; Parser variables

(deflocal js3-parsed-errors nil
  "List of errors produced during scanning/parsing.")

(deflocal js3-parsed-warnings nil
  "List of warnings produced during scanning/parsing.")

(deflocal js3-recover-from-parse-errors t
  "Non-nil to continue parsing after a syntax error.

In recovery mode, the AST will be built in full, and any error
nodes will be flagged with appropriate error information.  If
this flag is nil, a syntax error will result in an error being
signaled.

The variable is automatically buffer-local, because different
modes that use the parser will need different settings.")

(deflocal js3-parse-hook nil
  "List of callbacks for receiving parsing progress.")

(defvar js3-parse-finished-hook nil
  "List of callbacks to notify when parsing finishes.
Not called if parsing was interrupted.")

(deflocal js3-is-eval-code nil
  "True if we're evaluating code in a string.
If non-nil, the tokenizer will record the token text, and the AST nodes
will record their source text.  Off by default for IDE modes, since the
text is available in the buffer.")

(defvar js3-parse-ide-mode t
  "Non-nil if the parser is being used for `js3-mode'.
If non-nil, the parser will set text properties for fontification
and the syntax-table.  The value should be nil when using the
parser as a frontend to an interpreter or byte compiler.")

;;; Parser instance variables (buffer-local vars for js3-parse)

(defconst js3-clear-ti-mask #xFFFF
  "Mask to clear token information bits.")

(defconst js3-ti-after-eol (lsh 1 16)
  "Flag:  first token of the source line.")

(defconst js3-ti-check-label (lsh 1 17)
  "Flag:  indicates to check for label.")

;; Inline Rhino's CompilerEnvirons vars as buffer-locals.

(deflocal js3-compiler-generate-debug-info t)
(deflocal js3-compiler-use-dynamic-scope nil)
(deflocal js3-compiler-reserved-keywords-as-identifier nil)
(deflocal js3-compiler-optimization-level 0)
(deflocal js3-compiler-generating-source t)
(deflocal js3-compiler-strict-mode nil)
(deflocal js3-compiler-report-warning-as-error nil)
(deflocal js3-compiler-generate-observer-count nil)
(deflocal js3-compiler-activation-names nil)

;; SKIP:  sourceURI

;; There's a compileFunction method in Context.java - may need it.
(deflocal js3-called-by-compile-function nil
  "True if `js3-parse' was called by `js3-compile-function'.
Will only be used when we finish implementing the interpreter.")

;; SKIP:  ts  (we just call `js3-init-scanner' and use its vars)

(deflocal js3-current-flagged-token js3-EOF)
(deflocal js3-current-token js3-EOF)

;; SKIP:  node factory - we're going to just call functions directly,
;; and eventually go to a unified AST format.

(deflocal js3-nesting-of-function 0)

(deflocal js3-recorded-identifiers nil
  "Tracks identifiers found during parsing.")

(defcustom js3-global-externs nil
  "A list of any extern names you'd like to consider always declared.
This list is global and is used by all js3-mode files.
You can create buffer-local externs list using `js3-additional-externs'.

There is also a buffer-local variable `js3-default-externs',
which is initialized by default to include the Ecma-262 externs
and the standard browser externs.  The three lists are all
checked during highlighting."
  :type 'list
  :group 'js3-mode)

(deflocal js3-default-externs nil
  "Default external declarations.

These are currently only used for highlighting undeclared variables,
which only worries about top-level (unqualified) references.
As js3-mode's processing improves, we will flesh out this list.

The initial value is set to `js3-ecma-262-externs', unless you
have set `js3-include-browser-externs', in which case the browser
externs are also included.

See `js3-additional-externs' for more information.")

(defcustom js3-include-browser-externs t
  "Non-nil to include browser externs in the master externs list.
If you work on JavaScript files that are not intended for browsers,
such as Mozilla Rhino server-side JavaScript, set this to nil.
You can always include them on a per-file basis by calling
`js3-add-browser-externs' from a function on `js3-mode-hook'.

See `js3-additional-externs' for more information about externs."
  :type 'boolean
  :group 'js3-mode)

(defcustom js3-include-rhino-externs t
  "Non-nil to include Mozilla Rhino externs in the master externs list.
See `js3-additional-externs' for more information about externs."
  :type 'boolean
  :group 'js3-mode)

(defcustom js3-include-gears-externs t
  "Non-nil to include Google Gears externs in the master externs list.
See `js3-additional-externs' for more information about externs."
  :type 'boolean
  :group 'js3-mode)

(deflocal js3-additional-externs nil
  "A buffer-local list of additional external declarations.
It is used to decide whether variables are considered undeclared
for purposes of highlighting.

Each entry is a lisp string.  The string should be the fully qualified
name of an external entity.  All externs should be added to this list,
so that as js3-mode's processing improves it can take advantage of them.

You may want to declare your externs in three ways.
First, you can add externs that are valid for all your JavaScript files.
You should probably do this by adding them to `js3-global-externs', which
is a global list used for all js3-mode files.

Next, you can add a function to `js3-mode-hook' that adds additional
externs appropriate for the specific file, perhaps based on its path.
These should go in `js3-additional-externs', which is buffer-local.

Finally, you can add a function to `js3-post-parse-callbacks',
which is called after parsing completes, and `root' is bound to
the root of the parse tree.  At this stage you can set up an AST
node visitor using `js3-visit-ast' and examine the parse tree
for specific import patterns that may imply the existence of
other externs, possibly tied to your build system.  These should also
be added to `js3-additional-externs'.

Your post-parse callback may of course also use the simpler and
faster (but perhaps less robust) approach of simply scanning the
buffer text for your imports, using regular expressions.")

(deflocal js3-declared-globals nil
  "A buffer-local list of globals declared at the top of the file.")

;; SKIP:  decompiler
;; SKIP:  encoded-source

;;; The following variables are per-function and should be saved/restored
;;; during function parsing...

(deflocal js3-current-script-or-fn nil)
(deflocal js3-current-scope nil)
(deflocal js3-nesting-of-with 0)
(deflocal js3-label-set nil
  "An alist mapping label names to nodes.")

(deflocal js3-loop-set nil)
(deflocal js3-loop-and-switch-set nil)
(deflocal js3-has-return-value nil)
(deflocal js3-end-flags 0)

;;; ...end of per function variables

;; Without 2-token lookahead, labels are a problem.
;; These vars store the token info of the last matched name,
;; iff it wasn't the last matched token.  Only valid in some contexts.
(defvar js3-prev-name-token-start nil)
(defvar js3-prev-name-token-string nil)

(defsubst js3-save-name-token-data (pos name)
  (setq js3-prev-name-token-start pos
        js3-prev-name-token-string name))

;; These flags enumerate the possible ways a statement/function can
;; terminate. These flags are used by endCheck() and by the Parser to
;; detect inconsistent return usage.
;;
;; END_UNREACHED is reserved for code paths that are assumed to always be
;; able to execute (example: throw, continue)
;;
;; END_DROPS_OFF indicates if the statement can transfer control to the
;; next one. Statement such as return dont. A compound statement may have
;; some branch that drops off control to the next statement.
;;
;; END_RETURNS indicates that the statement can return (without arguments)
;; END_RETURNS_VALUE indicates that the statement can return a value.
;;
;; A compound statement such as
;; if (condition) {
;;   return value;
;; }
;; Will be detected as (END_DROPS_OFF | END_RETURN_VALUE) by endCheck()

(defconst js3-end-unreached     #x0)
(defconst js3-end-drops-off     #x1)
(defconst js3-end-returns       #x2)
(defconst js3-end-returns-value #x4)
(defconst js3-end-yields        #x8)

;; Rhino awkwardly passes a statementLabel parameter to the
;; statementHelper() function, the main statement parser, which
;; is then used by quite a few of the sub-parsers.  We just make
;; it a buffer-local variable and make sure it's cleaned up properly.
(deflocal js3-labeled-stmt nil)  ; type `js3-labeled-stmt-node'

;; Similarly, Rhino passes an inForInit boolean through about half
;; the expression parsers.  We use a dynamically-scoped variable,
;; which makes it easier to funcall the parsers individually without
;; worrying about whether they take the parameter or not.
(deflocal js3-in-for-init nil)
(deflocal js3-temp-name-counter 0)
(deflocal js3-parse-stmt-count 0)

(defsubst js3-get-next-temp-name ()
  (format "$%d" (incf js3-temp-name-counter)))

(defvar js3-parse-interruptable-p t
  "Set this to nil to force parse to continue until finished.
This will mostly be useful for interpreters.")

(defvar js3-statements-per-pause 50
  "Pause after this many statements to check for user input.
If user input is pending, stop the parse and discard the tree.
This makes for a smoother user experience for large files.
You may have to wait a second or two before the highlighting
and error-reporting appear, but you can always type ahead if
you wish.  This appears to be more or less how Eclipse, IntelliJ
and other editors work.")

(deflocal js3-record-comments t
  "Instructs the scanner to record comments in `js3-scanned-comments'.")

(deflocal js3-scanned-comments nil
  "List of all comments from the current parse.")

(defun js3-underline-color (color)
  "Return a legal value for the :underline face attribute based on COLOR."
  ;; In XEmacs the :underline attribute can only be a boolean.
  ;; In GNU it can be the name of a colour.
  (if (featurep 'xemacs)
      (if color t nil)
    color))

(defface js3-warning-face
  `((((class color) (background light))
     (:underline ,(js3-underline-color "orange")))
    (((class color) (background dark))
     (:underline ,(js3-underline-color "orange")))
    (t (:underline t)))
  "Face for JavaScript warnings."
  :group 'js3-mode)

(defface js3-error-face
  `((((class color) (background light))
     (:foreground "red"))
    (((class color) (background dark))
     (:foreground "red"))
    (t (:foreground "red")))
  "Face for JavaScript errors."
  :group 'js3-mode)

(defface js3-jsdoc-tag-face
  '((t :foreground "SlateGray"))
  "Face used to highlight @whatever tags in jsdoc comments."
  :group 'js3-mode)

(defface js3-jsdoc-type-face
  '((t :foreground "SteelBlue"))
  "Face used to highlight {FooBar} types in jsdoc comments."
  :group 'js3-mode)

(defface js3-jsdoc-value-face
  '((t :foreground "PeachPuff3"))
  "Face used to highlight tag values in jsdoc comments."
  :group 'js3-mode)

(defface js3-function-param-face
  '((t :foreground "SeaGreen"))
  "Face used to highlight function parameters in javascript."
  :group 'js3-mode)

(defface js3-instance-member-face
  '((t :foreground "DarkOrchid"))
  "Face used to highlight instance variables in javascript.
Not currently used."
  :group 'js3-mode)

(defface js3-private-member-face
  '((t :foreground "PeachPuff3"))
  "Face used to highlight calls to private methods in javascript.
Not currently used."
  :group 'js3-mode)

(defface js3-private-function-call-face
  '((t :foreground "goldenrod"))
  "Face used to highlight calls to private functions in javascript.
Not currently used."
  :group 'js3-mode)

(defface js3-jsdoc-html-tag-name-face
  (if js3-emacs22
      '((((class color) (min-colors 88) (background light))
         (:foreground "rosybrown"))
        (((class color) (min-colors 8) (background dark))
         (:foreground "yellow"))
        (((class color) (min-colors 8) (background light))
         (:foreground "magenta")))
    '((((type tty pc) (class color) (background light))
       (:foreground "magenta"))
      (((type tty pc) (class color) (background dark))
       (:foreground "yellow"))
      (t (:foreground "RosyBrown"))))
  "Face used to highlight jsdoc html tag names"
  :group 'js3-mode)

(defface js3-jsdoc-html-tag-delimiter-face
  (if js3-emacs22
      '((((class color) (min-colors 88) (background light))
         (:foreground "dark khaki"))
        (((class color) (min-colors 8) (background dark))
         (:foreground "green"))
        (((class color) (min-colors 8) (background light))
         (:foreground "green")))
    '((((type tty pc) (class color) (background light))
       (:foreground "green"))
      (((type tty pc) (class color) (background dark))
       (:foreground "green"))
      (t (:foreground "dark khaki"))))
  "Face used to highlight brackets in jsdoc html tags."
  :group 'js3-mode)

(defface js3-magic-paren-face
  '((t :underline t))
  "Face used to color parens that will be auto-overwritten."
  :group 'js3-mode)

(defcustom js3-post-parse-callbacks nil
  "A list of callback functions invoked after parsing finishes.
Currently, the main use for this function is to add synthetic
declarations to `js3-recorded-identifiers', which see."
  :type 'list
  :group 'js3-mode)

(defface js3-external-variable-face
  '((t :foreground "orange"))
  "Face used to highlight undeclared variable identifiers.
An undeclared variable is any variable not declared with var or let
in the current scope or any lexically enclosing scope.  If you use
such a variable, then you are either expecting it to originate from
another file, or you've got a potential bug."
  :group 'js3-mode)

(defcustom js3-highlight-external-variables t
  "Non-nil to highlight assignments to undeclared variables."
  :type 'boolean
  :group 'js3-mode)

(defcustom js3-auto-insert-catch-block t
  "Non-nil to insert matching catch block on open-curly after `try'."
  :type 'boolean
  :group 'js3-mode)

(defcustom js3-indent-level 2
  "Number of spaces for each indentation step in `js3-mode'."
  :type 'integer
  :group 'js3-mode)
(js3-mark-safe-local 'js3-indent-level 'integerp)

(defcustom js3-expr-indent-offset 0
  "Number of additional spaces for indenting continued expressions.
The value must be no less than minus `js3-indent-level'."
  :type 'integer
  :group 'js3-mode)
(js3-mark-safe-local 'js3-expr-indent-offset 'integerp)

(defcustom js3-paren-indent-offset 0
  "Number of additional spaces for indenting expressions in parentheses.
The value must be no less than minus `js3-indent-level'."
  :type 'integer
  :group 'js3-mode
  :version "24.1")
(js3-mark-safe-local 'js3-paren-indent-offset 'integerp)

(defcustom js3-square-indent-offset 0
  "Number of additional spaces for indenting expressions in square braces.
The value must be no less than minus `js3-indent-level'."
  :type 'integer
  :group 'js3-mode
  :version "24.1")
(js3-mark-safe-local 'js3-square-indent-offset 'integerp)

(defcustom js3-curly-indent-offset 0
  "Number of additional spaces for indenting expressions in curly braces.
The value must be no less than minus `js3-indent-level'."
  :type 'integer
  :group 'js3-mode
  :version "24.1")
(js3-mark-safe-local 'js3-curly-indent-offset 'integerp)

(defcustom js3-label-indent-offset 0
  "Number of additional spaces for indenting labels.
The value must be no less than minus `js3-indent-level'."
  :type 'integer
  :group 'js3-mode
  :version "24.1")
(js3-mark-safe-local 'js3-label-indent-offset 'integerp)

(defcustom js3-comment-lineup-func #'c-lineup-C-comments
  "Lineup function for `cc-mode-style', for C comments in `js3-mode'."
  :type 'function
  :group 'js3-mode)

(defcustom js3-reparse-on-indent t
  "Whether `js3-mode' should perform a reparse before indenting.
Might be slow, but important for comma-first and operator-first style,
as well as pretty var statements."
  :type 'boolean
  :group 'js3-mode)
(js3-mark-safe-local 'js3-reparse-on-indent 'booleanp)

(defcustom js3-lazy-commas nil
  "Whether `js3-mode' should line up commas to the indent-minus-2,
rather than trying to line up to braces."
  :type 'boolean
  :group 'js3-mode)
(js3-mark-safe-local 'js3-lazy-commas 'booleanp)

(defcustom js3-lazy-semicolons nil
  "Whether `js3-mode' should line up semicolons to the indent-minus-2,
rather than trying to line up to braces, in for loop defs."
  :type 'boolean
  :group 'js3-mode)
(js3-mark-safe-local 'js3-lazy-semicolons 'booleanp)

(defcustom js3-lazy-operators nil
  "Whether `js3-mode' should line up operators to the indent-minus-2,
rather than trying to line up to braces."
  :type 'boolean
  :group 'js3-mode)
(js3-mark-safe-local 'js3-lazy-operators 'booleanp)

(defcustom js3-lazy-dots nil
  "Whether `js3-mode' should line up dots to the next indent level,
rather than trying to line up to dots."
  :type 'boolean
  :group 'js3-mode)
(js3-mark-safe-local 'js3-lazy-dots 'booleanp)

(defcustom js3-indent-dots nil
  "Whether `js3-mode' should line up dots at all"
  :type 'boolean
  :group 'js3-mode)
(js3-mark-safe-local 'js3-indent-dots 'booleanp)

(defcustom js3-dont-rebind-backtick nil
  "Whether `js3-mode' should bind C-c C-` to js3-next-error"
  :type 'boolean
  :group 'js3-mode)
(js3-mark-safe-local 'js3-dont-rebind-backtick 'booleanp)

(defvar js3-mode-map
  (let ((map (make-sparse-keymap))
        keys)
    (define-key map [mouse-1] #'js3-mode-show-node)
    (define-key map (kbd "C-m") #'js3-enter-key)
    (when js3-rebind-eol-bol-keys
      (define-key map (kbd "C-a") #'js3-beginning-of-line)
      (define-key map (kbd "C-e") #'js3-end-of-line))
    (define-key map (kbd "C-c C-e") #'js3-mode-hide-element)
    (define-key map (kbd "C-c C-s") #'js3-mode-show-element)
    (define-key map (kbd "C-c C-a") #'js3-mode-show-all)
    (define-key map (kbd "C-c C-f") #'js3-mode-toggle-hide-functions)
    (define-key map (kbd "C-c C-t") #'js3-mode-toggle-hide-comments)
    (define-key map (kbd "C-c C-o") #'js3-mode-toggle-element)
    (define-key map (kbd "C-c C-w") #'js3-mode-toggle-warnings-and-errors)
    (define-key map (kbd "C-c C-g") #'js3-add-to-globals)
    (when (not js3-dont-rebind-backtick)
      (define-key map (kbd "C-c C-`") #'js3-next-error))
    ;; also define user's preference for next-error, if available
    (if (setq keys (where-is-internal #'next-error))
        (define-key map (car keys) #'js3-next-error))
    (define-key map (or (car (where-is-internal #'mark-defun))
                        (kbd "M-C-h"))
      #'js3-mark-defun)
    (define-key map (or (car (where-is-internal #'narrow-to-defun))
                        (kbd "C-x nd"))
      #'js3-narrow-to-defun)
    (define-key map [down-mouse-3] #'js3-down-mouse-3)
    (when js3-auto-indent-p
      (mapc (lambda (key)
              (define-key map key #'js3-insert-and-indent))
            js3-electric-keys))

    (define-key map [menu-bar javascript]
      (cons "JavaScript" (make-sparse-keymap "JavaScript")))

    (define-key map [menu-bar javascript customize-js3-mode]
      '(menu-item "Customize js3-mode" js3-mode-customize
                  :help "Customize the behavior of this mode"))

    (define-key map [menu-bar javascript js3-force-refresh]
      '(menu-item "Force buffer refresh" js3-mode-reset
                  :help "Re-parse the buffer from scratch"))

    (define-key map [menu-bar javascript separator-2]
      '("--"))

    (define-key map [menu-bar javascript next-error]
      '(menu-item "Next warning or error" js3-next-error
                  :enabled (and js3-mode-ast
                                (or (js3-ast-root-errors js3-mode-ast)
                                    (js3-ast-root-warnings js3-mode-ast)))
                  :help "Move to next warning or error"))

    (define-key map [menu-bar javascript display-errors]
      '(menu-item "Show errors and warnings" js3-mode-display-warnings-and-errors
                  :visible (not js3-mode-show-parse-errors)
                  :help "Turn on display of warnings and errors"))

    (define-key map [menu-bar javascript hide-errors]
      '(menu-item "Hide errors and warnings" js3-mode-hide-warnings-and-errors
                  :visible js3-mode-show-parse-errors
                  :help "Turn off display of warnings and errors"))

    (define-key map [menu-bar javascript separator-1]
      '("--"))

    (define-key map [menu-bar javascript js3-toggle-function]
      '(menu-item "Show/collapse element" js3-mode-toggle-element
                  :help "Hide or show function body or comment"))

    (define-key map [menu-bar javascript show-comments]
      '(menu-item "Show block comments" js3-mode-toggle-hide-comments
                  :visible js3-mode-comments-hidden
                  :help "Expand all hidden block comments"))

    (define-key map [menu-bar javascript hide-comments]
      '(menu-item "Hide block comments" js3-mode-toggle-hide-comments
                  :visible (not js3-mode-comments-hidden)
                  :help "Show block comments as /*...*/"))

    (define-key map [menu-bar javascript show-all-functions]
      '(menu-item "Show function bodies" js3-mode-toggle-hide-functions
                  :visible js3-mode-functions-hidden
                  :help "Expand all hidden function bodies"))

    (define-key map [menu-bar javascript hide-all-functions]
      '(menu-item "Hide function bodies" js3-mode-toggle-hide-functions
                  :visible (not js3-mode-functions-hidden)
                  :help "Show {...} for all top-level function bodies"))

    map)
  "Keymap used in `js3-mode' buffers.")

(defconst js3-mode-identifier-re "[a-zA-Z_$][a-zA-Z0-9_$]*")

(defvar js3-mode-//-comment-re "^\\(\\s-*\\)//.+"
  "Matches a //-comment line.  Must be first non-whitespace on line.
First match-group is the leading whitespace.")

(defvar js3-mode-hook nil)

(deflocal js3-mode-ast nil "Private variable.")
(deflocal js3-mode-parse-timer nil "Private variable.")
(deflocal js3-mode-buffer-dirty-p nil "Private variable.")
(deflocal js3-mode-parsing nil "Private variable.")
(deflocal js3-mode-node-overlay nil)

(defvar js3-mode-show-overlay js3-mode-dev-mode-p
  "Debug:  Non-nil to highlight AST nodes on mouse-down.")

(deflocal js3-mode-fontifications nil "Private variable")
(deflocal js3-mode-deferred-properties nil "Private variable")
(deflocal js3-imenu-recorder nil "Private variable")
(deflocal js3-imenu-function-map nil "Private variable")

(defvar js3-paragraph-start
  "\\(@[a-zA-Z]+\\>\\|$\\)")

;; Note that we also set a 'c-in-sws text property in html comments,
;; so that `c-forward-sws' and `c-backward-sws' work properly.
(defvar js3-syntactic-ws-start
  "\\s \\|/[*/]\\|[\n\r]\\|\\\\[\n\r]\\|\\s!\\|<!--\\|^\\s-*-->")

(defvar js3-syntactic-ws-end
  "\\s \\|[\n\r/]\\|\\s!")

(defvar js3-syntactic-eol
  (concat "\\s *\\(/\\*[^*\n\r]*"
          "\\(\\*+[^*\n\r/][^*\n\r]*\\)*"
          "\\*+/\\s *\\)*"
          "\\(//\\|/\\*[^*\n\r]*"
          "\\(\\*+[^*\n\r/][^*\n\r]*\\)*$"
          "\\|\\\\$\\|$\\)")
  "Copied from java-mode.  Needed for some cc-engine functions.")

(defvar js3-comment-prefix-regexp
  "//+\\|\\**")

(defvar js3-comment-start-skip
  "\\(//+\\|/\\*+\\)\\s *")

(defvar js3-mode-verbose-parse-p js3-mode-dev-mode-p
  "Non-nil to emit status messages during parsing.")

(defvar js3-mode-functions-hidden nil "private variable")
(defvar js3-mode-comments-hidden nil "private variable")

(defvar js3-mode-syntax-table
  (let ((table (make-syntax-table)))
    (c-populate-syntax-table table)
    table)
  "Syntax table used in js3-mode buffers.")

(defvar js3-mode-abbrev-table nil
  "Abbrev table in use in `js3-mode' buffers.")
(define-abbrev-table 'js3-mode-abbrev-table ())

(defvar js3-mode-must-byte-compile (not js3-mode-dev-mode-p)
  "Non-nil to have `js3-mode' signal an error if not byte-compiled.")

(defvar js3-mode-pending-parse-callbacks nil
  "List of functions waiting to be notified that parse is finished.")

(defvar js3-mode-last-indented-line -1)

;; Printing variables
(defvar js3-multiln-case nil)
(defvar js3-looking-at-parent-for-update nil)
(defvar js3-node-found-for-update nil)
(defvar js3-node-for-update nil)
(defvar js3-pos-for-update 0)
(defvar js3-multiln nil)
(defvar js3-current-buffer nil)
(defvar js3-temp-buffer "js3-temp")

(eval-when-compile
  (defvar c-paragraph-start nil)
  (defvar c-paragraph-separate nil)
  (defvar c-syntactic-ws-start nil)
  (defvar c-syntactic-ws-end nil)
  (defvar c-syntactic-eol nil)
  (defvar running-xemacs nil)
  (defvar font-lock-mode nil)
  (defvar font-lock-keywords nil))

;; Workaround for buggy Emacs 21 behavior.
(eval-when-compile
  (if (< emacs-major-version 22)
      (defun c-setup-paragraph-variables () nil)))

(provide 'js3-vars)

;;; js3-vars.el ends here
