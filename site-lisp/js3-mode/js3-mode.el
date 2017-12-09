;;; js3-mode.el --- An improved JavaScript editing mode
;;;

;;; js3-head.el

;; Author:  Thom Blake (webmaster@thomblake.com)
;; Authors of historical versions:
;;  (espresso-mode) Karl Landstrom <karl.landstrom@brgeight.se>
;;  (js2-mode)      Steve Yegge (steve.yegge@gmail.com)
;;  (js-mode)       Daniel Colascione <dan.colascione@gmail.com>
;; With some code from: https://github.com/mooz/js2-mode/
;;
;; Keywords:  javascript languages

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2 of
;; the License, or (at your option) any later version.

;; This program is distributed in the hope that it will be
;; useful, but WITHOUT ANY WARRANTY; without even the implied
;; warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR
;; PURPOSE.  See the GNU General Public License for more details.

;; You should have received a copy of the GNU General Public
;; License along with this program; if not, write to the Free
;; Software Foundation, Inc., 59 Temple Place, Suite 330, Boston,
;; MA 02111-1307 USA

;;; Commentary:

;; This JavaScript editing mode supports:
;;
;;  - the full JavaScript language through version 1.8
;;  - support for most Rhino and SpiderMonkey extensions from 1.5 to 1.8
;;  - accurate syntax highlighting using a recursive-descent parser
;;  - syntax-error and strict-mode warning reporting
;;  - smart line-wrapping within comments (Emacs 22+) and strings
;;  - code folding:
;;    - show some or all function bodies as {...}
;;    - show some or all block comments as /*...*/
;;  - context-sensitive menu bar and popup menus
;;  - code browsing using the `imenu' package
;;  - typing helpers (e.g. inserting matching braces/parens)
;;  - many customization options
;;
;; It is only compatible with GNU Emacs versions 21 and higher (not XEmacs).
;;
;; Installation:
;;
;;  - put `js3.el' somewhere in your emacs load path
;;  - M-x byte-compile-file RET <path-to-js3.el> RET
;;    Note:  it will refuse to run unless byte-compiled
;;  - add these lines to your .emacs file:
;;    (autoload 'js3-mode "js3" nil t)
;;    (add-to-list 'auto-mode-alist '("\\.js$" . js3-mode))
;;
;; To customize how it works:
;;   M-x customize-group RET js3-mode RET
;;
;; The variable `js3-mode-version' is a date stamp.  When you upgrade
;; to a newer version, you must byte-compile the file again.
;;
;; Notes:
;;
;; This mode is different in many ways from standard Emacs language editing
;; modes, inasmuch as it attempts to be more like an IDE.  If this drives
;; you crazy, it IS possible to customize it to be more like other Emacs
;; editing modes.  Please customize the group `js3-mode' to see all of the
;; configuration options.
;;
;; Some of the functionality does not work in Emacs 21 -- upgrading to
;; Emacs 22 or higher will get you better results.  If you byte-compiled
;; js3.el with Emacs 21, you should re-compile it for Emacs 22.
;;
;; This mode does not yet work with "multi-mode" modes such as mmm-mode
;; and mumamo, although it could possibly be made to do so with some effort.
;; This means that js3-mode is currently only useful for editing JavaScript
;; files, and not for editing JavaScript within <script> tags or templates.
;;
;; Please submit bug reports to github at https://github.com/thomblake/js3-mode

;;; Code:

;;; js3-head.el ends here
;;; js3-externs.el -- external name definitions

(defvar js3-ecma-262-externs
  (mapcar 'symbol-name
          '(Array
            Boolean
            Date
            Error
            EvalError
            Function
            Infinity
            JSON
            Math
            NaN
            Number
            Object
            RangeError
            ReferenceError
            RegExp
            String
            SyntaxError
            TypeError
            URIError
            arguments
            decodeURI
            decodeURIComponent
            encodeURI
            encodeURIComponent
            escape
            eval
            isFinite
            isNaN
            parseFloat
            parseInt
            undefined
            unescape))
  "Ecma-262 externs.  Included in `js3-externs' by default.")

(defvar js3-browser-externs
  (mapcar 'symbol-name
          '(;; DOM level 1
            Attr
            CDATASection
            CharacterData
            Comment
            DOMException
            DOMImplementation
            Document
            DocumentFragment
            DocumentType
            Element
            Entity
            EntityReference
            ExceptionCode
            NamedNodeMap
            Node
            NodeList
            Notation
            ProcessingInstruction
            Text

            ;; DOM level 2
            HTMLAnchorElement
            HTMLAppletElement
            HTMLAreaElement
            HTMLBRElement
            HTMLBaseElement
            HTMLBaseFontElement
            HTMLBodyElement
            HTMLButtonElement
            HTMLCollection
            HTMLDListElement
            HTMLDirectoryElement
            HTMLDivElement
            HTMLDocument
            HTMLElement
            HTMLFieldSetElement
            HTMLFontElement
            HTMLFormElement
            HTMLFrameElement
            HTMLFrameSetElement
            HTMLHRElement
            HTMLHeadElement
            HTMLHeadingElement
            HTMLHtmlElement
            HTMLIFrameElement
            HTMLImageElement
            HTMLInputElement
            HTMLIsIndexElement
            HTMLLIElement
            HTMLLabelElement
            HTMLLegendElement
            HTMLLinkElement
            HTMLMapElement
            HTMLMenuElement
            HTMLMetaElement
            HTMLModElement
            HTMLOListElement
            HTMLObjectElement
            HTMLOptGroupElement
            HTMLOptionElement
            HTMLOptionsCollection
            HTMLParagraphElement
            HTMLParamElement
            HTMLPreElement
            HTMLQuoteElement
            HTMLScriptElement
            HTMLSelectElement
            HTMLStyleElement
            HTMLTableCaptionElement
            HTMLTableCellElement
            HTMLTableColElement
            HTMLTableElement
            HTMLTableRowElement
            HTMLTableSectionElement
            HTMLTextAreaElement
            HTMLTitleElement
            HTMLUListElement

            ;; DOM level 3
            DOMConfiguration
            DOMError
            DOMException
            DOMImplementationList
            DOMImplementationSource
            DOMLocator
            DOMStringList
            NameList
            TypeInfo
            UserDataHandler

            ;; Window
            window
            alert
            confirm
            document
            java
            navigator
            prompt
            screen
            self
            top

            ;; W3C CSS
            CSSCharsetRule
            CSSFontFace
            CSSFontFaceRule
            CSSImportRule
            CSSMediaRule
            CSSPageRule
            CSSPrimitiveValue
            CSSProperties
            CSSRule
            CSSRuleList
            CSSStyleDeclaration
            CSSStyleRule
            CSSStyleSheet
            CSSValue
            CSSValueList
            Counter
            DOMImplementationCSS
            DocumentCSS
            DocumentStyle
            ElementCSSInlineStyle
            LinkStyle
            MediaList
            RGBColor
            Rect
            StyleSheet
            StyleSheetList
            ViewCSS

            ;; W3C Event
            EventListener
            EventTarget
            Event
            DocumentEvent
            UIEvent
            MouseEvent
            MutationEvent
            KeyboardEvent

            ;; W3C Range
            DocumentRange
            Range
            RangeException

            ;; W3C XML
            XPathResult
            XMLHttpRequest
            ))
  "Browser externs.
You can cause these to be included or excluded with the custom
variable `js3-include-browser-externs'.")

(defvar js3-rhino-externs
  (mapcar 'symbol-name
          '(Packages
            importClass
            importPackage
            com
            org
            java

            ;; Global object (shell) externs
            defineClass
            deserialize
            doctest
            gc
            help
            load
            loadClass
            print
            quit
            readFile
            readUrl
            runCommand
            seal
            serialize
            spawn
            sync
            toint32
            version))
  "Mozilla Rhino externs.
Set `js3-include-rhino-externs' to t to include them.")

(defvar js3-gears-externs
  (mapcar 'symbol-name
          '(
            ;; finish me!
            ))
  "Google Gears externs.
Set `js3-include-gears-externs' to t to include them.")

(provide 'js3-externs)

;;; js3-externs.el ends here
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
;;; js3-util.el -- JavaScript utilities

;;; Code

(eval-when-compile
  (require 'cl))


;; Emacs21 compatibility, plus some stuff to avoid runtime dependency on CL

(unless (fboundp #'looking-back)
  (defun looking-back (regexp &optional limit greedy)
    "Return non-nil if text before point matches regular expression REGEXP.
Like `looking-at' except matches before point, and is slower.
LIMIT if non-nil speeds up the search by specifying a minimum
starting position, to avoid checking matches that would start
before LIMIT.

If GREEDY is non-nil, extend the match backwards as far as possible,
stopping when a single additional previous character cannot be part
of a match for REGEXP."
    (let ((start (point))
          (pos
           (save-excursion
             (and (re-search-backward (concat "\\(?:" regexp "\\)\\=") limit t)
                  (point)))))
      (if (and greedy pos)
          (save-restriction
            (narrow-to-region (point-min) start)
            (while (and (> pos (point-min))
                        (save-excursion
                          (goto-char pos)
                          (backward-char 1)
                          (looking-at (concat "\\(?:"  regexp "\\)\\'"))))
              (setq pos (1- pos)))
            (save-excursion
              (goto-char pos)
              (looking-at (concat "\\(?:"  regexp "\\)\\'")))))
      (not (null pos)))))

(unless (fboundp #'copy-overlay)
  (defun copy-overlay (o)
    "Return a copy of overlay O."
    (let ((o1 (make-overlay (overlay-start o) (overlay-end o)
                            ;; FIXME: there's no easy way to find the
                            ;; insertion-type of the two markers.
                            (overlay-buffer o)))
          (props (overlay-properties o)))
      (while props
        (overlay-put o1 (pop props) (pop props)))
      o1)))

(unless (fboundp #'remove-overlays)
  (defun remove-overlays (&optional beg end name val)
    "Clear BEG and END of overlays whose property NAME has value VAL.
Overlays might be moved and/or split.
BEG and END default respectively to the beginning and end of buffer."
    (unless beg (setq beg (point-min)))
    (unless end (setq end (point-max)))
    (if (< end beg)
        (setq beg (prog1 end (setq end beg))))
    (save-excursion
      (dolist (o (overlays-in beg end))
        (when (eq (overlay-get o name) val)
          ;; Either push this overlay outside beg...end
          ;; or split it to exclude beg...end
          ;; or delete it entirely (if it is contained in beg...end).
          (if (< (overlay-start o) beg)
              (if (> (overlay-end o) end)
                  (progn
                    (move-overlay (copy-overlay o)
                                  (overlay-start o) beg)
                    (move-overlay o end (overlay-end o)))
                (move-overlay o (overlay-start o) beg))
            (if (> (overlay-end o) end)
                (move-overlay o end (overlay-end o))
              (delete-overlay o))))))))

;; we don't want a runtime dependency on the CL package, so define
;; our own versions of these functions.

(defun js3-delete-if (predicate list)
  "Remove all items satisfying PREDICATE in LIST."
  (loop for item in list
        if (not (funcall predicate item))
        collect item))

(defun js3-position (element list)
  "Find 0-indexed position of ELEMENT in LIST comparing with `eq'.
Returns nil if element is not found in the list."
  (let ((count 0)
        found)
    (while (and list (not found))
      (if (eq element (car list))
          (setq found t)
        (setq count (1+ count)
              list (cdr list))))
    (if found count)))

(defun js3-find-if (predicate list)
  "Find first item satisfying PREDICATE in LIST."
  (let (result)
    (while (and list (not result))
      (if (funcall predicate (car list))
          (setq result (car list)))
      (setq list (cdr list)))
    result))

;;; end Emacs 21 compat

(defmacro js3-time (form)
  "Evaluate FORM, discard result, and return elapsed time in sec"
  (let ((beg (make-symbol "--js3-time-beg--"))
        (delta (make-symbol "--js3-time-end--")))
    `(let ((,beg (current-time))
           ,delta)
       ,form
       (/ (truncate (* (- (float-time (current-time))
                          (float-time ,beg))
                       10000))
          10000.0))))

(def-edebug-spec js3-time t)

(defsubst neq (expr1 expr2)
  "Return (not (eq expr1 expr2))."
  (not (eq expr1 expr2)))

(defsubst js3-same-line (pos)
  "Return t if POS is on the same line as current point."
  (and (>= pos (point-at-bol))
       (<= pos (point-at-eol))))

(defsubst js3-same-line-2 (p1 p2)
  "Return t if p1 is on the same line as p2."
  (save-excursion
    (goto-char p1)
    (js3-same-line p2)))

(defun js3-code-bug ()
  "Signal an error when we encounter an unexpected code path."
  (error "failed assertion"))

(defsubst js3-record-text-property (beg end prop value)
  "Record a text property to set when parsing finishes."
  (push (list beg end prop value) js3-mode-deferred-properties))

;; I'd like to associate errors with nodes, but for now the
;; easiest thing to do is get the context info from the last token.
(defsubst js3-record-parse-error (msg &optional arg pos len)
  (push (list (list msg arg)
              (or pos js3-token-beg)
              (or len (- js3-token-end js3-token-beg)))
        js3-parsed-errors))

(defsubst js3-report-error (msg &optional msg-arg pos len)
  "Signal a syntax error or record a parse error."
  (if js3-recover-from-parse-errors
      (js3-record-parse-error msg msg-arg pos len)
    (signal 'js3-syntax-error
            (list msg
                  js3-ts-lineno
                  (save-excursion
                    (goto-char js3-ts-cursor)
                    (current-column))
                  js3-ts-hit-eof))))

(defsubst js3-report-warning (msg &optional msg-arg pos len)
  (if js3-compiler-report-warning-as-error
      (js3-report-error msg msg-arg pos len)
    (push (list (list msg msg-arg)
                (or pos js3-token-beg)
                (or len (- js3-token-end js3-token-beg)))
          js3-parsed-warnings)))

(defsubst js3-add-strict-warning (msg-id &optional msg-arg beg end)
  (if js3-compiler-strict-mode
      (js3-report-warning msg-id msg-arg beg
                          (and beg end (- end beg)))))

(put 'js3-syntax-error 'error-conditions
     '(error syntax-error js3-syntax-error))
(put 'js3-syntax-error 'error-message "Syntax error")

(put 'js3-parse-error 'error-conditions
     '(error parse-error js3-parse-error))
(put 'js3-parse-error 'error-message "Parse error")

(defmacro js3-clear-flag (flags flag)
  `(setq ,flags (logand ,flags (lognot ,flag))))

(defmacro js3-set-flag (flags flag)
  "Logical-or FLAG into FLAGS."
  `(setq ,flags (logior ,flags ,flag)))

(defsubst js3-flag-set-p (flags flag)
  (/= 0 (logand flags flag)))

(defsubst js3-flag-not-set-p (flags flag)
  (zerop (logand flags flag)))

;; Stolen shamelessly from James Clark's nxml-mode.
(defmacro js3-with-unmodifying-text-property-changes (&rest body)
  "Evaluate BODY without any text property changes modifying the buffer.
Any text properties changes happen as usual but the changes are not treated as
modifications to the buffer."
  (let ((modified (make-symbol "modified")))
    `(let ((,modified (buffer-modified-p))
           (inhibit-read-only t)
           (inhibit-modification-hooks t)
           (buffer-undo-list t)
           (deactivate-mark nil)
           ;; Apparently these avoid file locking problems.
           (buffer-file-name nil)
           (buffer-file-truename nil))
       (unwind-protect
           (progn ,@body)
         (unless ,modified
           (restore-buffer-modified-p nil))))))

(put 'js3-with-unmodifying-text-property-changes 'lisp-indent-function 0)
(def-edebug-spec js3-with-unmodifying-text-property-changes t)

(defmacro js3-with-underscore-as-word-syntax (&rest body)
  "Evaluate BODY with the _ character set to be word-syntax."
  (let ((old-syntax (make-symbol "old-syntax")))
    `(let ((,old-syntax (string (char-syntax ?_))))
       (unwind-protect
           (progn
             (modify-syntax-entry ?_ "w" js3-mode-syntax-table)
             ,@body)
         (modify-syntax-entry ?_ ,old-syntax js3-mode-syntax-table)))))

(put 'js3-with-underscore-as-word-syntax 'lisp-indent-function 0)
(def-edebug-spec js3-with-underscore-as-word-syntax t)

(defmacro with-buffer (buf form)
  "Executes FORM in buffer BUF.
BUF can be a buffer name or a buffer object.
If the buffer doesn't exist, it's created."
  `(let ((buffer (gentemp)))
     (setq buffer
           (if (stringp ,buf)
               (get-buffer-create ,buf)
             ,buf))
     (save-excursion
       (set-buffer buffer)
       ,form)))

(defsubst char-is-uppercase (c)
  "Return t if C is an uppercase character.
Handles unicode and latin chars properly."
  (/= c (downcase c)))

(defsubst char-is-lowercase (c)
  "Return t if C is an uppercase character.
Handles unicode and latin chars properly."
  (/= c (upcase c)))

(put 'with-buffer 'lisp-indent-function 1)
(def-edebug-spec with-buffer t)

(provide 'js3-util)

;;; js3-util.el ends here
;;; js3-scan.el --- JavaScript scanner

;;; Commentary:

;; A port of Mozilla Rhino's scanner.
;; Corresponds to Rhino files Token.java and TokenStream.java.

;;; Code:


(eval-when-compile
  (require 'cl))

(defvar js3-tokens nil
  "List of all defined token names.")  ; initialized in `js3-token-names'

(defconst js3-token-names
  (let* ((names (make-vector js3-num-tokens -1))
         (case-fold-search nil)  ; only match js3-UPPER_CASE
         (syms (apropos-internal "^js3-\\(?:[A-Z_]+\\)")))
    (loop for sym in syms
          for i from 0
          do
          (unless (or (memq sym '(js3-EOF_CHAR js3-ERROR))
                      (not (boundp sym)))
            (aset names (symbol-value sym)         ; code, e.g. 152
                  (substring (symbol-name sym) 4)) ; name, e.g. "LET"
            (push sym js3-tokens)))
    names)
  "Vector mapping int values to token string names, sans `js3-' prefix.")

(defun js3-token-name (tok)
  "Return a string name for TOK, a token symbol or code.
Signals an error if it's not a recognized token."
  (let ((code tok))
    (if (symbolp tok)
        (setq code (symbol-value tok)))
    (if (eq code -1)
        "ERROR"
      (if (and (numberp code)
               (not (minusp code))
               (< code js3-num-tokens))
          (aref js3-token-names code)
        (error "Invalid token: %s" code)))))

(defsubst js3-token-sym (tok)
  "Return symbol for TOK given its code, e.g. 'js3-LP for code 86."
  (intern (js3-token-name tok)))

(defconst js3-token-codes
  (let ((table (make-hash-table :test 'eq :size 256)))
    (loop for name across js3-token-names
          for sym = (intern (concat "js3-" name))
          do
          (puthash sym (symbol-value sym) table))
    ;; clean up a few that are "wrong" in Rhino's token codes
    (puthash 'js3-DELETE js3-DELPROP table)
    table)
  "Hashtable mapping token symbols to their bytecodes.")

(defsubst js3-token-code (sym)
  "Return code for token symbol SYM, e.g. 86 for 'js3-LP."
  (or (gethash sym js3-token-codes)
      (error "Invalid token symbol: %s " sym)))  ; signal code bug

(defsubst js3-report-scan-error (msg &optional no-throw beg len)
  (setq js3-token-end js3-ts-cursor)
  (js3-report-error msg nil
                    (or beg js3-token-beg)
                    (or len (- js3-token-end js3-token-beg)))
  (unless no-throw
    (throw 'return js3-ERROR)))

(defsubst js3-get-string-from-buffer ()
  "Reverse the char accumulator and return it as a string."
  (setq js3-token-end js3-ts-cursor)
  (if js3-ts-string-buffer
      (apply #'string (nreverse js3-ts-string-buffer))
    ""))

;; TODO:  could potentially avoid a lot of consing by allocating a
;; char buffer the way Rhino does.
(defsubst js3-add-to-string (c)
  (push c js3-ts-string-buffer))

;; Note that when we "read" the end-of-file, we advance js3-ts-cursor
;; to (1+ (point-max)), which lets the scanner treat end-of-file like
;; any other character:  when it's not part of the current token, we
;; unget it, allowing it to be read again by the following call.
(defsubst js3-unget-char ()
  (decf js3-ts-cursor))

;; Rhino distinguishes \r and \n line endings.  We don't need to
;; because we only scan from Emacs buffers, which always use \n.
(defsubst js3-get-char ()
  "Read and return the next character from the input buffer.
Increments `js3-ts-lineno' if the return value is a newline char.
Updates `js3-ts-cursor' to the point after the returned char.
Returns `js3-EOF_CHAR' if we hit the end of the buffer.
Also updates `js3-ts-hit-eof' and `js3-ts-line-start' as needed."
  (let (c)
    ;; check for end of buffer
    (if (>= js3-ts-cursor (point-max))
        (setq js3-ts-hit-eof t
              js3-ts-cursor (1+ js3-ts-cursor)
              c js3-EOF_CHAR)  ; return value
      ;; otherwise read next char
      (setq c (char-before (incf js3-ts-cursor)))
      ;; if we read a newline, update counters
      (if (= c ?\n)
          (setq js3-ts-line-start js3-ts-cursor
                js3-ts-lineno (1+ js3-ts-lineno)))
      ;; TODO:  skip over format characters
      c)))

(defsubst js3-read-unicode-escape ()
  "Read a \\uNNNN sequence from the input.
Assumes the ?\ and ?u have already been read.
Returns the unicode character, or nil if it wasn't a valid character.
Doesn't change the values of any scanner variables."
  ;; I really wish I knew a better way to do this, but I can't
  ;; find the Emacs function that takes a 16-bit int and converts
  ;; it to a Unicode/utf-8 character.  So I basically eval it with (read).
  ;; Have to first check that it's 4 hex characters or it may stop
  ;; the read early.
  (ignore-errors
   (let ((s (buffer-substring-no-properties js3-ts-cursor
                                            (+ 4 js3-ts-cursor))))
     (if (string-match "[a-zA-Z0-9]\\{4\\}" s)
         (read (concat "?\\u" s))))))

(defsubst js3-match-char (test)
  "Consume and return next character if it matches TEST, a character.
Returns nil and consumes nothing if TEST is not the next character."
  (let ((c (js3-get-char)))
    (if (eq c test)
        t
      (js3-unget-char)
      nil)))

(defsubst js3-peek-char ()
  (prog1
      (js3-get-char)
    (js3-unget-char)))

(defsubst js3-java-identifier-start-p (c)
  (or
   (memq c '(?$ ?_))
   (char-is-uppercase c)
   (char-is-lowercase c)))

(defsubst js3-java-identifier-part-p (c)
  "Implementation of java.lang.Character.isJavaIdentifierPart()"
  ;; TODO:  make me Unicode-friendly.  See comments above.
  (or
   (memq c '(?$ ?_))
   (char-is-uppercase c)
   (char-is-lowercase c)
   (and (>= c ?0) (<= c ?9))))

(defsubst js3-alpha-p (c)
  (cond ((and (<= ?A c) (<= c ?Z)) t)
        ((and (<= ?a c) (<= c ?z)) t)
        (t nil)))

(defsubst js3-digit-p (c)
  (and (<= ?0 c) (<= c ?9)))

(defsubst js3-js-space-p (c)
  (if (<= c 127)
      (memq c '(#x20 #x9 #xB #xC #xD))
    (or
     (eq c #xA0)
     ;; TODO:  change this nil to check for Unicode space character
     nil)))

(defconst js3-eol-chars (list js3-EOF_CHAR ?\n ?\r))

(defsubst js3-skip-line ()
  "Skip to end of line"
  (let (c)
    (while (not (memq (setq c (js3-get-char)) js3-eol-chars)))
    (js3-unget-char)
    (setq js3-token-end js3-ts-cursor)))

(defun js3-init-scanner (&optional buf line)
  "Create token stream for BUF starting on LINE.
BUF defaults to current-buffer and line defaults to 1.

A buffer can only have one scanner active at a time, which yields
dramatically simpler code than using a defstruct.  If you need to
have simultaneous scanners in a buffer, copy the regions to scan
into temp buffers."
  (save-excursion
    (when buf
      (set-buffer buf))
    (setq js3-ts-dirty-line nil
          js3-ts-regexp-flags nil
          js3-ts-string ""
          js3-ts-number nil
          js3-ts-hit-eof nil
          js3-ts-line-start 0
          js3-ts-lineno (or line 1)
          js3-ts-line-end-char -1
          js3-ts-cursor (point-min)
          js3-ts-string-buffer nil)))

;; This function uses the cached op, string and number fields in
;; TokenStream; if getToken has been called since the passed token
;; was scanned, the op or string printed may be incorrect.
(defun js3-token-to-string (token)
  ;; Not sure where this function is used in Rhino.  Not tested.
  (if (not js3-debug-print-trees)
      ""
    (let ((name (js3-token-name token)))
      (cond
       ((memq token (list js3-STRING js3-REGEXP js3-NAME))
        (concat name " `" js3-ts-string "'"))
       ((eq token js3-NUMBER)
        (format "NUMBER %g" js3-ts-number))
       (t
        name)))))

(defconst js3-keywords
  '(break
    case catch const continue
    debugger default delete do
    else enum
    false finally for function
    if in instanceof import
    let
    new null
    return
    switch
    this throw true try typeof
    var void
    while with
    yield))

;; Token names aren't exactly the same as the keywords, unfortunately.
;; E.g. enum isn't in the tokens, and delete is js3-DELPROP.
(defconst js3-kwd-tokens
  (let ((table (make-vector js3-num-tokens nil))
        (tokens
         (list js3-BREAK
               js3-CASE js3-CATCH js3-CONST js3-CONTINUE
               js3-DEBUGGER js3-DEFAULT js3-DELPROP js3-DO
               js3-ELSE
               js3-FALSE js3-FINALLY js3-FOR js3-FUNCTION
               js3-IF js3-IN js3-INSTANCEOF js3-IMPORT
               js3-LET
               js3-NEW js3-NULL
               js3-RETURN
               js3-SWITCH
               js3-THIS js3-THROW js3-TRUE js3-TRY js3-TYPEOF
               js3-VAR
               js3-WHILE js3-WITH
               js3-YIELD)))
    (dolist (i tokens)
      (aset table i 'font-lock-keyword-face))
    (aset table js3-STRING 'font-lock-string-face)
    (aset table js3-REGEXP 'font-lock-string-face)
    (aset table js3-COMMENT 'font-lock-comment-face)
    (aset table js3-THIS 'font-lock-builtin-face)
    (aset table js3-VOID 'font-lock-constant-face)
    (aset table js3-NULL 'font-lock-constant-face)
    (aset table js3-TRUE 'font-lock-constant-face)
    (aset table js3-FALSE 'font-lock-constant-face)
    table)
  "Vector whose values are non-nil for tokens that are keywords.
The values are default faces to use for highlighting the keywords.")

(defconst js3-reserved-words
  '(abstract
    boolean byte
    char class
    double
    enum export extends
    final float
    goto
    implements import int interface
    long
    native
    package private protected public
    short static super synchronized
    throws transient
    volatile))

(defconst js3-keyword-names
  (let ((table (make-hash-table :test 'equal)))
    (loop for k in js3-keywords
          do (puthash
              (symbol-name k)                            ; instanceof
              (intern (concat "js3-"
                              (upcase (symbol-name k)))) ; js3-INSTANCEOF
              table))
    table)
  "JavaScript keywords by name, mapped to their symbols.")

(defconst js3-reserved-word-names
  (let ((table (make-hash-table :test 'equal)))
    (loop for k in js3-reserved-words
          do
          (puthash (symbol-name k) 'js3-RESERVED table))
    table)
  "JavaScript reserved words by name, mapped to 'js3-RESERVED.")

(defsubst js3-collect-string (buf)
  "Convert BUF, a list of chars, to a string.
Reverses BUF before converting."
  (cond
   ((stringp buf)
    buf)
   ((null buf)  ; for emacs21 compat
    "")
   (t
    (if buf
        (apply #'string (nreverse buf))
      ""))))

(defun js3-string-to-keyword (s)
  "Return token for S, a string, if S is a keyword or reserved word.
Returns a symbol such as 'js3-BREAK, or nil if not keyword/reserved."
  (or (gethash s js3-keyword-names)
      (gethash s js3-reserved-word-names)))

(defsubst js3-ts-set-char-token-bounds ()
  "Used when next token is one character."
  (setq js3-token-beg (1- js3-ts-cursor)
        js3-token-end js3-ts-cursor))

(defsubst js3-ts-return (token)
  "Return an N-character TOKEN from `js3-get-token'.
Updates `js3-token-end' accordingly."
  (setq js3-token-end js3-ts-cursor)
  (throw 'return token))

(defsubst js3-x-digit-to-int (c accumulator)
  "Build up a hex number.
If C is a hexadecimal digit, return ACCUMULATOR * 16 plus
corresponding number.  Otherwise return -1."
  (catch 'return
    (catch 'check
      ;; Use 0..9 < A..Z < a..z
      (cond
       ((<= c ?9)
        (decf c ?0)
        (if (<= 0 c)
            (throw 'check nil)))
       ((<= c ?F)
        (when (<= ?A c)
          (decf c (- ?A 10))
          (throw 'check nil)))
       ((<= c ?f)
        (when (<= ?a c)
          (decf c (- ?a 10))
          (throw 'check nil))))
      (throw 'return -1))
    (logior c (lsh accumulator 4))))

(defun js3-get-token ()
  "Return next JavaScript token, an int such as js3-RETURN."
  (let (c
        c1
        identifier-start
        is-unicode-escape-start
        contains-escape
        escape-val
        escape-start
        str
        result
        base
        is-integer
        quote-char
        val
        look-for-slash
        continue)
    (catch 'return
      (while t
        ;; Eat whitespace, possibly sensitive to newlines.
        (setq continue t)
        (while continue
          (setq c (js3-get-char))
          (cond
           ((eq c js3-EOF_CHAR)
            (js3-ts-set-char-token-bounds)
            (throw 'return js3-EOF))
           ((eq c ?\n)
            (js3-ts-set-char-token-bounds)
            (setq js3-ts-dirty-line nil)
            (throw 'return js3-EOL))
           ((not (js3-js-space-p c))
            (if (/= c ?-)               ; in case end of HTML comment
                (setq js3-ts-dirty-line t))
            (setq continue nil))))
        ;; Assume the token will be 1 char - fixed up below.
        (js3-ts-set-char-token-bounds)
        ;; identifier/keyword/instanceof?
        ;; watch out for starting with a <backslash>
        (cond
         ((eq c ?\\)
          (setq c (js3-get-char))
          (if (eq c ?u)
              (setq identifier-start t
                    is-unicode-escape-start t
                    js3-ts-string-buffer nil)
            (setq identifier-start nil)
            (js3-unget-char)
            (setq c ?\\)))
         (t
          (when (setq identifier-start (js3-java-identifier-start-p c))
            (setq js3-ts-string-buffer nil)
            (js3-add-to-string c))))
        (when identifier-start
          (setq contains-escape is-unicode-escape-start)
          (catch 'break
            (while t
              (if is-unicode-escape-start
                  ;; strictly speaking we should probably push-back
                  ;; all the bad characters if the <backslash>uXXXX
                  ;; sequence is malformed. But since there isn't a
                  ;; correct context(is there?) for a bad Unicode
                  ;; escape sequence in an identifier, we can report
                  ;; an error here.
                  (progn
                    (setq escape-val 0)
                    (dotimes (i 4)
                      (setq c (js3-get-char)
                            escape-val (js3-x-digit-to-int c escape-val))
                      ;; Next check takes care of c < 0 and bad escape
                      (if (minusp escape-val)
                          (throw 'break nil)))
                    (if (minusp escape-val)
                        (js3-report-scan-error "msg.invalid.escape" t))
                    (js3-add-to-string escape-val)
                    (setq is-unicode-escape-start nil))
                (setq c (js3-get-char))
                (cond
                 ((eq c ?\\)
                  (setq c (js3-get-char))
                  (if (eq c ?u)
                      (setq is-unicode-escape-start t
                            contains-escape t)
                    (js3-report-scan-error "msg.illegal.character" t)))
                 (t
                  (if (or (eq c js3-EOF_CHAR)
                          (not (js3-java-identifier-part-p c)))
                      (throw 'break nil))
                  (js3-add-to-string c))))))
          (js3-unget-char)
          (setq str (js3-get-string-from-buffer))
          (unless contains-escape
            ;; OPT we shouldn't have to make a string (object!) to
            ;; check if it's a keyword.
            ;; Return the corresponding token if it's a keyword
            (when (setq result (js3-string-to-keyword str))
              (if (and (< js3-language-version 170)
                       (memq result '(js3-LET js3-YIELD)))
                  ;; LET and YIELD are tokens only in 1.7 and later
                  (setq result 'js3-NAME))
              (if (neq result 'js3-RESERVED)
                  (throw 'return (js3-token-code result)))
              (js3-report-warning "msg.reserved.keyword" str)))
          ;; If we want to intern these as Rhino does, just use (intern str)
          (setq js3-ts-string str)
          (throw 'return js3-NAME))     ; end identifier/kwd check
        ;; is it a number?
        (when (or (js3-digit-p c)
                  (and (eq c ?.) (js3-digit-p (js3-peek-char))))
          (setq js3-ts-string-buffer nil
                base 10)
          (when (eq c ?0)
            (setq c (js3-get-char))
            (cond
             ((or (eq c ?x) (eq c ?X))
              (setq base 16)
              (setq c (js3-get-char)))
             ((js3-digit-p c)
              (setq base 8))
             (t
              (js3-add-to-string ?0))))
          (if (eq base 16)
              (while (<= 0 (js3-x-digit-to-int c 0))
                (js3-add-to-string c)
                (setq c (js3-get-char)))
            (while (and (<= ?0 c) (<= c ?9))
              ;; We permit 08 and 09 as decimal numbers, which
              ;; makes our behavior a superset of the ECMA
              ;; numeric grammar.  We might not always be so
              ;; permissive, so we warn about it.
              (when (and (eq base 8) (>= c ?8))
                (js3-report-warning "msg.bad.octal.literal"
                                    (if (eq c ?8) "8" "9"))
                (setq base 10))
              (js3-add-to-string c)
              (setq c (js3-get-char))))
          (setq is-integer t)
          (when (and (eq base 10) (memq c '(?. ?e ?E)))
            (setq is-integer nil)
            (when (eq c ?.)
              (loop do
                    (js3-add-to-string c)
                    (setq c (js3-get-char))
                    while (js3-digit-p c)))
            (when (memq c '(?e ?E))
              (js3-add-to-string c)
              (setq c (js3-get-char))
              (when (memq c '(?+ ?-))
                (js3-add-to-string c)
                (setq c (js3-get-char)))
              (unless (js3-digit-p c)
                (js3-report-scan-error "msg.missing.exponent" t))
              (loop do
                    (js3-add-to-string c)
                    (setq c (js3-get-char))
                    while (js3-digit-p c))))
          (js3-unget-char)
          (setq js3-ts-string (js3-get-string-from-buffer)
                js3-ts-number
                (if (and (eq base 10) (not is-integer))
                    (string-to-number js3-ts-string)
                  ;; TODO:  call runtime number-parser.  Some of it is in
                  ;; js3-util.el, but I need to port ScriptRuntime.stringToNumber.
                  (string-to-number js3-ts-string)))
          (throw 'return js3-NUMBER))
        ;; is it a string?
        (when (memq c '(?\" ?\'))
          ;; We attempt to accumulate a string the fast way, by
          ;; building it directly out of the reader.  But if there
          ;; are any escaped characters in the string, we revert to
          ;; building it out of a string buffer.
          (setq quote-char c
                js3-ts-string-buffer nil
                c (js3-get-char))
          (catch 'break
            (while (/= c quote-char)
              (catch 'continue
                (when (or (eq c ?\n) (eq c js3-EOF_CHAR))
                  (js3-unget-char)
                  (setq js3-token-end js3-ts-cursor)
                  (js3-report-error "msg.unterminated.string.lit")
                  (throw 'return js3-STRING))
                (when (eq c ?\\)
                  ;; We've hit an escaped character
                  (setq c (js3-get-char))
                  (case c
                        (?b (setq c ?\b))
                        (?f (setq c ?\f))
                        (?n (setq c ?\n))
                        (?r (setq c ?\r))
                        (?t (setq c ?\t))
                        (?v (setq c ?\v))
                        (?u
                         (setq c1 (js3-read-unicode-escape))
                         (if js3-parse-ide-mode
                             (if c1
                                 (progn
                                   ;; just copy the string in IDE-mode
                                   (js3-add-to-string ?\\)
                                   (js3-add-to-string ?u)
                                   (dotimes (i 3)
                                     (js3-add-to-string (js3-get-char)))
                                   (setq c (js3-get-char))) ; added at end of loop
                               ;; flag it as an invalid escape
                               (js3-report-warning "msg.invalid.escape"
                                                   nil (- js3-ts-cursor 2) 6))
                           ;; Get 4 hex digits; if the u escape is not
                           ;; followed by 4 hex digits, use 'u' + the
                           ;; literal character sequence that follows.
                           (js3-add-to-string ?u)
                           (setq escape-val 0)
                           (dotimes (i 4)
                             (setq c (js3-get-char)
                                   escape-val (js3-x-digit-to-int c escape-val))
                             (if (minusp escape-val)
                                 (throw 'continue nil))
                             (js3-add-to-string c))
                           ;; prepare for replace of stored 'u' sequence by escape value
                           (setq js3-ts-string-buffer (nthcdr 5 js3-ts-string-buffer)
                                 c escape-val)))
                        (?x
                         ;; Get 2 hex digits, defaulting to 'x'+literal
                         ;; sequence, as above.
                         (setq c (js3-get-char)
                               escape-val (js3-x-digit-to-int c 0))
                         (if (minusp escape-val)
                             (progn
                               (js3-add-to-string ?x)
                               (throw 'continue nil))
                           (setq c1 c
                                 c (js3-get-char)
                                 escape-val (js3-x-digit-to-int c escape-val))
                           (if (minusp escape-val)
                               (progn
                                 (js3-add-to-string ?x)
                                 (js3-add-to-string c1)
                                 (throw 'continue nil))
                             ;; got 2 hex digits
                             (setq c escape-val))))
                        (?\n
                         ;; Remove line terminator after escape to follow
                         ;; SpiderMonkey and C/C++
                         (setq c (js3-get-char))
                         (throw 'continue nil))
                        (t
                         (when (and (<= ?0 c) (< c ?8))
                           (setq val (- c ?0)
                                 c (js3-get-char))
                           (when (and (<= ?0 c) (< c ?8))
                             (setq val (- (+ (* 8 val) c) ?0)
                                   c (js3-get-char))
                             (when (and (<= ?0 c)
                                        (< c ?8)
                                        (< val #o37))
                               ;; c is 3rd char of octal sequence only
                               ;; if the resulting val <= 0377
                               (setq val (- (+ (* 8 val) c) ?0)
                                     c (js3-get-char))))
                           (js3-unget-char)
                           (setq c val)))))
                (js3-add-to-string c)
                (setq c (js3-get-char)))))
          (setq js3-ts-string (js3-get-string-from-buffer))
          (throw 'return js3-STRING))
        (case c
              (?\;
               (throw 'return js3-SEMI))
              (?\[
               (throw 'return js3-LB))
              (?\]
               (throw 'return js3-RB))
              (?{
               (throw 'return js3-LC))
              (?}
               (throw 'return js3-RC))
              (?\(
               (throw 'return js3-LP))
              (?\)
               (throw 'return js3-RP))
              (?,
               (throw 'return js3-COMMA))
              (??
               (throw 'return js3-HOOK))
              (?:
               (throw 'return js3-COLON))
              (?.
               (throw 'return js3-DOT))
              (?|
               (if (js3-match-char ?|)
                   (throw 'return js3-OR)
                 (if (js3-match-char ?=)
                     (js3-ts-return js3-ASSIGN_BITOR)
                   (throw 'return js3-BITOR))))
              (?^
               (if (js3-match-char ?=)
                   (js3-ts-return js3-ASSIGN_BITOR)
                 (throw 'return js3-BITXOR)))
              (?&
               (if (js3-match-char ?&)
                   (throw 'return js3-AND)
                 (if (js3-match-char ?=)
                     (js3-ts-return js3-ASSIGN_BITAND)
                   (throw 'return js3-BITAND))))
              (?=
               (if (js3-match-char ?=)
                   (if (js3-match-char ?=)
                       (js3-ts-return js3-SHEQ)
                     (throw 'return js3-EQ))
                 (throw 'return js3-ASSIGN)))
              (?!
               (if (js3-match-char ?=)
                   (if (js3-match-char ?=)
                       (js3-ts-return js3-SHNE)
                     (js3-ts-return js3-NE))
                 (throw 'return js3-NOT)))
              (?<
               ;; NB:treat HTML begin-comment as comment-till-eol
               (when (js3-match-char ?!)
                 (when (js3-match-char ?-)
                   (when (js3-match-char ?-)
                     (js3-skip-line)
                     (setq js3-ts-comment-type 'html)
                     (throw 'return js3-COMMENT)))
                 (js3-unget-char))
               (if (js3-match-char ?<)
                   (if (js3-match-char ?=)
                       (js3-ts-return js3-ASSIGN_LSH)
                     (js3-ts-return js3-LSH))
                 (if (js3-match-char ?=)
                     (js3-ts-return js3-LE)
                   (throw 'return js3-LT))))
              (?>
               (if (js3-match-char ?>)
                   (if (js3-match-char ?>)
                       (if (js3-match-char ?=)
                           (js3-ts-return js3-ASSIGN_URSH)
                         (js3-ts-return js3-URSH))
                     (if (js3-match-char ?=)
                         (js3-ts-return js3-ASSIGN_RSH)
                       (js3-ts-return js3-RSH)))
                 (if (js3-match-char ?=)
                     (js3-ts-return js3-GE)
                   (throw 'return js3-GT))))
              (?*
               (if (js3-match-char ?=)
                   (js3-ts-return js3-ASSIGN_MUL)
                 (throw 'return js3-MUL)))
              (?/
               ;; is it a // comment?
               (when (js3-match-char ?/)
                 (setq js3-token-beg (- js3-ts-cursor 2))
                 (js3-skip-line)
                 (setq js3-ts-comment-type 'line)
                 ;; include newline so highlighting goes to end of window
                 (incf js3-token-end)
                 (throw 'return js3-COMMENT))
               ;; is it a /* comment?
               (when (js3-match-char ?*)
                 (setq look-for-slash nil
                       js3-token-beg (- js3-ts-cursor 2)
                       js3-ts-comment-type
                       (if (js3-match-char ?*)
                           (progn
                             (setq look-for-slash t)
                             'jsdoc)
                         'block))
                 (while t
                   (setq c (js3-get-char))
                   (cond
                    ((eq c js3-EOF_CHAR)
                     (setq js3-token-end (1- js3-ts-cursor))
                     (js3-report-error "msg.unterminated.comment")
                     (throw 'return js3-COMMENT))
                    ((eq c ?*)
                     (setq look-for-slash t))
                    ((eq c ?/)
                     (if look-for-slash
                         (js3-ts-return js3-COMMENT)))
                    (t
                     (setq look-for-slash nil
                           js3-token-end js3-ts-cursor)))))
               (if (js3-match-char ?=)
                   (js3-ts-return js3-ASSIGN_DIV)
                 (throw 'return js3-DIV)))
              (?#
               (when js3-skip-preprocessor-directives
                 (js3-skip-line)
                 (setq js3-ts-comment-type 'preprocessor
                       js3-token-end js3-ts-cursor)
                 (throw 'return js3-COMMENT))
               (throw 'return js3-ERROR))
              (?%
               (if (js3-match-char ?=)
                   (js3-ts-return js3-ASSIGN_MOD)
                 (throw 'return js3-MOD)))
              (?~
               (throw 'return js3-BITNOT))
              (?+
               (if (js3-match-char ?=)
                   (js3-ts-return js3-ASSIGN_ADD)
                 (if (js3-match-char ?+)
                     (js3-ts-return js3-INC)
                   (throw 'return js3-ADD))))
              (?-
               (cond
                ((js3-match-char ?=)
                 (setq c js3-ASSIGN_SUB))
                ((js3-match-char ?-)
                 (unless js3-ts-dirty-line
                   ;; treat HTML end-comment after possible whitespace
                   ;; after line start as comment-until-eol
                   (when (js3-match-char ?>)
                     (js3-skip-line)
                     (setq js3-ts-comment-type 'html)
                     (throw 'return js3-COMMENT)))
                 (setq c js3-DEC))
                (t
                 (setq c js3-SUB)))
               (setq js3-ts-dirty-line t)
               (js3-ts-return c))
              (otherwise
               (js3-report-scan-error "msg.illegal.character")))))))

(defun js3-read-regexp (start-token)
  "Called by parser when it gets / or /= in literal context."
  (let (c
        err
        in-class  ; inside a '[' .. ']' character-class
        flags
        (continue t))
    (setq js3-token-beg js3-ts-cursor
          js3-ts-string-buffer nil
          js3-ts-regexp-flags nil)
    (if (eq start-token js3-ASSIGN_DIV)
        ;; mis-scanned /=
        (js3-add-to-string ?=)
      (if (neq start-token js3-DIV)
          (error "failed assertion")))
    (while (and (not err)
                (or (/= (setq c (js3-get-char)) ?/)
                    in-class))
      (cond
       ((or (= c ?\n)
            (= c js3-EOF_CHAR))
        (setq js3-token-end (1- js3-ts-cursor)
              err t
              js3-ts-string (js3-collect-string js3-ts-string-buffer))
        (js3-report-error "msg.unterminated.re.lit"))
       (t (cond
           ((= c ?\\)
            (js3-add-to-string c)
            (setq c (js3-get-char)))
           ((= c ?\[)
            (setq in-class t))
           ((= c ?\])
            (setq in-class nil)))
          (js3-add-to-string c))))
    (unless err
      (while continue
        (cond
         ((js3-match-char ?g)
          (push ?g flags))
         ((js3-match-char ?i)
          (push ?i flags))
         ((js3-match-char ?m)
          (push ?m flags))
         (t
          (setq continue nil))))
      (if (js3-alpha-p (js3-peek-char))
          (js3-report-scan-error "msg.invalid.re.flag" t
                                 js3-ts-cursor 1))
      (setq js3-ts-string (js3-collect-string js3-ts-string-buffer)
            js3-ts-regexp-flags (js3-collect-string flags)
            js3-token-end js3-ts-cursor)
      ;; tell `parse-partial-sexp' to ignore this range of chars
      (js3-record-text-property
       js3-token-beg js3-token-end 'syntax-class '(2)))))

(defun js3-scanner-get-line ()
  "Return the text of the current scan line."
  (buffer-substring (point-at-bol) (point-at-eol)))

(provide 'js3-scan)

;;; js3-scan.el ends here
;;; js3-messages:  localizable messages for js3-mode

;;; Commentary:

;; Messages are copied from Rhino's Messages.properties.
;; Many of the Java-specific messages have been elided.
;; Add any js3-specific ones at the end, so we can keep
;; this file synced with changes to Rhino's.
;;
;; TODO:
;;  - move interpreter messages into separate file

;;; Code:

(defvar js3-message-table
  (make-hash-table :test 'equal :size 250)
  "Contains localized messages for js3-mode.")

;; TODO:  construct this hashtable at compile-time.
(defmacro js3-msg (key &rest strings)
  `(puthash ,key (funcall #'concat ,@strings)
            js3-message-table))

(defun js3-get-msg (msg-key)
  "Look up a localized message.
MSG-KEY is a list of (MSG ARGS).  If the message takes parameters,
the correct number of ARGS must be provided."
  (let* ((key (if (listp msg-key) (car msg-key) msg-key))
         (args (if (listp msg-key) (cdr msg-key)))
         (msg (gethash key js3-message-table)))
    (if msg
        (apply #'format msg args)
      key)))  ; default to showing the key

(js3-msg "msg.dup.parms"
         "Duplicate parameter name '%s'.")

(js3-msg "msg.too.big.jump"
         "Program too complex: jump offset too big.")

(js3-msg "msg.too.big.index"
         "Program too complex: internal index exceeds 64K limit.")

(js3-msg "msg.while.compiling.fn"
         "Encountered code generation error while compiling function '%s': %s")

(js3-msg "msg.while.compiling.script"
         "Encountered code generation error while compiling script: %s")

;; Context
(js3-msg "msg.ctor.not.found"
         "Constructor for '%s' not found.")

(js3-msg "msg.not.ctor"
         "'%s' is not a constructor.")

;; FunctionObject
(js3-msg "msg.varargs.ctor"
         "Method or constructor '%s' must be static "
         "with the signature (Context cx, Object[] args, "
         "Function ctorObj, boolean inNewExpr) "
         "to define a variable arguments constructor.")

(js3-msg "msg.varargs.fun"
         "Method '%s' must be static with the signature "
         "(Context cx, Scriptable thisObj, Object[] args, Function funObj) "
         "to define a variable arguments function.")

(js3-msg "msg.incompat.call"
         "Method '%s' called on incompatible object.")

(js3-msg "msg.bad.parms"
         "Unsupported parameter type '%s' in method '%s'.")

(js3-msg "msg.bad.method.return"
         "Unsupported return type '%s' in method '%s'.")

(js3-msg "msg.bad.ctor.return"
         "Construction of objects of type '%s' is not supported.")

(js3-msg "msg.no.overload"
         "Method '%s' occurs multiple times in class '%s'.")

(js3-msg "msg.method.not.found"
         "Method '%s' not found in '%s'.")

;; IRFactory

(js3-msg "msg.bad.for.in.lhs"
         "Invalid left-hand side of for..in loop.")

(js3-msg "msg.mult.index"
         "Only one variable allowed in for..in loop.")

(js3-msg "msg.bad.for.in.destruct"
         "Left hand side of for..in loop must be an array of "
         "length 2 to accept key/value pair.")

(js3-msg "msg.cant.convert"
         "Can't convert to type '%s'.")

(js3-msg "msg.bad.assign.left"
         "Invalid assignment left-hand side.")

(js3-msg "msg.bad.decr"
         "Invalid decerement operand.")

(js3-msg "msg.bad.incr"
         "Invalid increment operand.")

(js3-msg "msg.bad.yield"
         "yield must be in a function.")

(js3-msg "msg.yield.parenthesized"
         "yield expression must be parenthesized.")

;; NativeGlobal
(js3-msg "msg.cant.call.indirect"
         "Function '%s' must be called directly, and not by way of a "
         "function of another name.")

(js3-msg "msg.eval.nonstring"
         "Calling eval() with anything other than a primitive "
         "string value will simply return the value. "
         "Is this what you intended?")

(js3-msg "msg.eval.nonstring.strict"
         "Calling eval() with anything other than a primitive "
         "string value is not allowed in strict mode.")

(js3-msg "msg.bad.destruct.op"
         "Invalid destructuring assignment operator")

;; NativeCall
(js3-msg "msg.only.from.new"
         "'%s' may only be invoked from a `new' expression.")

(js3-msg "msg.deprec.ctor"
         "The '%s' constructor is deprecated.")

;; NativeFunction
(js3-msg "msg.no.function.ref.found"
         "no source found to decompile function reference %s")

(js3-msg "msg.arg.isnt.array"
         "second argument to Function.prototype.apply must be an array")

;; NativeGlobal
(js3-msg "msg.bad.esc.mask"
         "invalid string escape mask")

;; NativeRegExp
(js3-msg "msg.bad.quant"
         "Invalid quantifier %s")

(js3-msg "msg.overlarge.backref"
         "Overly large back reference %s")

(js3-msg "msg.overlarge.min"
         "Overly large minimum %s")

(js3-msg "msg.overlarge.max"
         "Overly large maximum %s")

(js3-msg "msg.zero.quant"
         "Zero quantifier %s")

(js3-msg "msg.max.lt.min"
         "Maximum %s less than minimum")

(js3-msg "msg.unterm.quant"
         "Unterminated quantifier %s")

(js3-msg "msg.unterm.paren"
         "Unterminated parenthetical %s")

(js3-msg "msg.unterm.class"
         "Unterminated character class %s")

(js3-msg "msg.bad.range"
         "Invalid range in character class.")

(js3-msg "msg.trail.backslash"
         "Trailing \\ in regular expression.")

(js3-msg "msg.re.unmatched.right.paren"
         "unmatched ) in regular expression.")

(js3-msg "msg.no.regexp"
         "Regular expressions are not available.")

(js3-msg "msg.bad.backref"
         "back-reference exceeds number of capturing parentheses.")

(js3-msg "msg.bad.regexp.compile"
         "Only one argument may be specified if the first "
         "argument to RegExp.prototype.compile is a RegExp object.")

;; Parser
(js3-msg "msg.got.syntax.errors"
         "Compilation produced %s syntax errors.")

(js3-msg "msg.var.redecl"
         "TypeError: redeclaration of var %s.")

(js3-msg "msg.const.redecl"
         "TypeError: redeclaration of const %s.")

(js3-msg "msg.let.redecl"
         "TypeError: redeclaration of variable %s.")

(js3-msg "msg.parm.redecl"
         "TypeError: redeclaration of formal parameter %s.")

(js3-msg "msg.fn.redecl"
         "TypeError: redeclaration of function %s.")

(js3-msg "msg.let.decl.not.in.block"
         "SyntaxError: let declaration not directly within block")

;; NodeTransformer
(js3-msg "msg.dup.label"
         "duplicated label")

(js3-msg "msg.undef.label"
         "undefined label")

(js3-msg "msg.bad.break"
         "unlabelled break must be inside loop or switch")

(js3-msg "msg.continue.outside"
         "continue must be inside loop")

(js3-msg "msg.continue.nonloop"
         "continue can only use labels of iteration statements")

(js3-msg "msg.bad.throw.eol"
         "Line terminator is not allowed between the throw "
         "keyword and throw expression.")

(js3-msg "msg.no.paren.parms"
         "missing ( before function parameters.")

(js3-msg "msg.no.parm"
         "missing formal parameter")

(js3-msg "msg.no.paren.after.parms"
         "missing ) after formal parameters")

(js3-msg "msg.no.brace.body"
         "missing '{' before function body")

(js3-msg "msg.no.brace.after.body"
         "missing } after function body")

(js3-msg "msg.no.paren.cond"
         "missing ( before condition")

(js3-msg "msg.no.paren.after.cond"
         "missing ) after condition")

(js3-msg "msg.no.semi.stmt"
         "missing ; before statement")

(js3-msg "msg.missing.semi"
         "missing ; after statement")

(js3-msg "msg.no.name.after.dot"
         "missing name after . operator")

(js3-msg "msg.no.bracket.index"
         "missing ] in index expression")

(js3-msg "msg.no.paren.switch"
         "missing ( before switch expression")

(js3-msg "msg.no.paren.after.switch"
         "missing ) after switch expression")

(js3-msg "msg.no.brace.switch"
         "missing '{' before switch body")

(js3-msg "msg.bad.switch"
         "invalid switch statement")

(js3-msg "msg.no.colon.case"
         "missing : after case expression")

(js3-msg "msg.double.switch.default"
         "double default label in the switch statement")

(js3-msg "msg.no.while.do"
         "missing while after do-loop body")

(js3-msg "msg.no.paren.for"
         "missing ( after for")

(js3-msg "msg.no.semi.for"
         "missing ; after for-loop initializer")

(js3-msg "msg.no.semi.for.cond"
         "missing ; after for-loop condition")

(js3-msg "msg.in.after.for.name"
         "missing in after for")

(js3-msg "msg.no.paren.for.ctrl"
         "missing ) after for-loop control")

(js3-msg "msg.no.paren.with"
         "missing ( before with-statement object")

(js3-msg "msg.no.paren.after.with"
         "missing ) after with-statement object")

(js3-msg "msg.no.paren.after.let"
         "missing ( after let")

(js3-msg "msg.no.paren.let"
         "missing ) after variable list")

(js3-msg "msg.no.curly.let"
         "missing } after let statement")

(js3-msg "msg.bad.return"
         "invalid return")

(js3-msg "msg.no.brace.block"
         "missing } in compound statement")

(js3-msg "msg.bad.label"
         "invalid label")

(js3-msg "msg.bad.var"
         "missing variable name")

(js3-msg "msg.bad.var.init"
         "invalid variable initialization")

(js3-msg "msg.no.colon.cond"
         "missing : in conditional expression")

(js3-msg "msg.no.paren.arg"
         "missing ) after argument list")

(js3-msg "msg.no.bracket.arg"
         "missing ] after element list")

(js3-msg "msg.bad.prop"
         "invalid property id")

(js3-msg "msg.no.colon.prop"
         "missing : after property id")

(js3-msg "msg.no.brace.prop"
         "missing } after property list")

(js3-msg "msg.no.paren"
         "missing ) in parenthetical")

(js3-msg "msg.reserved.id"
         "identifier is a reserved word")

(js3-msg "msg.no.paren.catch"
         "missing ( before catch-block condition")

(js3-msg "msg.bad.catchcond"
         "invalid catch block condition")

(js3-msg "msg.catch.unreachable"
         "any catch clauses following an unqualified catch are unreachable")

(js3-msg "msg.no.brace.try"
         "missing '{' before try block")

(js3-msg "msg.no.brace.catchblock"
         "missing '{' before catch-block body")

(js3-msg "msg.try.no.catchfinally"
         "'try' without 'catch' or 'finally'")

(js3-msg "msg.no.return.value"
         "function %s does not always return a value")

(js3-msg "msg.anon.no.return.value"
         "anonymous function does not always return a value")

(js3-msg "msg.return.inconsistent"
         "return statement is inconsistent with previous usage")

(js3-msg "msg.generator.returns"
         "TypeError: generator function '%s' returns a value")

(js3-msg "msg.anon.generator.returns"
         "TypeError: anonymous generator function returns a value")

(js3-msg "msg.syntax"
         "syntax error")

(js3-msg "msg.unexpected.eof"
         "Unexpected end of file")

(js3-msg "msg.too.deep.parser.recursion"
         "Too deep recursion while parsing")

(js3-msg "msg.no.side.effects"
         "Code has no side effects")

(js3-msg "msg.extra.trailing.comma"
         "Trailing comma is not legal in an ECMA-262 object initializer")

(js3-msg "msg.array.trailing.comma"
         "Trailing comma yields different behavior across browsers")

(js3-msg "msg.equal.as.assign"
         (concat "Test for equality (==) mistyped as assignment (=)?"
                 " (parenthesize to suppress warning)"))

(js3-msg "msg.var.hides.arg"
         "Variable %s hides argument")

(js3-msg "msg.destruct.assign.no.init"
         "Missing = in destructuring declaration")

;; ScriptRuntime
(js3-msg "msg.no.properties"
         "%s has no properties.")

(js3-msg "msg.invalid.iterator"
         "Invalid iterator value")

(js3-msg "msg.iterator.primitive"
         "__iterator__ returned a primitive value")

(js3-msg "msg.assn.create.strict"
         "Assignment to undeclared variable %s")

(js3-msg "msg.ref.undefined.prop"
         "Reference to undefined property '%s'")

(js3-msg "msg.prop.not.found"
         "Property %s not found.")

(js3-msg "msg.invalid.type"
         "Invalid JavaScript value of type %s")

(js3-msg "msg.primitive.expected"
         "Primitive type expected (had %s instead)")

(js3-msg "msg.namespace.expected"
         "Namespace object expected to left of :: (found %s instead)")

(js3-msg "msg.null.to.object"
         "Cannot convert null to an object.")

(js3-msg "msg.undef.to.object"
         "Cannot convert undefined to an object.")

(js3-msg "msg.cyclic.value"
         "Cyclic %s value not allowed.")

(js3-msg "msg.is.not.defined"
         "'%s' is not defined.")

(js3-msg "msg.undef.prop.read"
         "Cannot read property '%s' from %s")

(js3-msg "msg.undef.prop.write"
         "Cannot set property '%s' of %s to '%s'")

(js3-msg "msg.undef.prop.delete"
         "Cannot delete property '%s' of %s")

(js3-msg "msg.undef.method.call"
         "Cannot call method '%s' of %s")

(js3-msg "msg.undef.with"
         "Cannot apply 'with' to %s")

(js3-msg "msg.isnt.function"
         "%s is not a function, it is %s.")

(js3-msg "msg.isnt.function.in"
         "Cannot call property %s in object %s. "
         "It is not a function, it is '%s'.")

(js3-msg "msg.function.not.found"
         "Cannot find function %s.")

(js3-msg "msg.function.not.found.in"
         "Cannot find function %s in object %s.")

(js3-msg "msg.no.ref.to.get"
         "%s is not a reference to read reference value.")

(js3-msg "msg.no.ref.to.set"
         "%s is not a reference to set reference value to %s.")

(js3-msg "msg.no.ref.from.function"
         "Function %s can not be used as the left-hand "
         "side of assignment or as an operand of ++ or -- operator.")

(js3-msg "msg.bad.default.value"
         "Object's getDefaultValue() method returned an object.")

(js3-msg "msg.instanceof.not.object"
         "Can't use instanceof on a non-object.")

(js3-msg "msg.instanceof.bad.prototype"
         "'prototype' property of %s is not an object.")

(js3-msg "msg.bad.radix"
         "illegal radix %s.")

;; ScriptableObject
(js3-msg "msg.default.value"
         "Cannot find default value for object.")

(js3-msg "msg.zero.arg.ctor"
         "Cannot load class '%s' which has no zero-parameter constructor.")

(js3-msg "msg.ctor.multiple.parms"
         "Can't define constructor or class %s since more than "
         "one constructor has multiple parameters.")

(js3-msg "msg.extend.scriptable"
         "%s must extend ScriptableObject in order to define property %s.")

(js3-msg "msg.bad.getter.parms"
         "In order to define a property, getter %s must have zero "
         "parameters or a single ScriptableObject parameter.")

(js3-msg "msg.obj.getter.parms"
         "Expected static or delegated getter %s to take "
         "a ScriptableObject parameter.")

(js3-msg "msg.getter.static"
         "Getter and setter must both be static or neither be static.")

(js3-msg "msg.setter.return"
         "Setter must have void return type: %s")

(js3-msg "msg.setter2.parms"
         "Two-parameter setter must take a ScriptableObject as "
         "its first parameter.")

(js3-msg "msg.setter1.parms"
         "Expected single parameter setter for %s")

(js3-msg "msg.setter2.expected"
         "Expected static or delegated setter %s to take two parameters.")

(js3-msg "msg.setter.parms"
         "Expected either one or two parameters for setter.")

(js3-msg "msg.setter.bad.type"
         "Unsupported parameter type '%s' in setter '%s'.")

(js3-msg "msg.add.sealed"
         "Cannot add a property to a sealed object: %s.")

(js3-msg "msg.remove.sealed"
         "Cannot remove a property from a sealed object: %s.")

(js3-msg "msg.modify.sealed"
         "Cannot modify a property of a sealed object: %s.")

(js3-msg "msg.modify.readonly"
         "Cannot modify readonly property: %s.")

;; TokenStream
(js3-msg "msg.missing.exponent"
         "missing exponent")

(js3-msg "msg.caught.nfe"
         "number format error")

(js3-msg "msg.unterminated.string.lit"
         "unterminated string literal")

(js3-msg "msg.unterminated.comment"
         "unterminated comment")

(js3-msg "msg.unterminated.re.lit"
         "unterminated regular expression literal")

(js3-msg "msg.invalid.re.flag"
         "invalid flag after regular expression")

(js3-msg "msg.no.re.input.for"
         "no input for %s")

(js3-msg "msg.illegal.character"
         "illegal character")

(js3-msg "msg.invalid.escape"
         "invalid Unicode escape sequence")

;; TokensStream warnings
(js3-msg "msg.bad.octal.literal"
         "illegal octal literal digit %s; "
         "interpreting it as a decimal digit")

(js3-msg "msg.reserved.keyword"
         "illegal usage of future reserved keyword %s; "
         "interpreting it as ordinary identifier")

(js3-msg "msg.script.is.not.constructor"
         "Script objects are not constructors.")

;; Arrays
(js3-msg "msg.arraylength.bad"
         "Inappropriate array length.")

;; Arrays
(js3-msg "msg.arraylength.too.big"
         "Array length %s exceeds supported capacity limit.")

;; URI
(js3-msg "msg.bad.uri"
         "Malformed URI sequence.")

;; Number
(js3-msg "msg.bad.precision"
         "Precision %s out of range.")

;; NativeGenerator
(js3-msg "msg.send.newborn"
         "Attempt to send value to newborn generator")

(js3-msg "msg.already.exec.gen"
         "Already executing generator")

(js3-msg "msg.StopIteration.invalid"
         "StopIteration may not be changed to an arbitrary object.")

;; Interpreter
(js3-msg "msg.yield.closing"
         "Yield from closing generator")

(provide 'js3-messages)

;; js3-messages.el ends here
;;; js3-ast.el --- JavaScript syntax tree node definitions

;;; Code:

(eval-when-compile
  (require 'cl))


(defsubst js3-relpos (pos anchor)
  "Convert POS to be relative to ANCHOR.
If POS is nil, returns nil."
  (and pos (- pos anchor)))

(defun js3-visit-ast (node callback)
  "Visit every node in ast NODE with visitor CALLBACK.

CALLBACK is a function that takes two arguments:  (NODE END-P).  It is
called twice:  once to visit the node, and again after all the node's
children have been processed.  The END-P argument is nil on the first
call and non-nil on the second call.  The return value of the callback
affects the traversal:  if non-nil, the children of NODE are processed.
If the callback returns nil, or if the node has no children, then the
callback is called immediately with a non-nil END-P argument.

The node traversal is approximately lexical-order, although there
are currently no guarantees around this."
  (when node
    (let ((vfunc (get (aref node 0) 'js3-visitor)))
      ;; visit the node
      (when  (funcall callback node nil)
        ;; visit the kids
        (cond
         ((eq vfunc 'js3-visit-none)
          nil)                            ; don't even bother calling it
         ;; Each AST node type has to define a `js3-visitor' function
         ;; that takes a node and a callback, and calls `js3-visit-ast'
         ;; on each child of the node.
         (vfunc
          (funcall vfunc node callback))
         (t
          (error "%s does not define a visitor-traversal function"
                 (aref node 0)))))
      ;; call the end-visit
      (funcall callback node t))))

(defstruct (js3-node
            (:constructor nil))  ; abstract
  "Base AST node type."
  (type -1)  ; token type
  (pos -1)   ; start position of this AST node in parsed input
  (abs -1)   ; absolute start of node, saved
  (len 1)    ; num characters spanned by the node
  props      ; optional node property list (an alist)
  parent)    ; link to parent node; null for root

(defsubst js3-node-get-prop (node prop &optional default)
  (or (cadr (assoc prop (js3-node-props node))) default))

(defsubst js3-node-set-prop (node prop value)
  (setf (js3-node-props node)
        (cons (list prop value) (js3-node-props node))))

(defsubst js3-fixup-starts (n nodes)
  "Adjust the start positions of NODES to be relative to N.
Any node in the list may be nil, for convenience."
  (dolist (node nodes)
    (when node
      (setf (js3-node-abs node) (js3-node-pos node))
      (setf (js3-node-pos node) (- (js3-node-pos node)
                                   (js3-node-pos n))))))

(defsubst js3-node-add-children (parent &rest nodes)
  "Set parent node of NODES to PARENT, and return PARENT.
Does nothing if we're not recording parent links.
If any given node in NODES is nil, doesn't record that link."
  (js3-fixup-starts parent nodes)
  (dolist (node nodes)
    (and node
         (setf (js3-node-parent node) parent))))

;; Non-recursive since it's called a frightening number of times.
(defsubst js3-node-abs-pos (n)
  (let ((pos (js3-node-pos n)))
    (while (setq n (js3-node-parent n))
      (setq pos (+ pos (js3-node-pos n))))
    pos))

(defsubst js3-node-abs-end (n)
  "Return absolute buffer position of end of N."
  (+ (js3-node-abs-pos n) (js3-node-len n)))

(defun js3-node-update-len (n p)
  (setf (js3-node-len n) (+ (js3-node-len n) p))
  (while (setq n (js3-node-parent n))
    (setq js3-looking-at-parent-for-update t)
    (setq js3-node-found-for-update nil)
    (setq js3-pos-for-update p)
    (setq js3-node-for-update n)
    (js3-visit-ast (js3-node-parent n)
                   #'js3-node-update-sibling-pos)
    (setf (js3-node-len n) (+ (js3-node-len n) p))))

(defun js3-node-update-pos (n p)
  (while (= (js3-node-pos n) 0)
    (setq n (js3-node-parent n)))
  (setf (js3-node-pos n) (+ (js3-node-pos n) p))
  (setq js3-looking-at-parent-for-update t)
  (setq js3-node-found-for-update nil)
  (setq js3-pos-for-update p)
  (setq js3-node-for-update n)
  (js3-visit-ast (js3-node-parent n) #'js3-node-update-sibling-pos)
  (while (setq n (js3-node-parent n))
    (setq js3-looking-at-parent-for-update t)
    (setq js3-node-found-for-update nil)
    (setq js3-pos-for-update p)
    (setq js3-node-for-update n)
    (js3-visit-ast (js3-node-parent n)
                   #'js3-node-update-sibling-pos)
    (setf (js3-node-len n) (+ (js3-node-len n) p)))
  t)

(defun js3-node-update-sibling-pos (n end-p)
  (if end-p
      nil
    (if js3-looking-at-parent-for-update
        (progn
          (setq js3-looking-at-parent-for-update nil)
          t)
      (if (eq n js3-node-for-update)
          (setq js3-node-found-for-update t)
        (when js3-node-found-for-update
          (setf (js3-node-pos n) (+ (js3-node-pos n)
                                    js3-pos-for-update))))
      nil)))

;; It's important to make sure block nodes have a lisp list for the
;; child nodes, to limit printing recursion depth in an AST that
;; otherwise consists of defstruct vectors.  Emacs will crash printing
;; a sufficiently large vector tree.

(defstruct (js3-block-node
            (:include js3-node)
            (:constructor nil)
            (:constructor make-js3-block-node
                          (&key (type js3-BLOCK)
                                (pos js3-token-beg)
                                len
                                props
                                kids)))
  "A block of statements."
  kids)  ; a lisp list of the child statement nodes

(put 'cl-struct-js3-block-node 'js3-visitor 'js3-visit-block)
(put 'cl-struct-js3-block-node 'js3-printer 'js3-print-block)
(put 'cl-struct-js3-block-node 'js3-printer-test 'js3-print-block-test)

(defsubst js3-visit-block (ast callback)
  "Visit the `js3-block-node' children of AST."
  (dolist (kid (js3-block-node-kids ast))
    (js3-visit-ast kid callback)))

(defun js3-print-block (n i)
  (js3-print "{\n")
  (dolist (kid (js3-block-node-kids n))
    (js3-print-ast kid (1+ i)))
  (js3-print "}\n"))

(defun js3-print-block-test (n i)
  "\n\n")

(defstruct (js3-scope
            (:include js3-block-node)
            (:constructor nil)
            (:constructor make-js3-scope
                          (&key (type js3-BLOCK)
                                (pos js3-token-beg)
                                len
                                kids)))
  ;; The symbol-table is a LinkedHashMap<String,Symbol> in Rhino.
  ;; I don't have one of those handy, so I'll use an alist for now.
  ;; It's as fast as an emacs hashtable for up to about 50 elements,
  ;; and is much lighter-weight to construct (both CPU and mem).
  ;; The keys are interned strings (symbols) for faster lookup.
  ;; Should switch to hybrid alist/hashtable eventually.
  symbol-table  ; an alist of (symbol . js3-symbol)
  parent-scope  ; a `js3-scope'
  top)          ; top-level `js3-scope' (script/function)

(put 'cl-struct-js3-scope 'js3-visitor 'js3-visit-none)
(put 'cl-struct-js3-scope 'js3-printer 'js3-print-none)
(put 'cl-struct-js3-scope 'js3-printer-test 'js3-print-none-test)

(defun js3-scope-set-parent-scope (scope parent)
  (setf (js3-scope-parent-scope scope) parent
        (js3-scope-top scope) (if (null parent)
                                  scope
                                (js3-scope-top parent))))

(defun js3-node-get-enclosing-scope (node)
  "Return the innermost `js3-scope' node surrounding NODE.
Returns nil if there is no enclosing scope node."
  (let ((parent (js3-node-parent node)))
    (while (not (js3-scope-p parent))
      (setq parent (js3-node-parent parent)))
    parent))

(defun js3-get-defining-scope (scope name)
  "Search up scope chain from SCOPE looking for NAME, a string or symbol.
Returns `js3-scope' in which NAME is defined, or nil if not found."
  (let ((sym (if (symbolp name)
                 name
               (intern name)))
        table
        result
        (continue t))
    (while (and scope continue)
      (if (and (setq table (js3-scope-symbol-table scope))
               (assq sym table))
          (setq continue nil
                result scope)
        (setq scope (js3-scope-parent-scope scope))))
    result))

(defsubst js3-scope-get-symbol (scope name)
  "Return symbol table entry for NAME in SCOPE.
NAME can be a string or symbol.   Returns a `js3-symbol' or nil if not found."
  (and (js3-scope-symbol-table scope)
       (cdr (assq (if (symbolp name)
                      name
                    (intern name))
                  (js3-scope-symbol-table scope)))))

(defsubst js3-scope-put-symbol (scope name symbol)
  "Enter SYMBOL into symbol-table for SCOPE under NAME.
NAME can be a lisp symbol or string.  SYMBOL is a `js3-symbol'."
  (let* ((table (js3-scope-symbol-table scope))
         (sym (if (symbolp name) name (intern name)))
         (entry (assq sym table)))
    (if entry
        (setcdr entry symbol)
      (push (cons sym symbol)
            (js3-scope-symbol-table scope)))))

(defstruct (js3-symbol
            (:constructor nil)
            (:constructor make-js3-symbol (decl-type name &optional ast-node)))
  "A symbol table entry."
  ;; One of js3-FUNCTION, js3-LP (for parameters), js3-VAR,
  ;; js3-LET, or js3-CONST
  decl-type
  name  ; string
  ast-node) ; a `js3-node'

(defstruct (js3-error-node
            (:include js3-node)
            (:constructor nil) ; silence emacs21 byte-compiler
            (:constructor make-js3-error-node
                          (&key (type js3-ERROR)
                                (pos js3-token-beg)
                                len)))
  "AST node representing a parse error.")

(put 'cl-struct-js3-error-node 'js3-visitor 'js3-visit-none)
(put 'cl-struct-js3-error-node 'js3-printer 'js3-print-none)
(put 'cl-struct-js3-error-node 'js3-printer-test 'js3-print-none-test)

(defstruct (js3-script-node
            (:include js3-scope)
            (:constructor nil)
            (:constructor make-js3-script-node
                          (&key (type js3-SCRIPT)
                                (pos js3-token-beg)
                                len
                                var-decls
                                fun-decls)))
  functions   ; lisp list of nested functions
  regexps     ; lisp list of (string . flags)
  symbols     ; alist (every symbol gets unique index)
  (param-count 0)
  var-names   ; vector of string names
  consts      ; bool-vector matching var-decls
  (temp-number 0))  ; for generating temp variables

(put 'cl-struct-js3-script-node 'js3-visitor 'js3-visit-block)
(put 'cl-struct-js3-script-node 'js3-printer 'js3-print-script)
(put 'cl-struct-js3-script-node 'js3-printer-test 'js3-print-script-test)

(defun js3-print-script (node indent)
  (dolist (kid (js3-block-node-kids node))
    (js3-print-ast kid indent)))

(defun js3-print-script-test (node indent)
  (dolist (kid (js3-block-node-kids node))
    (js3-print-ast-test kid indent)))

(defstruct (js3-ast-root
            (:include js3-script-node)
            (:constructor nil)
            (:constructor make-js3-ast-root
                          (&key (type js3-SCRIPT)
                                (pos js3-token-beg)
                                len
                                buffer)))
  "The root node of a js3 AST."
  buffer         ; the source buffer from which the code was parsed
  comments       ; a lisp list of comments, ordered by start position
  errors         ; a lisp list of errors found during parsing
  warnings       ; a lisp list of warnings found during parsing
  node-count)    ; number of nodes in the tree, including the root

(put 'cl-struct-js3-ast-root 'js3-visitor 'js3-visit-ast-root)
(put 'cl-struct-js3-ast-root 'js3-printer 'js3-print-script)
(put 'cl-struct-js3-ast-root 'js3-printer-test 'js3-print-script-test)

(defun js3-visit-ast-root (ast callback)
  (dolist (kid (js3-ast-root-kids ast))
    (js3-visit-ast kid callback))
  (dolist (comment (js3-ast-root-comments ast))
    (js3-visit-ast comment callback)))

(defstruct (js3-comment-node
            (:include js3-node)
            (:constructor nil)
            (:constructor make-js3-comment-node
                          (&key (type js3-COMMENT)
                                (pos js3-token-beg)
                                len
                                (format js3-ts-comment-type))))
  format)  ; 'line, 'block, 'jsdoc or 'html

(put 'cl-struct-js3-comment-node 'js3-visitor 'js3-visit-none)
(put 'cl-struct-js3-comment-node 'js3-printer 'js3-print-comment)
(put 'cl-struct-js3-comment-node 'js3-printer-test 'js3-print-comment-test)

(defun js3-print-comment (n i)
  ;; We really ought to link end-of-line comments to their nodes.
  ;; Or maybe we could add a new comment type, 'endline.
  (js3-print (js3-node-string n)))

(defun js3-print-comment-test (n i)
  (js3-print-test (js3-node-string n)))

(defstruct (js3-expr-stmt-node
            (:include js3-node)
            (:constructor nil)
            (:constructor make-js3-expr-stmt-node
                          (&key (type js3-EXPR_VOID)
                                (pos js3-ts-cursor)
                                len
                                expr)))
  "An expression statement."
  expr)

(defsubst js3-expr-stmt-node-set-has-result (node)
  "Change the node type to `js3-EXPR_RESULT'.  Used for code generation."
  (setf (js3-node-type node) js3-EXPR_RESULT))

(put 'cl-struct-js3-expr-stmt-node 'js3-visitor 'js3-visit-expr-stmt-node)
(put 'cl-struct-js3-expr-stmt-node 'js3-printer 'js3-print-expr-stmt-node)
(put 'cl-struct-js3-expr-stmt-node 'js3-printer-test 'js3-print-expr-stmt-node-test)

(defun js3-visit-expr-stmt-node (n v)
  (js3-visit-ast (js3-expr-stmt-node-expr n) v))

(defun js3-print-expr-stmt-node (n indent)
  (let* ((expr (js3-expr-stmt-node-expr n))
         (type (js3-node-type expr))
         (target expr))
    (when (= js3-CALL type)
      (setq target (js3-call-node-target expr))
      (setq type (js3-node-type target)))
    (when (= js3-GETPROP (js3-node-type target))
      (setq target (js3-prop-get-node-left target))
      (setq type (js3-node-type target)))
    (when (or (= js3-ARRAYLIT type)
              (= js3-LP type)
              (= js3-POS type)
              (= js3-NEG type))
      (js3-print ";")))
  (js3-print-ast (js3-expr-stmt-node-expr n) indent)
  (if (and (not js3-multiln-case)
           (= js3-CASE
              (js3-node-type (js3-node-parent n))))
      (js3-print "; ")
    (js3-print "\n")
    (if (= js3-VAR
           (js3-node-type (js3-expr-stmt-node-expr n)))
        (js3-print "\n"))))

(defun js3-print-expr-stmt-node-test (n indent)
  (concat
   (let* ((expr (js3-expr-stmt-node-expr n))
          (type (js3-node-type expr))
          (target expr))
     (when (= js3-CALL type)
       (setq target (js3-call-node-target expr))
       (setq type (js3-node-type target)))
     (when (= js3-GETPROP (js3-node-type target))
       (setq target (js3-prop-get-node-left target))
       (setq type (js3-node-type target)))
     (when (or (= js3-ARRAYLIT type)
               (= js3-LP type)
               (= js3-POS type)
               (= js3-NEG type))
       (js3-print-test ";")))
   (js3-print-ast-test (js3-expr-stmt-node-expr n) indent)
   (if (and (not js3-multiln-case)
            (= js3-CASE
               (js3-node-type (js3-node-parent n))))
       (js3-print-test "; ")
     (js3-print-test "\n")
     (if (= js3-VAR
            (js3-node-type (js3-expr-stmt-node-expr n)))
         (js3-print-test "\n")))))

(defstruct (js3-loop-node
            (:include js3-scope)
            (:constructor nil))
  "Abstract supertype of loop nodes."
  body      ; a `js3-block-node'
  lp        ; position of left-paren, nil if omitted
  rp)       ; position of right-paren, nil if omitted

(defstruct (js3-do-node
            (:include js3-loop-node)
            (:constructor nil)
            (:constructor make-js3-do-node
                          (&key (type js3-DO)
                                (pos js3-token-beg)
                                len
                                body
                                condition
                                while-pos
                                lp
                                rp)))
  "AST node for do-loop."
  condition  ; while (expression)
  while-pos) ; buffer position of 'while' keyword

(put 'cl-struct-js3-do-node 'js3-visitor 'js3-visit-do-node)
(put 'cl-struct-js3-do-node 'js3-printer 'js3-print-do-node)
(put 'cl-struct-js3-do-node 'js3-printer-test 'js3-print-do-node-test)

(defun js3-visit-do-node (n v)
  (js3-visit-ast (js3-do-node-body n) v)
  (js3-visit-ast (js3-do-node-condition n) v))

(defun js3-print-do-node (n i)
  (js3-print "do {\n")
  (dolist (kid (js3-block-node-kids (js3-do-node-body n)))
    (js3-print-ast kid (1+ i)))
  (js3-print "} while (")
  (js3-print-ast (js3-do-node-condition n) 0)
  (js3-print ")\n"))

(defun js3-print-do-node-test (n i)
  "\n\n")

(defstruct (js3-while-node
            (:include js3-loop-node)
            (:constructor nil)
            (:constructor make-js3-while-node
                          (&key (type js3-WHILE)
                                (pos js3-token-beg)
                                len
                                body
                                condition
                                lp
                                rp)))
  "AST node for while-loop."
  condition)    ; while-condition

(put 'cl-struct-js3-while-node 'js3-visitor 'js3-visit-while-node)
(put 'cl-struct-js3-while-node 'js3-printer 'js3-print-while-node)
(put 'cl-struct-js3-while-node 'js3-printer-test 'js3-print-while-node-test)

(defun js3-visit-while-node (n v)
  (js3-visit-ast (js3-while-node-condition n) v)
  (js3-visit-ast (js3-while-node-body n) v))

(defun js3-print-while-node (n i)
  (if (or (not (or js3-compact js3-compact-while))
          (and (js3-block-node-p (js3-while-node-body n))
               (> (length (js3-block-node-kids
                           (js3-while-node-body n)))
                  1)))
      (js3-print-while-node-long n i)
    (let ((temp (js3-print-while-node-test n i)))
      (if (or (> (length temp) js3-max-columns)
              (string-match "\n\\(.\\|\n\\)" temp))
          (js3-print-while-node-long n i))
      (js3-print-while-node-compact n i))))

(defun js3-print-while-node-long (n i)
  (js3-print "while (")
  (js3-print-ast (js3-while-node-condition n) 0)
  (js3-print ") {\n")
  (js3-print-body (js3-while-node-body n) (1+ i))
  (js3-print "}\n"))

(defun js3-print-while-node-compact (n i)
  (js3-print "while (")
  (js3-print-ast (js3-while-node-condition n) 0)
  (js3-print ") ")
  (js3-print-body (js3-while-node-body n) (1+ i)))

(defun js3-print-while-node-test (n i)
  (concat
   (js3-print-test "while (")
   (js3-print-ast-test (js3-while-node-condition n) 0)
   (js3-print-test ") ")
   (js3-print-body-test (js3-while-node-body n) (1+ i))))

(defstruct (js3-for-node
            (:include js3-loop-node)
            (:constructor nil)
            (:constructor make-js3-for-node
                          (&key (type js3-FOR)
                                (pos js3-ts-cursor)
                                len
                                body
                                init
                                condition
                                update
                                lp
                                rp)))
  "AST node for a C-style for-loop."
  init       ; initialization expression
  condition  ; loop condition
  update)    ; update clause

(put 'cl-struct-js3-for-node 'js3-visitor 'js3-visit-for-node)
(put 'cl-struct-js3-for-node 'js3-printer 'js3-print-for-node)
(put 'cl-struct-js3-for-node 'js3-printer-test 'js3-print-for-node-test)

(defun js3-visit-for-node (n v)
  (js3-visit-ast (js3-for-node-init n) v)
  (js3-visit-ast (js3-for-node-condition n) v)
  (js3-visit-ast (js3-for-node-update n) v)
  (js3-visit-ast (js3-for-node-body n) v))

(defun js3-print-for-node (n i)
  (if (or (not (or js3-compact js3-compact-for))
          (and (js3-block-node-p (js3-for-node-body n))
               (> (length (js3-block-node-kids
                           (js3-for-node-body n)))
                  1)))
      (js3-print-for-node-long n i)
    (let ((temp (js3-print-for-node-test n i)))
      (if (or (> (length temp) js3-max-columns)
              (string-match "\n\\(.\\|\n\\)" temp))
          (js3-print-for-node-long n i)
        (js3-print-for-node-compact n i)))))

(defun js3-print-for-node-long (n i)
  (js3-print "for (")
  (js3-print-ast (js3-for-node-init n) 0)
  (js3-print "; ")
  (js3-print-ast (js3-for-node-condition n) 0)
  (js3-print "; ")
  (js3-print-ast (js3-for-node-update n) 0)
  (js3-print ") {\n")
  (js3-print-body (js3-for-node-body n) (1+ i))
  (js3-print "}\n"))

(defun js3-print-for-node-compact (n i)
  (js3-print "for (")
  (js3-print-ast (js3-for-node-init n) 0)
  (js3-print "; ")
  (js3-print-ast (js3-for-node-condition n) 0)
  (js3-print "; ")
  (js3-print-ast (js3-for-node-update n) 0)
  (js3-print ") ")
  (js3-print-body (js3-for-node-body n) (1+ i)))

(defun js3-print-for-node-test (n i)
  (concat
   (js3-print-test "for (")
   (js3-print-ast-test (js3-for-node-init n) 0)
   (js3-print-test "; ")
   (js3-print-ast-test (js3-for-node-condition n) 0)
   (js3-print-test "; ")
   (js3-print-ast-test (js3-for-node-update n) 0)
   (js3-print-test ") ")
   (js3-print-body-test (js3-for-node-body n) (1+ i))))

(defstruct (js3-for-in-node
            (:include js3-loop-node)
            (:constructor nil)
            (:constructor make-js3-for-in-node
                          (&key (type js3-FOR)
                                (pos js3-ts-cursor)
                                len
                                body
                                iterator
                                object
                                in-pos
                                each-pos
                                foreach-p
                                lp
                                rp)))
  "AST node for a for..in loop."
  iterator  ; [var] foo in ...
  object    ; object over which we're iterating
  in-pos    ; buffer position of 'in' keyword
  each-pos  ; buffer position of 'each' keyword, if foreach-p
  foreach-p) ; t if it's a for-each loop

(put 'cl-struct-js3-for-in-node 'js3-visitor 'js3-visit-for-in-node)
(put 'cl-struct-js3-for-in-node 'js3-printer 'js3-print-for-in-node)
(put 'cl-struct-js3-for-in-node 'js3-printer-test 'js3-print-for-in-node-test)

(defun js3-visit-for-in-node (n v)
  (js3-visit-ast (js3-for-in-node-iterator n) v)
  (js3-visit-ast (js3-for-in-node-object n) v)
  (js3-visit-ast (js3-for-in-node-body n) v))

(defun js3-print-for-in-node (n i)
  (js3-print "for ")
  (if (js3-for-in-node-foreach-p n)
      (js3-print "each "))
  (js3-print "(")
  (js3-print-ast (js3-for-in-node-iterator n) 0)
  (js3-print " in ")
  (js3-print-ast (js3-for-in-node-object n) 0)
  (js3-print ") {\n")
  (js3-print-body (js3-for-in-node-body n) (1+ i))
  (js3-print "}\n"))

(defun js3-print-for-in-node-test (n i)
  "\n\n")

(defstruct (js3-return-node
            (:include js3-node)
            (:constructor nil)
            (:constructor make-js3-return-node
                          (&key (type js3-RETURN)
                                (pos js3-ts-cursor)
                                len
                                retval)))
  "AST node for a return statement."
  retval)  ; expression to return, or 'undefined

(put 'cl-struct-js3-return-node 'js3-visitor 'js3-visit-return-node)
(put 'cl-struct-js3-return-node 'js3-printer 'js3-print-return-node)
(put 'cl-struct-js3-return-node 'js3-printer-test 'js3-print-return-node-test)

(defun js3-visit-return-node (n v)
  (js3-visit-ast (js3-return-node-retval n) v))

(defun js3-print-return-node (n i)
  (js3-print "return ")
  (if (js3-return-node-retval n)
      (js3-print-ast (js3-return-node-retval n) 0))
  (js3-print "\n"))

(defun js3-print-return-node-test (n i)
  "\n\n")

(defstruct (js3-if-node
            (:include js3-node)
            (:constructor nil)
            (:constructor make-js3-if-node
                          (&key (type js3-IF)
                                (pos js3-ts-cursor)
                                len
                                condition
                                then-part
                                else-pos
                                else-part
                                lp
                                rp)))
  "AST node for an if-statement."
  condition   ; expression
  then-part   ; statement or block
  else-pos    ; optional buffer position of 'else' keyword
  else-part   ; optional statement or block
  lp          ; position of left-paren, nil if omitted
  rp)         ; position of right-paren, nil if omitted

(put 'cl-struct-js3-if-node 'js3-visitor 'js3-visit-if-node)
(put 'cl-struct-js3-if-node 'js3-printer 'js3-print-if-node)
(put 'cl-struct-js3-if-node 'js3-printer-test 'js3-print-if-node-test)

(defun js3-visit-if-node (n v)
  (js3-visit-ast (js3-if-node-condition n) v)
  (js3-visit-ast (js3-if-node-then-part n) v)
  (js3-visit-ast (js3-if-node-else-part n) v))

(defun js3-print-if-node (n i)
  (if (or (not (or js3-compact js3-compact-if))
          (js3-if-node-else-part n)
          (and (js3-block-node-p (js3-if-node-then-part n))
               (> (length (js3-block-node-kids
                           (js3-if-node-then-part n)))
                  1)))
      (js3-print-if-node-long n i)
    (let ((temp (js3-print-if-node-test n i)))
      (if (or (> (length temp) js3-max-columns)
              (string-match "\n\\(.\\|\n\\)" temp))
          (js3-print-if-node-long n i)
        (js3-print-if-node-compact n i)))))

(defun js3-print-if-node-long (n i)
  (js3-print "if (")
  (js3-print-expr (js3-if-node-condition n) 0)
  (js3-print ") {\n")
  (js3-print-body (js3-if-node-then-part n) (1+ i))
  (js3-print "}\n")
  (cond
   ((not (js3-if-node-else-part n))
    (js3-print " "))
   ((js3-if-node-p (js3-if-node-else-part n))
    (js3-print " else ")
    (js3-print-body (js3-if-node-else-part n) i))
   (t
    (js3-print " else {\n")
    (js3-print-body (js3-if-node-else-part n) (1+ i))
    (js3-print "}\n"))))

(defun js3-print-if-node-compact (n i)
  (js3-print "if (")
  (js3-print-expr (js3-if-node-condition n) 0)
  (js3-print ") ")
  (js3-print-body (js3-if-node-then-part n) (1+ i)))

(defun js3-print-if-node-test (n i)
  (concat
   (js3-print-test "if (")
   (js3-print-expr-test (js3-if-node-condition n) 0)
   (js3-print-test ") ")
   (js3-print-body-test (js3-if-node-then-part n) (1+ i))))

(defstruct (js3-try-node
            (:include js3-node)
            (:constructor nil)
            (:constructor make-js3-try-node
                          (&key (type js3-TRY)
                                (pos js3-ts-cursor)
                                len
                                try-block
                                catch-clauses
                                finally-block)))
  "AST node for a try-statement."
  try-block
  catch-clauses  ; a lisp list of `js3-catch-node'
  finally-block) ; a `js3-finally-node'

(put 'cl-struct-js3-try-node 'js3-visitor 'js3-visit-try-node)
(put 'cl-struct-js3-try-node 'js3-printer 'js3-print-try-node)
(put 'cl-struct-js3-try-node 'js3-printer-test 'js3-print-try-node-test)

(defun js3-visit-try-node (n v)
  (js3-visit-ast (js3-try-node-try-block n) v)
  (dolist (clause (js3-try-node-catch-clauses n))
    (js3-visit-ast clause v))
  (js3-visit-ast (js3-try-node-finally-block n) v))

(defun js3-print-try-node (n i)
  (let ((catches (js3-try-node-catch-clauses n))
        (finally (js3-try-node-finally-block n)))
    (js3-print "try {\n")
    (js3-print-body (js3-try-node-try-block n) (1+ i))
    (js3-print "}\n")
    (when catches
      (dolist (catch catches)
        (js3-print-ast catch i)))
    (if finally
        (js3-print-ast finally i)
      (js3-print "\n"))))

(defun js3-print-try-node-test (n i)
  "\n\n")

(defstruct (js3-catch-node
            (:include js3-node)
            (:constructor nil)
            (:constructor make-js3-catch-node
                          (&key (type js3-CATCH)
                                (pos js3-ts-cursor)
                                len
                                var-name
                                guard-kwd
                                guard-expr
                                block
                                lp
                                rp)))
  "AST node for a catch clause."
  var-name    ; a `js3-name-node'
  guard-kwd   ; relative buffer position of "if" in "catch (x if ...)"
  guard-expr  ; catch condition, a `js3-node'
  block       ; statements, a `js3-block-node'
  lp          ; buffer position of left-paren, nil if omitted
  rp)         ; buffer position of right-paren, nil if omitted

(put 'cl-struct-js3-catch-node 'js3-visitor 'js3-visit-catch-node)
(put 'cl-struct-js3-catch-node 'js3-printer 'js3-print-catch-node)
(put 'cl-struct-js3-catch-node 'js3-printer-test 'js3-print-catch-node-test)

(defun js3-visit-catch-node (n v)
  (js3-visit-ast (js3-catch-node-var-name n) v)
  (when (js3-catch-node-guard-kwd n)
    (js3-visit-ast (js3-catch-node-guard-expr n) v))
  (js3-visit-ast (js3-catch-node-block n) v))

(defun js3-print-catch-node (n i)
  (js3-print " catch (")
  (js3-print-ast (js3-catch-node-var-name n) 0)
  (when (js3-catch-node-guard-kwd n)
    (js3-print " if ")
    (js3-print-ast (js3-catch-node-guard-expr n) 0))
  (js3-print ") {\n")
  (js3-print-body (js3-catch-node-block n) (1+ i))
  (js3-print "}\n"))

(defun js3-print-catch-node-test (n i)
  "\n\n")

(defstruct (js3-finally-node
            (:include js3-node)
            (:constructor nil)
            (:constructor make-js3-finally-node
                          (&key (type js3-FINALLY)
                                (pos js3-ts-cursor)
                                len
                                body)))
  "AST node for a finally clause."
  body)  ; a `js3-node', often but not always a block node

(put 'cl-struct-js3-finally-node 'js3-visitor 'js3-visit-finally-node)
(put 'cl-struct-js3-finally-node 'js3-printer 'js3-print-finally-node)
(put 'cl-struct-js3-finally-node 'js3-printer-test 'js3-print-finally-node-test)

(defun js3-visit-finally-node (n v)
  (js3-visit-ast (js3-finally-node-body n) v))

(defun js3-print-finally-node (n i)
  (js3-print " finally {\n")
  (js3-print-body (js3-finally-node-body n) (1+ i))
  (js3-print "}\n"))

(defun js3-print-finally-node-test (n i)
  "\n\n")

(defstruct (js3-switch-node
            (:include js3-node)
            (:constructor nil)
            (:constructor make-js3-switch-node
                          (&key (type js3-SWITCH)
                                (pos js3-ts-cursor)
                                len
                                discriminant
                                cases
                                lp
                                rp)))
  "AST node for a switch statement."
  discriminant  ; a `js3-node' (switch expression)
  cases  ; a lisp list of `js3-case-node'
  lp     ; position of open-paren for discriminant, nil if omitted
  rp)    ; position of close-paren for discriminant, nil if omitted

(put 'cl-struct-js3-switch-node 'js3-visitor 'js3-visit-switch-node)
(put 'cl-struct-js3-switch-node 'js3-printer 'js3-print-switch-node)
(put 'cl-struct-js3-switch-node 'js3-printer-test 'js3-print-switch-node-test)

(defun js3-visit-switch-node (n v)
  (js3-visit-ast (js3-switch-node-discriminant n) v)
  (dolist (c (js3-switch-node-cases n))
    (js3-visit-ast c v)))

(defun js3-print-switch-node (n i)
  (js3-print "switch (")
  (js3-print-ast (js3-switch-node-discriminant n) 0)
  (js3-print ") {\n")
  (dolist (case (js3-switch-node-cases n))
    (js3-print-ast case i))
  (js3-print "\n}\n"))

(defun js3-print-switch-node-test (n i)
  "\n\n")

(defstruct (js3-case-node
            (:include js3-block-node)
            (:constructor nil)
            (:constructor make-js3-case-node
                          (&key (type js3-CASE)
                                (pos js3-ts-cursor)
                                len
                                kids
                                expr)))
  "AST node for a case clause of a switch statement."
  expr)   ; the case expression (nil for default)

(put 'cl-struct-js3-case-node 'js3-visitor 'js3-visit-case-node)
(put 'cl-struct-js3-case-node 'js3-printer 'js3-print-case-node)
(put 'cl-struct-js3-case-node 'js3-printer-test 'js3-print-case-node-test)

(defun js3-visit-case-node (n v)
  (js3-visit-ast (js3-case-node-expr n) v)
  (js3-visit-block n v))

(defun js3-print-case-node (n i)
  (if (or (not (or js3-compact js3-compact-case))
          js3-multiln-case)
      (js3-print-case-node-long n i)
    (let ((temp (js3-print-case-node-test n i)))
      (if (or (> (length temp) js3-max-columns)
              (string-match "\n" temp))
          (progn
            (setq js3-multiln-case t)
            (js3-print-case-node-long n i)
            (setq js3-multiln-case nil))
        (js3-print-case-node-compact n i)))))

(defun js3-print-case-node-long (n i)
  (if (null (js3-case-node-expr n))
      (js3-print "default: ")
    (js3-print "case ")
    (js3-print-ast (js3-case-node-expr n) 0)
    (js3-print ": "))
  (dolist (kid (js3-case-node-kids n))
    (js3-print-ast kid (1+ i)))
  (js3-delete-semicolons)
  (js3-print "\n"))

(defun js3-print-case-node-compact (n i)
  (if (null (js3-case-node-expr n))
      (js3-print "default: ")
    (js3-print "case ")
    (js3-print-ast (js3-case-node-expr n) 0)
    (js3-print ": "))
  (dolist (kid (js3-case-node-kids n))
    (js3-print-ast kid (1+ i)))
  (print (point))
  (js3-delete-semicolons)
  (js3-print "\n"))

(defun js3-print-case-node-test (n i)
  (concat
   (if (null (js3-case-node-expr n))
       (js3-print-test "default: ")
     (concat
      (js3-print-test "case ")
      (js3-print-ast-test (js3-case-node-expr n) 0)
      (js3-print-test ": ")))
   (let ((temp ""))
     (dolist (kid (js3-case-node-kids n))
       (setq temp (concat temp (js3-print-ast-test kid (1+ i)))))
     temp)))

(defstruct (js3-throw-node
            (:include js3-node)
            (:constructor nil)
            (:constructor make-js3-throw-node
                          (&key (type js3-THROW)
                                (pos js3-ts-cursor)
                                len
                                expr)))
  "AST node for a throw statement."
  expr)   ; the expression to throw

(put 'cl-struct-js3-throw-node 'js3-visitor 'js3-visit-throw-node)
(put 'cl-struct-js3-throw-node 'js3-printer 'js3-print-throw-node)
(put 'cl-struct-js3-throw-node 'js3-printer-test 'js3-print-throw-node-test)

(defun js3-visit-throw-node (n v)
  (js3-visit-ast (js3-throw-node-expr n) v))

(defun js3-print-throw-node (n i)
  (js3-print "throw ")
  (js3-print-ast (js3-throw-node-expr n) 0)
  (js3-print "\n"))

(defun js3-print-throw-node-test (n i)
  (concat
   (js3-print-test "throw ")
   (js3-print-ast-test (js3-throw-node-expr n) 0)
   (js3-print-test "\n")))

(defstruct (js3-with-node
            (:include js3-node)
            (:constructor nil)
            (:constructor make-js3-with-node
                          (&key (type js3-WITH)
                                (pos js3-ts-cursor)
                                len
                                object
                                body
                                lp
                                rp)))
  "AST node for a with-statement."
  object
  body
  lp    ; buffer position of left-paren around object, nil if omitted
  rp)   ; buffer position of right-paren around object, nil if omitted

(put 'cl-struct-js3-with-node 'js3-visitor 'js3-visit-with-node)
(put 'cl-struct-js3-with-node 'js3-printer 'js3-print-with-node)
(put 'cl-struct-js3-with-node 'js3-printer-test 'js3-print-with-node-test)

(defun js3-visit-with-node (n v)
  (js3-visit-ast (js3-with-node-object n) v)
  (js3-visit-ast (js3-with-node-body n) v))

(defun js3-print-with-node (n i)
  (js3-print "with (")
  (js3-print-ast (js3-with-node-object n) 0)
  (js3-print ") {\n")
  (js3-print-body (js3-with-node-body n) (1+ i))
  (js3-print "}\n"))

(defun js3-print-with-node-test (n i)
  "\n\n")

(defstruct (js3-label-node
            (:include js3-node)
            (:constructor nil)
            (:constructor make-js3-label-node
                          (&key (type js3-LABEL)
                                (pos js3-ts-cursor)
                                len
                                name)))
  "AST node for a statement label or case label."
  name   ; a string
  loop)  ; for validating and code-generating continue-to-label

(put 'cl-struct-js3-label-node 'js3-visitor 'js3-visit-none)
(put 'cl-struct-js3-label-node 'js3-printer 'js3-print-label)
(put 'cl-struct-js3-label-node 'js3-printer-test 'js3-print-label-test)

(defun js3-print-label (n i)
  (js3-print (concat (js3-label-node-name n) ":")))

(defun js3-print-label-test (n i)
  (js3-print-test (concat (js3-label-node-name n) ":")))

(defstruct (js3-labeled-stmt-node
            (:include js3-node)
            (:constructor nil)
            ;; type needs to be in `js3-side-effecting-tokens' to avoid spurious
            ;; no-side-effects warnings, hence js3-EXPR_RESULT.
            (:constructor make-js3-labeled-stmt-node
                          (&key (type js3-EXPR_RESULT)
                                (pos js3-ts-cursor)
                                len
                                labels
                                stmt)))
  "AST node for a statement with one or more labels.
Multiple labels for a statement are collapsed into the labels field."
  labels  ; lisp list of `js3-label-node'
  stmt)   ; the statement these labels are for

(put 'cl-struct-js3-labeled-stmt-node 'js3-visitor 'js3-visit-labeled-stmt)
(put 'cl-struct-js3-labeled-stmt-node 'js3-printer 'js3-print-labeled-stmt)
(put 'cl-struct-js3-labeled-stmt-node 'js3-printer-test 'js3-print-labeled-stmt-test)

(defun js3-get-label-by-name (lbl-stmt name)
  "Return a `js3-label-node' by NAME from LBL-STMT's labels list.
Returns nil if no such label is in the list."
  (let ((label-list (js3-labeled-stmt-node-labels lbl-stmt))
        result)
    (while (and label-list (not result))
      (if (string= (js3-label-node-name (car label-list)) name)
          (setq result (car label-list))
        (setq label-list (cdr label-list))))
    result))

(defun js3-visit-labeled-stmt (n v)
  (dolist (label (js3-labeled-stmt-node-labels n))
    (js3-visit-ast label v))
  (js3-visit-ast (js3-labeled-stmt-node-stmt n) v))

(defun js3-print-labeled-stmt (n i)
  (dolist (label (js3-labeled-stmt-node-labels n))
    (js3-print-ast label i))
  (js3-print-ast (js3-labeled-stmt-node-stmt n) (1+ i)))

(defun js3-print-labeled-stmt-test (n i)
  (concat
   (let ((temp ""))
     (dolist (label (js3-labeled-stmt-node-labels n))
       (setq temp (concat temp (js3-print-ast-test label i))))
     temp)
   (js3-print-ast-test (js3-labeled-stmt-node-stmt n) (1+ i))))

(defun js3-labeled-stmt-node-contains (node label)
  "Return t if NODE contains LABEL in its label set.
NODE is a `js3-labels-node'.  LABEL is an identifier."
  (loop for nl in (js3-labeled-stmt-node-labels node)
        if (string= label (js3-label-node-name nl))
        return t
        finally return nil))

(defsubst js3-labeled-stmt-node-add-label (node label)
  "Add a `js3-label-node' to the label set for this statement."
  (setf (js3-labeled-stmt-node-labels node)
        (nconc (js3-labeled-stmt-node-labels node) (list label))))

(defstruct (js3-jump-node
            (:include js3-node)
            (:constructor nil))
  "Abstract supertype of break and continue nodes."
  label   ; `js3-name-node' for location of label identifier, if present
  target) ; target js3-labels-node or loop/switch statement

(defun js3-visit-jump-node (n v)
  (js3-visit-ast (js3-jump-node-label n) v))

(defstruct (js3-break-node
            (:include js3-jump-node)
            (:constructor nil)
            (:constructor make-js3-break-node
                          (&key (type js3-BREAK)
                                (pos js3-ts-cursor)
                                len
                                label
                                target)))
  "AST node for a break statement.
The label field is a `js3-name-node', possibly nil, for the named label
if provided.  E.g. in 'break foo', it represents 'foo'.  The target field
is the target of the break - a label node or enclosing loop/switch statement.")

(put 'cl-struct-js3-break-node 'js3-visitor 'js3-visit-jump-node)
(put 'cl-struct-js3-break-node 'js3-printer 'js3-print-break-node)
(put 'cl-struct-js3-break-node 'js3-printer-test 'js3-print-break-node-test)

(defun js3-print-break-node (n i)
  (js3-print "break")
  (when (js3-break-node-label n)
    (js3-print " ")
    (js3-print-ast (js3-break-node-label n) 0))
  (if (and (not js3-multiln-case)
           (= js3-CASE
              (js3-node-type (js3-node-parent n))))
      (js3-print "; ")
    (js3-print "\n")))

(defun js3-print-break-node-test (n i)
  (concat
   (js3-print-test "break")
   (when (js3-break-node-label n)
     (concat
      (js3-print-test " ")
      (js3-print-ast-test (js3-break-node-label n) 0)))
   (if (and (not js3-multiln-case)
            (= js3-CASE
               (js3-node-type (js3-node-parent n))))
       (js3-print-test "; ")
     (js3-print-test "\n"))))

(defstruct (js3-continue-node
            (:include js3-jump-node)
            (:constructor nil)
            (:constructor make-js3-continue-node
                          (&key (type js3-CONTINUE)
                                (pos js3-ts-cursor)
                                len
                                label
                                target)))
  "AST node for a continue statement.
The label field is the user-supplied enclosing label name, a `js3-name-node'.
It is nil if continue specifies no label.  The target field is the jump target:
a `js3-label-node' or the innermost enclosing loop.")

(put 'cl-struct-js3-continue-node 'js3-visitor 'js3-visit-jump-node)
(put 'cl-struct-js3-continue-node 'js3-printer 'js3-print-continue-node)
(put 'cl-struct-js3-continue-node 'js3-printer-test 'js3-print-continue-node-test)

(defun js3-print-continue-node (n i)
  (js3-print "continue")
  (when (js3-continue-node-label n)
    (js3-print " ")
    (js3-print-ast (js3-continue-node-label n) 0))
  (if (and (not js3-multiln-case)
           (= js3-CASE
              (js3-node-type (js3-node-parent n))))
      (js3-print "; ")
    (js3-print "\n")))

(defun js3-print-continue-node-test (n i)
  (concat
   (js3-print-test "continue")
   (when (js3-continue-node-label n)
     (concat
      (js3-print-test " ")
      (js3-print-ast-test (js3-continue-node-label n) 0)))
   (if (and (not js3-multiln-case)
            (= js3-CASE
               (js3-node-type (js3-node-parent n))))
       (js3-print-test "; ")
     (js3-print-test "\n"))))

(defstruct (js3-function-node
            (:include js3-script-node)
            (:constructor nil)
            (:constructor make-js3-function-node
                          (&key (type js3-FUNCTION)
                                (pos js3-ts-cursor)
                                len
                                (ftype 'FUNCTION)
                                (form 'FUNCTION_STATEMENT)
                                (name "")
                                params
                                body
                                lp
                                rp)))
  "AST node for a function declaration.
The `params' field is a lisp list of nodes.  Each node is either a simple
`js3-name-node', or if it's a destructuring-assignment parameter, a
`js3-array-node' or `js3-object-node'."
  ftype            ; FUNCTION, GETTER or SETTER
  form             ; FUNCTION_{STATEMENT|EXPRESSION|EXPRESSION_STATEMENT}
  name             ; function name (a `js3-name-node', or nil if anonymous)
  params           ; a lisp list of destructuring forms or simple name nodes
  body             ; a `js3-block-node' or expression node (1.8 only)
  lp               ; position of arg-list open-paren, or nil if omitted
  rp               ; position of arg-list close-paren, or nil if omitted
  ignore-dynamic   ; ignore value of the dynamic-scope flag (interpreter only)
  needs-activation ; t if we need an activation object for this frame
  is-generator     ; t if this function contains a yield
  member-expr)     ; nonstandard Ecma extension from Rhino

(put 'cl-struct-js3-function-node 'js3-visitor 'js3-visit-function-node)
(put 'cl-struct-js3-function-node 'js3-printer 'js3-print-function-node)
(put 'cl-struct-js3-function-node 'js3-printer-test 'js3-print-function-node-test)

(defun js3-visit-function-node (n v)
  (js3-visit-ast (js3-function-node-name n) v)
  (dolist (p (js3-function-node-params n))
    (js3-visit-ast p v))
  (js3-visit-ast (js3-function-node-body n) v))

(defun js3-print-function-node (n i)
  (let ((getter (js3-node-get-prop n 'GETTER_SETTER))
        (name (js3-function-node-name n))
        (params (js3-function-node-params n))
        (body (js3-function-node-body n))
        (expr (eq (js3-function-node-form n) 'FUNCTION_EXPRESSION)))
    (unless expr
      (js3-print "\n"))
    (unless getter
      (js3-print "function"))
    (when name
      (js3-print " ")
      (js3-print-ast name 0))
    (js3-print " (")
    (loop with len = (length params)
          for param in params
          for count from 1
          do
          (js3-print-ast param 0)
          (if (< count len)
              (js3-print ", ")))
    (js3-print ") {\n")
    (js3-print-body body (1+ i))
    (js3-print "}")
    (unless expr
      (js3-print "\n"))))

(defun js3-print-function-node-test (n i)
  "\n\n")

(defsubst js3-function-name (node)
  "Return function name for NODE, a `js3-function-node', or nil if anonymous."
  (and (js3-function-node-name node)
       (js3-name-node-name (js3-function-node-name node))))

;; Having this be an expression node makes it more flexible.
;; There are IDE contexts, such as indentation in a for-loop initializer,
;; that work better if you assume it's an expression.  Whenever we have
;; a standalone var/const declaration, we just wrap with an expr stmt.
;; Eclipse apparently screwed this up and now has two versions, expr and stmt.
(defstruct (js3-var-decl-node
            (:include js3-node)
            (:constructor nil)
            (:constructor make-js3-var-decl-node
                          (&key (type js3-VAR)
                                (pos js3-token-beg)
                                len
                                kids
                                decl-type)))
  "AST node for a variable declaration list (VAR, CONST or LET).
The node bounds differ depending on the declaration type.  For VAR or
CONST declarations, the bounds include the var/const keyword.  For LET
declarations, the node begins at the position of the first child."
  kids        ; a lisp list of `js3-var-init-node' structs.
  decl-type)  ; js3-VAR, js3-CONST or js3-LET

(put 'cl-struct-js3-var-decl-node 'js3-visitor 'js3-visit-var-decl)
(put 'cl-struct-js3-var-decl-node 'js3-printer 'js3-print-var-decl)
(put 'cl-struct-js3-var-decl-node 'js3-printer-test 'js3-print-var-decl-test)

(defun js3-visit-var-decl (n v)
  (dolist (kid (js3-var-decl-node-kids n))
    (js3-visit-ast kid v)))

(defun js3-print-var-decl (n i)
  (let ((tt (js3-var-decl-node-decl-type n)))
    (js3-print
     (cond
      ((= tt js3-VAR) "var ")
      ((= tt js3-LET) "")  ; handled by parent let-{expr/stmt}
      ((= tt js3-CONST) "const ")
      (t
       (error "malformed var-decl node"))))
    (loop with kids = (js3-var-decl-node-kids n)
          with len = (length kids)
          for kid in kids
          for count from 1
          do
          (js3-print-ast kid 0)
          (if (< count len)
              (js3-print "\n, ")))))

(defun js3-print-var-decl-test (n i)
  (let ((tt (js3-var-decl-node-decl-type n)))
    (concat
     (js3-print-test
      (cond
       ((= tt js3-VAR) "var ")
       ((= tt js3-LET) "")  ; handled by parent let-{expr/stmt}
       ((= tt js3-CONST) "const ")
       (t
        (error "malformed var-decl node"))))
     (let ((temp ""))
       (loop with kids = (js3-var-decl-node-kids n)
             with len = (length kids)
             for kid in kids
             for count from 1
             do
             (setq temp
                   (concat
                    temp
                    (js3-print-ast-test kid 0)
                    (if (< count len)
                        (js3-print-test "\n, ")))))
       temp))))

(defstruct (js3-var-init-node
            (:include js3-node)
            (:constructor nil)
            (:constructor make-js3-var-init-node
                          (&key (type js3-VAR)
                                (pos js3-ts-cursor)
                                len
                                target
                                initializer)))
  "AST node for a variable declaration.
The type field will be js3-CONST for a const decl."
  target        ; `js3-name-node', `js3-object-node', or `js3-array-node'
  initializer)  ; initializer expression, a `js3-node'

(put 'cl-struct-js3-var-init-node 'js3-visitor 'js3-visit-var-init-node)
(put 'cl-struct-js3-var-init-node 'js3-printer 'js3-print-var-init-node)
(put 'cl-struct-js3-var-init-node 'js3-printer-test 'js3-print-var-init-node-test)

(defun js3-visit-var-init-node (n v)
  (js3-visit-ast (js3-var-init-node-target n) v)
  (js3-visit-ast (js3-var-init-node-initializer n) v))

(defun js3-print-var-init-node (n i)
  (js3-print-ast (js3-var-init-node-target n) 0)
  (when (js3-var-init-node-initializer n)
    (js3-print " = ")
    (js3-print-ast (js3-var-init-node-initializer n) 0)))

(defun js3-print-var-init-node-test (n i)
  (concat
   (js3-print-ast-test (js3-var-init-node-target n) 0)
   (when (js3-var-init-node-initializer n)
     (concat
      (js3-print-test " = ")
      (js3-print-ast-test (js3-var-init-node-initializer n) 0)))))

(defstruct (js3-cond-node
            (:include js3-node)
            (:constructor nil)
            (:constructor make-js3-cond-node
                          (&key (type js3-HOOK)
                                (pos js3-ts-cursor)
                                len
                                test-expr
                                true-expr
                                false-expr
                                q-pos
                                c-pos)))
  "AST node for the ternary operator"
  test-expr
  true-expr
  false-expr
  q-pos   ; buffer position of ?
  c-pos)  ; buffer position of :

(put 'cl-struct-js3-cond-node 'js3-visitor 'js3-visit-cond-node)
(put 'cl-struct-js3-cond-node 'js3-printer 'js3-print-cond-node)
(put 'cl-struct-js3-cond-node 'js3-printer-test 'js3-print-cond-node-test)

(defun js3-visit-cond-node (n v)
  (js3-visit-ast (js3-cond-node-test-expr n) v)
  (js3-visit-ast (js3-cond-node-true-expr n) v)
  (js3-visit-ast (js3-cond-node-false-expr n) v))

(defun js3-print-cond-node (n i)
  (if (or (not (or js3-compact js3-compact-infix))
          js3-multiln)
      (js3-print-cond-node-long n i)
    (let ((temp (js3-print-cond-node-test n i)))
      (if (or (> (length temp) js3-max-columns)
              (string-match "\n" temp))
          (js3-print-cond-node-long n i)
        (js3-print-cond-node-compact n i)))))

(defun js3-print-cond-node-long (n i)
  (js3-print-ast (js3-cond-node-test-expr n) 0)
  (js3-print "\n? ")
  (js3-print-ast (js3-cond-node-true-expr n) 0)
  (js3-print "\n: ")
  (js3-print-ast (js3-cond-node-false-expr n) 0))

(defun js3-print-cond-node-compact (n i)
  (js3-print-ast (js3-cond-node-test-expr n) 0)
  (js3-print " ? ")
  (js3-print-ast (js3-cond-node-true-expr n) 0)
  (js3-print " : ")
  (js3-print-ast (js3-cond-node-false-expr n) 0))

(defun js3-print-cond-node-test (n i)
  (concat
   (js3-print-ast-test (js3-cond-node-test-expr n) 0)
   (js3-print-test " ? ")
   (js3-print-ast-test (js3-cond-node-true-expr n) 0)
   (js3-print-test " : ")
   (js3-print-ast-test (js3-cond-node-false-expr n) 0)))

(defstruct (js3-infix-node
            (:include js3-node)
            (:constructor nil)
            (:constructor make-js3-infix-node
                          (&key type
                                (pos js3-ts-cursor)
                                len
                                op-pos
                                left
                                right)))
  "Represents infix expressions.
Includes assignment ops like `|=', and the comma operator.
The type field inherited from `js3-node' holds the operator."
  op-pos    ; buffer position where operator begins
  left      ; any `js3-node'
  right)    ; any `js3-node'

(put 'cl-struct-js3-infix-node 'js3-visitor 'js3-visit-infix-node)
(put 'cl-struct-js3-infix-node 'js3-printer 'js3-print-infix-node)
(put 'cl-struct-js3-infix-node 'js3-printer-test 'js3-print-infix-node-test)

(defun js3-visit-infix-node (n v)
  (js3-visit-ast (js3-infix-node-left n) v)
  (js3-visit-ast (js3-infix-node-right n) v))

(defconst js3-operator-tokens
  (let ((table (make-hash-table :test 'eq))
        (tokens
         (list (cons js3-IN "in")
               (cons js3-TYPEOF "typeof")
               (cons js3-INSTANCEOF "instanceof")
               (cons js3-DELPROP "delete")
               (cons js3-COMMA ",")
               (cons js3-COLON ":")
               (cons js3-OR "||")
               (cons js3-AND "&&")
               (cons js3-INC "++")
               (cons js3-DEC "--")
               (cons js3-BITOR "|")
               (cons js3-BITXOR "^")
               (cons js3-BITAND "&")
               (cons js3-EQ "==")
               (cons js3-NE "!=")
               (cons js3-LT "<")
               (cons js3-LE "<=")
               (cons js3-GT ">")
               (cons js3-GE ">=")
               (cons js3-LSH "<<")
               (cons js3-RSH ">>")
               (cons js3-URSH ">>>")
               (cons js3-ADD "+")       ; infix plus
               (cons js3-SUB "-")       ; infix minus
               (cons js3-MUL "*")
               (cons js3-DIV "/")
               (cons js3-MOD "%")
               (cons js3-NOT "!")
               (cons js3-BITNOT "~")
               (cons js3-POS "+")       ; unary plus
               (cons js3-NEG "-")       ; unary minus
               (cons js3-SHEQ "===")    ; shallow equality
               (cons js3-SHNE "!==")    ; shallow inequality
               (cons js3-ASSIGN "=")
               (cons js3-ASSIGN_BITOR "|=")
               (cons js3-ASSIGN_BITXOR "^=")
               (cons js3-ASSIGN_BITAND "&=")
               (cons js3-ASSIGN_LSH "<<=")
               (cons js3-ASSIGN_RSH ">>=")
               (cons js3-ASSIGN_URSH ">>>=")
               (cons js3-ASSIGN_ADD "+=")
               (cons js3-ASSIGN_SUB "-=")
               (cons js3-ASSIGN_MUL "*=")
               (cons js3-ASSIGN_DIV "/=")
               (cons js3-ASSIGN_MOD "%="))))
    (loop for (k . v) in tokens do
          (puthash k v table))
    table))

(defun js3-print-infix-node (args &optional delimiter)
  (if (or (not (or js3-compact js3-compact-infix))
          js3-multiln)
      (js3-print-infix-node-long args delimiter)
    (let ((temp (js3-print-infix-node-test args delimiter)))
      (if (or (> (length temp) js3-max-columns)
              (string-match "\n" temp))
          (js3-print-infix-node-long args delimiter)
        (js3-print-infix-node-compact args delimiter)))))

(defun js3-print-infix-node-long (n i)
  (let* ((tt (js3-node-type n))
         (op (gethash tt js3-operator-tokens)))
    (unless op
      (error "unrecognized infix operator %s" (js3-node-type n)))
    (js3-print-ast (js3-infix-node-left n) 0)
    (if (and (/= tt js3-ASSIGN)
             (/= tt js3-ASSIGN_BITOR)
             (/= tt js3-ASSIGN_BITXOR)
             (/= tt js3-ASSIGN_BITAND)
             (/= tt js3-ASSIGN_LSH)
             (/= tt js3-ASSIGN_RSH)
             (/= tt js3-ASSIGN_URSH)
             (/= tt js3-ASSIGN_ADD)
             (/= tt js3-ASSIGN_SUB)
             (/= tt js3-ASSIGN_MUL)
             (/= tt js3-ASSIGN_DIV)
             (/= tt js3-ASSIGN_MOD))
        (js3-print "\n")
      (js3-print " "))
    (js3-print op)
    (js3-print " ")
    (js3-print-ast (js3-infix-node-right n) 0)))

(defun js3-print-infix-node-compact (n i)
  (let* ((tt (js3-node-type n))
         (op (gethash tt js3-operator-tokens)))
    (unless op
      (error "unrecognized infix operator %s" (js3-node-type n)))
    (js3-print-ast (js3-infix-node-left n) 0)
    (unless (= tt js3-COMMA)
      (js3-print " "))
    (js3-print op)
    (js3-print " ")
    (js3-print-ast (js3-infix-node-right n) 0)))

(defun js3-print-infix-node-test (n i)
  (let* ((tt (js3-node-type n))
         (op (gethash tt js3-operator-tokens)))
    (unless op
      (error "unrecognized infix operator %s" (js3-node-type n)))
    (concat
     (js3-print-ast-test (js3-infix-node-left n) 0)
     (unless (= tt js3-COMMA)
       (js3-print-test " "))
     (js3-print-test op)
     (js3-print-test " ")
     (js3-print-ast-test (js3-infix-node-right n) 0))))

(defstruct (js3-assign-node
            (:include js3-infix-node)
            (:constructor nil)
            (:constructor make-js3-assign-node
                          (&key type
                                (pos js3-ts-cursor)
                                len
                                op-pos
                                left
                                right)))
  "Represents any assignment.
The type field holds the actual assignment operator.")

(put 'cl-struct-js3-assign-node 'js3-visitor 'js3-visit-infix-node)
(put 'cl-struct-js3-assign-node 'js3-printer 'js3-print-infix-node)
(put 'cl-struct-js3-assign-node 'js3-printer-test 'js3-print-infix-node-test)

(defstruct (js3-unary-node
            (:include js3-node)
            (:constructor nil)
            (:constructor make-js3-unary-node
                          (&key type ; required
                                (pos js3-ts-cursor)
                                len
                                operand)))
  "AST node type for unary operator nodes.
The type field can be NOT, BITNOT, POS, NEG, INC, DEC,
TYPEOF, or DELPROP.  For INC or DEC, a 'postfix node
property is added if the operator follows the operand."
  operand)  ; a `js3-node' expression

(put 'cl-struct-js3-unary-node 'js3-visitor 'js3-visit-unary-node)
(put 'cl-struct-js3-unary-node 'js3-printer 'js3-print-unary-node)
(put 'cl-struct-js3-unary-node 'js3-printer-test 'js3-print-unary-node-test)

(defun js3-visit-unary-node (n v)
  (js3-visit-ast (js3-unary-node-operand n) v))

(defun js3-print-unary-node (n i)
  (let* ((tt (js3-node-type n))
         (op (gethash tt js3-operator-tokens))
         (postfix (js3-node-get-prop n 'postfix)))
    (unless op
      (error "unrecognized unary operator %s" tt))
    (unless postfix
      (js3-print op))
    (if (or (= tt js3-TYPEOF)
            (= tt js3-DELPROP))
        (js3-print " "))
    (js3-print-ast (js3-unary-node-operand n) 0)
    (when postfix
      (js3-print op))))

(defun js3-print-unary-node-test (n i)
  (let* ((tt (js3-node-type n))
         (op (gethash tt js3-operator-tokens))
         (postfix (js3-node-get-prop n 'postfix)))
    (unless op
      (error "unrecognized unary operator %s" tt))
    (concat
     (unless postfix
       (js3-print-test op))
     (if (or (= tt js3-TYPEOF)
             (= tt js3-DELPROP))
         (js3-print-test " "))
     (js3-print-ast-test (js3-unary-node-operand n) 0)
     (when postfix
       (js3-print-test op)))))

(defstruct (js3-let-node
            (:include js3-scope)
            (:constructor nil)
            (:constructor make-js3-let-node
                          (&key (type js3-LETEXPR)
                                (pos js3-token-beg)
                                len
                                vars
                                body
                                lp
                                rp)))
  "AST node for a let expression or a let statement.
Note that a let declaration such as let x=6, y=7 is a `js3-var-decl-node'."
  vars   ; a `js3-var-decl-node'
  body   ; a `js3-node' representing the expression or body block
  lp
  rp)

(put 'cl-struct-js3-let-node 'js3-visitor 'js3-visit-let-node)
(put 'cl-struct-js3-let-node 'js3-printer 'js3-print-let-node)
(put 'cl-struct-js3-let-node 'js3-printer-test 'js3-print-let-node-test)

(defun js3-visit-let-node (n v)
  (js3-visit-ast (js3-let-node-vars n) v)
  (js3-visit-ast (js3-let-node-body n) v))

(defun js3-print-let-node (n i)
  (js3-print "let (")
  (js3-print-ast (js3-let-node-vars n) 0)
  (js3-print ") ")
  (js3-print-ast (js3-let-node-body n) i))

(defun js3-print-let-node-test (n i)
  (concat
   (js3-print-test "let (")
   (js3-print-ast-test (js3-let-node-vars n) 0)
   (js3-print-test ") ")
   (js3-print-ast-test (js3-let-node-body n) i)))

(defstruct (js3-keyword-node
            (:include js3-node)
            (:constructor nil)
            (:constructor make-js3-keyword-node
                          (&key type
                                (pos js3-token-beg)
                                (len (- js3-ts-cursor pos)))))
  "AST node representing a literal keyword such as `null'.
Used for `null', `this', `true', `false' and `debugger'.
The node type is set to js3-NULL, js3-THIS, etc.")

(put 'cl-struct-js3-keyword-node 'js3-visitor 'js3-visit-none)
(put 'cl-struct-js3-keyword-node 'js3-printer 'js3-print-keyword-node)
(put 'cl-struct-js3-keyword-node 'js3-printer-test 'js3-print-keyword-node-test)

(defun js3-print-keyword-node (n i)
  (js3-print
   (let ((tt (js3-node-type n)))
     (cond
      ((= tt js3-THIS) "this")
      ((= tt js3-NULL) "null")
      ((= tt js3-TRUE) "true")
      ((= tt js3-FALSE) "false")
      ((= tt js3-DEBUGGER) "debugger")
      (t (error "Invalid keyword literal type: %d" tt))))))

(defun js3-print-keyword-node-test (n i)
  (js3-print-test
   (let ((tt (js3-node-type n)))
     (cond
      ((= tt js3-THIS) "this")
      ((= tt js3-NULL) "null")
      ((= tt js3-TRUE) "true")
      ((= tt js3-FALSE) "false")
      ((= tt js3-DEBUGGER) "debugger")
      (t (error "Invalid keyword literal type: %d" tt))))))

(defsubst js3-this-node-p (node)
  "Return t if this node is a `js3-literal-node' of type js3-THIS."
  (eq (js3-node-type node) js3-THIS))

(defstruct (js3-new-node
            (:include js3-node)
            (:constructor nil)
            (:constructor make-js3-new-node
                          (&key (type js3-NEW)
                                (pos js3-token-beg)
                                len
                                target
                                args
                                initializer
                                lp
                                rp)))
  "AST node for new-expression such as new Foo()."
  target  ; an identifier or reference
  args    ; a lisp list of argument nodes
  lp      ; position of left-paren, nil if omitted
  rp      ; position of right-paren, nil if omitted
  initializer) ; experimental Rhino syntax:  optional `js3-object-node'

(put 'cl-struct-js3-new-node 'js3-visitor 'js3-visit-new-node)
(put 'cl-struct-js3-new-node 'js3-printer 'js3-print-new-node)
(put 'cl-struct-js3-new-node 'js3-printer-test 'js3-print-new-node-test)

(defun js3-visit-new-node (n v)
  (js3-visit-ast (js3-new-node-target n) v)
  (dolist (arg (js3-new-node-args n))
    (js3-visit-ast arg v))
  (js3-visit-ast (js3-new-node-initializer n) v))

(defun js3-print-new-node (n i)
  (js3-print "new ")
  (js3-print-ast (js3-new-node-target n))
  (js3-print "(")
  (js3-print-list (js3-new-node-args n))
  (js3-print ")")
  (when (js3-new-node-initializer n)
    (js3-print " ")
    (js3-print-ast (js3-new-node-initializer n))))

(defun js3-print-new-node-test (n i)
  (concat
   (js3-print-test "new ")
   (js3-print-ast-test (js3-new-node-target n))
   (js3-print-test "(")
   (js3-print-list-test (js3-new-node-args n))
   (js3-print-test ")")
   (when (js3-new-node-initializer n)
     (concat
      (js3-print-test " ")
      (js3-print-ast-test (js3-new-node-initializer n))))))

(defstruct (js3-name-node
            (:include js3-node)
            (:constructor nil)
            (:constructor make-js3-name-node
                          (&key (type js3-NAME)
                                (pos js3-token-beg)
                                (len (- js3-ts-cursor
                                        js3-token-beg))
                                (name js3-ts-string))))
  "AST node for a JavaScript identifier"
  name   ; a string
  scope) ; a `js3-scope' (optional, used for codegen)

(put 'cl-struct-js3-name-node 'js3-visitor 'js3-visit-none)
(put 'cl-struct-js3-name-node 'js3-printer 'js3-print-name-node)
(put 'cl-struct-js3-name-node 'js3-printer-test 'js3-print-name-node-test)

(defun js3-print-name-node (n i)
  (js3-print (js3-name-node-name n)))

(defun js3-print-name-node-test (n i)
  (js3-print-test (js3-name-node-name n)))

(defsubst js3-name-node-length (node)
  "Return identifier length of NODE, a `js3-name-node'.
Returns 0 if NODE is nil or its identifier field is nil."
  (if node
      (length (js3-name-node-name node))
    0))

(defstruct (js3-number-node
            (:include js3-node)
            (:constructor nil)
            (:constructor make-js3-number-node
                          (&key (type js3-NUMBER)
                                (pos js3-token-beg)
                                (len (- js3-ts-cursor
                                        js3-token-beg))
                                (value js3-ts-string)
                                (num-value js3-ts-number))))
  "AST node for a number literal."
  value      ; the original string, e.g. "6.02e23"
  num-value) ; the parsed number value

(put 'cl-struct-js3-number-node 'js3-visitor 'js3-visit-none)
(put 'cl-struct-js3-number-node 'js3-printer 'js3-print-number-node)
(put 'cl-struct-js3-number-node 'js3-printer-test 'js3-print-number-node-test)

(defun js3-print-number-node (n i)
  (js3-print
   (number-to-string (js3-number-node-num-value n))))

(defun js3-print-number-node-test (n i)
  (js3-print-test
   (number-to-string (js3-number-node-num-value n))))

(defstruct (js3-regexp-node
            (:include js3-node)
            (:constructor nil)
            (:constructor make-js3-regexp-node
                          (&key (type js3-REGEXP)
                                (pos js3-token-beg)
                                (len (- js3-ts-cursor
                                        js3-token-beg))
                                value
                                flags)))
  "AST node for a regular expression literal."
  value  ; the regexp string, without // delimiters
  flags) ; a string of flags, e.g. `mi'.

(put 'cl-struct-js3-regexp-node 'js3-visitor 'js3-visit-none)
(put 'cl-struct-js3-regexp-node 'js3-printer 'js3-print-regexp)
(put 'cl-struct-js3-regexp-node 'js3-printer-test 'js3-print-regexp-test)

(defun js3-print-regexp (n i)
  (js3-print
   (concat
    "/"
    (js3-regexp-node-value n)
    "/"))
  (if (js3-regexp-node-flags n)
      (js3-print (js3-regexp-node-flags n))))

(defun js3-print-regexp-test (n i)
  (concat
   (js3-print-test
    (concat
     "/"
     (js3-regexp-node-value n)
     "/"))
   (if (js3-regexp-node-flags n)
       (js3-print-test (js3-regexp-node-flags n)))))

(defstruct (js3-string-node
            (:include js3-node)
            (:constructor nil)
            (:constructor make-js3-string-node
                          (&key (type js3-STRING)
                                (pos js3-token-beg)
                                (len (- js3-ts-cursor
                                        js3-token-beg))
                                (value js3-ts-string))))
  "String literal.
Escape characters are not evaluated; e.g. \n is 2 chars in value field.
You can tell the quote type by looking at the first character."
  value) ; the characters of the string, including the quotes

(put 'cl-struct-js3-string-node 'js3-visitor 'js3-visit-none)
(put 'cl-struct-js3-string-node 'js3-printer 'js3-print-string-node)
(put 'cl-struct-js3-string-node 'js3-printer-test 'js3-print-string-node-test)

(defun js3-print-string-node (n i)
  (js3-print (js3-node-string n)))

(defun js3-print-string-node-test (n i)
  (js3-print-test (js3-node-string n)))

(defstruct (js3-array-node
            (:include js3-node)
            (:constructor nil)
            (:constructor make-js3-array-node
                          (&key (type js3-ARRAYLIT)
                                (pos js3-ts-cursor)
                                len
                                elems)))
  "AST node for an array literal."
  elems)  ; list of expressions.  [foo,,bar] yields a nil middle element.

(put 'cl-struct-js3-array-node 'js3-visitor 'js3-visit-array-node)
(put 'cl-struct-js3-array-node 'js3-printer 'js3-print-array-node)
(put 'cl-struct-js3-array-node 'js3-printer-test 'js3-print-array-node-test)

(defun js3-visit-array-node (n v)
  (dolist (e (js3-array-node-elems n))
    (js3-visit-ast e v)))

(defun js3-print-array-node (n i)
  (js3-print "[")
  (js3-print-list (js3-array-node-elems n))
  (js3-print "]"))

(defun js3-print-array-node-test (n i)
  (concat
   (js3-print-test "[")
   (js3-print-list-test (js3-array-node-elems n))
   (js3-print-test "]")))

(defstruct (js3-object-node
            (:include js3-node)
            (:constructor nil)
            (:constructor make-js3-object-node
                          (&key (type js3-OBJECTLIT)
                                (pos js3-ts-cursor)
                                len
                                elems)))
  "AST node for an object literal expression."
  elems)  ; a lisp list of `js3-object-prop-node'

(put 'cl-struct-js3-object-node 'js3-visitor 'js3-visit-object-node)
(put 'cl-struct-js3-object-node 'js3-printer 'js3-print-object-node)
(put 'cl-struct-js3-object-node 'js3-printer-test 'js3-print-object-node-test)

(defun js3-visit-object-node (n v)
  (dolist (e (js3-object-node-elems n))
    (js3-visit-ast e v)))

(defun js3-print-object-node (n i)
  (js3-print "{")
  (js3-print-list (js3-object-node-elems n))
  (js3-print "}"))

(defun js3-print-object-node-test (n i)
  (concat
   (js3-print-test "{")
   (js3-print-list-test (js3-object-node-elems n))
   (js3-print-test "}")))

(defstruct (js3-object-prop-node
            (:include js3-infix-node)
            (:constructor nil)
            (:constructor make-js3-object-prop-node
                          (&key (type js3-COLON)
                                (pos js3-ts-cursor)
                                len
                                left
                                right
                                op-pos)))
  "AST node for an object literal prop:value entry.
The `left' field is the property:  a name node, string node or number node.
The `right' field is a `js3-node' representing the initializer value.")

(put 'cl-struct-js3-object-prop-node 'js3-visitor 'js3-visit-infix-node)
(put 'cl-struct-js3-object-prop-node 'js3-printer 'js3-print-object-prop-node)
(put 'cl-struct-js3-object-prop-node 'js3-printer-test 'js3-print-object-prop-node-test)

(defun js3-print-object-prop-node (n i)
  (js3-print-ast (js3-object-prop-node-left n) 0)
  (js3-print ": ")
  (js3-print-ast (js3-object-prop-node-right n) 0))

(defun js3-print-object-prop-node-test (n i)
  (concat
   (js3-print-ast-test (js3-object-prop-node-left n) 0)
   (js3-print-test ": ")
   (js3-print-ast-test (js3-object-prop-node-right n) 0)))

(defstruct (js3-getter-setter-node
            (:include js3-infix-node)
            (:constructor nil)
            (:constructor make-js3-getter-setter-node
                          (&key type ; GET or SET
                                (pos js3-ts-cursor)
                                len
                                left
                                right)))
  "AST node for a getter/setter property in an object literal.
The `left' field is the `js3-name-node' naming the getter/setter prop.
The `right' field is always an anonymous `js3-function-node' with a node
property `GETTER_SETTER' set to js3-GET or js3-SET. ")

(put 'cl-struct-js3-getter-setter-node 'js3-visitor 'js3-visit-infix-node)
(put 'cl-struct-js3-getter-setter-node 'js3-printer 'js3-print-getter-setter)
(put 'cl-struct-js3-getter-setter-node 'js3-printer-test 'js3-print-getter-setter-test)

(defun js3-print-getter-setter (n i)
  (js3-print (if (= (js3-node-type n) js3-GET) "get " "set "))
  (js3-print-ast (js3-getter-setter-node-left n) 0)
  (js3-print-ast (js3-getter-setter-node-right n) 0))

(defun js3-print-getter-setter-test (n i)
  (concat
   (js3-print-test (if (= (js3-node-type n) js3-GET) "get " "set "))
   (js3-print-ast-test (js3-getter-setter-node-left n) 0)
   (js3-print-ast-test (js3-getter-setter-node-right n) 0)))

(defstruct (js3-prop-get-node
            (:include js3-infix-node)
            (:constructor nil)
            (:constructor make-js3-prop-get-node
                          (&key (type js3-GETPROP)
                                (pos js3-ts-cursor)
                                len
                                left
                                right)))
  "AST node for a dotted property reference, e.g. foo.bar or foo().bar")

(put 'cl-struct-js3-prop-get-node 'js3-visitor 'js3-visit-prop-get-node)
(put 'cl-struct-js3-prop-get-node 'js3-printer 'js3-print-prop-get-node)
(put 'cl-struct-js3-prop-get-node 'js3-printer-test 'js3-print-prop-get-node-test)

(defun js3-visit-prop-get-node (n v)
  (js3-visit-ast (js3-prop-get-node-left n) v)
  (js3-visit-ast (js3-prop-get-node-right n) v))

(defun js3-print-prop-get-node (n i)
  (js3-print-ast (js3-prop-get-node-left n) 0)
  (js3-print ".")
  (js3-print-ast (js3-prop-get-node-right n) 0))

(defun js3-print-prop-get-node-test (n i)
  (concat
   (js3-print-ast-test (js3-prop-get-node-left n) 0)
   (js3-print-test ".")
   (js3-print-ast-test (js3-prop-get-node-right n) 0)))

(defstruct (js3-elem-get-node
            (:include js3-node)
            (:constructor nil)
            (:constructor make-js3-elem-get-node
                          (&key (type js3-GETELEM)
                                (pos js3-ts-cursor)
                                len
                                target
                                element
                                lb
                                rb)))
  "AST node for an array index expression such as foo[bar]."
  target  ; a `js3-node' - the expression preceding the "."
  element ; a `js3-node' - the expression in brackets
  lb      ; position of left-bracket, nil if omitted
  rb)     ; position of right-bracket, nil if omitted

(put 'cl-struct-js3-elem-get-node 'js3-visitor 'js3-visit-elem-get-node)
(put 'cl-struct-js3-elem-get-node 'js3-printer 'js3-print-elem-get-node)
(put 'cl-struct-js3-elem-get-node 'js3-printer-test 'js3-print-elem-get-node-test)

(defun js3-visit-elem-get-node (n v)
  (when (js3-elem-get-node-target n)
    (js3-visit-ast (js3-elem-get-node-target n) v))
  (when (js3-elem-get-node-element n)
    (js3-visit-ast (js3-elem-get-node-element n) v)))

(defun js3-print-elem-get-node (n i)
  (js3-print-ast (js3-elem-get-node-target n) 0)
  (js3-print "[")
  (js3-print-ast (js3-elem-get-node-element n) 0)
  (js3-print "]"))

(defun js3-print-elem-get-node-test (n i)
  (concat
   (js3-print-ast-test (js3-elem-get-node-target n) 0)
   (js3-print-test "[")
   (js3-print-ast-test (js3-elem-get-node-element n) 0)
   (js3-print-test "]")))

(defstruct (js3-call-node
            (:include js3-node)
            (:constructor nil)
            (:constructor make-js3-call-node
                          (&key (type js3-CALL)
                                (pos js3-ts-cursor)
                                len
                                target
                                args
                                lp
                                rp)))
  "AST node for a JavaScript function call."
  target  ; a `js3-node' evaluating to the function to call
  args  ; a lisp list of `js3-node' arguments
  lp    ; position of open-paren, or nil if missing
  rp)   ; position of close-paren, or nil if missing

(put 'cl-struct-js3-call-node 'js3-visitor 'js3-visit-call-node)
(put 'cl-struct-js3-call-node 'js3-printer 'js3-print-call-node)
(put 'cl-struct-js3-call-node 'js3-printer-test 'js3-print-call-node-test)

(defun js3-visit-call-node (n v)
  (js3-visit-ast (js3-call-node-target n) v)
  (dolist (arg (js3-call-node-args n))
    (js3-visit-ast arg v)))

(defun js3-print-call-node (n i)
  (js3-print-ast (js3-call-node-target n) 0)
  (js3-print "(")
  (js3-print-list (js3-call-node-args n))
  (js3-print ")"))

(defun js3-print-call-node-test (n i)
  (concat
   (js3-print-ast-test (js3-call-node-target n) 0)
   (js3-print-test "(")
   (js3-print-list-test (js3-call-node-args n))
   (js3-print-test ")")))

(defstruct (js3-yield-node
            (:include js3-node)
            (:constructor nil)
            (:constructor make-js3-yield-node
                          (&key (type js3-YIELD)
                                (pos js3-ts-cursor)
                                len
                                value)))
  "AST node for yield statement or expression."
  value) ; optional:  value to be yielded

(put 'cl-struct-js3-yield-node 'js3-visitor 'js3-visit-yield-node)
(put 'cl-struct-js3-yield-node 'js3-printer 'js3-print-yield-node)
(put 'cl-struct-js3-yield-node 'js3-printer-test 'js3-print-yield-node-test)

(defun js3-visit-yield-node (n v)
  (js3-visit-ast (js3-yield-node-value n) v))

(defun js3-print-yield-node (n i)
  (js3-print "yield")
  (when (js3-yield-node-value n)
    (js3-print " ")
    (js3-print-ast (js3-yield-node-value n) 0)))

(defun js3-print-yield-node-test (n i)
  (concat
   (js3-print-test "yield")
   (when (js3-yield-node-value n)
     (concat
      (js3-print-test " ")
      (js3-print-ast-test (js3-yield-node-value n) 0)))))

(defstruct (js3-paren-node
            (:include js3-node)
            (:constructor nil)
            (:constructor make-js3-paren-node
                          (&key (type js3-LP)
                                (pos js3-ts-cursor)
                                len
                                expr)))
  "AST node for a parenthesized expression.
In particular, used when the parens are syntactically optional,
as opposed to required parens such as those enclosing an if-conditional."
  expr)   ; `js3-node'

(put 'cl-struct-js3-paren-node 'js3-visitor 'js3-visit-paren-node)
(put 'cl-struct-js3-paren-node 'js3-printer 'js3-print-paren-node)
(put 'cl-struct-js3-paren-node 'js3-printer-test 'js3-print-paren-node-test)

(defun js3-visit-paren-node (n v)
  (js3-visit-ast (js3-paren-node-expr n) v))

(defun js3-print-paren-node (n i)
  (js3-print "(")
  (js3-print-expr (js3-paren-node-expr n) 0)
  (js3-print ")"))

(defun js3-print-paren-node-test (n i)
  (concat
   (js3-print-test "(")
   (js3-print-expr-test (js3-paren-node-expr n) 0)
   (js3-print-test ")")))

(defun js3-print-expr (n i)
  (if (not (or js3-compact js3-compact-expr))
      (js3-print-ast n i)
    (let ((temp (js3-print-expr-test n i)))
      (if (or (> (length temp) js3-max-columns)
              (string-match "\n" temp))
          (progn
            (js3-print " ")
            (js3-print-ast n i)
            (js3-print "\n"))
        (js3-print-expr-compact n i)))))

(defun js3-print-expr-compact (n i)
  (js3-print-ast n i))

(defun js3-print-expr-test (n i)
  (js3-print-ast-test n i))

(defstruct (js3-array-comp-node
            (:include js3-scope)
            (:constructor nil)
            (:constructor make-js3-array-comp-node
                          (&key (type js3-ARRAYCOMP)
                                (pos js3-ts-cursor)
                                len
                                result
                                loops
                                filter
                                if-pos
                                lp
                                rp)))
  "AST node for an Array comprehension such as [[x,y] for (x in foo) for (y in bar)]."
  result  ; result expression (just after left-bracket)
  loops   ; a lisp list of `js3-array-comp-loop-node'
  filter  ; guard/filter expression
  if-pos  ; buffer pos of 'if' keyword, if present, else nil
  lp      ; buffer position of if-guard left-paren, or nil if not present
  rp)     ; buffer position of if-guard right-paren, or nil if not present

(put 'cl-struct-js3-array-comp-node 'js3-visitor 'js3-visit-array-comp-node)
(put 'cl-struct-js3-array-comp-node 'js3-printer 'js3-print-array-comp-node)
(put 'cl-struct-js3-array-comp-node 'js3-printer-test 'js3-print-array-comp-node-test)

(defun js3-visit-array-comp-node (n v)
  (js3-visit-ast (js3-array-comp-node-result n) v)
  (dolist (l (js3-array-comp-node-loops n))
    (js3-visit-ast l v))
  (js3-visit-ast (js3-array-comp-node-filter n) v))

(defun js3-print-array-comp-node (n i)
  (js3-print "[")
  (js3-print-ast (js3-array-comp-node-result n) 0)
  (dolist (l (js3-array-comp-node-loops n))
    (js3-print " ")
    (js3-print-ast l 0))
  (when (js3-array-comp-node-filter n)
    (js3-print " if (")
    (js3-print-ast (js3-array-comp-node-filter n) 0))
  (js3-print ")]"))

(defun js3-print-array-comp-node-test (n i)
  (concat
   (js3-print-test "[")
   (js3-print-ast-test (js3-array-comp-node-result n) 0)
   (let ((temp ""))
     (dolist (l (js3-array-comp-node-loops n))
       (setq temp
             (concat
              temp
              (js3-print-test " ")
              (js3-print-ast-test l 0))))
     temp)
   (when (js3-array-comp-node-filter n)
     (concat
      (js3-print-test " if (")
      (js3-print-ast-test (js3-array-comp-node-filter n) 0)))
   (js3-print-test ")]")))

(defstruct (js3-array-comp-loop-node
            (:include js3-for-in-node)
            (:constructor nil)
            (:constructor make-js3-array-comp-loop-node
                          (&key (type js3-FOR)
                                (pos js3-ts-cursor)
                                len
                                iterator
                                object
                                in-pos
                                foreach-p
                                each-pos
                                lp
                                rp)))
  "AST subtree for each 'for (foo in bar)' loop in an array comprehension.")

(put 'cl-struct-js3-array-comp-loop-node 'js3-visitor 'js3-visit-array-comp-loop)
(put 'cl-struct-js3-array-comp-loop-node 'js3-printer 'js3-print-array-comp-loop)
(put 'cl-struct-js3-array-comp-loop-node 'js3-printer-test 'js3-print-array-comp-loop-test)

(defun js3-visit-array-comp-loop (n v)
  (js3-visit-ast (js3-array-comp-loop-node-iterator n) v)
  (js3-visit-ast (js3-array-comp-loop-node-object n) v))

(defun js3-print-array-comp-loop (n i)
  (js3-print "for (")
  (js3-print-ast (js3-array-comp-loop-node-iterator n) 0)
  (js3-print " in ")
  (js3-print-ast (js3-array-comp-loop-node-object n) 0)
  (js3-print ")"))

(defun js3-print-array-comp-loop-test (n i)
  (concat
   (js3-print-test "for (")
   (js3-print-ast-test (js3-array-comp-loop-node-iterator n) 0)
   (js3-print-test " in ")
   (js3-print-ast-test (js3-array-comp-loop-node-object n) 0)
   (js3-print-test ")")))

(defstruct (js3-empty-expr-node
            (:include js3-node)
            (:constructor nil)
            (:constructor make-js3-empty-expr-node
                          (&key (type js3-EMPTY)
                                (pos js3-token-beg)
                                len)))
  "AST node for an empty expression.")

(put 'cl-struct-js3-empty-expr-node 'js3-visitor 'js3-visit-none)
(put 'cl-struct-js3-empty-expr-node 'js3-printer 'js3-print-none)
(put 'cl-struct-js3-empty-expr-node 'js3-printer-test 'js3-print-none-test)

;;; Node utilities

(defsubst js3-node-line (n)
  "Fetch the source line number at the start of node N.
This is O(n) in the length of the source buffer; use prudently."
  (1+ (count-lines (point-min) (js3-node-abs-pos n))))

(defsubst js3-block-node-kid (n i)
  "Return child I of node N, or nil if there aren't that many."
  (nth i (js3-block-node-kids n)))

(defsubst js3-block-node-first (n)
  "Return first child of block node N, or nil if there is none."
  (first (js3-block-node-kids n)))

(defun js3-node-root (n)
  "Return the root of the AST containing N.
If N has no parent pointer, returns N."
  (let ((parent (js3-node-parent n)))
    (if parent
        (js3-node-root parent)
      n)))

(defun js3-node-position-in-parent (node &optional parent)
  "Return the position of NODE in parent's block-kids list.
PARENT can be supplied if known.  Positioned returned is zero-indexed.
Returns 0 if NODE is not a child of a block statement, or if NODE
is not a statement node."
  (let ((p (or parent (js3-node-parent node)))
        (i 0))
    (if (not (js3-block-node-p p))
        i
      (or (js3-position node (js3-block-node-kids p))
          0))))

(defsubst js3-node-short-name (n)
  "Return the short name of node N as a string, e.g. `js3-if-node'."
  (substring (symbol-name (aref n 0))
             (length "cl-struct-")))

(defsubst js3-node-child-list (node)
  "Return the child list for NODE, a lisp list of nodes.
Works for block nodes, array nodes, obj literals, funarg lists,
var decls and try nodes (for catch clauses).  Note that you should call
`js3-block-node-kids' on the function body for the body statements.
Returns nil for zero-length child lists or unsupported nodes."
  (cond
   ((js3-function-node-p node)
    (js3-function-node-params node))
   ((js3-block-node-p node)
    (js3-block-node-kids node))
   ((js3-try-node-p node)
    (js3-try-node-catch-clauses node))
   ((js3-array-node-p node)
    (js3-array-node-elems node))
   ((js3-object-node-p node)
    (js3-object-node-elems node))
   ((js3-call-node-p node)
    (js3-call-node-args node))
   ((js3-new-node-p node)
    (js3-new-node-args node))
   ((js3-var-decl-node-p node)
    (js3-var-decl-node-kids node))
   (t
    nil)))

(defsubst js3-node-set-child-list (node kids)
  "Set the child list for NODE to KIDS."
  (cond
   ((js3-function-node-p node)
    (setf (js3-function-node-params node) kids))
   ((js3-block-node-p node)
    (setf (js3-block-node-kids node) kids))
   ((js3-try-node-p node)
    (setf (js3-try-node-catch-clauses node) kids))
   ((js3-array-node-p node)
    (setf (js3-array-node-elems node) kids))
   ((js3-object-node-p node)
    (setf (js3-object-node-elems node) kids))
   ((js3-call-node-p node)
    (setf (js3-call-node-args node) kids))
   ((js3-new-node-p node)
    (setf (js3-new-node-args node) kids))
   ((js3-var-decl-node-p node)
    (setf (js3-var-decl-node-kids node) kids))
   (t
    (error "Unsupported node type: %s" (js3-node-short-name node))))
  kids)

;; All because Common Lisp doesn't support multiple inheritance for defstructs.
(defconst js3-paren-expr-nodes
  '(cl-struct-js3-array-comp-loop-node
    cl-struct-js3-array-comp-node
    cl-struct-js3-call-node
    cl-struct-js3-catch-node
    cl-struct-js3-do-node
    cl-struct-js3-elem-get-node
    cl-struct-js3-for-in-node
    cl-struct-js3-for-node
    cl-struct-js3-function-node
    cl-struct-js3-if-node
    cl-struct-js3-let-node
    cl-struct-js3-new-node
    cl-struct-js3-paren-node
    cl-struct-js3-switch-node
    cl-struct-js3-while-node
    cl-struct-js3-with-node)
  "Node types that can have a parenthesized child expression.
In particular, nodes that respond to `js3-node-lp' and `js3-node-rp'.")

(defsubst js3-paren-expr-node-p (node)
  "Return t for nodes that typically have a parenthesized child expression.
Useful for computing the indentation anchors for arg-lists and conditions.
Note that it may return a false positive, for instance when NODE is
a `js3-new-node' and there are no arguments or parentheses."
  (memq (aref node 0) js3-paren-expr-nodes))

;; Fake polymorphism... yech.
(defsubst js3-node-lp (node)
  "Return relative left-paren position for NODE, if applicable.
For `js3-elem-get-node' structs, returns left-bracket position.
Note that the position may be nil in the case of a parse error."
  (cond
   ((js3-elem-get-node-p node)
    (js3-elem-get-node-lb node))
   ((js3-loop-node-p node)
    (js3-loop-node-lp node))
   ((js3-function-node-p node)
    (js3-function-node-lp node))
   ((js3-if-node-p node)
    (js3-if-node-lp node))
   ((js3-new-node-p node)
    (js3-new-node-lp node))
   ((js3-call-node-p node)
    (js3-call-node-lp node))
   ((js3-paren-node-p node)
    (js3-node-pos node))
   ((js3-switch-node-p node)
    (js3-switch-node-lp node))
   ((js3-catch-node-p node)
    (js3-catch-node-lp node))
   ((js3-let-node-p node)
    (js3-let-node-lp node))
   ((js3-array-comp-node-p node)
    (js3-array-comp-node-lp node))
   ((js3-with-node-p node)
    (js3-with-node-lp node))
   (t
    (error "Unsupported node type: %s" (js3-node-short-name node)))))

;; Fake polymorphism... blech.
(defsubst js3-node-rp (node)
  "Return relative right-paren position for NODE, if applicable.
For `js3-elem-get-node' structs, returns right-bracket position.
Note that the position may be nil in the case of a parse error."
  (cond
   ((js3-elem-get-node-p node)
    (js3-elem-get-node-lb node))
   ((js3-loop-node-p node)
    (js3-loop-node-rp node))
   ((js3-function-node-p node)
    (js3-function-node-rp node))
   ((js3-if-node-p node)
    (js3-if-node-rp node))
   ((js3-new-node-p node)
    (js3-new-node-rp node))
   ((js3-call-node-p node)
    (js3-call-node-rp node))
   ((js3-paren-node-p node)
    (+ (js3-node-pos node) (js3-node-len node)))
   ((js3-switch-node-p node)
    (js3-switch-node-rp node))
   ((js3-catch-node-p node)
    (js3-catch-node-rp node))
   ((js3-let-node-p node)
    (js3-let-node-rp node))
   ((js3-array-comp-node-p node)
    (js3-array-comp-node-rp node))
   ((js3-with-node-p node)
    (js3-with-node-rp node))
   (t
    (error "Unsupported node type: %s" (js3-node-short-name node)))))

(defsubst js3-node-first-child (node)
  "Returns the first element of `js3-node-child-list' for NODE."
  (car (js3-node-child-list node)))

(defsubst js3-node-last-child (node)
  "Returns the last element of `js3-node-last-child' for NODE."
  (car (last (js3-node-child-list node))))

(defun js3-node-prev-sibling (node)
  "Return the previous statement in parent.
Works for parents supported by `js3-node-child-list'.
Returns nil if NODE is not in the parent, or PARENT is
not a supported node, or if NODE is the first child."
  (let* ((p (js3-node-parent node))
         (kids (js3-node-child-list p))
         (sib (car kids)))
    (while (and kids
                (neq node (cadr kids)))
      (setq kids (cdr kids)
            sib (car kids)))
    sib))

(defun js3-node-next-sibling (node)
  "Return the next statement in parent block.
Returns nil if NODE is not in the block, or PARENT is not
a block node, or if NODE is the last statement."
  (let* ((p (js3-node-parent node))
         (kids (js3-node-child-list p)))
    (while (and kids
                (neq node (car kids)))
      (setq kids (cdr kids)))
    (cadr kids)))

(defun js3-node-find-child-before (pos parent &optional after)
  "Find the last child that starts before POS in parent.
If AFTER is non-nil, returns first child starting after POS.
POS is an absolute buffer position.  PARENT is any node
supported by `js3-node-child-list'.
Returns nil if no applicable child is found."
  (let ((kids (if (js3-function-node-p parent)
                  (js3-block-node-kids (js3-function-node-body parent))
                (js3-node-child-list parent)))
        (beg (if (js3-function-node-p parent)
                 (js3-node-abs-pos (js3-function-node-body parent))
               (js3-node-abs-pos parent)))
        kid
        result
        fn
        (continue t))
    (setq fn (if after '> '<))
    (while (and kids continue)
      (setq kid (car kids))
      (if (funcall fn (+ beg (js3-node-pos kid)) pos)
          (setq result kid
                continue (if after nil t))
        (setq continue (if after t nil)))
      (setq kids (cdr kids)))
    result))

(defun js3-node-find-child-after (pos parent)
  "Find first child that starts after POS in parent.
POS is an absolute buffer position.  PARENT is any node
supported by `js3-node-child-list'.
Returns nil if no applicable child is found."
  (js3-node-find-child-before pos parent 'after))

(defun js3-node-replace-child (pos parent new-node)
  "Replace node at index POS in PARENT with NEW-NODE.
Only works for parents supported by `js3-node-child-list'."
  (let ((kids (js3-node-child-list parent))
        (i 0))
    (while (< i pos)
      (setq kids (cdr kids)
            i (1+ i)))
    (setcar kids new-node)
    (js3-node-add-children parent new-node)))

(defun js3-node-buffer (n)
  "Return the buffer associated with AST N.
Returns nil if the buffer is not set as a property on the root
node, or if parent links were not recorded during parsing."
  (let ((root (js3-node-root n)))
    (and root
         (js3-ast-root-p root)
         (js3-ast-root-buffer root))))

(defsubst js3-block-node-push (n kid)
  "Push js3-node KID onto the end of js3-block-node N's child list.
KID is always added to the -end- of the kids list.
Function also calls `js3-node-add-children' to add the parent link."
  (let ((kids (js3-node-child-list n)))
    (if kids
        (setcdr kids (nconc (cdr kids) (list kid)))
      (js3-node-set-child-list n (list kid)))
    (js3-node-add-children n kid)))

(defun js3-node-string (node)
  (let ((buf (js3-node-buffer node))
        pos)
    (unless buf
      (error "No buffer available for node %s" node))
    (save-excursion
      (let ()
        (set-buffer buf)
        (buffer-substring-no-properties (setq pos (js3-node-abs-pos node))
                                        (+ pos (js3-node-len node)))))))

;; Container for storing the node we're looking for in a traversal.
(defvar js3-discovered-node nil)
(make-variable-buffer-local 'js3-discovered-node)

;; Keep track of absolute node position during traversals.
(defvar js3-visitor-offset nil)
(make-variable-buffer-local 'js3-visitor-offset)

(defvar js3-node-search-point nil)
(make-variable-buffer-local 'js3-node-search-point)

(when js3-mode-dev-mode-p
  (defun js3-find-node-at-point ()
    (interactive)
    (let ((node (js3-node-at-point)))
      (message "%s" (or node "No node found at point"))))
  (defun js3-node-name-at-point ()
    (interactive)
    (let ((node (js3-node-at-point)))
      (message "%s" (if node
                        (js3-node-short-name node)
                      "No node found at point."))))
  (defun js3-print-debug-tree ()
    (interactive)
    (print (js3-node-at-point))))

(defun js3-node-at-point (&optional pos skip-comments)
  "Return AST node at POS, a buffer position, defaulting to current point.
The `js3-mode-ast' variable must be set to the current parse tree.
Signals an error if the AST (`js3-mode-ast') is nil.
Always returns a node - if it can't find one, it returns the root.
If SKIP-COMMENTS is non-nil, comment nodes are ignored."
  (let ((ast js3-mode-ast)
        result)
    (unless ast
      (error "No JavaScript AST available"))
    ;; Look through comments first, since they may be inside nodes that
    ;; would otherwise report a match.
    (setq pos (or pos (point))
          result (if (> pos (js3-node-abs-end ast))
                     ast
                   (if (not skip-comments)
                       (js3-comment-at-point pos))))
    (unless result
      (setq js3-discovered-node nil
            js3-visitor-offset 0
            js3-node-search-point pos)
      (unwind-protect
          (catch 'js3-visit-done
            (js3-visit-ast ast #'js3-node-at-point-visitor))
        (setq js3-visitor-offset nil
              js3-node-search-point nil))
      (setq result js3-discovered-node))
    ;; may have found a comment beyond end of last child node,
    ;; since visiting the ast-root looks at the comment-list last.
    (if (and skip-comments
             (js3-comment-node-p result))
        (setq result nil))
    (or result js3-mode-ast)))

(defun js3-node-at-point-visitor (node end-p)
  (let ((rel-pos (js3-node-pos node))
        abs-pos
        abs-end
        (point js3-node-search-point))
    (cond
     (end-p
      ;; this evaluates to a non-nil return value, even if it's zero
      (decf js3-visitor-offset rel-pos))
     ;; we already looked for comments before visiting, and don't want them now
     ((js3-comment-node-p node)
      nil)
     (t
      (setq abs-pos (incf js3-visitor-offset rel-pos)
            ;; we only want to use the node if the point is before
            ;; the last character position in the node, so we decrement
            ;; the absolute end by 1.
            abs-end (+ abs-pos (js3-node-len node) -1))
      (cond
       ;; If this node starts after search-point, stop the search.
       ((> abs-pos point)
        (throw 'js3-visit-done nil))
       ;; If this node ends before the search-point, don't check kids.
       ((> point abs-end)
        nil)
       (t
        ;; Otherwise point is within this node, possibly in a child.
        (setq js3-discovered-node node)
        t))))))  ; keep processing kids to look for more specific match

(defsubst js3-block-comment-p (node)
  "Return non-nil if NODE is a comment node of format `jsdoc' or `block'."
  (and (js3-comment-node-p node)
       (memq (js3-comment-node-format node) '(jsdoc block))))

;; TODO:  put the comments in a vector and binary-search them instead
(defun js3-comment-at-point (&optional pos)
  "Look through scanned comment nodes for one containing POS.
POS is a buffer position that defaults to current point.
Function returns nil if POS was not in any comment node."
  (let ((ast js3-mode-ast)
        (x (or pos (point)))
        beg
        end)
    (unless ast
      (error "No JavaScript AST available"))
    (catch 'done
      ;; Comments are stored in lexical order.
      (dolist (comment (js3-ast-root-comments ast) nil)
        (setq beg (js3-node-abs-pos comment)
              end (+ beg (js3-node-len comment)))
        (if (and (>= x beg)
                 (<= x end))
            (throw 'done comment))))))

(defun js3-mode-find-parent-fn (node)
  "Find function enclosing NODE.
Returns nil if NODE is not inside a function."
  (setq node (js3-node-parent node))
  (while (and node (not (js3-function-node-p node)))
    (setq node (js3-node-parent node)))
  (and (js3-function-node-p node) node))

(defun js3-mode-find-enclosing-fn (node)
  "Find function or root enclosing NODE."
  (if (js3-ast-root-p node)
      node
    (setq node (js3-node-parent node))
    (while (not (or (js3-ast-root-p node)
                    (js3-function-node-p node)))
      (setq node (js3-node-parent node)))
    node))

(defun js3-mode-find-enclosing-node (beg end)
  "Find script or function fully enclosing BEG and END."
  (let ((node (js3-node-at-point beg))
        pos
        (continue t))
    (while continue
      (if (or (js3-ast-root-p node)
              (and (js3-function-node-p node)
                   (<= (setq pos (js3-node-abs-pos node)) beg)
                   (>= (+ pos (js3-node-len node)) end)))
          (setq continue nil)
        (setq node (js3-node-parent node))))
    node))

(defun js3-node-parent-script-or-fn (node)
  "Find script or function immediately enclosing NODE.
If NODE is the ast-root, returns nil."
  (if (js3-ast-root-p node)
      nil
    (setq node (js3-node-parent node))
    (while (and node (not (or (js3-function-node-p node)
                              (js3-script-node-p node))))
      (setq node (js3-node-parent node)))
    node))

(defsubst js3-nested-function-p (node)
  "Return t if NODE is a nested function, or is inside a nested function."
  (unless (js3-ast-root-p node)
    (js3-function-node-p (if (js3-function-node-p node)
                             (js3-node-parent-script-or-fn node)
                           (js3-node-parent-script-or-fn
                            (js3-node-parent-script-or-fn node))))))

(defsubst js3-mode-shift-kids (kids start offset)
  (dolist (kid kids)
    (if (> (js3-node-pos kid) start)
        (incf (js3-node-pos kid) offset))))

(defsubst js3-mode-shift-children (parent start offset)
  "Update start-positions of all children of PARENT beyond START."
  (let ((root (js3-node-root parent)))
    (js3-mode-shift-kids (js3-node-child-list parent) start offset)
    (js3-mode-shift-kids (js3-ast-root-comments root) start offset)))

(defsubst js3-node-is-descendant (node ancestor)
  "Return t if NODE is a descendant of ANCESTOR."
  (while (and node
              (neq node ancestor))
    (setq node (js3-node-parent node)))
  node)

;;; visitor infrastructure

(defun js3-visit-none (node callback)
  "Visitor for AST node that have no node children."
  nil)

(defun js3-print-none (node indent)
  "Visitor for AST node with no printed representation.")

(defun js3-print-none-test (node indent)
  "")

(defun js3-print-body (node indent)
  "Print a statement, or a block without braces."
  (if (js3-block-node-p node)
      (dolist (kid (js3-block-node-kids node))
        (js3-print-ast kid indent))
    (js3-print-ast node indent)))

(defun js3-print-body-test (node indent)
  "Print a statement, or a block without braces."
  (if (js3-block-node-p node)
      (let ((temp ""))
        (dolist (kid (js3-block-node-kids node))
          (setq temp (concat temp (js3-print-ast-test kid indent))))
        temp)
    (js3-print-ast-test node indent)))

(defun js3-print-list (args &optional delimiter)
  (if (not (or js3-compact js3-compact-list))
      (js3-print-list-long args delimiter)
    (let ((temp (js3-print-list-test args delimiter)))
      (if (or (> (length temp) js3-max-columns)
              (string-match "\n" temp))
          (js3-print-list-long args delimiter)
        (js3-print-list-compact args delimiter)))))

(defun js3-print-list-long (args &optional delimiter)
  (loop with len = (length args)
        for arg in args
        for count from 1
        do
        (if (and (= count 1) (> len 1))
            (js3-print " "))
        (js3-print-ast arg 0)
        (if (< count len)
            (js3-print (or delimiter "\n, "))
          (when (> len 1)
            (js3-print "\n")))))

(defun js3-print-list-compact (args &optional delimiter)
  (loop with len = (length args)
        for arg in args
        for count from 1
        do
        (if (and (= count 1) (> len 1))
            (js3-print ""))
        (js3-print-ast arg 0)
        (if (< count len)
            (js3-print (or delimiter ", "))
          (when (> len 1)
            (js3-print "")))))

(defun js3-print-list-test (args &optional delimiter)
  (let ((temp ""))
    (loop with len = (length args)
          for arg in args
          for count from 1
          do
          (setq temp
                (concat
                 temp
                 (if (and (= count 1) (> len 1))
                     (js3-print-test "")
                   (js3-print-test ""))
                 (js3-print-ast-test arg 0)
                 (if (< count len)
                     (js3-print-test (or delimiter ", "))
                   (js3-print-test "")))))
    temp))

(defun js3-pretty-print-no-indent ()
  "Prints the current AST to the temp buffer"
  (interactive)
  (js3-reparse)
  (setq js3-current-buffer (current-buffer))
  (js3-print-tree js3-mode-ast))

(defun js3-print-tree (ast)
  "Prints an AST to the temp buffer.
Makes `js3-ast-parent-nodes' available to the printer functions."
  (let ((max-lisp-eval-depth (max max-lisp-eval-depth 1500)))
    (set-buffer (get-buffer-create js3-temp-buffer))
    (erase-buffer)
    (set-buffer js3-current-buffer)
    (js3-print-ast ast)
    (js3-print "\n")
    (js3-print "//Comments:\n")
    (dolist (comment (js3-ast-root-comments ast))
      (js3-print-ast comment 0))))

(defun js3-print-ast (node &optional indent)
  "Helper function for printing AST nodes.
Requires `js3-ast-parent-nodes' to be non-nil.
You should use `js3-print-tree' instead of this function."
  (let ((printer (get (aref node 0) 'js3-printer))
        (i (or indent 0))
        (pos (js3-node-abs-pos node)))
    ;; TODO:  wedge comments in here somewhere
    (if printer
        (funcall printer node i))))

(defun js3-print-ast-test (node &optional indent)
  "Helper function for printing AST nodes.
Requires `js3-ast-parent-nodes' to be non-nil.
You should use `js3-print-tree' instead of this function."
  (let ((printer (get (aref node 0) 'js3-printer-test))
        (i (or indent 0))
        (pos (js3-node-abs-pos node)))
    ;; TODO:  wedge comments in here somewhere
    (if printer
        (funcall printer node i))))

(defconst js3-side-effecting-tokens
  (let ((tokens (make-bool-vector js3-num-tokens nil)))
    (dolist (tt (list js3-ASSIGN
                      js3-ASSIGN_ADD
                      js3-ASSIGN_BITAND
                      js3-ASSIGN_BITOR
                      js3-ASSIGN_BITXOR
                      js3-ASSIGN_DIV
                      js3-ASSIGN_LSH
                      js3-ASSIGN_MOD
                      js3-ASSIGN_MUL
                      js3-ASSIGN_RSH
                      js3-ASSIGN_SUB
                      js3-ASSIGN_URSH
                      js3-BLOCK
                      js3-BREAK
                      js3-CALL
                      js3-CATCH
                      js3-CATCH_SCOPE
                      js3-CONST
                      js3-CONTINUE
                      js3-DEBUGGER
                      js3-DEC
                      js3-DELPROP
                      js3-DEL_REF
                      js3-DO
                      js3-ELSE
                      js3-EMPTY
                      js3-ENTERWITH
                      js3-EXPORT
                      js3-EXPR_RESULT
                      js3-FINALLY
                      js3-FOR
                      js3-FUNCTION
                      js3-GOTO
                      js3-IF
                      js3-IFEQ
                      js3-IFNE
                      js3-IMPORT
                      js3-INC
                      js3-JSR
                      js3-LABEL
                      js3-LEAVEWITH
                      js3-LET
                      js3-LETEXPR
                      js3-LOCAL_BLOCK
                      js3-LOOP
                      js3-NEW
                      js3-REF_CALL
                      js3-RETHROW
                      js3-RETURN
                      js3-RETURN_RESULT
                      js3-SEMI
                      js3-SETELEM
                      js3-SETELEM_OP
                      js3-SETNAME
                      js3-SETPROP
                      js3-SETPROP_OP
                      js3-SETVAR
                      js3-SET_REF
                      js3-SET_REF_OP
                      js3-SWITCH
                      js3-TARGET
                      js3-THROW
                      js3-TRY
                      js3-VAR
                      js3-WHILE
                      js3-WITH
                      js3-WITHEXPR
                      js3-YIELD))
      (aset tokens tt t))
    (if js3-instanceof-has-side-effects
        (aset tokens js3-INSTANCEOF t))
    tokens))

(defun js3-node-has-side-effects (node)
  "Return t if NODE has side effects."
  (when node  ; makes it easier to handle malformed expressions
    (let ((tt (js3-node-type node)))
      (cond
       ;; This doubtless needs some work, since EXPR_VOID is used
       ;; in several ways in Rhino, and I may not have caught them all.
       ;; I'll wait for people to notice incorrect warnings.
       ((and (= tt js3-EXPR_VOID)
             (js3-expr-stmt-node-p node)) ; but not if EXPR_RESULT
        (let ((expr (js3-expr-stmt-node-expr node)))
          (or (js3-node-has-side-effects expr)
              (when (js3-string-node-p expr)
                (string= "use strict" (js3-string-node-value expr))))))
       ((= tt js3-COMMA)
        (js3-node-has-side-effects (js3-infix-node-right node)))
       ((or (= tt js3-AND)
            (= tt js3-OR))
        (or (js3-node-has-side-effects (js3-infix-node-right node))
            (js3-node-has-side-effects (js3-infix-node-left node))))
       ((= tt js3-HOOK)
        (and (js3-node-has-side-effects (js3-cond-node-true-expr node))
             (js3-node-has-side-effects (js3-cond-node-false-expr node))))
       ((js3-paren-node-p node)
        (js3-node-has-side-effects (js3-paren-node-expr node)))
       ((= tt js3-ERROR) ; avoid cascaded error messages
        nil)
       (t
        (aref js3-side-effecting-tokens tt))))))

(defun js3-member-expr-leftmost-name (node)
  "For an expr such as foo.bar.baz, return leftmost node foo.
NODE is any `js3-node' object.  If it represents a member
expression, which is any sequence of property gets, element-gets,
or function calls, then we look at the lexically leftmost (first)
node in the chain.  If it is a name-node we return it.  Note that
NODE can be a raw name-node and it will be returned as well.  If
NODE is not a name-node or member expression, or if it is a
member expression whose leftmost target is not a name node,
returns nil."
  (let ((continue t)
        result)
    (while (and continue (not result))
      (cond
       ((js3-name-node-p node)
        (setq result node))
       ((js3-prop-get-node-p node)
        (setq node (js3-prop-get-node-left node)))
       (t
        (setq continue nil))))
    result))

(defconst js3-stmt-node-types
  (list js3-BLOCK
        js3-BREAK
        js3-CONTINUE
        js3-DO
        js3-EXPR_RESULT
        js3-EXPR_VOID
        js3-FOR
        js3-IF
        js3-RETURN
        js3-SWITCH
        js3-THROW
        js3-TRY
        js3-WHILE
        js3-WITH)
  "Node types that only appear in statement contexts.
The list does not include nodes that always appear as the child
of another specific statement type, such as switch-cases,
catch and finally blocks, and else-clauses.  The list also excludes
nodes like yield, let and var, which may appear in either expression
or statement context, and in the latter context always have a
`js3-expr-stmt-node' parent.  Finally, the list does not include
functions or scripts, which are treated separately from statements
by the JavaScript parser and runtime.")

(defun js3-stmt-node-p (node)
  "Heuristic for figuring out if NODE is a statement.
Some node types can appear in either an expression context or a
statement context, e.g. let-nodes, yield-nodes, and var-decl nodes.
For these node types in a statement context, the parent will be a
`js3-expr-stmt-node'.
Functions aren't included in the check."
  (memq (js3-node-type node) js3-stmt-node-types))

(defsubst js3-mode-find-first-stmt (node)
  "Search upward starting from NODE looking for a statement.
For purposes of this function, a `js3-function-node' counts."
  (while (not (or (js3-stmt-node-p node)
                  (js3-function-node-p node)))
    (setq node (js3-node-parent node)))
  node)

(defun js3-node-parent-stmt (node)
  "Return the node's first ancestor that is a statement.
Returns nil if NODE is a `js3-ast-root'.  Note that any expression
appearing in a statement context will have a parent that is a
`js3-expr-stmt-node' that will be returned by this function."
  (let ((parent (js3-node-parent node)))
    (if (or (null parent)
            (js3-stmt-node-p parent)
            (and (js3-function-node-p parent)
                 (neq (js3-function-node-form parent) 'FUNCTION_EXPRESSION)))
        parent
      (js3-node-parent-stmt parent))))

;; Roshan James writes:
;;  Does consistent-return analysis on the function body when strict mode is
;;  enabled.
;;
;;    function (x) { return (x+1) }
;;
;;  is ok, but
;;
;;    function (x) { if (x < 0) return (x+1); }
;;
;;  is not because the function can potentially return a value when the
;;  condition is satisfied and if not, the function does not explicitly
;;  return a value.
;;
;;  This extends to checking mismatches such as "return" and "return <value>"
;;  used in the same function. Warnings are not emitted if inconsistent
;;  returns exist in code that can be statically shown to be unreachable.
;;  Ex.
;;    function (x) { while (true) { ... if (..) { return value } ... } }
;;
;;  emits no warning. However if the loop had a break statement, then a
;;  warning would be emitted.
;;
;;  The consistency analysis looks at control structures such as loops, ifs,
;;  switch, try-catch-finally blocks, examines the reachable code paths and
;;  warns the user about an inconsistent set of termination possibilities.
;;
;;  These flags enumerate the possible ways a statement/function can
;;  terminate. These flags are used by endCheck() and by the Parser to
;;  detect inconsistent return usage.
;;
;;  END_UNREACHED is reserved for code paths that are assumed to always be
;;  able to execute (example: throw, continue)
;;
;;  END_DROPS_OFF indicates if the statement can transfer control to the
;;  next one. Statement such as return dont. A compound statement may have
;;  some branch that drops off control to the next statement.
;;
;;  END_RETURNS indicates that the statement can return with no value.
;;  END_RETURNS_VALUE indicates that the statement can return a value.
;;
;;  A compound statement such as
;;  if (condition) {
;;    return value;
;;  }
;;  Will be detected as (END_DROPS_OFF | END_RETURN_VALUE) by endCheck()

(defconst js3-END_UNREACHED 0)
(defconst js3-END_DROPS_OFF 1)
(defconst js3-END_RETURNS 2)
(defconst js3-END_RETURNS_VALUE 4)
(defconst js3-END_YIELDS 8)

(defun js3-has-consistent-return-usage (node)
  "Check that every return usage in a function body is consistent.
Returns t if the function satisfies strict mode requirement."
  (let ((n (js3-end-check node)))
    ;; either it doesn't return a value in any branch...
    (or (js3-flag-not-set-p n js3-END_RETURNS_VALUE)
        ;; or it returns a value (or is unreached) at every branch
        (js3-flag-not-set-p n (logior js3-END_DROPS_OFF
                                      js3-END_RETURNS
                                      js3-END_YIELDS)))))

(defun js3-end-check-if (node)
  "Returns in the then and else blocks must be consistent with each other.
If there is no else block, then the return statement can fall through.
Returns logical OR of END_* flags"
  (let ((th (js3-if-node-then-part node))
        (el (js3-if-node-else-part node)))
    (if (null th)
        js3-END_UNREACHED
      (logior (js3-end-check th) (if el
                                     (js3-end-check el)
                                   js3-END_DROPS_OFF)))))

(defun js3-end-check-switch (node)
  "Consistency of return statements is checked between the case statements.
If there is no default, then the switch can fall through. If there is a
default, we check to see if all code paths in the default return or if
there is a code path that can fall through.
Returns logical OR of END_* flags."
  (let ((rv js3-END_UNREACHED)
        default-case)
    ;; examine the cases
    (catch 'break
      (dolist (c (js3-switch-node-cases node))
        (if (js3-case-node-expr c)
            (js3-set-flag rv (js3-end-check-block c))
          (setq default-case c)
          (throw 'break nil))))
    ;; we don't care how the cases drop into each other
    (js3-clear-flag rv js3-END_DROPS_OFF)
    ;; examine the default
    (js3-set-flag rv (if default-case
                         (js3-end-check default-case)
                       js3-END_DROPS_OFF))
    rv))

(defun js3-end-check-try (node)
  "If the block has a finally, return consistency is checked in the
finally block. If all code paths in the finally return, then the
returns in the try-catch blocks don't matter. If there is a code path
that does not return or if there is no finally block, the returns
of the try and catch blocks are checked for mismatch.
Returns logical OR of END_* flags."
  (let ((finally (js3-try-node-finally-block node))
        rv)
    ;; check the finally if it exists
    (setq rv (if finally
                 (js3-end-check (js3-finally-node-body finally))
               js3-END_DROPS_OFF))
    ;; If the finally block always returns, then none of the returns
    ;; in the try or catch blocks matter.
    (when (js3-flag-set-p rv js3-END_DROPS_OFF)
      (js3-clear-flag rv js3-END_DROPS_OFF)
      ;; examine the try block
      (js3-set-flag rv (js3-end-check (js3-try-node-try-block node)))
      ;; check each catch block
      (dolist (cb (js3-try-node-catch-clauses node))
        (js3-set-flag rv (js3-end-check (js3-catch-node-block cb)))))
    rv))

(defun js3-end-check-loop (node)
  "Return statement in the loop body must be consistent. The default
assumption for any kind of a loop is that it will eventually terminate.
The only exception is a loop with a constant true condition. Code that
follows such a loop is examined only if one can statically determine
that there is a break out of the loop.

for(... ; ... ; ...) {}
for(... in ... ) {}
while(...) { }
do { } while(...)

Returns logical OR of END_* flags."
  (let ((rv (js3-end-check (js3-loop-node-body node)))
        (condition (cond
                    ((js3-while-node-p node)
                     (js3-while-node-condition node))
                    ((js3-do-node-p node)
                     (js3-do-node-condition node))
                    ((js3-for-node-p node)
                     (js3-for-node-condition node)))))

    ;; check to see if the loop condition is always true
    (if (and condition
             (eq (js3-always-defined-boolean-p condition) 'ALWAYS_TRUE))
        (js3-clear-flag rv js3-END_DROPS_OFF))

    ;; look for effect of breaks
    (js3-set-flag rv (js3-node-get-prop node
                                        'CONTROL_BLOCK_PROP
                                        js3-END_UNREACHED))
    rv))

(defun js3-end-check-block (node)
  "A general block of code is examined statement by statement.
If any statement (even a compound one) returns in all branches, then
subsequent statements are not examined.
Returns logical OR of END_* flags."
  (let* ((rv js3-END_DROPS_OFF)
         (kids (js3-block-node-kids node))
         (n (car kids)))
    ;; Check each statment.  If the statement can continue onto the next
    ;; one (i.e. END_DROPS_OFF is set), then check the next statement.
    (while (and n (js3-flag-set-p rv js3-END_DROPS_OFF))
      (js3-clear-flag rv js3-END_DROPS_OFF)
      (js3-set-flag rv (js3-end-check n))
      (setq kids (cdr kids)
            n (car kids)))
    rv))

(defun js3-end-check-label (node)
  "A labeled statement implies that there may be a break to the label.
The function processes the labeled statement and then checks the
CONTROL_BLOCK_PROP property to see if there is ever a break to the
particular label.
Returns logical OR of END_* flags."
  (let ((rv (js3-end-check (js3-labeled-stmt-node-stmt node))))
    (logior rv (js3-node-get-prop node
                                  'CONTROL_BLOCK_PROP
                                  js3-END_UNREACHED))))

(defun js3-end-check-break (node)
  "When a break is encountered annotate the statement being broken
out of by setting its CONTROL_BLOCK_PROP property.
Returns logical OR of END_* flags."
  (and (js3-break-node-target node)
       (js3-node-set-prop (js3-break-node-target node)
                          'CONTROL_BLOCK_PROP
                          js3-END_DROPS_OFF))
  js3-END_UNREACHED)

(defun js3-end-check (node)
  "Examine the body of a function, doing a basic reachability analysis.
Returns a combination of flags END_* flags that indicate
how the function execution can terminate. These constitute only the
pessimistic set of termination conditions. It is possible that at
runtime certain code paths will never be actually taken. Hence this
analysis will flag errors in cases where there may not be errors.
Returns logical OR of END_* flags"
  (let (kid)
    (cond
     ((js3-break-node-p node)
      (js3-end-check-break node))
     ((js3-expr-stmt-node-p node)
      (if (setq kid (js3-expr-stmt-node-expr node))
          (js3-end-check kid)
        js3-END_DROPS_OFF))
     ((or (js3-continue-node-p node)
          (js3-throw-node-p node))
      js3-END_UNREACHED)
     ((js3-return-node-p node)
      (if (setq kid (js3-return-node-retval node))
          js3-END_RETURNS_VALUE
        js3-END_RETURNS))
     ((js3-loop-node-p node)
      (js3-end-check-loop node))
     ((js3-switch-node-p node)
      (js3-end-check-switch node))
     ((js3-labeled-stmt-node-p node)
      (js3-end-check-label node))
     ((js3-if-node-p node)
      (js3-end-check-if node))
     ((js3-try-node-p node)
      (js3-end-check-try node))
     ((js3-block-node-p node)
      (if (null (js3-block-node-kids node))
          js3-END_DROPS_OFF
        (js3-end-check-block node)))
     ((js3-yield-node-p node)
      js3-END_YIELDS)
     (t
      js3-END_DROPS_OFF))))

(defun js3-always-defined-boolean-p (node)
  "Check if NODE always evaluates to true or false in boolean context.
Returns 'ALWAYS_TRUE, 'ALWAYS_FALSE, or nil if it's neither always true
nor always false."
  (let ((tt (js3-node-type node))
        num)
    (cond
     ((or (= tt js3-FALSE) (= tt js3-NULL))
      'ALWAYS_FALSE)
     ((= tt js3-TRUE)
      'ALWAYS_TRUE)
     ((= tt js3-NUMBER)
      (setq num (js3-number-node-num-value node))
      (if (and (not (eq num 0.0e+NaN))
               (not (zerop num)))
          'ALWAYS_TRUE
        'ALWAYS_FALSE))
     (t
      nil))))

(defun js3-print (str)
  "print the string"
  (set-buffer (get-buffer-create js3-temp-buffer))
  (insert str)
  (set-buffer js3-current-buffer))

(defun js3-delete-semicolons ()
  "backspace over semicolons in the output buffer"
  (set-buffer (get-buffer-create js3-temp-buffer))
  (while (looking-back "\\(;\\|\\s-\\|\n\\)+" nil)
    (delete-char -1))
  (set-buffer js3-current-buffer))

(defun js3-print-test (str)
  str)

(provide 'js3-ast)

;;; js3-ast.el ends here
;;; js3-highlight.el --- JavaScript syntax coloring support

;;; Code:


(defsubst js3-set-face (beg end face &optional record)
  "Fontify a region.  If RECORD is non-nil, record for later."
  (when (plusp js3-highlight-level)
    (setq beg (min (point-max) beg)
          beg (max (point-min) beg)
          end (min (point-max) end)
          end (max (point-min) end))
    (if record
        (push (list beg end face) js3-mode-fontifications)
      (put-text-property beg end 'font-lock-face face))))

(defsubst js3-set-kid-face (pos kid len face)
  "Set-face on a child node.
POS is absolute buffer position of parent.
KID is the child node.
LEN is the length to fontify.
FACE is the face to fontify with."
  (js3-set-face (+ pos (js3-node-pos kid))
                (+ pos (js3-node-pos kid) (js3-node-len kid))
                face))

(defsubst js3-fontify-kwd (start length)
  (js3-set-face start (+ start length) 'font-lock-keyword-face))

(defsubst js3-clear-face (beg end)
  (remove-text-properties beg end '(font-lock-face nil
						   help-echo nil
						   point-entered nil
						   c-in-sws nil)))

(defconst js3-ecma-global-props
  (concat "^"
          (regexp-opt
           '("Infinity" "NaN" "undefined" "arguments") t)
          "$")
  "Value properties of the Ecma-262 Global Object.
Shown at or above `js3-highlight-level' 2.")

;; might want to add the name "arguments" to this list?
(defconst js3-ecma-object-props
  (concat "^"
          (regexp-opt
           '("prototype" "__proto__" "__parent__") t)
          "$")
  "Value properties of the Ecma-262 Object constructor.
Shown at or above `js3-highlight-level' 2.")

(defconst js3-ecma-global-funcs
  (concat
   "^"
   (regexp-opt
    '("decodeURI" "decodeURIComponent" "encodeURI" "encodeURIComponent"
      "eval" "isFinite" "isNaN" "parseFloat" "parseInt") t)
   "$")
  "Function properties of the Ecma-262 Global object.
Shown at or above `js3-highlight-level' 2.")

(defconst js3-ecma-number-props
  (concat "^"
          (regexp-opt '("MAX_VALUE" "MIN_VALUE" "NaN"
                        "NEGATIVE_INFINITY"
                        "POSITIVE_INFINITY") t)
          "$")
  "Properties of the Ecma-262 Number constructor.
Shown at or above `js3-highlight-level' 2.")

(defconst js3-ecma-date-props "^\\(parse\\|UTC\\)$"
  "Properties of the Ecma-262 Date constructor.
Shown at or above `js3-highlight-level' 2.")

(defconst js3-ecma-math-props
  (concat "^"
          (regexp-opt
           '("E" "LN10" "LN2" "LOG2E" "LOG10E" "PI" "SQRT1_2" "SQRT2")
           t)
          "$")
  "Properties of the Ecma-262 Math object.
Shown at or above `js3-highlight-level' 2.")

(defconst js3-ecma-math-funcs
  (concat "^"
          (regexp-opt
           '("abs" "acos" "asin" "atan" "atan2" "ceil" "cos" "exp" "floor"
             "log" "max" "min" "pow" "random" "round" "sin" "sqrt" "tan") t)
          "$")
  "Function properties of the Ecma-262 Math object.
Shown at or above `js3-highlight-level' 2.")

(defconst js3-ecma-function-props
  (concat
   "^"
   (regexp-opt
    '(;; properties of the Object prototype object
      "hasOwnProperty" "isPrototypeOf" "propertyIsEnumerable"
      "toLocaleString" "toString" "valueOf"
      ;; properties of the Function prototype object
      "apply" "call"
      ;; properties of the Array prototype object
      "concat" "join" "pop" "push" "reverse" "shift" "slice" "sort"
      "splice" "unshift"
      ;; properties of the String prototype object
      "charAt" "charCodeAt" "fromCharCode" "indexOf" "lastIndexOf"
      "localeCompare" "match" "replace" "search" "split" "substring"
      "toLocaleLowerCase" "toLocaleUpperCase" "toLowerCase"
      "toUpperCase"
      ;; properties of the Number prototype object
      "toExponential" "toFixed" "toPrecision"
      ;; properties of the Date prototype object
      "getDate" "getDay" "getFullYear" "getHours" "getMilliseconds"
      "getMinutes" "getMonth" "getSeconds" "getTime"
      "getTimezoneOffset" "getUTCDate" "getUTCDay" "getUTCFullYear"
      "getUTCHours" "getUTCMilliseconds" "getUTCMinutes" "getUTCMonth"
      "getUTCSeconds" "setDate" "setFullYear" "setHours"
      "setMilliseconds" "setMinutes" "setMonth" "setSeconds" "setTime"
      "setUTCDate" "setUTCFullYear" "setUTCHours" "setUTCMilliseconds"
      "setUTCMinutes" "setUTCMonth" "setUTCSeconds" "toDateString"
      "toLocaleDateString" "toLocaleString" "toLocaleTimeString"
      "toTimeString" "toUTCString"
      ;; properties of the RegExp prototype object
      "exec" "test"
      ;; SpiderMonkey/Rhino extensions, versions 1.5+
      "toSource" "__defineGetter__" "__defineSetter__"
      "__lookupGetter__" "__lookupSetter__" "__noSuchMethod__"
      "every" "filter" "forEach" "lastIndexOf" "map" "some")
    t)
   "$")
  "Built-in functions defined by Ecma-262 and SpiderMonkey extensions.
Shown at or above `js3-highlight-level' 3.")

(defsubst js3-parse-highlight-prop-get (parent target prop call-p)
  (let ((target-name (and target
                          (js3-name-node-p target)
                          (js3-name-node-name target)))
        (prop-name (if prop (js3-name-node-name prop)))
        (level1 (>= js3-highlight-level 1))
        (level2 (>= js3-highlight-level 2))
        (level3 (>= js3-highlight-level 3))
        pos
        face)
    (when level2
      (if call-p
          (cond
           ((and target prop)
            (cond
             ((and level3 (string-match js3-ecma-function-props prop-name))
              (setq face 'font-lock-builtin-face))
             ((and target-name prop)
              (cond
               ((string= target-name "Date")
                (if (string-match js3-ecma-date-props prop-name)
                    (setq face 'font-lock-builtin-face)))
               ((string= target-name "Math")
                (if (string-match js3-ecma-math-funcs prop-name)
                    (setq face 'font-lock-builtin-face)))))))
           (prop
            (if (string-match js3-ecma-global-funcs prop-name)
                (setq face 'font-lock-builtin-face))))
        (cond
         ((and target prop)
          (cond
           ((string= target-name "Number")
            (if (string-match js3-ecma-number-props prop-name)
                (setq face 'font-lock-constant-face)))
           ((string= target-name "Math")
            (if (string-match js3-ecma-math-props prop-name)
                (setq face 'font-lock-constant-face)))))
         (prop
          (if (string-match js3-ecma-object-props prop-name)
              (setq face 'font-lock-constant-face)))))
      (when face
        (js3-set-face (setq pos (+ (js3-node-pos parent) ; absolute
                                   (js3-node-pos prop))) ; relative
                      (+ pos (js3-node-len prop))
                      face)))))

(defun js3-parse-highlight-member-expr-node (node)
  "Perform syntax highlighting of EcmaScript built-in properties.
The variable `js3-highlight-level' governs this highighting."
  (let (face target prop name pos end parent call-p callee)
    (cond
     ;; case 1:  simple name, e.g. foo
     ((js3-name-node-p node)
      (setq name (js3-name-node-name node))
      ;; possible for name to be nil in rare cases - saw it when
      ;; running js3-mode on an elisp buffer.  Might as well try to
      ;; make it so js3-mode never barfs.
      (when name
        (setq face (if (string-match js3-ecma-global-props name)
                       'font-lock-constant-face))
        (when face
          (setq pos (js3-node-pos node)
                end (+ pos (js3-node-len node)))
          (js3-set-face pos end face))))
     ;; case 2:  property access or function call
     ((or (js3-prop-get-node-p node)
          ;; highlight function call if expr is a prop-get node
          ;; or a plain name (i.e. unqualified function call)
          (and (setq call-p (js3-call-node-p node))
               (setq callee (js3-call-node-target node)) ; separate setq!
               (or (js3-prop-get-node-p callee)
                   (js3-name-node-p callee))))
      (setq parent node
            node (if call-p callee node))
      (if (and call-p (js3-name-node-p callee))
          (setq prop callee)
        (setq target (js3-prop-get-node-left node)
              prop (js3-prop-get-node-right node)))
      (cond
       ((js3-name-node-p target)
        (if (js3-name-node-p prop)
            ;; case 2a:  simple target, simple prop name, e.g. foo.bar
            (js3-parse-highlight-prop-get parent target prop call-p)
          ;; case 2b:  simple target, complex name, e.g. foo.x[y]
          (js3-parse-highlight-prop-get parent target nil call-p)))
       ((js3-name-node-p prop)
        ;; case 2c:  complex target, simple name, e.g. x[y].bar
        (js3-parse-highlight-prop-get parent target prop call-p)))))))

(defun js3-parse-highlight-member-expr-fn-name (expr)
  "Highlight the `baz' in function foo.bar.baz(args) {...}.
This is experimental Rhino syntax.  EXPR is the foo.bar.baz member expr.
We currently only handle the case where the last component is a prop-get
of a simple name.  Called before EXPR has a parent node."
  (let (pos
        (name (and (js3-prop-get-node-p expr)
                   (js3-prop-get-node-right expr))))
    (when (js3-name-node-p name)
      (js3-set-face (setq pos (+ (js3-node-pos expr)  ; parent is absolute
                                 (js3-node-pos name)))
                    (+ pos (js3-node-len name))
                    'font-lock-function-name-face
                    'record))))

;; source:  http://jsdoc.sourceforge.net/
;; Note - this syntax is for Google's enhanced jsdoc parser that
;; allows type specifications, and needs work before entering the wild.

(defconst js3-jsdoc-param-tag-regexp
  (concat "^\\s-*\\*+\\s-*\\(@"
          "\\(?:param\\|argument\\)"
          "\\)"
          "\\s-*\\({[^}]+}\\)?"         ; optional type
          "\\s-*\\([a-zA-Z0-9_$]+\\)?"  ; name
          "\\>")
  "Matches jsdoc tags with optional type and optional param name.")

(defconst js3-jsdoc-typed-tag-regexp
  (concat "^\\s-*\\*+\\s-*\\(@\\(?:"
          (regexp-opt
           '("enum"
             "extends"
             "field"
             "id"
             "implements"
             "lends"
             "mods"
             "requires"
             "return"
             "returns"
             "throw"
             "throws"))
          "\\)\\)\\s-*\\({[^}]+}\\)?")
  "Matches jsdoc tags with optional type.")

(defconst js3-jsdoc-arg-tag-regexp
  (concat "^\\s-*\\*+\\s-*\\(@\\(?:"
          (regexp-opt
           '("alias"
             "augments"
             "borrows"
             "bug"
             "base"
             "config"
             "default"
             "define"
             "exception"
             "function"
             "member"
             "memberOf"
             "name"
             "namespace"
             "property"
             "since"
             "suppress"
             "this"
             "throws"
             "type"
             "version"))
          "\\)\\)\\s-+\\([^ \t]+\\)")
  "Matches jsdoc tags with a single argument.")

(defconst js3-jsdoc-empty-tag-regexp
  (concat "^\\s-*\\*+\\s-*\\(@\\(?:"
          (regexp-opt
           '("addon"
             "author"
             "class"
             "const"
             "constant"
             "constructor"
             "constructs"
             "deprecated"
             "desc"
             "description"
             "event"
             "example"
             "exec"
             "export"
             "fileoverview"
             "final"
             "function"
             "hidden"
             "ignore"
             "implicitCast"
             "inheritDoc"
             "inner"
             "interface"
             "license"
             "noalias"
             "noshadow"
             "notypecheck"
             "override"
             "owner"
             "preserve"
             "preserveTry"
             "private"
             "protected"
             "public"
             "static"
             "supported"
             ))
          "\\)\\)\\s-*")
  "Matches empty jsdoc tags.")

(defconst js3-jsdoc-link-tag-regexp
  "{\\(@\\(?:link\\|code\\)\\)\\s-+\\([^#}\n]+\\)\\(#.+\\)?}"
  "Matches a jsdoc link or code tag.")

(defconst js3-jsdoc-see-tag-regexp
  "^\\s-*\\*+\\s-*\\(@see\\)\\s-+\\([^#}\n]+\\)\\(#.+\\)?"
  "Matches a jsdoc @see tag.")

(defconst js3-jsdoc-html-tag-regexp
  "\\(</?\\)\\([a-zA-Z]+\\)\\s-*\\(/?>\\)"
  "Matches a simple (no attributes) html start- or end-tag.")

(defsubst js3-jsdoc-highlight-helper ()
  (js3-set-face (match-beginning 1)
                (match-end 1)
                'js3-jsdoc-tag-face)
  (if (match-beginning 2)
      (if (save-excursion
            (goto-char (match-beginning 2))
            (= (char-after) ?{))
          (js3-set-face (1+ (match-beginning 2))
                        (1- (match-end 2))
                        'js3-jsdoc-type-face)
        (js3-set-face (match-beginning 2)
                      (match-end 2)
                      'js3-jsdoc-value-face)))
  (if (match-beginning 3)
      (js3-set-face (match-beginning 3)
                    (match-end 3)
                    'js3-jsdoc-value-face)))

(defun js3-highlight-jsdoc (ast)
  "Highlight doc comment tags."
  (let ((comments (js3-ast-root-comments ast))
        beg end)
    (save-excursion
      (dolist (node comments)
        (when (eq (js3-comment-node-format node) 'jsdoc)
          (setq beg (js3-node-abs-pos node)
                end (+ beg (js3-node-len node)))
          (save-restriction
            (narrow-to-region beg end)
            (dolist (re (list js3-jsdoc-param-tag-regexp
                              js3-jsdoc-typed-tag-regexp
                              js3-jsdoc-arg-tag-regexp
                              js3-jsdoc-link-tag-regexp
                              js3-jsdoc-see-tag-regexp
                              js3-jsdoc-empty-tag-regexp))
              (goto-char beg)
              (while (re-search-forward re nil t)
                (js3-jsdoc-highlight-helper)))
            ;; simple highlighting for html tags
            (goto-char beg)
            (while (re-search-forward js3-jsdoc-html-tag-regexp nil t)
              (js3-set-face (match-beginning 1)
                            (match-end 1)
                            'js3-jsdoc-html-tag-delimiter-face)
              (js3-set-face (match-beginning 2)
                            (match-end 2)
                            'js3-jsdoc-html-tag-name-face)
              (js3-set-face (match-beginning 3)
                            (match-end 3)
                            'js3-jsdoc-html-tag-delimiter-face))))))))

(defun js3-highlight-assign-targets (node left right)
  "Highlight function properties and external variables."
  (let (leftpos end name)
    ;; highlight vars and props assigned function values
    (when (js3-function-node-p right)
      (cond
       ;; var foo = function() {...}
       ((js3-name-node-p left)
        (setq name left))
       ;; foo.bar.baz = function() {...}
       ((and (js3-prop-get-node-p left)
             (js3-name-node-p (js3-prop-get-node-right left)))
        (setq name (js3-prop-get-node-right left))))
      (when name
        (js3-set-face (setq leftpos (js3-node-abs-pos name))
                      (+ leftpos (js3-node-len name))
                      'font-lock-function-name-face
                      'record)))))

(defun js3-record-name-node (node)
  "Saves NODE to `js3-recorded-identifiers' to check for undeclared variables
later. NODE must be a name node."
  (let (leftpos end)
    (push (list node js3-current-scope
                (setq leftpos (js3-node-abs-pos node))
                (setq end (+ leftpos (js3-node-len node))))
          js3-recorded-identifiers)))

(defun js3-highlight-undeclared-vars ()
  "After entire parse is finished, look for undeclared variable references.
We have to wait until entire buffer is parsed, since JavaScript permits var
decls to occur after they're used.

If any undeclared var name is in `js3-externs' or `js3-additional-externs',
it is considered declared."
  (let (name)
    (dolist (entry js3-recorded-identifiers)
      (destructuring-bind (name-node scope pos end) entry
                          (setq name (js3-name-node-name name-node))
                          (unless (or (member name js3-global-externs)
                                      (member name js3-default-externs)
                                      (member name js3-additional-externs)
				      (member name js3-declared-globals)
                                      (js3-get-defining-scope scope name))
                            (js3-set-face pos end 'js3-external-variable-face 'record)
                            (js3-record-text-property pos end 'help-echo "Undeclared variable")
                            (js3-record-text-property pos end 'point-entered 'js3-echo-help))))
    (setq js3-recorded-identifiers nil)))

(provide 'js3-highlight)

;;; js3-highlight.el ends here
;;; js3-browse.el --- browsing/hierarchy support for js3-mode

;; Commentary:
;;
;; We currently only support imenu, but eventually should support speedbar and
;; possibly other browsing mechanisms.
;;
;; The basic strategy is to identify function assignment targets of the form
;; `foo.bar.baz', convert them to (list foo bar baz <position>), and push the
;; list into `js3-imenu-recorder'.  The lists are merged into a trie-like tree
;; for imenu after parsing is finished.
;;
;; A `foo.bar.baz' assignment target may be expressed in many ways in
;; JavaScript, and the general problem is undecidable.  However, several forms
;; are readily recognizable at parse-time; the forms we attempt to recognize
;; include:
;;
;;  function foo()  -- function declaration
;;  foo = function()  -- function expression assigned to variable
;;  foo.bar.baz = function()  -- function expr assigned to nested property-get
;;  foo = {bar: function()}  -- fun prop in object literal assigned to var
;;  foo = {bar: {baz: function()}} -- inside nested object literal
;;  foo.bar = {baz: function()}} -- obj lit assigned to nested prop get
;;  a.b = {c: {d: function()}} -- nested obj lit assigned to nested prop get
;;  foo = {get bar() {...}}  -- getter/setter in obj literal
;;  function foo() {function bar() {...}}  -- nested function
;;  foo['a'] = function()  -- fun expr assigned to deterministic element-get
;;
;; This list boils down to a few forms that can be combined recursively.
;; Top-level named function declarations include both the left-hand (name)
;; and the right-hand (function value) expressions needed to produce an imenu
;; entry.  The other "right-hand" forms we need to look for are:
;;  - functions declared as props/getters/setters in object literals
;;  - nested named function declarations
;; The "left-hand" expressions that functions can be assigned to include:
;;  - local/global variables
;;  - nested property-get expressions like a.b.c.d
;;  - element gets like foo[10] or foo['bar'] where the index
;;    expression can be trivially converted to a property name.  They
;;    effectively then become property gets.
;;
;; All the different definition types are canonicalized into the form
;; foo.bar.baz = position-of-function-keyword
;;
;; We need to build a trie-like structure for imenu.  As an example,
;; consider the following JavaScript code:
;;
;; a = function() {...}  // function at position 5
;; b = function() {...}  // function at position 25
;; foo = function() {...} // function at position 100
;; foo.bar = function() {...} // function at position 200
;; foo.bar.baz = function() {...} // function at position 300
;; foo.bar.zab = function() {...} // function at position 400
;;
;; During parsing we accumulate an entry for each definition in
;; the variable `js3-imenu-recorder', like so:
;;
;; '((a 5)
;;   (b 25)
;;   (foo 100)
;;   (foo bar 200)
;;   (foo bar baz 300)
;;   (foo bar zab 400))
;;
;; After parsing these entries are merged into this alist-trie:
;;
;; '((a . 1)
;;   (b . 2)
;;   (foo (<definition> . 3)
;;        (bar (<definition> . 6)
;;             (baz . 100)
;;             (zab . 200))))
;;
;; Note the wacky need for a <definition> name.  The token can be anything
;; that isn't a valid JavaScript identifier, because you might make foo
;; a function and then start setting properties on it that are also functions.

;;; Code:


(defsubst js3-prop-node-name (node)
  "Return the name of a node that may be a property-get/property-name.
If NODE is not a valid name-node, string-node or integral number-node,
returns nil.  Otherwise returns the string name/value of the node."
  (cond
   ((js3-name-node-p node)
    (js3-name-node-name node))
   ((js3-string-node-p node)
    (js3-string-node-value node))
   ((and (js3-number-node-p node)
         (string-match "^[0-9]+$" (js3-number-node-value node)))
    (js3-number-node-value node))
   ((js3-this-node-p node)
    "this")))

(defsubst js3-node-qname-component (node)
  "Test function:  return the name of this node, if it contributes to a qname.
Returns nil if the node doesn't contribute."
  (copy-sequence
   (or (js3-prop-node-name node)
       (if (and (js3-function-node-p node)
                (js3-function-node-name node))
           (js3-name-node-name (js3-function-node-name node))))))

(defsubst js3-record-function-qname (fn-node qname)
  "Associate FN-NODE with its QNAME for later lookup.
This is used in postprocessing the chain list.  When we find a chain
whose first element is a js3-THIS keyword node, we look up the parent
function and see (using this map) whether it is the tail of a chain.
If so, we replace the this-node with a copy of the parent's qname."
  (unless js3-imenu-function-map
    (setq js3-imenu-function-map (make-hash-table :test 'eq)))
  (puthash fn-node qname js3-imenu-function-map))

(defun js3-record-imenu-functions (node &optional var)
  "Record function definitions for imenu.
NODE is a function node or an object literal.
VAR, if non-nil, is the expression that NODE is being assigned to."
  (when js3-parse-ide-mode
    (let ((fun-p (js3-function-node-p node))
          qname left fname-node pos)
      (cond
       ;; non-anonymous function declaration?
       ((and fun-p
             (not var)
             (setq fname-node (js3-function-node-name node)))
        (push (setq qname (list fname-node (js3-node-pos node)))
              js3-imenu-recorder)
        (js3-record-function-qname node qname))
       ;; for remaining forms, compute left-side tree branch first
       ((and var (setq qname (js3-compute-nested-prop-get var)))
        (cond
         ;; foo.bar.baz = function
         (fun-p
          (push (nconc qname (list (js3-node-pos node)))
                js3-imenu-recorder)
          (js3-record-function-qname node qname))
         ;; foo.bar.baz = object-literal
         ;; look for nested functions:  {a: {b: function() {...} }}
         ((js3-object-node-p node)
          ;; Node position here is still absolute, since the parser
          ;; passes the assignment target and value expressions
          ;; to us before they are added as children of the assignment node.
          (js3-record-object-literal node qname (js3-node-pos node)))))))))

(defun js3-compute-nested-prop-get (node)
  "If NODE is of form foo.bar, foo['bar'], or any nested combination, return
component nodes as a list.  Otherwise return nil.  Element-gets are treated
as property-gets if the index expression is a string, or a positive integer."
  (let (left right head)
    (cond
     ((or (js3-name-node-p node)
          (js3-this-node-p node))
      (list node))
     ;; foo.bar.baz is parenthesized as (foo.bar).baz => right operand is a leaf
     ((js3-prop-get-node-p node)        ; foo.bar
      (setq left (js3-prop-get-node-left node)
            right (js3-prop-get-node-right node))
      (if (setq head (js3-compute-nested-prop-get left))
          (nconc head (list right))))
     ((js3-elem-get-node-p node)        ; foo['bar'] or foo[101]
      (setq left (js3-elem-get-node-target node)
            right (js3-elem-get-node-element node))
      (if (or (js3-string-node-p right)      ; ['bar']
              (and (js3-number-node-p right) ; [10]
                   (string-match "^[0-9]+$"
                                 (js3-number-node-value right))))
          (if (setq head (js3-compute-nested-prop-get left))
              (nconc head (list right))))))))

(defun js3-record-object-literal (node qname pos)
  "Recursively process an object literal looking for functions.
NODE is an object literal that is the right-hand child of an assignment
expression.  QNAME is a list of nodes representing the assignment target,
e.g. for foo.bar.baz = {...}, QNAME is (foo-node bar-node baz-node).
POS is the absolute position of the node.
We do a depth-first traversal of NODE.  Any functions we find are prefixed
with QNAME plus the property name of the function and appended to the
variable `js3-imenu-recorder'."
  (let (left right)
    (dolist (e (js3-object-node-elems node))  ; e is a `js3-object-prop-node'
      (let ((left (js3-infix-node-left e))
            ;; Element positions are relative to the parent position.
            (pos (+ pos (js3-node-pos e))))
        (cond
         ;; foo: function() {...}
         ((js3-function-node-p (setq right (js3-infix-node-right e)))
          (when (js3-prop-node-name left)
            ;; As a policy decision, we record the position of the property,
            ;; not the position of the `function' keyword, since the property
            ;; is effectively the name of the function.
            (push (append qname (list left pos))
                  js3-imenu-recorder)
            (js3-record-function-qname right qname)))
;;; foo: {object-literal} -- add foo to qname, offset position, and recurse
         ((js3-object-node-p right)
          (js3-record-object-literal
           right
           (append qname (list (js3-infix-node-left e)))
           (+ pos (js3-node-pos right)))))))))

(defsubst js3-node-top-level-decl-p (node)
  "Return t if NODE's name is defined in the top-level scope.
Also returns t if NODE's name is not defined in any scope, since it implies
that it's an external variable, which must also be in the top-level scope."
  (let* ((name (js3-prop-node-name node))
         (this-scope (js3-node-get-enclosing-scope node))
         defining-scope)
    (cond
     ((js3-this-node-p node)
      nil)
     ((null this-scope)
      t)
     ((setq defining-scope (js3-get-defining-scope this-scope name))
      (js3-ast-root-p defining-scope))
     (t t))))

(defsubst js3-anonymous-wrapper-fn-p (node)
  "Returns t if NODE is an anonymous function that's invoked immediately.
NODE must be `js3-function-node'."
  (let ((parent (js3-node-parent node)))
    (and (js3-paren-node-p parent)
         ;; (function(){...})();
         (or (js3-call-node-p (setq parent (js3-node-parent parent)))
             ;; (function(){...}).call(this);
             (and (js3-prop-get-node-p parent)
                  (member (js3-name-node-name (js3-prop-get-node-right parent))
                          '("call" "apply"))
                  (js3-call-node-p (js3-node-parent parent)))))))

(defun js3-browse-postprocess-chains (chains)
  "Modify function-declaration name chains after parsing finishes.
Some of the information is only available after the parse tree is complete.
For instance, following a 'this' reference requires a parent function node."
  (let ((js3-imenu-fn-type-map (make-hash-table :test 'eq))
        result head fn fn-type parent-chain p elem parent)
    (dolist (chain chains)
      ;; examine the head of each node to get its defining scope
      (setq head (car chain))
      ;; if top-level/external, keep as-is
      (if (js3-node-top-level-decl-p head)
          (push chain result)
        (cond
         ((js3-this-node-p head)
          (setq fn (js3-node-parent-script-or-fn head)
                chain (cdr chain))) ; discard this-node
         ;; nested named function
         ((js3-function-node-p (setq parent (js3-node-parent head)))
          (setq fn (js3-node-parent-script-or-fn parent)))
         ;; variable assigned a function expression
         (t (setq fn (js3-node-parent-script-or-fn head))))
        (when fn
          (setq fn-type (gethash fn js3-imenu-fn-type-map))
          (unless fn-type
            (setq fn-type
                  (cond ((js3-nested-function-p fn) 'skip)
                        ((setq parent-chain
                               (gethash fn js3-imenu-function-map))
                         'named)
                        ((js3-anonymous-wrapper-fn-p fn) 'anon)
                        (t 'skip)))
            (puthash fn fn-type js3-imenu-fn-type-map))
          (case fn-type
                ('anon (push chain result)) ; anonymous top-level wrapper
                ('named                     ; top-level named function
                 ;; prefix parent fn qname, which is
                 ;; parent-chain sans last elem, to this chain.
                 (push (append (butlast parent-chain) chain) result))))))
    ;; finally replace each node in each chain with its name.
    (dolist (chain result)
      (setq p chain)
      (while p
        (if (js3-node-p (setq elem (car p)))
            (setcar p (js3-node-qname-component elem)))
        (setq p (cdr p))))
    result))

;; Merge name chains into a trie-like tree structure of nested lists.
;; To simplify construction of the trie, we first build it out using the rule
;; that the trie consists of lists of pairs.  Each pair is a 2-element array:
;; [key, num-or-list].  The second element can be a number; if so, this key
;; is a leaf-node with only one value.  (I.e. there is only one declaration
;; associated with the key at this level.)  Otherwise the second element is
;; a list of pairs, with the rule applied recursively.  This symmetry permits
;; a simple recursive formulation.
;;
;; js3-mode is building the data structure for imenu.  The imenu documentation
;; claims that it's the structure above, but in practice it wants the children
;; at the same list level as the key for that level, which is how I've drawn
;; the "Expected final result" above.  We'll postprocess the trie to remove the
;; list wrapper around the children at each level.
;;
;; A completed nested imenu-alist entry looks like this:
;;       '(("foo"
;;          ("<definition>" . 7)
;;          ("bar"
;;           ("a" . 40)
;;           ("b" . 60))))
;;
;; In particular, the documentation for `imenu--index-alist' says that
;; a nested sub-alist element looks like (INDEX-NAME SUB-ALIST).
;; The sub-alist entries immediately follow INDEX-NAME, the head of the list.

(defun js3-treeify (lst)
  "Convert (a b c d) to (a ((b ((c d)))))"
  (if (null (cddr lst))  ; list length <= 2
      lst
    (list (car lst) (list (js3-treeify (cdr lst))))))

(defun js3-build-alist-trie (chains trie)
  "Merge declaration name chains into a trie-like alist structure for imenu.
CHAINS is the qname chain list produced during parsing. TRIE is a
list of elements built up so far."
  (let (head tail pos branch kids)
    (dolist (chain chains)
      (setq head (car chain)
            tail (cdr chain)
            pos (if (numberp (car tail)) (car tail))
            branch (js3-find-if (lambda (n)
                                  (string= (car n) head))
                                trie)
            kids (second branch))
      (cond
       ;; case 1:  this key isn't in the trie yet
       ((null branch)
        (if trie
            (setcdr (last trie) (list (js3-treeify chain)))
          (setq trie (list (js3-treeify chain)))))
       ;; case 2:  key is present with a single number entry:  replace w/ list
       ;;  ("a1" 10)  +  ("a1" 20) => ("a1" (("<definition>" 10)
       ;;                                    ("<definition>" 20)))
       ((numberp kids)
        (setcar (cdr branch)
                (list (list "<definition-1>" kids)
                      (if pos
                          (list "<definition-2>" pos)
                        (js3-treeify tail)))))
       ;; case 3:  key is there (with kids), and we're a number entry
       (pos
        (setcdr (last kids)
                (list
                 (list (format "<definition-%d>"
                               (1+ (loop for kid in kids
                                         count (eq ?< (aref (car kid) 0)))))
                       pos))))

       ;; case 4:  key is there with kids, need to merge in our chain
       (t
        (js3-build-alist-trie (list tail) kids))))
    trie))

(defun js3-flatten-trie (trie)
  "Convert TRIE to imenu-format.
Recurses through nodes, and for each one whose second element is a list,
appends the list's flattened elements to the current element.  Also
changes the tails into conses.  For instance, this pre-flattened trie

'(a ((b 20)
(c ((d 30)
    (e 40)))))

becomes

'(a (b . 20)
(c (d . 30)
   (e . 40)))

Note that the root of the trie has no key, just a list of chains.
This is also true for the value of any key with multiple children,
e.g. key 'c' in the example above."
(cond
 ((listp (car trie))
  (mapcar #'js3-flatten-trie trie))
 (t
  (if (numberp (second trie))
      (cons (car trie) (second trie))
    ;; else pop list and append its kids
    (apply #'append (list (car trie)) (js3-flatten-trie (cdr trie)))))))

(defun js3-build-imenu-index ()
  "Turn `js3-imenu-recorder' into an imenu data structure."
  (unless (eq js3-imenu-recorder 'empty)
    (let* ((chains (js3-browse-postprocess-chains js3-imenu-recorder))
           (result (js3-build-alist-trie chains nil)))
      (js3-flatten-trie result))))

(defun js3-test-print-chains (chains)
  "Print a list of qname chains.
Each element of CHAINS is a list of the form (NODE [NODE *] pos);
i.e. one or more nodes, and an integer position as the list tail."
  (mapconcat (lambda (chain)
               (concat "("
                       (mapconcat (lambda (elem)
                                    (if (js3-node-p elem)
                                        (or (js3-node-qname-component elem)
                                            "nil")
                                      (number-to-string elem)))
                                  chain
                                  " ")
                       ")"))
             chains
             "\n"))

(provide 'js3-browse)

;;; js3-browse.el ends here
;;; js3-parse.el --- JavaScript parser

;; Commentary:

;; This is based on Rhino's parser and tries to follow its code
;; structure as closely as practical, so that changes to the Rhino
;; parser can easily be propagated into this code.  However, Rhino
;; does not currently generate a usable AST representation, at least
;; from an IDE perspective, so we build our own more suitable AST.

;; The AST node structures are defined in `js3-ast.el'.
;; Every parser function that creates and returns an AST node has
;; the following responsibilities:

;;   1) set the node start to the absolute buffer start position
;;   2) set the node length to include any closing chars (RC, SEMI)
;;   3) fix up any child-node starts to be relative to this node
;;   4) set any field positions (e.g. keywords) relative to this node
;;   5) report any child nodes with `js3-node-add-children'
;;      (note that this call fixes up start positions by default)

;; The resulting AST has all node start positions relative to the
;; parent nodes; only the root has an absolute start position.

;; Note: fontification is done inline while parsing.  It used to be
;; done in a second pass over the AST, but doing it inline is about
;; twice as fast.  Most of the fontification happens when tokens are
;; scanned, and the parser has a few spots that perform extra
;; fontification.  In addition to speed, a second benefit of inline
;; parsing is that if a long parse is interrupted, everything parsed
;; so far is still fontified.

;; The editing mode that uses this parser, `js3-mode', directs the
;; parser to check periodically for user input.  If user input
;; arrives, the parse is abandoned, except for the highlighting that
;; has occurred so far, and a re-parse is rescheduled for when Emacs
;; becomes idle again.  This works pretty well, but could be better.
;; In particular, when the user input has not resulted in changes to
;; the buffer (for instance, navigation input), the parse tree built
;; so far should not be discarded, and the parse should continue where
;; it left off.  It will be some work to create what amounts to a
;; continuation, but it should not be unreasonably difficult.

;; TODO:
;; - make non-editing input restart parse at previous continuation
;; - in Eclipse, sibling nodes never overlap start/end ranges
;;   - for getters, prop name and function nodes overlap
;;   - should write a debug tree visitor to look for overlaps
;; - mark array and object literals as "destructuring" (node prop?)
;;   so we can syntax-highlight them properly.
;; - figure out a way not to store value in string/name nodes
;;   - needs a solution for synthetic nodes

;;; Code

(eval-when-compile
  (require 'cl))  ; for delete-if


(defconst js3-version "1.8.0"
  "Version of JavaScript supported, plus minor js3 version.")

(defmacro js3-record-face (face)
  "Record a style run of FACE for the current token."
  `(js3-set-face js3-token-beg js3-token-end ,face 'record))

(defsubst js3-node-end (n)
  "Computes the absolute end of node N.
Use with caution!  Assumes `js3-node-pos' is -absolute-, which
is only true until the node is added to its parent; i.e., while parsing."
  (+ (js3-node-pos n)
     (js3-node-len n)))

(defsubst js3-record-comment ()
  (push (make-js3-comment-node :len (- js3-token-end js3-token-beg)
                               :format js3-ts-comment-type)
        js3-scanned-comments)
  (when js3-parse-ide-mode
    (js3-record-face (if (eq js3-ts-comment-type 'jsdoc)
                         'font-lock-doc-face
                       'font-lock-comment-face))
    (when (memq js3-ts-comment-type '(html preprocessor))
      ;; Tell cc-engine the bounds of the comment.
      (js3-record-text-property js3-token-beg (1- js3-token-end) 'c-in-sws t))))

;; This function is called depressingly often, so it should be fast.
;; Most of the time it's looking at the same token it peeked before.
(defsubst js3-peek-token ()
  "Returns the next token without consuming it.
If previous token was consumed, calls scanner to get new token.
If previous token was -not- consumed, returns it (idempotent).

This function will not return a newline (js3-EOL) - instead, it
gobbles newlines until it finds a non-newline token, and flags
that token as appearing just after a newline.

This function will also not return a js3-COMMENT.  Instead, it
records comments found in `js3-scanned-comments'.  If the token
returned by this function immediately follows a jsdoc comment,
the token is flagged as such.

Note that this function always returned the un-flagged token!
The flags, if any, are saved in `js3-current-flagged-token'."
  (if (/= js3-current-flagged-token js3-EOF) ; last token not consumed
      js3-current-token  ; most common case - return already-peeked token
    (let ((tt (js3-get-token))          ; call scanner
          saw-eol
          face)
      ;; process comments and whitespace
      (while (or (= tt js3-EOL)
                 (= tt js3-COMMENT))
        (if (= tt js3-EOL)
            (setq saw-eol t)
          (setq saw-eol nil)
          (if js3-record-comments
              (js3-record-comment)))
        (setq tt (js3-get-token)))  ; call scanner
      (setq js3-current-token tt
            js3-current-flagged-token (if saw-eol
                                          (logior tt js3-ti-after-eol)
                                        tt))
      ;; perform lexical fontification as soon as token is scanned
      (when js3-parse-ide-mode
        (cond
         ((minusp tt)
          (js3-record-face 'js3-error-face))
         ((setq face (aref js3-kwd-tokens tt))
          (js3-record-face face))
         ((and (= tt js3-NAME)
               (equal js3-ts-string "undefined"))
          (js3-record-face 'font-lock-constant-face))))
      tt)))  ; return unflagged token

(defsubst js3-peek-flagged-token ()
  "Returns the current token along with any flags set for it."
  (js3-peek-token)
  js3-current-flagged-token)

(defsubst js3-consume-token ()
  (setq js3-current-flagged-token js3-EOF))

(defsubst js3-next-token ()
  (prog1
      (js3-peek-token)
    (js3-consume-token)))

(defsubst js3-next-flagged-token ()
  (js3-peek-token)
  (prog1 js3-current-flagged-token
    (js3-consume-token)))

(defsubst js3-match-token (match)
  "Consume and return t if next token matches MATCH, a bytecode.
Returns nil and consumes nothing if MATCH is not the next token."
  (if (/= (js3-peek-token) match)
      nil
    (js3-consume-token)
    t))

(defsubst js3-valid-prop-name-token (tt)
  (or (= tt js3-NAME)
      (and js3-allow-keywords-as-property-names
           (plusp tt)
           (aref js3-kwd-tokens tt))))

(defsubst js3-match-prop-name ()
  "Consume token and return t if next token is a valid property name.
It's valid if it's a js3-NAME, or `js3-allow-keywords-as-property-names'
is non-nil and it's a keyword token."
  (if (js3-valid-prop-name-token (js3-peek-token))
      (progn
        (js3-consume-token)
        t)
    nil))

(defsubst js3-must-match-prop-name (msg-id &optional pos len)
  (if (js3-match-prop-name)
      t
    (js3-report-error msg-id nil pos len)
    nil))

(defsubst js3-peek-token-or-eol ()
  "Return js3-EOL if the current token immediately follows a newline.
Else returns the current token.  Used in situations where we don't
consider certain token types valid if they are preceded by a newline.
One example is the postfix ++ or -- operator, which has to be on the
same line as its operand."
  (let ((tt (js3-peek-token)))
    ;; Check for last peeked token flags
    (if (js3-flag-set-p js3-current-flagged-token js3-ti-after-eol)
        js3-EOL
      tt)))

(defsubst js3-set-check-for-label ()
  (assert (= (logand js3-current-flagged-token js3-clear-ti-mask) js3-NAME))
  (js3-set-flag js3-current-flagged-token js3-ti-check-label))

(defsubst js3-must-match (token msg-id &optional pos len)
  "Match next token to token code TOKEN, or record a syntax error.
MSG-ID is the error message to report if the match fails.
Returns t on match, nil if no match."
  (if (js3-match-token token)
      t
    (js3-report-error msg-id nil pos len)
    nil))

(defsubst js3-inside-function ()
  (plusp js3-nesting-of-function))

(defsubst js3-set-requires-activation ()
  (if (js3-function-node-p js3-current-script-or-fn)
      (setf (js3-function-node-needs-activation js3-current-script-or-fn) t)))

(defsubst js3-check-activation-name (name token)
  (when (js3-inside-function)
    ;; skip language-version 1.2 check from Rhino
    (if (or (string= "arguments" name)
            (and js3-compiler-activation-names  ; only used in codegen
                 (gethash name js3-compiler-activation-names)))
        (js3-set-requires-activation))))

(defsubst js3-set-is-generator ()
  (if (js3-function-node-p js3-current-script-or-fn)
      (setf (js3-function-node-is-generator js3-current-script-or-fn) t)))

(defsubst js3-push-scope (scope)
  "Push SCOPE, a `js3-scope', onto the lexical scope chain."
  (assert (js3-scope-p scope))
  (assert (null (js3-scope-parent-scope scope)))
  (assert (neq js3-current-scope scope))
  (setf (js3-scope-parent-scope scope) js3-current-scope
        js3-current-scope scope))

(defsubst js3-pop-scope ()
  (setq js3-current-scope
        (js3-scope-parent-scope js3-current-scope)))

(defsubst js3-enter-loop (loop-node)
  (push loop-node js3-loop-set)
  (push loop-node js3-loop-and-switch-set)
  (js3-push-scope loop-node)
  ;; Tell the current labeled statement (if any) its statement,
  ;; and set the jump target of the first label to the loop.
  ;; These are used in `js3-parse-continue' to verify that the
  ;; continue target is an actual labeled loop.  (And for codegen.)
  (when js3-labeled-stmt
    (setf (js3-labeled-stmt-node-stmt js3-labeled-stmt) loop-node
          (js3-label-node-loop (car (js3-labeled-stmt-node-labels
                                     js3-labeled-stmt))) loop-node)))

(defsubst js3-exit-loop ()
  (pop js3-loop-set)
  (pop js3-loop-and-switch-set)
  (js3-pop-scope))

(defsubst js3-enter-switch (switch-node)
  (push switch-node js3-loop-and-switch-set))

(defsubst js3-exit-switch ()
  (pop js3-loop-and-switch-set))

(defun js3-parse (&optional buf cb)
  "Tells the js3 parser to parse a region of JavaScript.

BUF is a buffer or buffer name containing the code to parse.
Call `narrow-to-region' first to parse only part of the buffer.

The returned AST root node is given some additional properties:
`node-count' - total number of nodes in the AST
`buffer' - BUF.  The buffer it refers to may change or be killed,
so the value is not necessarily reliable.

An optional callback CB can be specified to report parsing
progress.  If `(functionp CB)' returns t, it will be called with
the current line number once before parsing begins, then again
each time the lexer reaches a new line number.

CB can also be a list of the form `(symbol cb ...)' to specify
multiple callbacks with different criteria.  Each symbol is a
criterion keyword, and the following element is the callback to
call

:line  - called whenever the line number changes
:token - called for each new token consumed

The list of criteria could be extended to include entering or
leaving a statement, an expression, or a function definition."
  (if (and cb (not (functionp cb)))
      (error "criteria callbacks not yet implemented"))
  (let ((inhibit-point-motion-hooks t)
        ;; This is a recursive-descent parser, so give it a big stack.
        (max-lisp-eval-depth (max max-lisp-eval-depth 3000))
        (max-specpdl-size (max max-specpdl-size 3000))
        (case-fold-search nil)
        ast)
    (message nil)  ; clear any error message from previous parse
    (save-excursion
      (let ()
        (when buf (set-buffer buf))
        (setq js3-scanned-comments nil
              js3-parsed-errors nil
              js3-parsed-warnings nil
              js3-imenu-recorder nil
              js3-imenu-function-map nil
              js3-label-set nil)
        (js3-init-scanner)
        (setq ast (js3-with-unmodifying-text-property-changes
                   (js3-do-parse)))
        (unless js3-ts-hit-eof
          (js3-report-error "msg.got.syntax.errors" (length js3-parsed-errors)))
        (setf (js3-ast-root-errors ast) js3-parsed-errors
              (js3-ast-root-warnings ast) js3-parsed-warnings)
        ;; if we didn't find any declarations, put a dummy in this list so we
        ;; don't end up re-parsing the buffer in `js3-mode-create-imenu-index'
        (unless js3-imenu-recorder
          (setq js3-imenu-recorder 'empty))
        (run-hooks 'js3-parse-finished-hook)
        ast))))

;; Corresponds to Rhino's Parser.parse() method.
(defun js3-do-parse ()
  "Parse current buffer starting from current point.
Scanner should be initialized."
  (let ((pos js3-ts-cursor)
        (end js3-ts-cursor)  ; in case file is empty
        root n tt)
    ;; initialize buffer-local parsing vars
    (setf root (make-js3-ast-root :buffer (buffer-name) :pos pos)
          js3-current-script-or-fn root
          js3-current-scope root
          js3-current-flagged-token js3-EOF
          js3-nesting-of-function 0
          js3-labeled-stmt nil
          js3-recorded-identifiers nil)  ; for js3-highlight
    (while (/= (setq tt (js3-peek-token)) js3-EOF)
      (if (= tt js3-FUNCTION)
          (progn
            (js3-consume-token)
            (setq n (js3-parse-function (if js3-called-by-compile-function
                                            'FUNCTION_EXPRESSION
                                          'FUNCTION_STATEMENT))))
        ;; not a function - parse a statement
        (setq n (js3-parse-statement)))
      ;; add function or statement to script
      (setq end (js3-node-end n))
      (js3-block-node-push root n))
    ;; add comments to root in lexical order
    (when js3-scanned-comments
      ;; if we find a comment beyond end of normal kids, use its end
      (setq end (max end (js3-node-end (first js3-scanned-comments))))
      (dolist (comment js3-scanned-comments)
        (push comment (js3-ast-root-comments root))
        (js3-node-add-children root comment)))
    (setf (js3-node-len root) (- end pos))
    ;; Give extensions a chance to muck with things before highlighting starts.
    (dolist (callback js3-post-parse-callbacks)
      (funcall callback))
    (let ((btext
           (replace-regexp-in-string
            "[\n\t ]+" " "
            (buffer-substring-no-properties
             1 (buffer-size)) t t)))
      (setq js3-declared-globals
            (nconc js3-declared-globals
                   (split-string
                    (if (string-match "/\\* *globals? \\(.*?\\)\\*/" btext)
                        (match-string-no-properties 1 btext)
                      "")
                    "\\(:true\\|:false\\)?[ ,]+" t))))
    (delete-dups js3-declared-globals)
    (js3-highlight-undeclared-vars)
    root))

(defun js3-function-parser ()
  (js3-consume-token)
  (js3-parse-function 'FUNCTION_EXPRESSION_STATEMENT))

(defun js3-parse-function-closure-body (fn-node)
  "Parse a JavaScript 1.8 function closure body."
  (let ((js3-nesting-of-function (1+ js3-nesting-of-function)))
    (if js3-ts-hit-eof
        (js3-report-error "msg.no.brace.body" nil
                          (js3-node-pos fn-node)
                          (- js3-ts-cursor (js3-node-pos fn-node)))
      (js3-node-add-children fn-node
                             (setf (js3-function-node-body fn-node)
                                   (js3-parse-expr))))))

(defun js3-parse-function-body (fn-node)
  (js3-must-match js3-LC "msg.no.brace.body"
                  (js3-node-pos fn-node)
                  (- js3-ts-cursor (js3-node-pos fn-node)))
  (let ((pos js3-token-beg)         ; LC position
        (pn (make-js3-block-node))  ; starts at LC position
        tt
        end)
    (incf js3-nesting-of-function)
    (unwind-protect
        (while (not (or (= (setq tt (js3-peek-token)) js3-ERROR)
                        (= tt js3-EOF)
                        (= tt js3-RC)))
          (js3-block-node-push pn (if (/= tt js3-FUNCTION)
                                      (js3-parse-statement)
                                    (js3-consume-token)
                                    (js3-parse-function 'FUNCTION_STATEMENT))))
      (decf js3-nesting-of-function))
    (setq end js3-token-end)  ; assume no curly and leave at current token
    (if (js3-must-match js3-RC "msg.no.brace.after.body" pos)
        (setq end js3-token-end))
    (setf (js3-node-pos pn) pos
          (js3-node-len pn) (- end pos))
    (setf (js3-function-node-body fn-node) pn)
    (js3-node-add-children fn-node pn)
    pn))

(defun js3-parse-function-params (fn-node pos)
  (if (js3-match-token js3-RP)
      (setf (js3-function-node-rp fn-node) (- js3-token-beg pos))
    (let (params len param)
      (loop for tt = (js3-peek-token)
            do
            (cond
             ;; destructuring param
             ((or (= tt js3-LB) (= tt js3-LC))
              (push (js3-parse-primary-expr) params))
             ;; simple name
             (t
              (js3-must-match js3-NAME "msg.no.parm")
              (js3-record-face 'js3-function-param-face)
              (setq param (js3-create-name-node))
              (js3-define-symbol js3-LP js3-ts-string param)
              (push param params)))
            while
            (js3-match-token js3-COMMA))
      (if (js3-must-match js3-RP "msg.no.paren.after.parms")
          (setf (js3-function-node-rp fn-node) (- js3-token-beg pos)))
      (dolist (p params)
        (js3-node-add-children fn-node p)
        (push p (js3-function-node-params fn-node))))))

(defsubst js3-check-inconsistent-return-warning (fn-node name)
  "Possibly show inconsistent-return warning.
Last token scanned is the close-curly for the function body."
  (when (and js3-mode-show-strict-warnings
             js3-strict-inconsistent-return-warning
             (not (js3-has-consistent-return-usage
                   (js3-function-node-body fn-node))))
    ;; Have it extend from close-curly to bol or beginning of block.
    (let ((pos (save-excursion
                 (goto-char js3-token-end)
                 (max (js3-node-abs-pos (js3-function-node-body fn-node))
                      (point-at-bol))))
          (end js3-token-end))
      (if (plusp (js3-name-node-length name))
          (js3-add-strict-warning "msg.no.return.value"
                                  (js3-name-node-name name) pos end)
        (js3-add-strict-warning "msg.anon.no.return.value" nil pos end)))))

(defun js3-parse-function (function-type)
  "Function parser.  FUNCTION-TYPE is a symbol."
  (let ((pos js3-token-beg)  ; start of 'function' keyword
        name
        name-beg
        name-end
        fn-node
        lp
        (synthetic-type function-type)
        member-expr-node)
    ;; parse function name, expression, or non-name (anonymous)
    (cond
     ;; function foo(...)
     ((js3-match-token js3-NAME)
      (setq name (js3-create-name-node t)
            name-beg js3-token-beg
            name-end js3-token-end)
      (unless (js3-match-token js3-LP)
        (when js3-allow-member-expr-as-function-name
          ;; function foo.bar(...)
          (setq member-expr-node name
                name nil
                member-expr-node (js3-parse-member-expr-tail
                                  nil member-expr-node)))
        (js3-must-match js3-LP "msg.no.paren.parms")))
     ((js3-match-token js3-LP)
      nil)  ; anonymous function:  leave name as null
     (t
      ;; function random-member-expr(...)
      (when js3-allow-member-expr-as-function-name
        ;; Note that memberExpr can not start with '(' like
        ;; in function (1+2).toString(), because 'function (' already
        ;; processed as anonymous function
        (setq member-expr-node (js3-parse-member-expr)))
      (js3-must-match js3-LP "msg.no.paren.parms")))
    (if (= js3-current-token js3-LP)  ; eventually matched LP?
        (setq lp js3-token-beg))
    (if member-expr-node
        (progn
          (setq synthetic-type 'FUNCTION_EXPRESSION)
          (js3-parse-highlight-member-expr-fn-name member-expr-node))
      (if name
          (js3-set-face name-beg name-end
                        'font-lock-function-name-face 'record)))
    (if (and (neq synthetic-type 'FUNCTION_EXPRESSION)
             (plusp (js3-name-node-length name)))
        ;; Function statements define a symbol in the enclosing scope
        (js3-define-symbol js3-FUNCTION (js3-name-node-name name) fn-node))
    (setf fn-node (make-js3-function-node :pos pos
                                          :name name
                                          :form function-type
                                          :lp (if lp (- lp pos))))
    (if (or (js3-inside-function) (plusp js3-nesting-of-with))
        ;; 1. Nested functions are not affected by the dynamic scope flag
        ;;    as dynamic scope is already a parent of their scope.
        ;; 2. Functions defined under the with statement also immune to
        ;;    this setup, in which case dynamic scope is ignored in favor
        ;;    of the with object.
        (setf (js3-function-node-ignore-dynamic fn-node) t))
    ;; dynamically bind all the per-function variables
    (let ((js3-current-script-or-fn fn-node)
          (js3-current-scope fn-node)
          (js3-nesting-of-with 0)
          (js3-end-flags 0)
          js3-label-set
          js3-loop-set
          js3-loop-and-switch-set)
      (js3-parse-function-params fn-node pos)
      (if (and (>= js3-language-version 180)
               (/= (js3-peek-token) js3-LC))
          (js3-parse-function-closure-body fn-node)
        (js3-parse-function-body fn-node))
      (if name
          (js3-node-add-children fn-node name))
      (js3-check-inconsistent-return-warning fn-node name)
      ;; Function expressions define a name only in the body of the
      ;; function, and only if not hidden by a parameter name
      (if (and name
               (eq synthetic-type 'FUNCTION_EXPRESSION)
               (null (js3-scope-get-symbol js3-current-scope
                                           (js3-name-node-name name))))
          (js3-define-symbol js3-FUNCTION
                             (js3-name-node-name name)
                             fn-node))
      (if (and name
               (not (eq function-type 'FUNCTION_EXPRESSION)))
          (js3-record-imenu-functions fn-node)))
    (setf (js3-node-len fn-node) (- js3-ts-cursor pos)
          (js3-function-node-member-expr fn-node) member-expr-node)  ; may be nil
    ;; Rhino doesn't do this, but we need it for finding undeclared vars.
    ;; We wait until after parsing the function to set its parent scope,
    ;; since `js3-define-symbol' needs the defining-scope check to stop
    ;; at the function boundary when checking for redeclarations.
    (setf (js3-scope-parent-scope fn-node) js3-current-scope)
    fn-node))

(defun js3-parse-statements (&optional parent)
  "Parse a statement list.  Last token consumed must be js3-LC.

PARENT can be a `js3-block-node', in which case the statements are
appended to PARENT.  Otherwise a new `js3-block-node' is created
and returned.

This function does not match the closing js3-RC: the caller
matches the RC so it can provide a suitable error message if not
matched.  This means it's up to the caller to set the length of
the node to include the closing RC.  The node start pos is set to
the absolute buffer start position, and the caller should fix it
up to be relative to the parent node.  All children of this block
node are given relative start positions and correct lengths."
  (let ((pn (or parent (make-js3-block-node)))
        tt)
    (setf (js3-node-pos pn) js3-token-beg)
    (while (and (> (setq tt (js3-peek-token)) js3-EOF)
                (/= tt js3-RC))
      (js3-block-node-push pn (js3-parse-statement)))
    pn))

(defun js3-parse-statement ()
  (let (tt pn beg end)
    ;; coarse-grained user-interrupt check - needs work
    (and js3-parse-interruptable-p
         (zerop (% (incf js3-parse-stmt-count)
                   js3-statements-per-pause))
         (input-pending-p)
         (throw 'interrupted t))
    (setq pn (js3-statement-helper))
    ;; no-side-effects warning check
    (unless (js3-node-has-side-effects pn)
      (setq end (js3-node-end pn))
      (save-excursion
        (goto-char end)
        (setq beg (max (js3-node-pos pn) (point-at-bol))))
      (js3-add-strict-warning "msg.no.side.effects" nil beg end))
    pn))

;; These correspond to the switch cases in Parser.statementHelper
(defconst js3-parsers
  (let ((parsers (make-vector js3-num-tokens
                              #'js3-parse-expr-stmt)))
    (aset parsers js3-BREAK     #'js3-parse-break)
    (aset parsers js3-CONST     #'js3-parse-const-var)
    (aset parsers js3-CONTINUE  #'js3-parse-continue)
    (aset parsers js3-DEBUGGER  #'js3-parse-debugger)
    (aset parsers js3-DO        #'js3-parse-do)
    (aset parsers js3-FOR       #'js3-parse-for)
    (aset parsers js3-FUNCTION  #'js3-function-parser)
    (aset parsers js3-IF        #'js3-parse-if)
    (aset parsers js3-LC        #'js3-parse-block)
    (aset parsers js3-LET       #'js3-parse-let-stmt)
    (aset parsers js3-NAME      #'js3-parse-name-or-label)
    (aset parsers js3-RETURN    #'js3-parse-ret-yield)
    (aset parsers js3-SEMI      #'js3-parse-semi)
    (aset parsers js3-SWITCH    #'js3-parse-switch)
    (aset parsers js3-THROW     #'js3-parse-throw)
    (aset parsers js3-TRY       #'js3-parse-try)
    (aset parsers js3-VAR       #'js3-parse-const-var)
    (aset parsers js3-WHILE     #'js3-parse-while)
    (aset parsers js3-WITH      #'js3-parse-with)
    (aset parsers js3-YIELD     #'js3-parse-ret-yield)
    parsers)
  "A vector mapping token types to parser functions.")

(defsubst js3-parse-warn-missing-semi (beg end)
  (and js3-mode-show-strict-warnings
       js3-strict-missing-semi-warning
       (js3-add-strict-warning
        "msg.missing.semi" nil
        ;; back up to beginning of statement or line
        (max beg (save-excursion
                   (goto-char end)
                   (point-at-bol)))
        end)))

(defconst js3-no-semi-insertion
  (list js3-IF
        js3-SWITCH
        js3-WHILE
        js3-DO
        js3-FOR
        js3-TRY
        js3-WITH
        js3-LC
        js3-ERROR
        js3-SEMI
        js3-FUNCTION)
  "List of tokens that don't do automatic semicolon insertion.")

(defconst js3-autoinsert-semi-and-warn
  (list js3-ERROR js3-EOF js3-RC))

(defun js3-statement-helper ()
  (let* ((tt (js3-peek-token))
         (first-tt tt)
         (beg js3-token-beg)
         (parser (if (= tt js3-ERROR)
                     #'js3-parse-semi
                   (aref js3-parsers tt)))
         pn
         tt-flagged)
    ;; If the statement is set, then it's been told its label by now.
    (and js3-labeled-stmt
         (js3-labeled-stmt-node-stmt js3-labeled-stmt)
         (setq js3-labeled-stmt nil))
    (setq pn (funcall parser))
    ;; Don't do auto semi insertion for certain statement types.
    (unless (or (memq first-tt js3-no-semi-insertion)
                (js3-labeled-stmt-node-p pn))
      (js3-auto-insert-semicolon pn))
    pn))

(defun js3-auto-insert-semicolon (pn)
  (let* ((tt-flagged (js3-peek-flagged-token))
         (tt (logand tt-flagged js3-clear-ti-mask))
         (pos (js3-node-pos pn)))
    (cond
     ((= tt js3-SEMI)
      ;; Consume ';' as a part of expression
      (js3-consume-token)
      ;; extend the node bounds to include the semicolon.
      (setf (js3-node-len pn) (- js3-token-end pos)))
     ((memq tt js3-autoinsert-semi-and-warn)
      ;; Autoinsert ;
      (js3-parse-warn-missing-semi pos (js3-node-end pn)))
     (t
      (if (js3-flag-not-set-p tt-flagged js3-ti-after-eol)
          ;; Report error if no EOL or autoinsert ';' otherwise
          (js3-report-error "msg.no.semi.stmt")
        (js3-parse-warn-missing-semi pos (js3-node-end pn)))))))

(defun js3-parse-condition ()
  "Parse a parenthesized boolean expression, e.g. in an if- or while-stmt.
The parens are discarded and the expression node is returned.
The `pos' field of the return value is set to an absolute position
that must be fixed up by the caller.
Return value is a list (EXPR LP RP), with absolute paren positions."
  (let (pn lp rp)
    (if (js3-must-match js3-LP "msg.no.paren.cond")
        (setq lp js3-token-beg))
    (setq pn (js3-parse-expr))
    (if (js3-must-match js3-RP "msg.no.paren.after.cond")
        (setq rp js3-token-beg))
    ;; Report strict warning on code like "if (a = 7) ..."
    (if (and js3-strict-cond-assign-warning
             (js3-assign-node-p pn))
        (js3-add-strict-warning "msg.equal.as.assign" nil
                                (js3-node-pos pn)
                                (+ (js3-node-pos pn)
                                   (js3-node-len pn))))
    (list pn lp rp)))

(defun js3-parse-if ()
  "Parser for if-statement.  Last matched token must be js3-IF."
  (let ((pos js3-token-beg)
        cond
        if-true
        if-false
        else-pos
        end
        pn)
    (js3-consume-token)
    (setq cond (js3-parse-condition)
          if-true (js3-parse-statement)
          if-false (if (js3-match-token js3-ELSE)
                       (progn
                         (setq else-pos (- js3-token-beg pos))
                         (js3-parse-statement)))
          end (js3-node-end (or if-false if-true))
          pn (make-js3-if-node :pos pos
                               :len (- end pos)
                               :condition (car cond)
                               :then-part if-true
                               :else-part if-false
                               :else-pos else-pos
                               :lp (js3-relpos (second cond) pos)
                               :rp (js3-relpos (third cond) pos)))
    (js3-node-add-children pn (car cond) if-true if-false)
    pn))

(defun js3-parse-switch ()
  "Parser for switch-statement.  Last matched token must be js3-SWITCH."
  (let ((pos js3-token-beg)
        tt
        pn
        discriminant
        has-default
        case-expr
        case-node
        case-pos
        cases
        stmt
        lp
        rp)
    (js3-consume-token)
    (if (js3-must-match js3-LP "msg.no.paren.switch")
        (setq lp js3-token-beg))
    (setq discriminant (js3-parse-expr)
          pn (make-js3-switch-node :discriminant discriminant
                                   :pos pos
                                   :lp (js3-relpos lp pos)))
    (js3-node-add-children pn discriminant)
    (js3-enter-switch pn)
    (unwind-protect
        (progn
          (if (js3-must-match js3-RP "msg.no.paren.after.switch")
              (setf (js3-switch-node-rp pn) (- js3-token-beg pos)))
          (js3-must-match js3-LC "msg.no.brace.switch")
          (catch 'break
            (while t
              (setq tt (js3-next-token)
                    case-pos js3-token-beg)
              (cond
               ((= tt js3-RC)
                (setf (js3-node-len pn) (- js3-token-end pos))
                (throw 'break nil))  ; done
               ((= tt js3-CASE)
                (setq case-expr (js3-parse-expr))
                (js3-must-match js3-COLON "msg.no.colon.case"))
               ((= tt js3-DEFAULT)
                (if has-default
                    (js3-report-error "msg.double.switch.default"))
                (setq has-default t
                      case-expr nil)
                (js3-must-match js3-COLON "msg.no.colon.case"))
               (t
                (js3-report-error "msg.bad.switch")
                (throw 'break nil)))
              (setq case-node (make-js3-case-node :pos case-pos
                                                  :len (- js3-token-end case-pos)
                                                  :expr case-expr))
              (js3-node-add-children case-node case-expr)
              (while (and (/= (setq tt (js3-peek-token)) js3-RC)
                          (/= tt js3-CASE)
                          (/= tt js3-DEFAULT)
                          (/= tt js3-EOF))
                (setf stmt (js3-parse-statement)
                      (js3-node-len case-node) (- (js3-node-end stmt) case-pos))
                (js3-block-node-push case-node stmt))
              (push case-node cases)))
          ;; add cases last, as pushing reverses the order to be correct
          (dolist (kid cases)
            (js3-node-add-children pn kid)
            (push kid (js3-switch-node-cases pn)))
          pn)  ; return value
      (js3-exit-switch))))

(defun js3-parse-while ()
  "Parser for while-statement.  Last matched token must be js3-WHILE."
  (let ((pos js3-token-beg)
        (pn (make-js3-while-node))
        cond
        body)
    (js3-consume-token)
    (js3-enter-loop pn)
    (unwind-protect
        (progn
          (setf cond (js3-parse-condition)
                (js3-while-node-condition pn) (car cond)
                body (js3-parse-statement)
                (js3-while-node-body pn) body
                (js3-node-len pn) (- (js3-node-end body) pos)
                (js3-while-node-lp pn) (js3-relpos (second cond) pos)
                (js3-while-node-rp pn) (js3-relpos (third cond) pos))
          (js3-node-add-children pn body (car cond)))
      (js3-exit-loop))
    pn))

(defun js3-parse-do ()
  "Parser for do-statement.  Last matched token must be js3-DO."
  (let ((pos js3-token-beg)
        (pn (make-js3-do-node))
        cond
        body
        end)
    (js3-consume-token)
    (js3-enter-loop pn)
    (unwind-protect
        (progn
          (setq body (js3-parse-statement))
          (js3-must-match js3-WHILE "msg.no.while.do")
          (setf (js3-do-node-while-pos pn) (- js3-token-beg pos)
                cond (js3-parse-condition)
                (js3-do-node-condition pn) (car cond)
                (js3-do-node-body pn) body
                end js3-ts-cursor
                (js3-do-node-lp pn) (js3-relpos (second cond) pos)
                (js3-do-node-rp pn) (js3-relpos (third cond) pos))
          (js3-node-add-children pn (car cond) body))
      (js3-exit-loop))
    ;; Always auto-insert semicolon to follow SpiderMonkey:
    ;; It is required by ECMAScript but is ignored by the rest of
    ;; world; see bug 238945
    (if (js3-match-token js3-SEMI)
        (setq end js3-ts-cursor))
    (setf (js3-node-len pn) (- end pos))
    pn))

(defun js3-parse-for ()
  "Parser for for-statement.  Last matched token must be js3-FOR.
Parses for, for-in, and for each-in statements."
  (let ((for-pos js3-token-beg)
        pn
        is-for-each
        is-for-in
        in-pos
        each-pos
        tmp-pos
        init  ; Node init is also foo in 'foo in object'
        cond  ; Node cond is also object in 'foo in object'
        incr  ; 3rd section of for-loop initializer
        body
        tt
        lp
        rp)
    (js3-consume-token)
    ;; See if this is a for each () instead of just a for ()
    (when (js3-match-token js3-NAME)
      (if (string= "each" js3-ts-string)
          (progn
            (setq is-for-each t
                  each-pos (- js3-token-beg for-pos)) ; relative
            (js3-record-face 'font-lock-keyword-face))
        (js3-report-error "msg.no.paren.for")))
    (if (js3-must-match js3-LP "msg.no.paren.for")
        (setq lp (- js3-token-beg for-pos)))
    (setq tt (js3-peek-token))
    ;; parse init clause
    (let ((js3-in-for-init t))  ; set as dynamic variable
      (cond
       ((= tt js3-SEMI)
        (setq init (make-js3-empty-expr-node)))
       ((or (= tt js3-VAR) (= tt js3-LET))
        (js3-consume-token)
        (setq init (js3-parse-variables tt js3-token-beg)))
       (t
        (setq init (js3-parse-expr)))))
    (if (js3-match-token js3-IN)
        (setq is-for-in t
              in-pos (- js3-token-beg for-pos)
              cond (js3-parse-expr))  ; object over which we're iterating
      ;; else ordinary for loop - parse cond and incr
      (js3-must-match js3-SEMI "msg.no.semi.for")
      (setq cond (if (= (js3-peek-token) js3-SEMI)
                     (make-js3-empty-expr-node) ; no loop condition
                   (js3-parse-expr)))
      (js3-must-match js3-SEMI "msg.no.semi.for.cond")
      (setq tmp-pos js3-token-end
            incr (if (= (js3-peek-token) js3-RP)
                     (make-js3-empty-expr-node :pos tmp-pos)
                   (js3-parse-expr))))
    (if (js3-must-match js3-RP "msg.no.paren.for.ctrl")
        (setq rp (- js3-token-beg for-pos)))
    (if (not is-for-in)
        (setq pn (make-js3-for-node :init init
                                    :condition cond
                                    :update incr
                                    :lp lp
                                    :rp rp))
      ;; cond could be null if 'in obj' got eaten by the init node.
      (if (js3-infix-node-p init)
          ;; it was (foo in bar) instead of (var foo in bar)
          (setq cond (js3-infix-node-right init)
                init (js3-infix-node-left init))
        (if (and (js3-var-decl-node-p init)
                 (> (length (js3-var-decl-node-kids init)) 1))
            (js3-report-error "msg.mult.index")))
      (setq pn (make-js3-for-in-node :iterator init
                                     :object cond
                                     :in-pos in-pos
                                     :foreach-p is-for-each
                                     :each-pos each-pos
                                     :lp lp
                                     :rp rp)))
    (unwind-protect
        (progn
          (js3-enter-loop pn)
          ;; We have to parse the body -after- creating the loop node,
          ;; so that the loop node appears in the js3-loop-set, allowing
          ;; break/continue statements to find the enclosing loop.
          (setf body (js3-parse-statement)
                (js3-loop-node-body pn) body
                (js3-node-pos pn) for-pos
                (js3-node-len pn) (- (js3-node-end body) for-pos))
          (js3-node-add-children pn init cond incr body))
      ;; finally
      (js3-exit-loop))
    pn))

(defun js3-parse-try ()
  "Parser for try-statement.  Last matched token must be js3-TRY."
  (let ((try-pos js3-token-beg)
        try-end
        try-block
        catch-blocks
        finally-block
        saw-default-catch
        peek
        var-name
        catch-cond
        catch-node
        guard-kwd
        catch-pos
        finally-pos
        pn
        block
        lp
        rp)
    (js3-consume-token)
    (if (/= (js3-peek-token) js3-LC)
        (js3-report-error "msg.no.brace.try"))
    (setq try-block (js3-parse-statement)
          try-end (js3-node-end try-block)
          peek (js3-peek-token))
    (cond
     ((= peek js3-CATCH)
      (while (js3-match-token js3-CATCH)
        (setq catch-pos js3-token-beg
              guard-kwd nil
              catch-cond nil
              lp nil
              rp nil)
        (if saw-default-catch
            (js3-report-error "msg.catch.unreachable"))
        (if (js3-must-match js3-LP "msg.no.paren.catch")
            (setq lp (- js3-token-beg catch-pos)))
        (js3-must-match js3-NAME "msg.bad.catchcond")
        (js3-push-scope (make-js3-scope))
        (setq var-name (js3-create-name-node))
        (js3-define-symbol js3-LET (js3-name-node-name var-name) var-name t)
        (if (js3-match-token js3-IF)
            (setq guard-kwd (- js3-token-beg catch-pos)
                  catch-cond (js3-parse-expr))
          (setq saw-default-catch t))
        (if (js3-must-match js3-RP "msg.bad.catchcond")
            (setq rp (- js3-token-beg catch-pos)))
        (js3-must-match js3-LC "msg.no.brace.catchblock")
        (setq block (js3-parse-statements)
              try-end (js3-node-end block)
              catch-node (make-js3-catch-node :pos catch-pos
                                              :var-name var-name
                                              :guard-expr catch-cond
                                              :guard-kwd guard-kwd
                                              :block block
                                              :lp lp
                                              :rp rp))
        (js3-pop-scope)
        (if (js3-must-match js3-RC "msg.no.brace.after.body")
            (setq try-end js3-token-beg))
        (setf (js3-node-len block) (- try-end (js3-node-pos block))
              (js3-node-len catch-node) (- try-end catch-pos))
        (js3-node-add-children catch-node var-name catch-cond block)
        (push catch-node catch-blocks)))
     ((/= peek js3-FINALLY)
      (js3-must-match js3-FINALLY "msg.try.no.catchfinally"
                      (js3-node-pos try-block)
                      (- (setq try-end (js3-node-end try-block))
                         (js3-node-pos try-block)))))
    (when (js3-match-token js3-FINALLY)
      (setq finally-pos js3-token-beg
            block (js3-parse-statement)
            try-end (js3-node-end block)
            finally-block (make-js3-finally-node :pos finally-pos
                                                 :len (- try-end finally-pos)
                                                 :body block))
      (js3-node-add-children finally-block block))
    (setq pn (make-js3-try-node :pos try-pos
                                :len (- try-end try-pos)
                                :try-block try-block
                                :finally-block finally-block))
    (js3-node-add-children pn try-block finally-block)
    ;; push them onto the try-node, which reverses and corrects their order
    (dolist (cb catch-blocks)
      (js3-node-add-children pn cb)
      (push cb (js3-try-node-catch-clauses pn)))
    pn))

(defun js3-parse-throw ()
  "Parser for throw-statement.  Last matched token must be js3-THROW."
  (let ((pos js3-token-beg)
        expr
        pn)
    (js3-consume-token)
    (if (= (js3-peek-token-or-eol) js3-EOL)
        ;; ECMAScript does not allow new lines before throw expression,
        ;; see bug 256617
        (js3-report-error "msg.bad.throw.eol"))
    (setq expr (js3-parse-expr)
          pn (make-js3-throw-node :pos pos
                                  :len (- (js3-node-end expr) pos)
                                  :expr expr))
    (js3-node-add-children pn expr)
    pn))

(defsubst js3-match-jump-label-name (label-name)
  "If break/continue specified a label, return that label's labeled stmt.
Returns the corresponding `js3-labeled-stmt-node', or if LABEL-NAME
does not match an existing label, reports an error and returns nil."
  (let ((bundle (cdr (assoc label-name js3-label-set))))
    (if (null bundle)
        (js3-report-error "msg.undef.label"))
    bundle))

(defun js3-parse-break ()
  "Parser for break-statement.  Last matched token must be js3-BREAK."
  (let ((pos js3-token-beg)
        (end js3-token-end)
        break-target ; statement to break from
        break-label  ; in "break foo", name-node representing the foo
        labels       ; matching labeled statement to break to
        pn)
    (js3-consume-token)  ; `break'
    (when (eq (js3-peek-token-or-eol) js3-NAME)
      (js3-consume-token)
      (setq break-label (js3-create-name-node)
            end (js3-node-end break-label)
            ;; matchJumpLabelName only matches if there is one
            labels (js3-match-jump-label-name js3-ts-string)
            break-target (if labels (car (js3-labeled-stmt-node-labels labels)))))
    (unless (or break-target break-label)
      ;; no break target specified - try for innermost enclosing loop/switch
      (if (null js3-loop-and-switch-set)
          (unless break-label
            (js3-report-error "msg.bad.break" nil pos (length "break")))
        (setq break-target (car js3-loop-and-switch-set))))
    (setq pn (make-js3-break-node :pos pos
                                  :len (- end pos)
                                  :label break-label
                                  :target break-target))
    (js3-node-add-children pn break-label)  ; but not break-target
    pn))

(defun js3-parse-continue ()
  "Parser for continue-statement.  Last matched token must be js3-CONTINUE."
  (let ((pos js3-token-beg)
        (end js3-token-end)
        label   ; optional user-specified label, a `js3-name-node'
        labels  ; current matching labeled stmt, if any
        target  ; the `js3-loop-node' target of this continue stmt
        pn)
    (js3-consume-token)  ; `continue'
    (when (= (js3-peek-token-or-eol) js3-NAME)
      (js3-consume-token)
      (setq label (js3-create-name-node)
            end (js3-node-end label)
            ;; matchJumpLabelName only matches if there is one
            labels (js3-match-jump-label-name js3-ts-string)))
    (cond
     ((null labels)  ; no current label to go to
      (if (null js3-loop-set)  ; no loop to continue to
          (js3-report-error "msg.continue.outside" nil pos
                            (length "continue"))
        (setq target (car js3-loop-set))))  ; innermost enclosing loop
     (t
      (if (js3-loop-node-p (js3-labeled-stmt-node-stmt labels))
          (setq target (js3-labeled-stmt-node-stmt labels))
        (js3-report-error "msg.continue.nonloop" nil pos (- end pos)))))
    (setq pn (make-js3-continue-node :pos pos
                                     :len (- end pos)
                                     :label label
                                     :target target))
    (js3-node-add-children pn label)  ; but not target - it's not our child
    pn))

(defun js3-parse-with ()
  "Parser for with-statement.  Last matched token must be js3-WITH."
  (js3-consume-token)
  (let ((pos js3-token-beg)
        obj body pn lp rp)
    (if (js3-must-match js3-LP "msg.no.paren.with")
        (setq lp js3-token-beg))
    (setq obj (js3-parse-expr))
    (if (js3-must-match js3-RP "msg.no.paren.after.with")
        (setq rp js3-token-beg))
    (let ((js3-nesting-of-with (1+ js3-nesting-of-with)))
      (setq body (js3-parse-statement)))
    (setq pn (make-js3-with-node :pos pos
                                 :len (- (js3-node-end body) pos)
                                 :object obj
                                 :body body
                                 :lp (js3-relpos lp pos)
                                 :rp (js3-relpos rp pos)))
    (js3-node-add-children pn obj body)
    pn))

(defun js3-parse-const-var ()
  "Parser for var- or const-statement.
Last matched token must be js3-CONST or js3-VAR."
  (let ((tt (js3-peek-token))
        (pos js3-token-beg)
        expr
        pn)
    (js3-consume-token)
    (setq expr (js3-parse-variables tt js3-token-beg)
          pn (make-js3-expr-stmt-node :pos pos
                                      :len (- (js3-node-end expr) pos)
                                      :expr expr))
    (js3-node-add-children pn expr)
    pn))

(defsubst js3-wrap-with-expr-stmt (pos expr &optional add-child)
  (let ((pn (make-js3-expr-stmt-node :pos pos
                                     :len (js3-node-len expr)
                                     :type (if (js3-inside-function)
                                               js3-EXPR_VOID
                                             js3-EXPR_RESULT)
                                     :expr expr)))
    (if add-child
        (js3-node-add-children pn expr))
    pn))

(defun js3-parse-let-stmt ()
  "Parser for let-statement.  Last matched token must be js3-LET."
  (js3-consume-token)
  (let ((pos js3-token-beg)
        expr
        pn)
    (if (= (js3-peek-token) js3-LP)
        ;; let expression in statement context
        (setq expr (js3-parse-let pos 'statement)
              pn (js3-wrap-with-expr-stmt pos expr t))
      ;; else we're looking at a statement like let x=6, y=7;
      (setf expr (js3-parse-variables js3-LET pos)
            pn (js3-wrap-with-expr-stmt pos expr t)
            (js3-node-type pn) js3-EXPR_RESULT))
    pn))

(defun js3-parse-ret-yield ()
  (js3-parse-return-or-yield (js3-peek-token) nil))

(defconst js3-parse-return-stmt-enders
  (list js3-SEMI js3-RC js3-EOF js3-EOL js3-ERROR js3-RB js3-RP js3-YIELD))

(defsubst js3-now-all-set (before after mask)
  "Return whether or not the bits in the mask have changed to all set.
BEFORE is bits before change, AFTER is bits after change, and MASK is
the mask for bits.  Returns t if all the bits in the mask are set in AFTER
but not BEFORE."
  (and (/= (logand before mask) mask)
       (= (logand after mask) mask)))

(defun js3-parse-return-or-yield (tt expr-context)
  (let ((pos js3-token-beg)
        (end js3-token-end)
        (before js3-end-flags)
        (inside-function (js3-inside-function))
        e
        ret
        name)
    (unless inside-function
      (js3-report-error (if (eq tt js3-RETURN)
                            "msg.bad.return"
                          "msg.bad.yield")))
    (js3-consume-token)
    ;; This is ugly, but we don't want to require a semicolon.
    (unless (memq (js3-peek-token-or-eol) js3-parse-return-stmt-enders)
      (setq e (js3-parse-expr)
            end (js3-node-end e)))
    (cond
     ((eq tt js3-RETURN)
      (js3-set-flag js3-end-flags (if (null e)
                                      js3-end-returns
                                    js3-end-returns-value))
      (setq ret (make-js3-return-node :pos pos
                                      :len (- end pos)
                                      :retval e))
      (js3-node-add-children ret e)
      ;; See if we need a strict mode warning.
      ;; TODO:  The analysis done by `js3-has-consistent-return-usage' is
      ;; more thorough and accurate than this before/after flag check.
      ;; E.g. if there's a finally-block that always returns, we shouldn't
      ;; show a warning generated by inconsistent returns in the catch blocks.
      ;; Basically `js3-has-consistent-return-usage' needs to keep more state,
      ;; so we know which returns/yields to highlight, and we should get rid of
      ;; all the checking in `js3-parse-return-or-yield'.
      (if (and js3-strict-inconsistent-return-warning
               (js3-now-all-set before js3-end-flags
                                (logior js3-end-returns js3-end-returns-value)))
          (js3-add-strict-warning "msg.return.inconsistent" nil pos end)))
     (t
      (unless (js3-inside-function)
        (js3-report-error "msg.bad.yield"))
      (js3-set-flag js3-end-flags js3-end-yields)
      (setq ret (make-js3-yield-node :pos pos
                                     :len (- end pos)
                                     :value e))
      (js3-node-add-children ret e)
      (unless expr-context
        (setq e ret
              ret (js3-wrap-with-expr-stmt pos e t))
        (js3-set-requires-activation)
        (js3-set-is-generator))))
    ;; see if we are mixing yields and value returns.
    (when (and inside-function
               (js3-now-all-set before js3-end-flags
                                (logior js3-end-yields js3-end-returns-value)))
      (setq name (js3-function-name js3-current-script-or-fn))
      (if (zerop (length name))
          (js3-report-error "msg.anon.generator.returns" nil pos (- end pos))
        (js3-report-error "msg.generator.returns" name pos (- end pos))))
    ret))

(defun js3-parse-debugger ()
  (js3-consume-token)
  (make-js3-keyword-node :type js3-DEBUGGER))

(defun js3-parse-block ()
  "Parser for a curly-delimited statement block.
Last token matched must be js3-LC."
  (let* ((pos js3-token-beg)
         (pn (make-js3-block-node :pos pos)))
    (js3-consume-token)
    (js3-push-scope (make-js3-scope))
    (unwind-protect
        (progn
          (js3-parse-statements pn)
          (js3-must-match js3-RC "msg.no.brace.block")
          (setf (js3-node-len pn) (- js3-token-end pos)))
      (js3-pop-scope))
    pn))

;; for js3-ERROR too, to have a node for error recovery to work on
(defun js3-parse-semi ()
  "Parse a statement or handle an error.
Last matched token is js3-SEMI or js3-ERROR."
  (let ((tt (js3-peek-token)) pos len)
    (js3-consume-token)
    (if (eq tt js3-SEMI)
        (make-js3-empty-expr-node :len 1)
      (setq pos js3-token-beg
            len (- js3-token-beg pos))
      (js3-report-error "msg.syntax" nil pos len)
      (make-js3-error-node :pos pos :len len))))

(defun js3-record-label (label bundle)
  ;; current token should be colon that `js3-parse-primary-expr' left untouched
  (js3-consume-token)
  (let ((name (js3-label-node-name label))
        labeled-stmt
        dup)
    (when (setq labeled-stmt (cdr (assoc name js3-label-set)))
      ;; flag both labels if possible when used in editing mode
      (if (and js3-parse-ide-mode
               (setq dup (js3-get-label-by-name labeled-stmt name)))
          (js3-report-error "msg.dup.label" nil
                            (js3-node-abs-pos dup) (js3-node-len dup)))
      (js3-report-error "msg.dup.label" nil
                        (js3-node-pos label) (js3-node-len label)))
    (js3-labeled-stmt-node-add-label bundle label)
    (js3-node-add-children bundle label)
    ;; Add one reference to the bundle per label in `js3-label-set'
    (push (cons name bundle) js3-label-set)))

(defun js3-parse-name-or-label ()
  "Parser for identifier or label.  Last token matched must be js3-NAME.
Called when we found a name in a statement context.  If it's a label, we gather
up any following labels and the next non-label statement into a
`js3-labeled-stmt-node' bundle and return that.  Otherwise we parse an
expression and return it wrapped in a `js3-expr-stmt-node'."
  (let ((pos js3-token-beg)
        (end js3-token-end)
        expr
        stmt
        pn
        bundle
        (continue t))
    ;; set check for label and call down to `js3-parse-primary-expr'
    (js3-set-check-for-label)
    (setq expr (js3-parse-expr))
    (if (/= (js3-node-type expr) js3-LABEL)
        ;; Parsed non-label expression - wrap with expression stmt.
        (setq pn (js3-wrap-with-expr-stmt pos expr t))
      ;; else parsed a label
      (setq bundle (make-js3-labeled-stmt-node :pos pos))
      (js3-record-label expr bundle)
      ;; look for more labels
      (while (and continue (= (js3-peek-token) js3-NAME))
        (js3-set-check-for-label)
        (setq expr (js3-parse-expr))
        (if (/= (js3-node-type expr) js3-LABEL)
            (progn
              (setq stmt (js3-wrap-with-expr-stmt (js3-node-pos expr) expr t)
                    continue nil)
              (js3-auto-insert-semicolon stmt))
          (js3-record-label expr bundle)))
      ;; no more labels; now parse the labeled statement
      (unwind-protect
          (unless stmt
            (let ((js3-labeled-stmt bundle))  ; bind dynamically
              (setq stmt (js3-statement-helper))))
        ;; remove the labels for this statement from the global set
        (dolist (label (js3-labeled-stmt-node-labels bundle))
          (setq js3-label-set (remove label js3-label-set))))
      (setf (js3-labeled-stmt-node-stmt bundle) stmt
            (js3-node-len bundle) (- (js3-node-end stmt) pos))
      (js3-node-add-children bundle stmt)
      bundle)))

(defun js3-parse-expr-stmt ()
  "Default parser in statement context, if no recognized statement found."
  (js3-wrap-with-expr-stmt js3-token-beg (js3-parse-expr) t))

(defun js3-parse-variables (decl-type pos)
  "Parse a comma-separated list of variable declarations.
Could be a 'var', 'const' or 'let' expression, possibly in a for-loop initializer.

DECL-TYPE is a token value: either VAR, CONST, or LET depending on context.
For 'var' or 'const', the keyword should be the token last scanned.

POS is the position where the node should start. It's sometimes the
var/const/let keyword, and other times the beginning of the first token
in the first variable declaration.

Returns the parsed `js3-var-decl-node' expression node."
  (let* ((result (make-js3-var-decl-node :decl-type decl-type
                                         :pos pos))
         destructuring
         kid-pos
         tt
         init
         name
         end
         nbeg nend
         vi
         (continue t))
    ;; Example:
    ;; var foo = {a: 1, b: 2}, bar = [3, 4];
    ;; var {b: s2, a: s1} = foo, x = 6, y, [s3, s4] = bar;
    (while continue
      (setq destructuring nil
            name nil
            tt (js3-peek-token)
            kid-pos js3-token-beg
            end js3-token-end
            init nil)
      (if (or (= tt js3-LB) (= tt js3-LC))
          ;; Destructuring assignment, e.g., var [a, b] = ...
          (setq destructuring (js3-parse-primary-expr)
                end (js3-node-end destructuring))
        ;; Simple variable name
        (when (js3-must-match js3-NAME "msg.bad.var")
          (setq name (js3-create-name-node)
                nbeg js3-token-beg
                nend js3-token-end
                end nend)
          (js3-define-symbol decl-type js3-ts-string name js3-in-for-init)))
      (when (js3-match-token js3-ASSIGN)
        (setq init (js3-parse-assign-expr)
              end (js3-node-end init))
        (if (and js3-parse-ide-mode
                 (or (js3-object-node-p init)
                     (js3-function-node-p init)))
            (js3-record-imenu-functions init name)))
      (when name
        (js3-set-face nbeg nend (if (js3-function-node-p init)
                                    'font-lock-function-name-face
                                  'font-lock-variable-name-face)
                      'record))
      (setq vi (make-js3-var-init-node :pos kid-pos
                                       :len (- end kid-pos)
                                       :type decl-type))
      (if destructuring
          (progn
            (if (and (null init) (not js3-in-for-init))
                (js3-report-error "msg.destruct.assign.no.init"))
            (setf (js3-var-init-node-target vi) destructuring))
        (setf (js3-var-init-node-target vi) name))
      (setf (js3-var-init-node-initializer vi) init)
      (js3-node-add-children vi name destructuring init)
      (js3-block-node-push result vi)
      (unless (js3-match-token js3-COMMA)
        (setq continue nil)))
    (setf (js3-node-len result) (- end pos))
    result))

(defun js3-parse-let (pos &optional stmt-p)
  "Parse a let expression or statement.
A let-expression is of the form `let (vars) expr'.
A let-statment is of the form `let (vars) {statements}'.
The third form of let is a variable declaration list, handled
by `js3-parse-variables'."
  (let ((pn (make-js3-let-node :pos pos))
        beg vars body)
    (if (js3-must-match js3-LP "msg.no.paren.after.let")
        (setf (js3-let-node-lp pn) (- js3-token-beg pos)))
    (js3-push-scope pn)
    (unwind-protect
        (progn
          (setq vars (js3-parse-variables js3-LET js3-token-beg))
          (if (js3-must-match js3-RP "msg.no.paren.let")
              (setf (js3-let-node-rp pn) (- js3-token-beg pos)))
          (if (and stmt-p (eq (js3-peek-token) js3-LC))
              ;; let statement
              (progn
                (js3-consume-token)
                (setf beg js3-token-beg  ; position stmt at LC
                      body (js3-parse-statements))
                (js3-must-match js3-RC "msg.no.curly.let")
                (setf (js3-node-len body) (- js3-token-end beg)
                      (js3-node-len pn) (- js3-token-end pos)
                      (js3-let-node-body pn) body
                      (js3-node-type pn) js3-LET))
            ;; let expression
            (setf body (js3-parse-expr)
                  (js3-node-len pn) (- (js3-node-end body) pos)
                  (js3-let-node-body pn) body))
          (js3-node-add-children pn vars body))
      (js3-pop-scope))
    pn))

(defsubst js3-define-new-symbol (decl-type name node &optional scope)
  (js3-scope-put-symbol (or scope js3-current-scope)
                        name
                        (make-js3-symbol decl-type name node)))

(defun js3-define-symbol (decl-type name &optional node ignore-not-in-block)
  "Define a symbol in the current scope.
If NODE is non-nil, it is the AST node associated with the symbol."
  (let* ((defining-scope (js3-get-defining-scope js3-current-scope name))
         (symbol (if defining-scope
                     (js3-scope-get-symbol defining-scope name)))
         (sdt (if symbol (js3-symbol-decl-type symbol) -1)))
    (cond
     ((and symbol ; already defined
           (or (= sdt js3-CONST) ; old version is const
               (= decl-type js3-CONST) ; new version is const
               ;; two let-bound vars in this block have same name
               (and (= sdt js3-LET)
                    (eq defining-scope js3-current-scope))))
      (js3-report-error
       (cond
        ((= sdt js3-CONST) "msg.const.redecl")
        ((= sdt js3-LET) "msg.let.redecl")
        ((= sdt js3-VAR) "msg.var.redecl")
        ((= sdt js3-FUNCTION) "msg.function.redecl")
        (t "msg.parm.redecl"))
       name))
     ((= decl-type js3-LET)
      (if (and (not ignore-not-in-block)
               (or (= (js3-node-type js3-current-scope) js3-IF)
                   (js3-loop-node-p js3-current-scope)))
          (js3-report-error "msg.let.decl.not.in.block")
        (js3-define-new-symbol decl-type name node
                               js3-current-script-or-fn)))
     ((or (= decl-type js3-VAR)
          (= decl-type js3-CONST)
          (= decl-type js3-FUNCTION))
      (if symbol
          (if (and js3-strict-var-redeclaration-warning (= sdt js3-VAR))
              (js3-add-strict-warning "msg.var.redecl" name)
            (if (and js3-strict-var-hides-function-arg-warning (= sdt js3-LP))
                (js3-add-strict-warning "msg.var.hides.arg" name)))
        (js3-define-new-symbol decl-type name node)))
     ((= decl-type js3-LP)
      (if symbol
          ;; must be duplicate parameter. Second parameter hides the
          ;; first, so go ahead and add the second pararameter
          (js3-report-warning "msg.dup.parms" name))
      (js3-define-new-symbol decl-type name node))
     (t (js3-code-bug)))))

(defun js3-parse-expr ()
  (let* ((pn (js3-parse-assign-expr))
         (pos (js3-node-pos pn))
         left
         right
         op-pos)
    (while (js3-match-token js3-COMMA)
      (setq op-pos (- js3-token-beg pos))  ; relative
      (if (= (js3-peek-token) js3-YIELD)
          (js3-report-error "msg.yield.parenthesized"))
      (setq right (js3-parse-assign-expr)
            left pn
            pn (make-js3-infix-node :type js3-COMMA
                                    :pos pos
                                    :len (- js3-ts-cursor pos)
                                    :op-pos op-pos
                                    :left left
                                    :right right))
      (js3-node-add-children pn left right))
    pn))

(defun js3-parse-assign-expr ()
  (let ((tt (js3-peek-token))
        (pos js3-token-beg)
        pn
        left
        right
        op-pos)
    (if (= tt js3-YIELD)
        (js3-parse-return-or-yield tt t)
      ;; not yield - parse assignment expression
      (setq pn (js3-parse-cond-expr)
            tt (js3-peek-token))
      (when (and (<= js3-first-assign tt)
                 (<= tt js3-last-assign))
        (js3-consume-token)
        (setq op-pos (- js3-token-beg pos)  ; relative
              left pn
              right (js3-parse-assign-expr)
              pn (make-js3-assign-node :type tt
                                       :pos pos
                                       :len (- (js3-node-end right) pos)
                                       :op-pos op-pos
                                       :left left
                                       :right right))
        (when js3-parse-ide-mode
          (js3-highlight-assign-targets pn left right)
          (if (or (js3-function-node-p right)
                  (js3-object-node-p right))
              (js3-record-imenu-functions right left)))
        ;; do this last so ide checks above can use absolute positions
        (js3-node-add-children pn left right))
      pn)))

(defun js3-parse-cond-expr ()
  (let ((pos js3-token-beg)
        (pn (js3-parse-or-expr))
        test-expr
        if-true
        if-false
        q-pos
        c-pos)
    (when (js3-match-token js3-HOOK)
      (setq q-pos (- js3-token-beg pos)
            if-true (js3-parse-assign-expr))
      (js3-must-match js3-COLON "msg.no.colon.cond")
      (setq c-pos (- js3-token-beg pos)
            if-false (js3-parse-assign-expr)
            test-expr pn
            pn (make-js3-cond-node :pos pos
                                   :len (- (js3-node-end if-false) pos)
                                   :test-expr test-expr
                                   :true-expr if-true
                                   :false-expr if-false
                                   :q-pos q-pos
                                   :c-pos c-pos))
      (js3-node-add-children pn test-expr if-true if-false))
    pn))

(defun js3-make-binary (type left parser)
  "Helper for constructing a binary-operator AST node.
LEFT is the left-side-expression, already parsed, and the
binary operator should have just been matched.
PARSER is a function to call to parse the right operand,
or a `js3-node' struct if it has already been parsed."
  (let* ((pos (js3-node-pos left))
         (op-pos (- js3-token-beg pos))
         (right (if (js3-node-p parser)
                    parser
                  (funcall parser)))
         (pn (make-js3-infix-node :type type
                                  :pos pos
                                  :len (- (js3-node-end right) pos)
                                  :op-pos op-pos
                                  :left left
                                  :right right)))
    (js3-node-add-children pn left right)
    pn))

(defun js3-parse-or-expr ()
  (let ((pn (js3-parse-and-expr)))
    (when (js3-match-token js3-OR)
      (setq pn (js3-make-binary js3-OR
                                pn
                                'js3-parse-or-expr)))
    pn))

(defun js3-parse-and-expr ()
  (let ((pn (js3-parse-bit-or-expr)))
    (when (js3-match-token js3-AND)
      (setq pn (js3-make-binary js3-AND
                                pn
                                'js3-parse-and-expr)))
    pn))

(defun js3-parse-bit-or-expr ()
  (let ((pn (js3-parse-bit-xor-expr)))
    (while (js3-match-token js3-BITOR)
      (setq pn (js3-make-binary js3-BITOR
                                pn
                                'js3-parse-bit-xor-expr)))
    pn))

(defun js3-parse-bit-xor-expr ()
  (let ((pn (js3-parse-bit-and-expr)))
    (while (js3-match-token js3-BITXOR)
      (setq pn (js3-make-binary js3-BITXOR
                                pn
                                'js3-parse-bit-and-expr)))
    pn))

(defun js3-parse-bit-and-expr ()
  (let ((pn (js3-parse-eq-expr)))
    (while (js3-match-token js3-BITAND)
      (setq pn (js3-make-binary js3-BITAND
                                pn
                                'js3-parse-eq-expr)))
    pn))

(defconst js3-parse-eq-ops
  (list js3-EQ js3-NE js3-SHEQ js3-SHNE))

(defun js3-parse-eq-expr ()
  (let ((pn (js3-parse-rel-expr))
        tt)
    (while (memq (setq tt (js3-peek-token)) js3-parse-eq-ops)
      (js3-consume-token)
      (setq pn (js3-make-binary tt
                                pn
                                'js3-parse-rel-expr)))
    pn))

(defconst js3-parse-rel-ops
  (list js3-IN js3-INSTANCEOF js3-LE js3-LT js3-GE js3-GT))

(defun js3-parse-rel-expr ()
  (let ((pn (js3-parse-shift-expr))
        (continue t)
        tt)
    (while continue
      (setq tt (js3-peek-token))
      (cond
       ((and js3-in-for-init (= tt js3-IN))
        (setq continue nil))
       ((memq tt js3-parse-rel-ops)
        (js3-consume-token)
        (setq pn (js3-make-binary tt pn 'js3-parse-shift-expr)))
       (t
        (setq continue nil))))
    pn))

(defconst js3-parse-shift-ops
  (list js3-LSH js3-URSH js3-RSH))

(defun js3-parse-shift-expr ()
  (let ((pn (js3-parse-add-expr))
        tt
        (continue t))
    (while continue
      (setq tt (js3-peek-token))
      (if (memq tt js3-parse-shift-ops)
          (progn
            (js3-consume-token)
            (setq pn (js3-make-binary tt pn 'js3-parse-add-expr)))
        (setq continue nil)))
    pn))

(defun js3-parse-add-expr ()
  (let ((pn (js3-parse-mul-expr))
        tt
        (continue t))
    (while continue
      (setq tt (js3-peek-token))
      (if (or (= tt js3-ADD) (= tt js3-SUB))
          (progn
            (js3-consume-token)
            (setq pn (js3-make-binary tt pn 'js3-parse-mul-expr)))
        (setq continue nil)))
    pn))

(defconst js3-parse-mul-ops
  (list js3-MUL js3-DIV js3-MOD))

(defun js3-parse-mul-expr ()
  (let ((pn (js3-parse-unary-expr))
        tt
        (continue t))
    (while continue
      (setq tt (js3-peek-token))
      (if (memq tt js3-parse-mul-ops)
          (progn
            (js3-consume-token)
            (setq pn (js3-make-binary tt pn 'js3-parse-unary-expr)))
        (setq continue nil)))
    pn))

(defsubst js3-make-unary (type parser &rest args)
  "Make a unary node of type TYPE.
PARSER is either a node (for postfix operators) or a function to call
to parse the operand (for prefix operators)."
  (let* ((pos js3-token-beg)
         (postfix (js3-node-p parser))
         (expr (if postfix
                   parser
                 (apply parser args)))
         end
         pn)
    (if postfix  ; e.g. i++
        (setq pos (js3-node-pos expr)
              end js3-token-end)
      (setq end (js3-node-end expr)))
    (setq pn (make-js3-unary-node :type type
                                  :pos pos
                                  :len (- end pos)
                                  :operand expr))
    (js3-node-add-children pn expr)
    pn))

(defconst js3-incrementable-node-types
  (list js3-NAME js3-GETPROP js3-GETELEM js3-GET_REF js3-CALL)
  "Node types that can be the operand of a ++ or -- operator.")

(defsubst js3-check-bad-inc-dec (tt beg end unary)
  (unless (memq (js3-node-type (js3-unary-node-operand unary))
                js3-incrementable-node-types)
    (js3-report-error (if (= tt js3-INC)
                          "msg.bad.incr"
                        "msg.bad.decr")
                      nil beg (- end beg))))

(defun js3-parse-unary-expr ()
  (let ((tt (js3-peek-token))
        pn expr beg end)
    (cond
     ((or (= tt js3-VOID)
          (= tt js3-NOT)
          (= tt js3-BITNOT)
          (= tt js3-TYPEOF))
      (js3-consume-token)
      (js3-make-unary tt 'js3-parse-unary-expr))
     ((= tt js3-ADD)
      (js3-consume-token)
      ;; Convert to special POS token in decompiler and parse tree
      (js3-make-unary js3-POS 'js3-parse-unary-expr))
     ((= tt js3-SUB)
      (js3-consume-token)
      ;; Convert to special NEG token in decompiler and parse tree
      (js3-make-unary js3-NEG 'js3-parse-unary-expr))
     ((or (= tt js3-INC)
          (= tt js3-DEC))
      (js3-consume-token)
      (prog1
          (setq beg js3-token-beg
                end js3-token-end
                expr (js3-make-unary tt 'js3-parse-member-expr t))
        (js3-check-bad-inc-dec tt beg end expr)))
     ((= tt js3-DELPROP)
      (js3-consume-token)
      (js3-make-unary js3-DELPROP 'js3-parse-unary-expr))
     ((= tt js3-ERROR)
      (js3-consume-token)
      (make-js3-error-node))  ; try to continue
     (t
      (setq pn (js3-parse-member-expr t)
            ;; Don't look across a newline boundary for a postfix incop.
            tt (js3-peek-token-or-eol))
      (when (or (= tt js3-INC) (= tt js3-DEC))
        (js3-consume-token)
        (setf expr pn
              pn (js3-make-unary tt expr))
        (js3-node-set-prop pn 'postfix t)
        (js3-check-bad-inc-dec tt js3-token-beg js3-token-end pn))
      pn))))


(defun js3-parse-argument-list ()
  "Parse an argument list and return it as a lisp list of nodes.
Returns the list in reverse order.  Consumes the right-paren token."
  (let (result)
    (unless (js3-match-token js3-RP)
      (loop do
            (if (= (js3-peek-token) js3-YIELD)
                (js3-report-error "msg.yield.parenthesized"))
            (push (js3-parse-assign-expr) result)
            while
            (js3-match-token js3-COMMA))
      (js3-must-match js3-RP "msg.no.paren.arg")
      result)))

(defun js3-parse-member-expr (&optional allow-call-syntax)
  (let ((tt (js3-peek-token))
        pn
        pos
        target
        args
        beg
        end
        init
        tail)
    (if (/= tt js3-NEW)
        (setq pn (js3-parse-primary-expr))
      ;; parse a 'new' expression
      (js3-consume-token)
      (setq pos js3-token-beg
            beg pos
            target (js3-parse-member-expr)
            end (js3-node-end target)
            pn (make-js3-new-node :pos pos
                                  :target target
                                  :len (- end pos)))
      (js3-node-add-children pn target)
      (when (js3-match-token js3-LP)
        ;; Add the arguments to pn, if any are supplied.
        (setf beg pos  ; start of "new" keyword
              pos js3-token-beg
              args (nreverse (js3-parse-argument-list))
              (js3-new-node-args pn) args
              end js3-token-end
              (js3-new-node-lp pn) (- pos beg)
              (js3-new-node-rp pn) (- end 1 beg))
        (apply #'js3-node-add-children pn args))
      (when (and js3-allow-rhino-new-expr-initializer
                 (js3-match-token js3-LC))
        (setf init (js3-parse-object-literal)
              end (js3-node-end init)
              (js3-new-node-initializer pn) init)
        (js3-node-add-children pn init))
      (setf (js3-node-len pn) (- end beg)))  ; end outer if
    (js3-parse-member-expr-tail allow-call-syntax pn)))

(defun js3-parse-member-expr-tail (allow-call-syntax pn)
  "Parse a chain of property/array accesses or function calls.
Includes parsing for E4X operators like `..' and `.@'.
If ALLOW-CALL-SYNTAX is nil, stops when we encounter a left-paren.
Returns an expression tree that includes PN, the parent node."
  (let ((beg (js3-node-pos pn))
        tt
        (continue t))
    (while continue
      (setq tt (js3-peek-token))
      (cond
       ((= tt js3-DOT)
        (setq pn (js3-parse-property-access tt pn)))
       ((= tt js3-LB)
        (setq pn (js3-parse-element-get pn)))
       ((= tt js3-LP)
        (if allow-call-syntax
            (setq pn (js3-parse-function-call pn))
          (setq continue nil)))
       (t
        (setq continue nil))))
    (if (>= js3-highlight-level 2)
        (js3-parse-highlight-member-expr-node pn))
    pn))

(defun js3-parse-element-get (pn)
  "Parse an element-get expression, e.g. foo[bar].
Last token parsed must be `js3-RB'."
  (let ((lb js3-token-beg)
        (pos (js3-node-pos pn))
        rb
        expr)
    (js3-consume-token)
    (setq expr (js3-parse-expr))
    (if (js3-must-match js3-RB "msg.no.bracket.index")
        (setq rb js3-token-beg))
    (setq pn (make-js3-elem-get-node :target pn
                                     :pos pos
                                     :element expr
                                     :lb (js3-relpos lb pos)
                                     :rb (js3-relpos rb pos)
                                     :len (- js3-token-end pos)))
    (js3-node-add-children pn
                           (js3-elem-get-node-target pn)
                           (js3-elem-get-node-element pn))
    pn))

(defun js3-parse-function-call (pn)
  (let (args
        (pos (js3-node-pos pn)))
    (js3-consume-token)
    (setq pn (make-js3-call-node :pos pos
                                 :target pn
                                 :lp (- js3-token-beg pos)))
    (js3-node-add-children pn (js3-call-node-target pn))
    ;; Add the arguments to pn, if any are supplied.
    (setf args (nreverse (js3-parse-argument-list))
          (js3-call-node-rp pn) (- js3-token-beg pos)
          (js3-call-node-args pn) args)
    (apply #'js3-node-add-children pn args)
    (setf (js3-node-len pn) (- js3-ts-cursor pos))
    pn))

(defun js3-parse-property-access (tt pn)
  "Parse a property access."
  (let (name
        (pos (js3-node-pos pn))
        end
        ref  ; right side of . operator
        result)
    (js3-consume-token)
    (js3-must-match-prop-name "msg.no.name.after.dot")
    (setq name (js3-create-name-node t js3-GETPROP)
          end (js3-node-end name)
          result (make-js3-prop-get-node :left pn
                                         :pos pos
                                         :right name
                                         :len (- end
                                                 pos)))
    (js3-node-add-children result pn name)
    result))


(defun js3-parse-primary-expr ()
  "Parses a literal (leaf) expression of some sort.
Includes complex literals such as functions, object-literals,
array-literals, array comprehensions and regular expressions."
  (let ((tt-flagged (js3-next-flagged-token))
        pn      ; parent node  (usually return value)
        tt
        px-pos  ; paren-expr pos
        len
        flags   ; regexp flags
        expr)
    (setq tt js3-current-token)
    (cond
     ((= tt js3-FUNCTION)
      (js3-parse-function 'FUNCTION_EXPRESSION))
     ((= tt js3-LB)
      (js3-parse-array-literal))
     ((= tt js3-LC)
      (js3-parse-object-literal))
     ((= tt js3-LET)
      (js3-parse-let js3-token-beg))
     ((= tt js3-LP)
      (setq px-pos js3-token-beg
            expr (js3-parse-expr))
      (js3-must-match js3-RP "msg.no.paren")
      (setq pn (make-js3-paren-node :pos px-pos
                                    :expr expr
                                    :len (- js3-token-end px-pos)))
      (js3-node-add-children pn (js3-paren-node-expr pn))
      pn)
     ((= tt js3-NAME)
      (js3-parse-name tt-flagged tt))
     ((= tt js3-NUMBER)
      (make-js3-number-node))
     ((= tt js3-STRING)
      (prog1
          (make-js3-string-node)
        (js3-record-face 'font-lock-string-face)))
     ((or (= tt js3-DIV) (= tt js3-ASSIGN_DIV))
      ;; Got / or /= which in this context means a regexp literal
      (setq px-pos js3-token-beg)
      (js3-read-regexp tt)
      (setq flags js3-ts-regexp-flags
            js3-ts-regexp-flags nil)
      (prog1
          (make-js3-regexp-node :pos px-pos
                                :len (- js3-ts-cursor px-pos)
                                :value js3-ts-string
                                :flags flags)
        (js3-set-face px-pos js3-ts-cursor 'font-lock-string-face 'record)
        (js3-record-text-property px-pos js3-ts-cursor 'syntax-table '(2))))
     ((or (= tt js3-NULL)
          (= tt js3-THIS)
          (= tt js3-FALSE)
          (= tt js3-TRUE))
      (make-js3-keyword-node :type tt))
     ((= tt js3-RESERVED)
      (js3-report-error "msg.reserved.id")
      (make-js3-name-node))
     ((= tt js3-ERROR)
      ;; the scanner or one of its subroutines reported the error.
      (make-js3-error-node))
     ((= tt js3-EOF)
      (setq px-pos (point-at-bol)
            len (- js3-ts-cursor px-pos))
      (js3-report-error "msg.unexpected.eof" nil px-pos len)
      (make-js3-error-node :pos px-pos :len len))
     (t
      (js3-report-error "msg.syntax")
      (make-js3-error-node)))))

(defun js3-parse-name (tt-flagged tt)
  (let ((name js3-ts-string)
        (name-pos js3-token-beg)
        node)
    (if (and (js3-flag-set-p tt-flagged js3-ti-check-label)
             (= (js3-peek-token) js3-COLON))
        (prog1
            ;; Do not consume colon, it is used as unwind indicator
            ;; to return to statementHelper.
            (make-js3-label-node :pos name-pos
                                 :len (- js3-token-end name-pos)
                                 :name name)
          (js3-set-face name-pos
                        js3-token-end
                        'font-lock-variable-name-face 'record))
      ;; Otherwise not a label, just a name.  Unfortunately peeking
      ;; the next token to check for a colon has biffed js3-token-beg
      ;; and js3-token-end.  We store the name's bounds in buffer vars
      ;; and `js3-create-name-node' uses them.
      (js3-save-name-token-data name-pos name)
      (setq node (js3-create-name-node 'check-activation))
      (if js3-highlight-external-variables
          (js3-record-name-node node))
      node)))

(defsubst js3-parse-warn-trailing-comma (msg pos elems comma-pos)
  (js3-add-strict-warning
   msg nil
   ;; back up from comma to beginning of line or array/objlit
   (max (if elems
            (js3-node-pos (car elems))
          pos)
        (save-excursion
          (goto-char comma-pos)
          (back-to-indentation)
          (point)))
   comma-pos))

(defun js3-parse-array-literal ()
  (let ((pos js3-token-beg)
        (end js3-token-end)
        (after-lb-or-comma t)
        after-comma
        tt
        elems
        pn
        (continue t))
    (while continue
      (setq tt (js3-peek-token))
      (cond
       ;; comma
       ((= tt js3-COMMA)
        (js3-consume-token)
        (setq after-comma js3-token-end)
        (if (not after-lb-or-comma)
            (setq after-lb-or-comma t)
          (push nil elems)))
       ;; end of array
       ((or (= tt js3-RB)
            (= tt js3-EOF))  ; prevent infinite loop
        (if (= tt js3-EOF)
            (js3-report-error "msg.no.bracket.arg" nil pos)
          (js3-consume-token))
        (setq continue nil
              end js3-token-end
              pn (make-js3-array-node :pos pos
                                      :len (- js3-ts-cursor pos)
                                      :elems (nreverse elems)))
        (apply #'js3-node-add-children pn (js3-array-node-elems pn))
        (when after-comma
          (js3-parse-warn-trailing-comma "msg.array.trailing.comma"
                                         pos elems after-comma)))
       ;; array comp
       ((and (>= js3-language-version 170)
             (= tt js3-FOR)          ; check for array comprehension
             (not after-lb-or-comma) ; "for" can't follow a comma
             elems                   ; must have at least 1 element
             (not (cdr elems)))      ; but no 2nd element
        (setf continue nil
              pn (js3-parse-array-comprehension (car elems) pos)))
       ;; another element
       (t
        (unless after-lb-or-comma
          (js3-report-error "msg.no.bracket.arg"))
        (push (js3-parse-assign-expr) elems)
        (setq after-lb-or-comma nil
              after-comma nil))))
    pn))

(defun js3-parse-array-comprehension (expr pos)
  "Parse a JavaScript 1.7 Array Comprehension.
EXPR is the first expression after the opening left-bracket.
POS is the beginning of the LB token preceding EXPR.
We should have just parsed the 'for' keyword before calling this function."
  (let (loops
        filter
        if-pos
        result)
    (while (= (js3-peek-token) js3-FOR)
      (push (js3-parse-array-comp-loop) loops))
    (when (= (js3-peek-token) js3-IF)
      (js3-consume-token)
      (setq if-pos (- js3-token-beg pos)  ; relative
            filter (js3-parse-condition)))
    (js3-must-match js3-RB "msg.no.bracket.arg" pos)
    (setq result (make-js3-array-comp-node :pos pos
                                           :len (- js3-ts-cursor pos)
                                           :result expr
                                           :loops (nreverse loops)
                                           :filter (car filter)
                                           :lp (js3-relpos (second filter) pos)
                                           :rp (js3-relpos (third filter) pos)
                                           :if-pos if-pos))
    (apply #'js3-node-add-children result expr (car filter)
           (js3-array-comp-node-loops result))
    result))

(defun js3-parse-array-comp-loop ()
  "Parse a 'for [each] (foo in bar)' expression in an Array comprehension.
Last token peeked should be the initial FOR."
  (let ((pos js3-token-beg)
        (pn (make-js3-array-comp-loop-node))
        tt
        iter
        obj
        foreach-p
        in-pos
        each-pos
        lp
        rp)
    (assert (= (js3-next-token) js3-FOR))  ; consumes token
    (js3-push-scope pn)
    (unwind-protect
        (progn
          (when (js3-match-token js3-NAME)
            (if (string= js3-ts-string "each")
                (progn
                  (setq foreach-p t
                        each-pos (- js3-token-beg pos)) ; relative
                  (js3-record-face 'font-lock-keyword-face))
              (js3-report-error "msg.no.paren.for")))
          (if (js3-must-match js3-LP "msg.no.paren.for")
              (setq lp (- js3-token-beg pos)))
          (setq tt (js3-peek-token))
          (cond
           ((or (= tt js3-LB)
                (= tt js3-LC))
            ;; handle destructuring assignment
            (setq iter (js3-parse-primary-expr)))
           ((js3-valid-prop-name-token tt)
            (js3-consume-token)
            (setq iter (js3-create-name-node)))
           (t
            (js3-report-error "msg.bad.var")))
          ;; Define as a let since we want the scope of the variable to
          ;; be restricted to the array comprehension
          (if (js3-name-node-p iter)
              (js3-define-symbol js3-LET (js3-name-node-name iter) pn t))
          (if (js3-must-match js3-IN "msg.in.after.for.name")
              (setq in-pos (- js3-token-beg pos)))
          (setq obj (js3-parse-expr))
          (if (js3-must-match js3-RP "msg.no.paren.for.ctrl")
              (setq rp (- js3-token-beg pos)))
          (setf (js3-node-pos pn) pos
                (js3-node-len pn) (- js3-ts-cursor pos)
                (js3-array-comp-loop-node-iterator pn) iter
                (js3-array-comp-loop-node-object pn) obj
                (js3-array-comp-loop-node-in-pos pn) in-pos
                (js3-array-comp-loop-node-each-pos pn) each-pos
                (js3-array-comp-loop-node-foreach-p pn) foreach-p
                (js3-array-comp-loop-node-lp pn) lp
                (js3-array-comp-loop-node-rp pn) rp)
          (js3-node-add-children pn iter obj))
      (js3-pop-scope))
    pn))

(defun js3-parse-object-literal ()
  (let ((pos js3-token-beg)
        tt
        elems
        result
        after-comma
        (continue t))
    (while continue
      (setq tt (js3-peek-token))
      (cond
       ;; {foo: ...}, {'foo': ...}, {get foo() {...}}, or {set foo(x) {...}}
       ((or (js3-valid-prop-name-token tt)
            (= tt js3-STRING))
        (setq after-comma nil
              result (js3-parse-named-prop tt))
        (if (and (null result)
                 (not js3-recover-from-parse-errors))
            (setq continue nil)
          (push result elems)))
       ;; {12: x} or {10.7: x}
       ((= tt js3-NUMBER)
        (js3-consume-token)
        (setq after-comma nil)
        (push (js3-parse-plain-property (make-js3-number-node)) elems))
       ;; trailing comma
       ((= tt js3-RC)
        (setq continue nil)
        (if after-comma
            (js3-parse-warn-trailing-comma "msg.extra.trailing.comma"
                                           pos elems after-comma)))
       (t
        (js3-report-error "msg.bad.prop")
        (unless js3-recover-from-parse-errors
          (setq continue nil))))         ; end switch
      (if (js3-match-token js3-COMMA)
          (setq after-comma js3-token-end)
        (setq continue nil)))           ; end loop
    (js3-must-match js3-RC "msg.no.brace.prop")
    (setq result (make-js3-object-node :pos pos
                                       :len (- js3-ts-cursor pos)
                                       :elems (nreverse elems)))
    (apply #'js3-node-add-children result (js3-object-node-elems result))
    result))

(defun js3-parse-named-prop (tt)
  "Parse a name, string, or getter/setter object property."
  (js3-consume-token)
  (let ((string-prop (and (= tt js3-STRING)
                          (make-js3-string-node)))
        expr
        (ppos js3-token-beg)
        (pend js3-token-end)
        (name (js3-create-name-node))
        (prop js3-ts-string))
    (if (and (= tt js3-NAME)
             (= (js3-peek-token) js3-NAME)
             (or (string= prop "get")
                 (string= prop "set")))
        (progn
          ;; getter/setter prop
          (js3-consume-token)
          (js3-set-face ppos pend 'font-lock-keyword-face 'record)  ; get/set
          (js3-record-face 'font-lock-function-name-face)      ; for peeked name
          (setq name (js3-create-name-node)) ; discard get/set & use peeked name
          (js3-parse-getter-setter-prop ppos name (string= prop "get")))
      ;; regular prop
      (prog1
          (setq expr (js3-parse-plain-property (or string-prop name)))
        (js3-set-face ppos pend
                      (if (js3-function-node-p
                           (js3-object-prop-node-right expr))
                          'font-lock-function-name-face
                        'font-lock-variable-name-face)
                      'record)))))

(defun js3-parse-plain-property (prop)
  "Parse a non-getter/setter property in an object literal.
PROP is the node representing the property:  a number, name or string."
  (js3-must-match js3-COLON "msg.no.colon.prop")
  (let* ((pos (js3-node-pos prop))
         (colon (- js3-token-beg pos))
         (expr (js3-parse-assign-expr))
         (result (make-js3-object-prop-node
                  :pos pos
                  ;; don't include last consumed token in length
                  :len (- (+ (js3-node-pos expr)
                             (js3-node-len expr))
                          pos)
                  :left prop
                  :right expr
                  :op-pos colon)))
    (js3-node-add-children result prop expr)
    result))

(defun js3-parse-getter-setter-prop (pos prop get-p)
  "Parse getter or setter property in an object literal.
JavaScript syntax is:

{ get foo() {...}, set foo(x) {...} }

POS is the start position of the `get' or `set' keyword.
PROP is the `js3-name-node' representing the property name.
GET-P is non-nil if the keyword was `get'."
  (let ((type (if get-p js3-GET js3-SET))
        result
        end
        (fn (js3-parse-function 'FUNCTION_EXPRESSION)))
    ;; it has to be an anonymous function, as we already parsed the name
    (if (/= (js3-node-type fn) js3-FUNCTION)
        (js3-report-error "msg.bad.prop")
      (if (plusp (length (js3-function-name fn)))
          (js3-report-error "msg.bad.prop")))
    (js3-node-set-prop fn 'GETTER_SETTER type)  ; for codegen
    (setq end (js3-node-end fn)
          result (make-js3-getter-setter-node :type type
                                              :pos pos
                                              :len (- end pos)
                                              :left prop
                                              :right fn))
    (js3-node-add-children result prop fn)
    result))

(defun js3-create-name-node (&optional check-activation-p token)
  "Create a name node using the token info from last scanned name.
In some cases we need to either synthesize a name node, or we lost
the name token information by peeking.  If the TOKEN parameter is
not `js3-NAME', then we use the token info saved in instance vars."
  (let ((beg js3-token-beg)
        (s js3-ts-string)
        name)
    (when (/= js3-current-token js3-NAME)
      (setq beg (or js3-prev-name-token-start js3-ts-cursor)
            s js3-prev-name-token-string
            js3-prev-name-token-start nil
            js3-prev-name-token-string nil))
    (setq name (make-js3-name-node :pos beg
                                   :name s
                                   :len (length s)))
    (if check-activation-p
        (js3-check-activation-name s (or token js3-NAME)))
    name))

(provide 'js3-parse)

;;; js3-parse.el ends here
;;; js3-indent.el --- indentation for js3-mode

;;; Commentary:

;; This code is taken as much as possible from the current version of
;; js.el included with emacs 24, with modifications.

;; Unlike js2-mode, this does not support bounce-indent.

;;; Code:

(defconst js3-possibly-braceless-keyword-re
  (regexp-opt
   '("catch" "do" "else" "finally" "for" "if" "try" "while" "with" "let" "each")
   'words)
  "Regular expression matching keywords that are optionally
followed by an opening brace.")

(defconst js3-indent-operator-re
  (concat "[-+*/%<>=&^|?:.]\\([^-+*/]\\|$\\)\\|"
          (regexp-opt '("in" "instanceof") 'words))
  "Regular expression matching operators that affect indentation
of continued expressions.")

(defconst js3-indent-lazy-operator-re
  (concat "[-+*/%<>=&^|?:]\\([^-+*/]\\|$\\)\\|"
          (regexp-opt '("in" "instanceof") 'words))
  "Regular expression matching operators that affect indentation
of continued expressions in lazy-operator-first style.")

(defconst js3-indent-operator-first-re
  (concat "[-+*/%<>!=&^|?:.]\\([^-+*/]\\|$\\)\\|"
          (regexp-opt '("in" "instanceof") 'words))
  "Regular expression matching operators that affect indentation
of continued expressions with operator-first style.")

(defconst js3-indent-brace-re
  "[[({]"
  "Regexp matching opening braces that affect indentation.")

(defconst js3-indent-operator-brace-re
  "[[(]"
  "Regexp matching opening braces that affect operator indentation.")

(defconst js3-skip-newlines-re
  "[ \t\n]*"
  "Regexp matching any amount of trailing whitespace and newlines.")

(defconst js3-opt-cpp-start "^\\s-*#\\s-*\\([[:alnum:]]+\\)"
  "Regexp matching the prefix of a cpp directive.
This includes the directive name, or nil in languages without
preprocessor support.  The first submatch surrounds the directive
name.")

(defun js3-backward-sws ()
  "Move backward through whitespace and comments."
  (interactive)
  (while (forward-comment -1)))

(defun js3-forward-sws ()
  "Move forward through whitespace and comments."
  (interactive)
  (while (forward-comment 1)))

(defun js3-beginning-of-macro (&optional lim)
  (let ((here (point)))
    (save-restriction
      (if lim (narrow-to-region lim (point-max)))
      (beginning-of-line)
      (while (eq (char-before (1- (point))) ?\\)
        (forward-line -1))
      (back-to-indentation)
      (if (and (<= (point) here)
               (looking-at js3-opt-cpp-start))
          t
        (goto-char here)
        nil))))

;; This function has horrible results if you're typing an array
;; such as [[1, 2], [3, 4], [5, 6]].  Bounce indenting -really- sucks
;; in conjunction with electric-indent, so just disabling it.
(defsubst js3-code-at-bol-p ()
  "Return t if the first character on line is non-whitespace."
  nil)

(defun js3-insert-and-indent (key)
  "Run command bound to key and indent current line. Runs the command
bound to KEY in the global keymap and indents the current line."
  (interactive (list (this-command-keys)))
  (let ((cmd (lookup-key (current-global-map) key)))
    (if (commandp cmd)
        (call-interactively cmd)))
  ;; don't do the electric keys inside comments or strings,
  ;; and don't do bounce-indent with them.
  (let ((parse-state (parse-partial-sexp (point-min) (point))))
    (unless (or (nth 3 parse-state)
                (nth 4 parse-state))
      (indent-according-to-mode))))


(defun js3-re-search-forward-inner (regexp &optional bound count)
  "Helper function for `js3-re-search-forward'."
  (let ((parse)
        str-terminator
        (orig-macro-end (save-excursion
                          (when (js3-beginning-of-macro)
                            (c-end-of-macro)
                            (point)))))
    (while (> count 0)
      (re-search-forward regexp bound)
      (setq parse (syntax-ppss))
      (cond ((setq str-terminator (nth 3 parse))
             (when (eq str-terminator t)
               (setq str-terminator ?/))
             (re-search-forward
              (concat "\\([^\\]\\|^\\)" (string str-terminator))
              (point-at-eol) t))
            ((nth 7 parse)
             (forward-line))
            ((or (nth 4 parse)
                 (and (eq (char-before) ?\/) (eq (char-after) ?\*)))
             (re-search-forward "\\*/"))
            ((and (not (and orig-macro-end
                            (<= (point) orig-macro-end)))
                  (js3-beginning-of-macro))
             (c-end-of-macro))
            (t
             (setq count (1- count))))))
  (point))


(defun js3-re-search-forward (regexp &optional bound noerror count)
  "Search forward, ignoring strings, cpp macros, and comments.
This function invokes `re-search-forward', but treats the buffer
as if strings, cpp macros, and comments have been removed.

If invoked while inside a macro, it treats the contents of the
macro as normal text."
  (unless count (setq count 1))
  (let ((saved-point (point))
        (search-fun
         (cond ((< count 0) (setq count (- count))
                #'js3-re-search-backward-inner)
               ((> count 0) #'js3-re-search-forward-inner)
               (t #'ignore))))
    (condition-case err
        (funcall search-fun regexp bound count)
      (search-failed
       (goto-char saved-point)
       (unless noerror
         (signal (car err) (cdr err)))))))


(defun js3-re-search-backward-inner (regexp &optional bound count)
  "Auxiliary function for `js3-re-search-backward'."
  (let ((parse)
        (last-point (point))
        str-terminator
        (orig-macro-start
         (save-excursion
           (and (js3-beginning-of-macro)
                (point)))))
    (while (> count 0)
      (re-search-backward regexp bound)
      (when (and (> (point) (point-min))
                 (save-excursion (backward-char) (looking-at "/[/*]")))
        (forward-char))
      (setq parse (syntax-ppss))
      (cond ((setq str-terminator (nth 3 parse))
             (when (eq str-terminator t)
               (setq str-terminator ?/))
             (re-search-backward
              (concat "\\([^\\]\\|^\\)" (string str-terminator))
              (point-at-bol) t)
             (when (not (string= "" (match-string 1)))
               (forward-char)))
            ((nth 7 parse)
             (goto-char (nth 8 parse)))
            ((or (nth 4 parse)
                 (and (eq (char-before) ?/) (eq (char-after) ?*)))
             (re-search-backward "/\\*"))
            ((and (not (and orig-macro-start
                            (>= (point) orig-macro-start)))
                  (js3-beginning-of-macro)))
            (t
             (setq count (1- count))))
      (when (= (point) last-point)
        (setq count 0))
      (setq last-point (point))))
  (point))


(defun js3-re-search-backward (regexp &optional bound noerror count)
  "Search backward, ignoring strings, preprocessor macros, and comments.

This function invokes `re-search-backward' but treats the buffer
as if strings, preprocessor macros, and comments have been
removed.

If invoked while inside a macro, treat the macro as normal text."
  (js3-re-search-forward regexp bound noerror (if count (- count) -1)))


(defun js3-looking-back (regexp)
  "This function returns t if regexp matches text before point, ending at point, and nil otherwise.

This function is similar to `looking-back' but ignores comments and strings"
  (save-excursion
    (let ((r (if (and (= ?\= (elt regexp (1- (length regexp))))
                      (= ?\\ (elt regexp (- (length regexp) 2))))
                 regexp
               (concat regexp "\\="))))
      (numberp (js3-re-search-backward r (point-min) t)))))

(defun js3-looking-at (regexp)
  "This function returns t if regexp matches text after point, beginning at point, and nil otherwise.

This function is similar to `looking-at' but ignores comments and strings"
  (save-excursion
    (let ((r (if (and (= ?\= (elt regexp 1))
                      (= ?\\ (elt regexp 0)))
                 regexp
               (concat "\\=" regexp))))
      (numberp (js3-re-search-forward r nil t)))))

(defun js3-looking-at-operator-p ()
  "Return non-nil if point is on a JavaScript operator, other than a comma."
  (save-match-data
    (and (looking-at js3-indent-operator-re)
         (or (not (= (following-char) ?\:))
             (save-excursion
               (and (js3-re-search-backward "[?:{]\\|\\_<case\\_>" nil t)
                    (= (following-char) ?\?)))))))


(defun js3-continued-expression-p ()
  "Return non-nil if the current line continues an expression."
  (save-excursion
    (back-to-indentation)
    (or (js3-looking-at-operator-p)
        (and (js3-re-search-backward "\n" nil t)
             (progn
               (skip-chars-backward " \t")
               (or (bobp) (backward-char))
               (and (> (point) (point-min))
                    (save-excursion (backward-char) (not (looking-at "[/*]/")))
                    (js3-looking-at-operator-p)
                    (and (progn (backward-char)
                                (not (looking-at "++\\|--\\|/[/*]"))))))))))


(defun js3-end-of-do-while-loop-p ()
  "Return non-nil if point is on the \"while\" of a do-while statement.
Otherwise, return nil.  A braceless do-while statement spanning
several lines requires that the start of the loop is indented to
the same column as the current line."
  (interactive)
  (save-excursion
    (save-match-data
      (when (looking-at "\\s-*\\_<while\\_>")
        (if (save-excursion
              (skip-chars-backward (concat js3-skip-newlines-re "}"))
              (looking-at (concat js3-skip-newlines-re "}")))
            (save-excursion
              (backward-list) (forward-symbol -1) (looking-at "\\_<do\\_>"))
          (js3-re-search-backward "\\_<do\\_>" (point-at-bol) t)
          (or (looking-at "\\_<do\\_>")
              (let ((saved-indent (current-indentation)))
                (while (and (js3-re-search-backward "^\\s-*\\_<" nil t)
                            (/= (current-indentation) saved-indent)))
                (and (looking-at "\\s-*\\_<do\\_>")
                     (not (js3-re-search-forward
                           "\\_<while\\_>" (point-at-eol) t))
                     (= (current-indentation) saved-indent)))))))))


(defun js3-backward-whitespace ()
  "Helper function for `js3-proper-indentation'.
Skip backwards over whitespace and comments."
  (let ((rv nil))
    (when (js3-looking-back "[ \t\n]")
      (setq rv t)
      (js3-re-search-backward (concat "[^ \t\n]" js3-skip-newlines-re)
                              (point-min) t)
      (forward-char))
    rv))


(defun js3-backward-sexp ()
  "Helper function for `js3-proper-indentation'.
Go backwards over matched braces, rather than whole expressions.
Only skip over strings while looking for braces.
Functionality does not exactly match backward-sexp."
  (let ((brackets 0)
        (rv nil))
    (while (js3-looking-back (concat "[]})]" js3-skip-newlines-re))
      (setq rv t)
      (js3-re-search-backward (concat "[]})]"
                                      js3-skip-newlines-re)
                              (point-min) t)
      (cond
       ((= (following-char) ?\])
        (setq brackets (1+ brackets))
        (while (/= brackets 0)
          (js3-re-search-backward "[][]" (point-min) t)
          (cond
           ((= (following-char) ?\])
            (setq brackets (1+ brackets)))
           ((= (following-char) ?\[)
            (setq brackets (1- brackets))))))

       ((= (following-char) ?\})
        (setq brackets (1+ brackets))
        (while (/= brackets 0)
          (js3-re-search-backward "[}{]" (point-min) t)
          (cond
           ((= (following-char) ?\})
            (setq brackets (1+ brackets)))
           ((= (following-char) ?\{)
            (setq brackets (1- brackets))))))

       ((= (following-char) ?\))
        (setq brackets (1+ brackets))
        (while (/= brackets 0)
          (js3-re-search-backward "[)(]" (point-min) t)
          (cond
           ((= (following-char) ?\))
            (setq brackets (1+ brackets)))
           ((= (following-char) ?\()
            (setq brackets (1- brackets))))))))
    rv))


(defun js3-backward-clean ()
  "Helper function for `js3-proper-indentation'.
Calls js3-backward-sexp and js3-backward-whitespace until they are done."
  (let ((rv nil))
    (while (or (js3-backward-whitespace) (js3-backward-sexp))
      (setq rv t))
    rv))


(defun js3-ctrl-statement-indentation ()
  "Helper function for `js3-proper-indentation'.
Return the proper indentation of the current line if it starts
the body of a control statement without braces; otherwise, return
nil."
  (save-excursion
    (back-to-indentation)
    (when (save-excursion
            (and (not (eq (point-at-bol) (point-min)))
                 (not (= (following-char) ?\{))
                 (progn
                   (js3-re-search-backward "[[:graph:]]" nil t)
                   (or (eobp) (forward-char))
                   (when (= (char-before) ?\)) (backward-list))
                   (skip-syntax-backward " ")
                   (skip-syntax-backward "w_")
                   (looking-at js3-possibly-braceless-keyword-re))
                 (not (js3-end-of-do-while-loop-p))))
      (save-excursion
        (goto-char (match-beginning 0))
        (+ (current-indentation) js3-indent-level)))))

(defun js3-get-c-offset (symbol anchor)
  (let ((c-offsets-alist
         (list (cons 'c js3-comment-lineup-func))))
    (c-get-syntactic-indentation (list (cons symbol anchor)))))

(defun js3-back-offset (abs offset)
  "Helper function for `js3-proper-indentation'."
  (goto-char abs)
  (while (= (preceding-char) ?\ )
    (backward-char))
  (backward-char offset)
  (current-column))

(defun js3-back-offset-re (abs re)
  "Helper function for `js3-proper-indentation'."
  (goto-char abs)
  (js3-re-search-forward re nil t)
  (backward-char)
  (current-column))

(defmacro lazy-detect (elems-func fallback)
  `(let* (sibcol
          (sibabs (js3-node-abs-pos
                   (car (,elems-func node))))
          (lazy-mode
           (save-excursion
             (goto-char sibabs)
             (setq sibcol (current-column))
             (back-to-indentation)
             (= (point) sibabs))))
     (if lazy-mode
         (max 0 (- sibcol 2))
       ,fallback)))

(defun js3-special-case-offset (type)
  "Add an offset for certain special cases"
  (cond
   ((or (= type js3-CASE)
	(= type js3-LABEL))
    js3-label-indent-offset)
   (t 0)))

(defun js3-proper-indentation (parse-status)
  "Return the proper indentation for the current line."
  (save-excursion
    (back-to-indentation)
    (let ((node (js3-node-at-point)))
      (if (not node)
          0
        (let ((char (following-char))
              (abs (js3-node-abs-pos node))
              (type (js3-node-type node)))
          (cond

           ;;inside a multi-line comment
           ((nth 4 parse-status)
            (cond
             ((= (char-after) ?*)
              (goto-char abs)
              (1+ (current-column)))
             (t
              (goto-char abs)
              (if (not (looking-at "/\\*\\s-*\\S-"))
                  (current-column)
                (forward-char 2)
                (re-search-forward "\\S-" nil t)
                (if (= 0 (current-column))
		    0
		  (1- (current-column)))))))

           ;;inside a string - indent to 0 since you can't do that.
           ((nth 8 parse-status) 0)

           ((and (not js3-indent-dots)
                 (= char ?\.))
            (goto-char abs)
            (current-column))

           ;;semicolon-first in for loop def
           ((and (not js3-lazy-semicolons)
                 (= char ?\;)
                 (= type js3-FOR))
            (js3-back-offset-re abs "("))

           ;;comma-first and operator-first
           ((or
             (and (not js3-lazy-commas)
                  (= char ?\,))
             (and (not js3-lazy-operators)
                  (looking-at js3-indent-operator-first-re)
                  (or (not (= char ?\.))
                      (and js3-indent-dots
                           (not js3-lazy-dots)))))
            (cond
             ;;bare statements
             ((= type js3-VAR)
              (goto-char abs)
              (+ (current-column) 2))
             ((= type js3-RETURN)
              (goto-char abs)
              (+ (current-column) 5))

             ;;lists
             ((= type js3-ARRAYLIT)
              (lazy-detect js3-array-node-elems
                           (js3-back-offset-re abs "[[]")))
             ((= type js3-OBJECTLIT)
              (lazy-detect js3-object-node-elems
                           (js3-back-offset-re abs "{")))
             ((= type js3-FUNCTION)
              (lazy-detect js3-function-node-params
                           (js3-back-offset-re abs "(")))
             ((= type js3-CALL)
              (lazy-detect js3-call-node-args
                           (progn (goto-char (+ abs (js3-call-node-lp node)))
                                  (current-column))))

             ;;operators
             ((and (>= type 9)
                   (<= type 18)) ; binary operators
              (js3-back-offset abs 1))
             ((= type js3-COMMA)
              (js3-back-offset abs 1))
             ((= type js3-ASSIGN)
              (js3-back-offset abs 1))
             ((= type js3-HOOK)
              (js3-back-offset abs 1))

             ((= type js3-GETPROP) ; dot operator
              (goto-char abs)
              (if (js3-looking-at ".*\\..*")
                  (progn (js3-re-search-forward "\\." nil t)
                         (backward-char)
                         (current-column))
                (+ (current-column)
                   js3-expr-indent-offset js3-indent-level)))

             ;; multi-char operators
             ((and (>= type 19)
                   (<= type 24)) ; 2-char binary operators
              (js3-back-offset abs 2))
             ((or (= type js3-URSH)
                  (= type js3-SHEQ)
                  (= type js3-SHNE)) ;3-char binary operators
              (js3-back-offset abs 3))
             ((and (>= type 103)
                   (<= type 104)) ; logical and/or
              (js3-back-offset abs 2))

             ;;multi-char assignment
             ((and (>= type 90)
                   (<= type 97)) ; assignment 2-char
              (js3-back-offset abs 2))
             ((and (>= type 98)
                   (<= type 99)) ; assignment 3-char
              (js3-back-offset abs 3))
             ((= type 100)       ; assignment 4-char
              (js3-back-offset abs 4))

             (t
              (goto-char abs)
              (+ (current-column) js3-indent-level js3-expr-indent-offset))))

           ;;lazy semicolon-first in for loop def
           ((and js3-lazy-semicolons
                 (= char ?\;)
                 (= type js3-FOR))
            (js3-backward-sexp)
            (cond

             ((js3-looking-back (concat "^[ \t]*;.*"
                                        js3-skip-newlines-re))
              (js3-re-search-backward (concat "^[ \t]*;.*"
                                              js3-skip-newlines-re)
                                      (point-min) t)
              (back-to-indentation)
              (current-column))

             ((looking-back (concat "^[ \t]*[^ \t\n].*"
                                    js3-skip-newlines-re)
			    nil)
              (re-search-backward (concat "^[ \t]*[^ \t\n].*"
                                          js3-skip-newlines-re)
                                  (point-min) t)
              (back-to-indentation)
              (if (< (current-column) 2)
                  (current-column)
                (- (current-column) 2)))

             (t
              (+ js3-indent-level js3-expr-indent-offset))))


           ;;lazy comma-first
           ((and js3-lazy-commas
                 (= char ?\,))
            (js3-backward-sexp)
            (cond

             ((and js3-pretty-lazy-vars
                   (= js3-VAR type))
              (save-excursion
                (js3-re-search-backward "\\<var\\>" (point-min) t)
                (+ (current-column) 2)))

             ((js3-looking-back (concat "^[ \t]*,.*"
                                        js3-skip-newlines-re))
              (js3-re-search-backward (concat "^[ \t]*,.*"
                                              js3-skip-newlines-re)
                                      (point-min) t)
              (back-to-indentation)
              (current-column))

             ((looking-back (concat "^[ \t]*[^ \t\n].*"
                                    js3-skip-newlines-re)
			    nil)
              (re-search-backward (concat "^[ \t]*[^ \t\n].*"
                                          js3-skip-newlines-re)
                                  (point-min) t)
              (back-to-indentation)
              (if (< (current-column) 2)
                  (current-column)
                (- (current-column) 2)))

             (t
              (+ js3-indent-level js3-expr-indent-offset))))

           ;;lazy dot-first
           ((and js3-indent-dots
                 js3-lazy-dots
                 (= char ?\.))
            (save-excursion
              (js3-backward-sexp)
              (if (looking-back (concat "^[ \t]*[^ \t\n].*"
                                        js3-skip-newlines-re)
				nil)
                  (progn
                    (re-search-backward (concat "^[ \t]*[^ \t\n].*"
                                                js3-skip-newlines-re)
                                        (point-min) t)
                    (back-to-indentation)
                    (if (= char ?\.)
                        (current-column)
                      (+ (current-column) js3-indent-level)))
                (+ js3-indent-level js3-expr-indent-offset))))

           ;;lazy operator-first
           ((and js3-lazy-operators
                 (looking-at js3-indent-lazy-operator-re))
            (save-excursion
              (js3-backward-sexp)
              (if (looking-back (concat "^[ \t]*[^ \t\n].*"
                                        js3-skip-newlines-re)
				nil)
                  (progn
                    (re-search-backward (concat "^[ \t]*[^ \t\n].*"
                                                js3-skip-newlines-re)
                                        (point-min) t)
                    (back-to-indentation)
                    (if (or (looking-at js3-indent-lazy-operator-re)
                            (< (current-column) 2))
                        (current-column)
                      (- (current-column) 2)))
                (+ js3-indent-level js3-expr-indent-offset))))

           ;;var special case for non-comma-first continued var statements
           ((and js3-pretty-vars
                 (looking-at "[^]})]")
                 (not (looking-at "\\<var\\>"))
                 (js3-node-at-point)
                 (js3-node-parent (js3-node-at-point))
                 (js3-node-type (js3-node-parent (js3-node-at-point)))
                 (= js3-VAR
                    (js3-node-type (js3-node-parent (js3-node-at-point)))))
            (save-excursion
              (js3-re-search-backward "\\<var\\>" (point-min) t)
              (+ (current-column) js3-pretty-vars-spaces)))

           ;;inside a parenthetical grouping
           ((nth 1 parse-status)
            ;; A single closing paren/bracket should be indented at the
            ;; same level as the opening statement.
            (let ((same-indent-p (looking-at "[]})]"))
                  (continued-expr-p (js3-continued-expression-p))
                  (ctrl-statement-indentation (js3-ctrl-statement-indentation)))
              (+ (js3-special-case-offset type) (if (and (not same-indent-p) ctrl-statement-indentation)
                  ;;indent control statement body without braces, if applicable
                  ctrl-statement-indentation
                (progn
                  (goto-char (nth 1 parse-status)) ; go to the opening char
                  (if (or js3-boring-indentation
			  (looking-at "[({[]\\s-*\\(/[/*]\\|$\\)"))
                      (progn ; nothing following the opening paren/bracket
                        (skip-syntax-backward " ")
                        ;;skip arg list
                        (when (eq (char-before) ?\)) (backward-list))
                        (if (and (not js3-consistent-level-indent-inner-bracket)
                                 (js3-looking-back (concat
                                                    "\\<function\\>"
                                                    js3-skip-newlines-re)))
                            (progn
                              (js3-re-search-backward (concat
                                                       "\\<function\\>"
                                                       js3-skip-newlines-re))
                              (let* ((fnode (js3-node-at-point))
                                     (fnabs (js3-node-abs-pos fnode))
                                     (fparent (js3-node-parent
                                               (js3-node-at-point)))
                                     (fpabs (js3-node-abs-pos fparent))
                                     (fptype (js3-node-type fparent)))
                                (cond
                                 ((and (eq fptype js3-VAR)
                                       (eq js3-VAR (js3-node-type
                                                    (js3-node-parent fparent))))
                                  (let* ((vnode (js3-node-parent fparent))
                                         (vabs (js3-node-abs-pos vnode))
                                         (vkids (js3-var-decl-node-kids vnode)))
                                    (if (eq 1 (length vkids))
                                        (goto-char vabs)
                                      (goto-char fpabs))))

                                 ((or (eq fptype js3-VAR)
                                      (eq fptype js3-RETURN)
                                      (eq fptype js3-COLON)
                                      (and (<= fptype js3-ASSIGN_URSH)
                                           (>= fptype js3-ASSIGN)))
                                  (goto-char fpabs))

                                 ((looking-back
                                   "\\(\n\\|\\`\\)[ \t]*;?[ \t]*(?[ \t]*" nil)
                                  (back-to-indentation))

                                 ((eq fptype js3-CALL)
                                  (let* ((target (js3-call-node-target fparent))
                                         (ttype (js3-node-type target)))
                                    (if (eq ttype js3-GETPROP)
                                        (let* ((tright
                                                (js3-prop-get-node-right
                                                 target))
                                               (trabs
                                                (js3-node-abs-pos tright)))
                                          (if (<= (count-lines trabs fnabs) 1)
                                              (goto-char fpabs)
                                            (goto-char fnabs)))
                                      (if (<= (count-lines fpabs fnabs) 1)
                                          (goto-char fpabs)
                                        (goto-char fnabs)))))

                                 (t
                                  (goto-char fnabs)))))
                          (back-to-indentation))
                        (cond (same-indent-p
                               (current-column))
                              (continued-expr-p
                               (+ (current-column) (* js3-continued-expr-mult
						      js3-indent-level)
                                  js3-expr-indent-offset))
                              (t
                               (+ (current-column) js3-indent-level
                                  (case (char-after (nth 1 parse-status))
                                        (?\( js3-paren-indent-offset)
                                        (?\[ js3-square-indent-offset)
                                        (?\{ js3-curly-indent-offset))))))
                    ;; If there is something following the opening
                    ;; paren/bracket, everything else should be indented at
                    ;; the same level.
                    (unless same-indent-p
                      (forward-char)
                      (skip-chars-forward " \t"))
                    (current-column)))))))

           ;;indent control statement body without braces, if applicable
           ((js3-ctrl-statement-indentation))

           ;;c preprocessor - indent to 0
           ((eq (char-after) ?#) 0)

           ;;we're in a cpp macro - indent to 4 why not
           ((save-excursion (js3-beginning-of-macro)) 4)

           ;;in a continued expression not handled by earlier cases
           ((js3-continued-expression-p)
            (+ js3-indent-level js3-expr-indent-offset))

           ;;if none of these cases, then indent to 0
           (t 0)))))))

(defun js3-indent-line ()
  "Indent the current line as JavaScript."
  (interactive)
  (if js3-manual-indentation
      (if js3-indent-tabs-mode
	  (insert "\t")
	(insert-char ?\  js3-indent-level))
    (when js3-reparse-on-indent (js3-reparse))
    (save-restriction
      (widen)
      (let* ((parse-status
	      (save-excursion (syntax-ppss (point-at-bol))))
	     (offset (- (current-column) (current-indentation))))
	(indent-line-to (js3-proper-indentation parse-status))
	(when (> offset 0) (forward-char offset))))))

;;; js3-indent.el ends here
;;; js3-foot.el

(eval-when-compile
  (require 'cl))

(require 'imenu)
(require 'cc-cmds)  ; for `c-fill-paragraph'


;;;###autoload (add-to-list 'auto-mode-alist '("\\.js$" . js3-mode))

;;;###autoload
(defun js3-mode ()
  "Major mode for editing JavaScript code.\n\n\\{js3-mode-map}"
  (interactive)
  (js3-mode-check-compat)
  (kill-all-local-variables)
  (set-syntax-table js3-mode-syntax-table)
  (use-local-map js3-mode-map)
  (make-local-variable 'comment-start)
  (make-local-variable 'comment-end)
  (make-local-variable 'comment-start-skip)
  (setq major-mode 'js3-mode
        mode-name "JavaScript-IDE"
        comment-start "//"  ; used by comment-region; don't change it
        comment-end "")
  (setq local-abbrev-table js3-mode-abbrev-table)
  (set (make-local-variable 'max-lisp-eval-depth)
       (max max-lisp-eval-depth 3000))
  (set (make-local-variable 'indent-line-function) #'js3-indent-line)
  (set (make-local-variable 'indent-tabs-mode) js3-indent-tabs-mode)

  ;; I tried an "improvement" to `c-fill-paragraph' that worked out badly
  ;; on most platforms other than the one I originally wrote it on.
  ;; So it's back to `c-fill-paragraph'.
  (set (make-local-variable 'fill-paragraph-function) #'c-fill-paragraph)

  (set (make-local-variable 'next-error-function) #'js3-next-error)
  (set (make-local-variable 'beginning-of-defun-function) #'js3-beginning-of-defun)
  (set (make-local-variable 'end-of-defun-function) #'js3-end-of-defun)
  ;; We un-confuse `parse-partial-sexp' by setting syntax-table properties
  ;; for characters inside regexp literals.
  (set (make-local-variable 'parse-sexp-lookup-properties) t)
  ;; this is necessary to make `show-paren-function' work properly
  (set (make-local-variable 'parse-sexp-ignore-comments) t)
  ;; needed for M-x rgrep, among other things
  (put 'js3-mode 'find-tag-default-function #'js3-mode-find-tag)

  ;; some variables needed by cc-engine for paragraph-fill, etc.
  (setq c-comment-prefix-regexp js3-comment-prefix-regexp
        c-comment-start-regexp "/[*/]\\|\\s|"
        c-line-comment-starter "//"
        c-paragraph-start js3-paragraph-start
        c-paragraph-separate "$"
        comment-start-skip js3-comment-start-skip
        c-syntactic-ws-start js3-syntactic-ws-start
        c-syntactic-ws-end js3-syntactic-ws-end
        c-syntactic-eol js3-syntactic-eol)

  (if js3-emacs22
      (let ((c-buffer-is-cc-mode t))
        ;; Copied from `js-mode'.  Also see Bug#6071.
        (make-local-variable 'paragraph-start)
        (make-local-variable 'paragraph-separate)
        (make-local-variable 'paragraph-ignore-fill-prefix)
        (make-local-variable 'adaptive-fill-mode)
        (make-local-variable 'adaptive-fill-regexp)
        (c-setup-paragraph-variables)))

  (setq js3-default-externs
        (append js3-ecma-262-externs
                (if js3-include-browser-externs
                    js3-browser-externs)
                (if js3-include-gears-externs
                    js3-gears-externs)
                (if js3-include-rhino-externs
                    js3-rhino-externs)))

  ;; We do our own syntax highlighting based on the parse tree.
  ;; However, we want minor modes that add keywords to highlight properly
  ;; (examples:  doxymacs, column-marker).
  ;; To customize highlighted keywords, use `font-lock-add-keywords'.
  (setq font-lock-defaults '(nil t))

  ;; Experiment:  make reparse-delay longer for longer files.
  (if (plusp js3-dynamic-idle-timer-adjust)
      (setq js3-idle-timer-delay
            (* js3-idle-timer-delay
               (/ (point-max) js3-dynamic-idle-timer-adjust))))

  (add-hook 'change-major-mode-hook #'js3-mode-exit nil t)
  (add-hook 'after-change-functions #'js3-mode-edit nil t)
  (setq imenu-create-index-function #'js3-mode-create-imenu-index)
  (imenu-add-to-menubar (concat "IM-" mode-name))
  (when js3-mirror-mode
    (js3-enter-mirror-mode))
  (add-to-invisibility-spec '(js3-outline . t))
  (set (make-local-variable 'line-move-ignore-invisible) t)
  (set (make-local-variable 'forward-sexp-function) #'js3-mode-forward-sexp)

  (if (fboundp 'run-mode-hooks)
      (run-mode-hooks 'js3-mode-hook)
    (run-hooks 'js3-mode-hook))

  (setq js3-mode-functions-hidden nil
        js3-mode-comments-hidden nil
        js3-mode-buffer-dirty-p t
        js3-mode-parsing nil)
  (if (not (zerop (buffer-size)))
      (js3-reparse)))

(defun js3-mode-check-compat ()
  "Signal an error if we can't run with this version of Emacs."
  (if (and js3-mode-must-byte-compile
           (not (byte-code-function-p (symbol-function 'js3-mode))))
      (error "You must byte-compile js3-mode before using it."))
  (if (and (boundp 'running-xemacs) running-xemacs)
      (error "js3-mode is not compatible with XEmacs"))
  (unless (>= emacs-major-version 21)
    (error "js3-mode requires GNU Emacs version 21 or higher")))

(defun js3-mode-exit ()
  (interactive)
  (when js3-mode-node-overlay
    (delete-overlay js3-mode-node-overlay)
    (setq js3-mode-node-overlay nil))
  (js3-remove-overlays)
  (setq js3-mode-ast nil)
  (remove-hook 'change-major-mode-hook #'js3-mode-exit t)
  (remove-from-invisibility-spec '(js3-outline . t))
  (js3-mode-show-all)
  (js3-with-unmodifying-text-property-changes
   (js3-clear-face (point-min) (point-max))))

(defsubst js3-mode-reset-timer ()
  (if js3-mode-parse-timer
      (cancel-timer js3-mode-parse-timer))
  (setq js3-mode-parsing nil)
  (setq js3-mode-parse-timer
        (run-with-idle-timer js3-idle-timer-delay nil #'js3-reparse)))

(defun js3-mode-edit (beg end len)
  "Schedule a new parse after buffer is edited.
Also clears the `js3-magic' bit on autoinserted parens/brackets
if the edit occurred on a line different from the magic paren."
  (let* ((magic-pos (next-single-property-change (point-min) 'js3-magic))
         (line (if magic-pos (line-number-at-pos magic-pos))))
    (and line
         (or (/= (line-number-at-pos beg) line)
             (and (> 0 len)
                  (/= (line-number-at-pos end) line)))
         (js3-mode-mundanify-parens)))
  (setq js3-mode-buffer-dirty-p t)
  (js3-mode-hide-overlay)
  (js3-mode-reset-timer))

(defun js3-reparse (&optional force)
  "Re-parse current buffer after user finishes some data entry.
If we get any user input while parsing, including cursor motion,
we discard the parse and reschedule it.  If FORCE is nil, then the
buffer will only rebuild its `js3-mode-ast' if the buffer is dirty."
  (let (time
        interrupted-p
        (js3-compiler-strict-mode js3-mode-show-strict-warnings))
    (unless js3-mode-parsing
      (setq js3-mode-parsing t)
      (unwind-protect
          (when (or js3-mode-buffer-dirty-p force)
            (js3-remove-overlays)
            (js3-with-unmodifying-text-property-changes
             (setq js3-mode-buffer-dirty-p nil
                   js3-mode-fontifications nil
                   js3-mode-deferred-properties nil)
             (if js3-mode-verbose-parse-p
                 (message "parsing..."))
             (setq time
                   (js3-time
                    (setq interrupted-p
                          (catch 'interrupted
                            (setq js3-mode-ast (js3-parse))
                            ;; if parsing is interrupted, comments and regex
                            ;; literals stay ignored by `parse-partial-sexp'
                            (remove-text-properties (point-min) (point-max)
                                                    '(syntax-table))
                            (js3-mode-apply-deferred-properties)
                            (js3-mode-remove-suppressed-warnings)
                            (js3-mode-show-warnings)
                            (js3-mode-show-errors)
                            (js3-mode-highlight-magic-parens)
                            (if (>= js3-highlight-level 1)
                                (js3-highlight-jsdoc js3-mode-ast))
                            nil))))
             (if interrupted-p
                 (progn
                   ;; unfinished parse => try again
                   (setq js3-mode-buffer-dirty-p t)
                   (js3-mode-reset-timer))
               (if js3-mode-verbose-parse-p
                   (message "Parse time: %s" time)))))
        ;; finally
        (setq js3-mode-parsing nil)
        (unless interrupted-p
          (setq js3-mode-parse-timer nil))))))

(defun js3-mode-show-node ()
  "Debugging aid:  highlight selected AST node on mouse click."
  (interactive)
  (let ((node (js3-node-at-point))
        beg
        end)
    (when js3-mode-show-overlay
      (if (null node)
          (message "No node found at location %s" (point))
        (setq beg (js3-node-abs-pos node)
              end (+ beg (js3-node-len node)))
        (if js3-mode-node-overlay
            (move-overlay js3-mode-node-overlay beg end)
          (setq js3-mode-node-overlay (make-overlay beg end))
          (overlay-put js3-mode-node-overlay 'font-lock-face 'highlight))
        (js3-with-unmodifying-text-property-changes
         (put-text-property beg end 'point-left #'js3-mode-hide-overlay))
        (message "%s, parent: %s"
                 (js3-node-short-name node)
                 (if (js3-node-parent node)
                     (js3-node-short-name (js3-node-parent node))
                   "nil"))))))

(defun js3-mode-hide-overlay (&optional p1 p2)
  "Remove the debugging overlay when the point moves."
  (when js3-mode-node-overlay
    (let ((beg (overlay-start js3-mode-node-overlay))
          (end (overlay-end js3-mode-node-overlay)))
      ;; Sometimes we're called spuriously.
      (unless (and p2
                   (>= p2 beg)
                   (<= p2 end))
        (js3-with-unmodifying-text-property-changes
         (remove-text-properties beg end '(point-left nil)))
        (delete-overlay js3-mode-node-overlay)
        (setq js3-mode-node-overlay nil)))))

(defun js3-mode-reset ()
  "Debugging helper; resets everything."
  (interactive)
  (js3-mode-exit)
  (js3-mode))

(defsubst js3-mode-show-warn-or-err (e face)
  "Highlight a warning or error E with FACE.
E is a list of ((MSG-KEY MSG-ARG) BEG END)."
  (let* ((key (first e))
         (beg (second e))
         (end (+ beg (third e)))
         ;; Don't inadvertently go out of bounds.
         (beg (max (point-min) (min beg (point-max))))
         (end (max (point-min) (min end (point-max))))
         (js3-highlight-level 3)    ; so js3-set-face is sure to fire
         (ovl (make-overlay beg end)))
    (overlay-put ovl 'font-lock-face face)
    (overlay-put ovl 'js3-error t)
    (put-text-property beg end 'help-echo (js3-get-msg key))
    (put-text-property beg end 'point-entered #'js3-echo-error)))

(defun js3-remove-overlays ()
  "Remove overlays from buffer that have a `js3-error' property."
  (let ((beg (point-min))
        (end (point-max)))
    (save-excursion
      (dolist (o (overlays-in beg end))
        (when (overlay-get o 'js3-error)
          (delete-overlay o))))))

(defun js3-error-at-point (&optional pos)
  "Return non-nil if there's an error overlay at POS.
Defaults to point."
  (loop with pos = (or pos (point))
        for o in (overlays-at pos)
        thereis (overlay-get o 'js3-error)))

(defun js3-mode-apply-deferred-properties ()
  "Apply fontifications and other text properties recorded during parsing."
  (when (plusp js3-highlight-level)
    ;; We defer clearing faces as long as possible to eliminate flashing.
    (js3-clear-face (point-min) (point-max))
    ;; Have to reverse the recorded fontifications list so that errors
    ;; and warnings overwrite the normal fontifications.
    (dolist (f (nreverse js3-mode-fontifications))
      (put-text-property (first f) (second f) 'font-lock-face (third f)))
    (setq js3-mode-fontifications nil))
  (dolist (p js3-mode-deferred-properties)
    (apply #'put-text-property p))
  (setq js3-mode-deferred-properties nil))

(defun js3-mode-show-errors ()
  "Highlight syntax errors."
  (when js3-mode-show-parse-errors
    (dolist (e (js3-ast-root-errors js3-mode-ast))
      (js3-mode-show-warn-or-err e 'js3-error-face))))

(defun js3-mode-remove-suppressed-warnings ()
  "Take suppressed warnings out of the AST warnings list.
This ensures that the counts and `next-error' are correct."
  (setf (js3-ast-root-warnings js3-mode-ast)
        (js3-delete-if
         (lambda (e)
           (let ((key (caar e)))
             (or
              (and (not js3-strict-trailing-comma-warning)
                   (string-match "trailing\\.comma" key))
              (and (not js3-strict-cond-assign-warning)
                   (string= key "msg.equal.as.assign"))
              (and js3-missing-semi-one-line-override
                   (string= key "msg.missing.semi")
                   (let* ((beg (second e))
                          (node (js3-node-at-point beg))
                          (fn (js3-mode-find-parent-fn node))
                          (body (and fn (js3-function-node-body fn)))
                          (lc (and body (js3-node-abs-pos body)))
                          (rc (and lc (+ lc (js3-node-len body)))))
                     (and fn
                          (or (null body)
                              (save-excursion
                                (goto-char beg)
                                (and (js3-same-line lc)
                                     (js3-same-line rc))))))))))
         (js3-ast-root-warnings js3-mode-ast))))

(defun js3-mode-show-warnings ()
  "Highlight strict-mode warnings."
  (when js3-mode-show-strict-warnings
    (dolist (e (js3-ast-root-warnings js3-mode-ast))
      (js3-mode-show-warn-or-err e 'js3-warning-face))))

(defun js3-echo-error (old-point new-point)
  "Called by point-motion hooks."
  (let ((msg (get-text-property new-point 'help-echo)))
    (when (and (stringp msg)
               (not (active-minibuffer-window))
               (not (current-message)))
      (message msg))))

(defalias 'js3-echo-help #'js3-echo-error)

(defun js3-enter-key ()
  "Handle user pressing the Enter key."
  (interactive)
  (let ((parse-status (save-excursion
                        (parse-partial-sexp (point-min) (point)))))
    (cond
     ;; check if inside a string
     ((nth 3 parse-status)
      (if (nth 5 parse-status)
          (js3-mode-split-string-with-backslash)
        (js3-mode-split-string parse-status)))
     ;; check if inside a block comment
     ((nth 4 parse-status)
      (js3-mode-extend-comment))
     (t
      ;; should probably figure out what the mode-map says we should do
      (if (and js3-indent-on-enter-key
               (not (zerop (buffer-size))))
          (js3-indent-line))
      (delete-horizontal-space t)
      (insert "\n")
      (if js3-enter-indents-newline
          (js3-indent-line))))))

(defun js3-mode-split-string-with-backslash ()
  "Turn a newline after backslash in mid-string into backslash-newline-separated multiline string."
  (insert "\n")
  (js3-mode-force-backslash))

(defun js3-mode-force-backslash ()
  "Force backslash character after a line of non-terminated string."
  (let* ((parse-status
          (save-excursion
            (parse-partial-sexp (point-min) (line-end-position)))))
    (when (and
           (not (nth 5 parse-status))
           (nth 3 parse-status))
      (save-excursion
        (end-of-line)
        (insert "\\")))))

(defun js3-mode-split-string (parse-status)
  "Turn a newline in mid-string into a string concatenation."
  (let* ((col (current-column))
         (quote-char (nth 3 parse-status))
         (quote-string (string quote-char))
         (string-beg (nth 8 parse-status))
         (indent (save-match-data
                   (or
                    (save-excursion
                      (back-to-indentation)
                      (if (looking-at "\\+")
                          (current-column)))
                    (save-excursion
                      (goto-char string-beg)
                      (if (looking-back "\\+\\s-+" nil)
                          (goto-char (match-beginning 0)))
                      (current-column))))))
    (insert quote-char "\n")
    (indent-to indent)
    (insert "+ " quote-string)
    (when (eolp)
      (insert quote-string)
      (backward-char 1))))

(defun js3-mode-extend-comment ()
  "Indent the line and, when inside a comment block, add comment prefix."
  (let (star single col first-line needs-close)
    (save-excursion
      (back-to-indentation)
      (cond
       ((looking-at "\\*[^/]")
        (setq star t
              col (current-column)))
       ((looking-at "/\\*")
        (setq star t
              first-line t
              col (1+ (current-column))))
       ((looking-at "//")
        (setq single t
              col (current-column)))))
    ;; Heuristic for whether we need to close the comment:
    ;; if we've got a parse error here, assume it's an unterminated
    ;; comment.
    (setq needs-close
          (or
           (eq (get-text-property (1- (point)) 'point-entered)
               'js3-echo-error)
           ;; The heuristic above doesn't work well when we're
           ;; creating a comment and there's another one downstream,
           ;; as our parser thinks this one ends at the end of the
           ;; next one.  (You can have a /* inside a js block comment.)
           ;; So just close it if the next non-ws char isn't a *.
           (and first-line
                (eolp)
                (save-excursion
                  (skip-chars-forward " \t\r\n")
                  (not (eq (char-after) ?*))))))
    (insert "\n")
    (cond
     (star
      (indent-to col)
      (insert "* ")
      (if (and first-line needs-close)
          (save-excursion
            (insert "\n")
            (indent-to col)
            (insert "*/"))))
     ((and single
           (save-excursion
             (and (zerop (forward-line 1))
                  (looking-at "\\s-*//"))))
      (indent-to col)
      (insert "// "))
     (js3-enter-indents-newline
      (js3-indent-line)))))

(defun js3-fill-string (beg quote)
  "Line-wrap a single-line string into a multi-line string.
BEG is the string beginning, QUOTE is the quote char."
  (let* ((squote (string quote))
         (end (if (re-search-forward (concat "[^\\]" squote)
                                     (point-at-eol) t)
                  (1+ (match-beginning 0))
                (point-at-eol)))
         (tag (make-marker))
         (fill-column (- fill-column 4)))  ; make room
    (unwind-protect
        (progn
          (move-marker tag end)
          (fill-paragraph nil)
          (goto-char beg)
          (while (not (js3-same-line tag))
            (goto-char (point-at-eol))
            (insert squote)
            (when (zerop (forward-line 1))
              (back-to-indentation)
              (if (looking-at (concat squote "\\s-*$"))
                  (progn
                    (setq end (point-at-eol))
                    (forward-line -1)
                    (delete-region (point-at-eol) end))
                (insert "+ " squote)))))
      (move-marker tag nil))))

(defun js3-fill-comment (parse-status arg)
  "Fill-paragraph in a block comment."
  (let* ((beg (nth 8 parse-status))
         (end (save-excursion
                (goto-char beg)
                (re-search-forward "[^\\]\\*/" nil t)))
         indent
         end-marker)
    (when end
      (setq end-marker (make-marker))
      (move-marker end-marker end))
    (when (and end js3-mode-squeeze-spaces)
      (save-excursion
        (save-restriction
          (narrow-to-region beg end)
          (goto-char (point-min))
          (while (re-search-forward "[ \t][ \t]+" nil t)
            (replace-match " ")))))
    ;; `c-fill-paragraph' doesn't indent the continuation stars properly
    ;; if the comment isn't left-justified.  They align to the first star
    ;; on the first continuation line after the comment-open, so we make
    ;; sure the first continuation line has the proper indentation.
    (save-excursion
      (goto-char beg)
      (setq indent (1+ (current-column)))
      (goto-char (point-at-eol))
      (skip-chars-forward " \t\r\n")
      (indent-line-to indent)

      ;; Invoke `c-fill-paragraph' from the first continuation line,
      ;; since it provides better results.  Otherwise if you're on the
      ;; last line, it doesn't prefix with stars the way you'd expect.
      ;; TODO:  write our own fill function that works in Emacs 21
      (let ((fill-paragraph-function 'c-fill-paragraph))
        (c-fill-paragraph arg)))

    ;; last line is typically indented wrong, so fix it
    (when end-marker
      (save-excursion
        (goto-char end-marker)
        (js3-indent-line)))))

(defun js3-beginning-of-line ()
  "Toggles point between bol and first non-whitespace char in line.
Also moves past comment delimiters when inside comments."
  (interactive)
  (let (node beg)
    (cond
     ((bolp)
      (back-to-indentation))
     ((looking-at "//")
      (skip-chars-forward "/ \t"))
     ((and (eq (char-after) ?*)
           (setq node (js3-comment-at-point))
           (memq (js3-comment-node-format node) '(jsdoc block))
           (save-excursion
             (skip-chars-backward " \t")
             (bolp)))
      (skip-chars-forward "\* \t"))
     (t
      (goto-char (point-at-bol))))))

(defun js3-end-of-line ()
  "Toggles point between eol and last non-whitespace char in line."
  (interactive)
  (if (eolp)
      (skip-chars-backward " \t")
    (goto-char (point-at-eol))))

(defun js3-enter-mirror-mode()
  "Turns on mirror mode, where quotes, brackets etc are mirrored automatically
on insertion."
  (interactive)
  (define-key js3-mode-map (read-kbd-macro "{")  'js3-mode-match-curly)
  (define-key js3-mode-map (read-kbd-macro "}")  'js3-mode-magic-close-paren)
  (define-key js3-mode-map (read-kbd-macro "\"") 'js3-mode-match-double-quote)
  (define-key js3-mode-map (read-kbd-macro "'")  'js3-mode-match-single-quote)
  (define-key js3-mode-map (read-kbd-macro "(")  'js3-mode-match-paren)
  (define-key js3-mode-map (read-kbd-macro ")")  'js3-mode-magic-close-paren)
  (define-key js3-mode-map (read-kbd-macro "[")  'js3-mode-match-bracket)
  (define-key js3-mode-map (read-kbd-macro "]")  'js3-mode-magic-close-paren))

(defun js3-leave-mirror-mode()
  "Turns off mirror mode."
  (interactive)
  (dolist (key '("{" "\"" "'" "(" ")" "[" "]"))
    (define-key js3-mode-map (read-kbd-macro key) 'self-insert-command)))

(defsubst js3-mode-inside-string ()
  "Return non-nil if inside a string.
Actually returns the quote character that begins the string."
  (let ((parse-state (save-excursion
                       (parse-partial-sexp (point-min) (point)))))
    (nth 3 parse-state)))

(defsubst js3-mode-inside-comment-or-string ()
  "Return non-nil if inside a comment or string."
  (or
   (let ((comment-start
          (save-excursion
            (goto-char (point-at-bol))
            (if (re-search-forward "//" (point-at-eol) t)
                (match-beginning 0)))))
     (and comment-start
          (<= comment-start (point))))
   (let ((parse-state (save-excursion
                        (parse-partial-sexp (point-min) (point)))))
     (or (nth 3 parse-state)
         (nth 4 parse-state)))))

(defsubst js3-make-magic-delimiter (delim &optional pos)
  "Add `js3-magic' and `js3-magic-paren-face' to DELIM, a string.
Sets value of `js3-magic' text property to line number at POS."
  (propertize delim
              'js3-magic (line-number-at-pos pos)
              'font-lock-face 'js3-magic-paren-face))

(defun js3-mode-match-delimiter (open close)
  "Insert OPEN (a string) and possibly matching delimiter CLOSE.
The rule we use, which as far as we can tell is how Eclipse works,
is that we insert the match if we're not in a comment or string,
and the next non-whitespace character is either punctuation or
occurs on another line."
  (insert open)
  (when (and (looking-at "\\s-*\\([[:punct:]]\\|$\\)")
             (not (js3-mode-inside-comment-or-string)))
    (save-excursion
      (insert (js3-make-magic-delimiter close)))
    (when js3-auto-indent-p
      (js3-indent-line))))

(defun js3-mode-match-bracket ()
  "Insert matching bracket."
  (interactive)
  (js3-mode-match-delimiter "[" "]"))

(defun js3-mode-match-paren ()
  "Insert matching paren unless already inserted."
  (interactive)
  (js3-mode-match-delimiter "(" ")"))

(defun js3-mode-match-curly (arg)
  "Insert matching curly-brace.
With prefix arg, no formatting or indentation will occur -- the close-brace
is simply inserted directly at the point."
  (interactive "p")
  (let (try-pos)
    (cond
     (current-prefix-arg
      (js3-mode-match-delimiter "{" "}"))
     ((and js3-auto-insert-catch-block
           (setq try-pos (if (looking-back "\\s-*\\(try\\)\\s-*"
                                           (point-at-bol))
                             (match-beginning 1))))
      (js3-insert-catch-skel try-pos))
     (t
      ;; Otherwise try to do something smarter.
      (insert "{")
      (unless (or (not (looking-at "\\s-*$"))
                  (save-excursion
                    (skip-chars-forward " \t\r\n")
                    (and (looking-at "}")
                         (js3-error-at-point)))
                  (js3-mode-inside-comment-or-string))
        (undo-boundary)
        ;; absolutely mystifying bug:  when inserting the next "\n",
        ;; the buffer-undo-list is given two new entries:  the inserted range,
        ;; and the incorrect position of the point.  It's recorded incorrectly
        ;; as being before the opening "{", not after it.  But it's recorded
        ;; as the correct value if you're debugging `js3-mode-match-curly'
        ;; in edebug.  I have no idea why it's doing this, but incrementing
        ;; the inserted position fixes the problem, so that the undo takes us
        ;; back to just after the user-inserted "{".
        (insert "\n")
        (ignore-errors
         (incf (cadr buffer-undo-list)))
        (js3-indent-line)
        (save-excursion
          (insert "\n}")
          (js3-indent-line)))))))

(defun js3-insert-catch-skel (try-pos)
  "Complete a try/catch block after inserting a { following a try keyword.
Rationale is that a try always needs a catch or a finally, and the catch is
the more likely of the two.

TRY-POS is the buffer position of the try keyword.  The open-curly should
already have been inserted."
  (insert "{")
  (let ((try-col (save-excursion
                   (goto-char try-pos)
                   (current-column))))
    (insert "\n")
    (undo-boundary)
    (js3-indent-line) ;; indent the blank line where cursor will end up
    (save-excursion
      (insert "\n")
      (indent-to try-col)
      (insert "} catch (x) {\n\n")
      (indent-to try-col)
      (insert "}"))))

(defun js3-mode-highlight-magic-parens ()
  "Re-highlight magic parens after parsing nukes the 'face prop."
  (let ((beg (point-min))
        end)
    (while (setq beg (next-single-property-change beg 'js3-magic))
      (setq end (next-single-property-change (1+ beg) 'js3-magic))
      (if (get-text-property beg 'js3-magic)
          (js3-with-unmodifying-text-property-changes
           (put-text-property beg (or end (1+ beg))
                              'font-lock-face 'js3-magic-paren-face))))))

(defun js3-mode-mundanify-parens ()
  "Clear all magic parens and brackets."
  (let ((beg (point-min))
        end)
    (while (setq beg (next-single-property-change beg 'js3-magic))
      (setq end (next-single-property-change (1+ beg) 'js3-magic))
      (remove-text-properties beg (or end (1+ beg))
                              '(js3-magic face)))))

(defsubst js3-match-quote (quote-string)
  (let ((start-quote (js3-mode-inside-string)))
    (cond
     ;; inside a comment - don't do quote-matching, since we can't
     ;; reliably figure out if we're in a string inside the comment
     ((js3-comment-at-point)
      (insert quote-string))
     ((not start-quote)
      ;; not in string => insert matched quotes
      (insert quote-string)
      ;; exception:  if we're just before a word, don't double it.
      (unless (looking-at "[^ \t\r\n]")
        (save-excursion
          (insert quote-string))))
     ((looking-at quote-string)
      (if (looking-back "[^\\]\\\\" nil)
          (insert quote-string)
        (forward-char 1)))
     ((and js3-mode-escape-quotes
           (save-excursion
             (save-match-data
               (re-search-forward quote-string (point-at-eol) t))))
      ;; inside terminated string, escape quote (unless already escaped)
      (insert (if (looking-back "[^\\]\\\\" nil)
                  quote-string
                (concat "\\" quote-string))))
     (t
      (insert quote-string)))))        ; else terminate the string

(defun js3-mode-match-single-quote ()
  "Insert matching single-quote."
  (interactive)
  (let ((parse-status (parse-partial-sexp (point-min) (point))))
    ;; don't match inside comments, since apostrophe is more common
    (if (nth 4 parse-status)
        (insert "'")
      (js3-match-quote "'"))))

(defun js3-mode-match-double-quote ()
  "Insert matching double-quote."
  (interactive)
  (js3-match-quote "\""))

;; Eclipse works as follows:
;;  * type an open-paren and it auto-inserts close-paren
;;    - auto-inserted paren gets a green bracket
;;    - green bracket means typing close-paren there will skip it
;;  * if you insert any text on a different line, it turns off
(defun js3-mode-magic-close-paren ()
  "Skip over close-paren rather than inserting, where appropriate."
  (interactive)
  (let* ((here (point))
         (parse-status (parse-partial-sexp (point-min) here))
         (open-pos (nth 1 parse-status))
         (close last-input-event)
         (open (cond
                ((eq close ?\))
                 ?\()
                ((eq close ?\])
                 ?\[)
                ((eq close ?})
                 ?{)
                (t nil))))
    (if (and (eq (char-after) close)
             (eq open (char-after open-pos))
             (js3-same-line open-pos)
             (get-text-property here 'js3-magic))
        (progn
          (remove-text-properties here (1+ here) '(js3-magic face))
          (forward-char 1))
      (insert-char close 1))
    (blink-matching-open)))

(defun js3-mode-wait-for-parse (callback)
  "Invoke CALLBACK when parsing is finished.
If parsing is already finished, calls CALLBACK immediately."
  (if (not js3-mode-buffer-dirty-p)
      (funcall callback)
    (push callback js3-mode-pending-parse-callbacks)
    (add-hook 'js3-parse-finished-hook #'js3-mode-parse-finished)))

(defun js3-mode-parse-finished ()
  "Invoke callbacks in `js3-mode-pending-parse-callbacks'."
  ;; We can't let errors propagate up, since it prevents the
  ;; `js3-parse' method from completing normally and returning
  ;; the ast, which makes things mysteriously not work right.
  (unwind-protect
      (dolist (cb js3-mode-pending-parse-callbacks)
        (condition-case err
            (funcall cb)
          (error (message "%s" err))))
    (setq js3-mode-pending-parse-callbacks nil)))

(defun js3-mode-flag-region (from to flag)
  "Hide or show text from FROM to TO, according to FLAG.
If FLAG is nil then text is shown, while if FLAG is t the text is hidden.
Returns the created overlay if FLAG is non-nil."
  (remove-overlays from to 'invisible 'js3-outline)
  (when flag
    (let ((o (make-overlay from to)))
      (overlay-put o 'invisible 'js3-outline)
      (overlay-put o 'isearch-open-invisible
                   'js3-isearch-open-invisible)
      o)))

;; Function to be set as an outline-isearch-open-invisible' property
;; to the overlay that makes the outline invisible (see
;; `js3-mode-flag-region').
(defun js3-isearch-open-invisible (overlay)
  ;; We rely on the fact that isearch places point on the matched text.
  (js3-mode-show-element))

(defun js3-mode-invisible-overlay-bounds (&optional pos)
  "Return cons cell of bounds of folding overlay at POS.
Returns nil if not found."
  (let ((overlays (overlays-at (or pos (point))))
        o)
    (while (and overlays
                (not o))
      (if (overlay-get (car overlays) 'invisible)
          (setq o (car overlays))
        (setq overlays (cdr overlays))))
    (if o
        (cons (overlay-start o) (overlay-end o)))))

(defun js3-mode-function-at-point (&optional pos)
  "Return the innermost function node enclosing current point.
Returns nil if point is not in a function."
  (let ((node (js3-node-at-point pos)))
    (while (and node (not (js3-function-node-p node)))
      (setq node (js3-node-parent node)))
    (if (js3-function-node-p node)
        node)))

(defun js3-mode-toggle-element ()
  "Hide or show the foldable element at the point."
  (interactive)
  (let (comment fn pos)
    (save-excursion
      (save-match-data
        (cond
         ;; /* ... */ comment?
         ((js3-block-comment-p (setq comment (js3-comment-at-point)))
          (if (js3-mode-invisible-overlay-bounds
               (setq pos (+ 3 (js3-node-abs-pos comment))))
              (progn
                (goto-char pos)
                (js3-mode-show-element))
            (js3-mode-hide-element)))

         ;; //-comment?
         ((save-excursion
            (back-to-indentation)
            (looking-at js3-mode-//-comment-re))
          (js3-mode-toggle-//-comment))

         ;; function?
         ((setq fn (js3-mode-function-at-point))
          (setq pos (and (js3-function-node-body fn)
                         (js3-node-abs-pos (js3-function-node-body fn))))
          (goto-char (1+ pos))
          (if (js3-mode-invisible-overlay-bounds)
              (js3-mode-show-element)
            (js3-mode-hide-element)))
         (t
          (message "Nothing at point to hide or show")))))))

(defun js3-mode-hide-element ()
  "Fold/hide contents of a block, showing ellipses.
Show the hidden text with \\[js3-mode-show-element]."
  (interactive)
  (if js3-mode-buffer-dirty-p
      (js3-mode-wait-for-parse #'js3-mode-hide-element))
  (let (node body beg end)
    (cond
     ((js3-mode-invisible-overlay-bounds)
      (message "already hidden"))
     (t
      (setq node (js3-node-at-point))
      (cond
       ((js3-block-comment-p node)
        (js3-mode-hide-comment node))
       (t
        (while (and node (not (js3-function-node-p node)))
          (setq node (js3-node-parent node)))
        (if (and node
                 (setq body (js3-function-node-body node)))
            (progn
              (setq beg (js3-node-abs-pos body)
                    end (+ beg (js3-node-len body)))
              (js3-mode-flag-region (1+ beg) (1- end) 'hide))
          (message "No collapsable element found at point"))))))))

(defun js3-mode-show-element ()
  "Show the hidden element at current point."
  (interactive)
  (let ((bounds (js3-mode-invisible-overlay-bounds)))
    (if bounds
        (js3-mode-flag-region (car bounds) (cdr bounds) nil)
      (message "Nothing to un-hide"))))

(defun js3-mode-show-all ()
  "Show all of the text in the buffer."
  (interactive)
  (js3-mode-flag-region (point-min) (point-max) nil))

(defun js3-mode-toggle-hide-functions ()
  (interactive)
  (if js3-mode-functions-hidden
      (js3-mode-show-functions)
    (js3-mode-hide-functions)))

(defun js3-mode-hide-functions ()
  "Hides all non-nested function bodies in the buffer.
Use \\[js3-mode-show-all] to reveal them, or \\[js3-mode-show-element]
to open an individual entry."
  (interactive)
  (if js3-mode-buffer-dirty-p
      (js3-mode-wait-for-parse #'js3-mode-hide-functions))
  (if (null js3-mode-ast)
      (message "Oops - parsing failed")
    (setq js3-mode-functions-hidden t)
    (js3-visit-ast js3-mode-ast #'js3-mode-function-hider)))

(defun js3-mode-function-hider (n endp)
  (when (not endp)
    (let ((tt (js3-node-type n))
          body beg end)
      (cond
       ((and (= tt js3-FUNCTION)
             (setq body (js3-function-node-body n)))
        (setq beg (js3-node-abs-pos body)
              end (+ beg (js3-node-len body)))
        (js3-mode-flag-region (1+ beg) (1- end) 'hide)
        nil)   ; don't process children of function
       (t
        t))))) ; keep processing other AST nodes

(defun js3-mode-show-functions ()
  "Un-hide any folded function bodies in the buffer."
  (interactive)
  (setq js3-mode-functions-hidden nil)
  (save-excursion
    (goto-char (point-min))
    (while (/= (goto-char (next-overlay-change (point)))
               (point-max))
      (dolist (o (overlays-at (point)))
        (when (and (overlay-get o 'invisible)
                   (not (overlay-get o 'comment)))
          (js3-mode-flag-region (overlay-start o) (overlay-end o) nil))))))

(defun js3-mode-hide-comment (n)
  (let* ((head (if (eq (js3-comment-node-format n) 'jsdoc)
                   3                    ; /**
                 2))                    ; /*
         (beg (+ (js3-node-abs-pos n) head))
         (end (- (+ beg (js3-node-len n)) head 2))
         (o (js3-mode-flag-region beg end 'hide)))
    (overlay-put o 'comment t)))

(defun js3-mode-toggle-hide-comments ()
  "Folds all block comments in the buffer.
Use \\[js3-mode-show-all] to reveal them, or \\[js3-mode-show-element]
to open an individual entry."
  (interactive)
  (if js3-mode-comments-hidden
      (js3-mode-show-comments)
    (js3-mode-hide-comments)))

(defun js3-mode-hide-comments ()
  (interactive)
  (if js3-mode-buffer-dirty-p
      (js3-mode-wait-for-parse #'js3-mode-hide-comments))
  (if (null js3-mode-ast)
      (message "Oops - parsing failed")
    (setq js3-mode-comments-hidden t)
    (dolist (n (js3-ast-root-comments js3-mode-ast))
      (let ((format (js3-comment-node-format n)))
        (when (js3-block-comment-p n)
          (js3-mode-hide-comment n))))
    (js3-mode-hide-//-comments)))

(defsubst js3-mode-extend-//-comment (direction)
  "Find start or end of a block of similar //-comment lines.
DIRECTION is -1 to look back, 1 to look forward.
INDENT is the indentation level to match.
Returns the end-of-line position of the furthest adjacent
//-comment line with the same indentation as the current line.
If there is no such matching line, returns current end of line."
  (let ((pos (point-at-eol))
        (indent (current-indentation)))
    (save-excursion
      (save-match-data
        (while (and (zerop (forward-line direction))
                    (looking-at js3-mode-//-comment-re)
                    (eq indent (length (match-string 1))))
          (setq pos (point-at-eol)))
        pos))))

(defun js3-mode-hide-//-comments ()
  "Fold adjacent 1-line comments, showing only snippet of first one."
  (let (beg end)
    (save-excursion
      (save-match-data
        (goto-char (point-min))
        (while (re-search-forward js3-mode-//-comment-re nil t)
          (setq beg (point)
                end (js3-mode-extend-//-comment 1))
          (unless (eq beg end)
            (overlay-put (js3-mode-flag-region beg end 'hide)
                         'comment t))
          (goto-char end)
          (forward-char 1))))))

(defun js3-mode-toggle-//-comment ()
  "Fold or un-fold any multi-line //-comment at point.
Caller should have determined that this line starts with a //-comment."
  (let* ((beg (point-at-eol))
         (end beg))
    (save-excursion
      (goto-char end)
      (if (js3-mode-invisible-overlay-bounds)
          (js3-mode-show-element)
        ;; else hide the comment
        (setq beg (js3-mode-extend-//-comment -1)
              end (js3-mode-extend-//-comment 1))
        (unless (eq beg end)
          (overlay-put (js3-mode-flag-region beg end 'hide)
                       'comment t))))))

(defun js3-mode-show-comments ()
  "Un-hide any hidden comments, leaving other hidden elements alone."
  (interactive)
  (setq js3-mode-comments-hidden nil)
  (save-excursion
    (goto-char (point-min))
    (while (/= (goto-char (next-overlay-change (point)))
               (point-max))
      (dolist (o (overlays-at (point)))
        (when (overlay-get o 'comment)
          (js3-mode-flag-region (overlay-start o) (overlay-end o) nil))))))

(defun js3-mode-display-warnings-and-errors ()
  "Turn on display of warnings and errors."
  (interactive)
  (setq js3-mode-show-parse-errors t
        js3-mode-show-strict-warnings t)
  (js3-reparse 'force))

(defun js3-mode-hide-warnings-and-errors ()
  "Turn off display of warnings and errors."
  (interactive)
  (setq js3-mode-show-parse-errors nil
        js3-mode-show-strict-warnings nil)
  (js3-reparse 'force))

(defun js3-mode-toggle-warnings-and-errors ()
  "Toggle the display of warnings and errors.
Some users don't like having warnings/errors reported while they type."
  (interactive)
  (setq js3-mode-show-parse-errors (not js3-mode-show-parse-errors)
        js3-mode-show-strict-warnings (not js3-mode-show-strict-warnings))
  (if (called-interactively-p 'interactive)
      (message "warnings and errors %s"
               (if js3-mode-show-parse-errors
                   "enabled"
                 "disabled")))
  (js3-reparse 'force))

(defun js3-mode-customize ()
  (interactive)
  (customize-group 'js3-mode))

(defun js3-mode-forward-sexp (&optional arg)
  "Move forward across one statement or balanced expression.
With ARG, do it that many times.  Negative arg -N means
move backward across N balanced expressions."
  (interactive "p")
  (setq arg (or arg 1))
  (if js3-mode-buffer-dirty-p
      (js3-mode-wait-for-parse #'js3-mode-forward-sexp))
  (let (node end (start (point)))
    (cond
     ;; backward-sexp
     ;; could probably make this "better" for some cases:
     ;;  - if in statement block (e.g. function body), go to parent
     ;;  - infix exprs like (foo in bar) - maybe go to beginning
     ;;    of infix expr if in the right-side expression?
     ((and arg (minusp arg))
      (dotimes (i (- arg))
        (js3-backward-sws)
        (forward-char -1)  ; enter the node we backed up to
        (setq node (js3-node-at-point (point) t))
        (goto-char (if node
                       (js3-node-abs-pos node)
                     (point-min)))))
     (t
      ;; forward-sexp
      (js3-forward-sws)
      (dotimes (i arg)
        (js3-forward-sws)
        (setq node (js3-node-at-point (point) t)
              end (if node (+ (js3-node-abs-pos node)
                              (js3-node-len node))))
        (goto-char (or end (point-max))))))))

(defun js3-next-error (&optional arg reset)
  "Move to next parse error.
Typically invoked via \\[next-error].
ARG is the number of errors, forward or backward, to move.
RESET means start over from the beginning."
  (interactive "p")
  (if (or (null js3-mode-ast)
          (and (null (js3-ast-root-errors js3-mode-ast))
               (null (js3-ast-root-warnings js3-mode-ast))))
      (message "No errors")
    (when reset
      (goto-char (point-min)))
    (let* ((errs (copy-sequence
                  (append (js3-ast-root-errors js3-mode-ast)
                          (js3-ast-root-warnings js3-mode-ast))))
           (continue t)
           (start (point))
           (count (or arg 1))
           (backward (minusp count))
           (sorter (if backward '> '<))
           (stopper (if backward '< '>))
           (count (abs count))
           all-errs
           err)
      ;; sort by start position
      (setq errs (sort errs (lambda (e1 e2)
                              (funcall sorter (second e1) (second e2))))
            all-errs errs)
      ;; find nth error with pos > start
      (while (and errs continue)
        (when (funcall stopper (cadar errs) start)
          (setq err (car errs))
          (if (zerop (decf count))
              (setq continue nil)))
        (setq errs (cdr errs)))
      (if err
          (goto-char (second err))
        ;; wrap around to first error
        (goto-char (second (car all-errs)))
        ;; if we were already on it, echo msg again
        (if (= (point) start)
            (js3-echo-error (point) (point)))))))

(defun js3-down-mouse-3 ()
  "Make right-click move the point to the click location.
This makes right-click context menu operations a bit more intuitive.
The point will not move if the region is active, however, to avoid
destroying the region selection."
  (interactive)
  (when (and js3-move-point-on-right-click
             (not mark-active))
    (let ((e last-input-event))
      (ignore-errors
       (goto-char (cadadr e))))))

(defun js3-mode-create-imenu-index ()
  "Return an alist for `imenu--index-alist'."
  ;; This is built up in `js3-parse-record-imenu' during parsing.
  (when js3-mode-ast
    ;; if we have an ast but no recorder, they're requesting a rescan
    (unless js3-imenu-recorder
      (js3-reparse 'force))
    (prog1
        (js3-build-imenu-index)
      (setq js3-imenu-recorder nil
            js3-imenu-function-map nil))))

(defun js3-mode-find-tag ()
  "Replacement for `find-tag-default'.
`find-tag-default' returns a ridiculous answer inside comments."
  (let (beg end)
    (js3-with-underscore-as-word-syntax
     (save-excursion
       (if (and (not (looking-at "[A-Za-z0-9_$]"))
                (looking-back "[A-Za-z0-9_$]" nil))
           (setq beg (progn (forward-word -1) (point))
                 end (progn (forward-word 1) (point)))
         (setq beg (progn (forward-word 1) (point))
               end (progn (forward-word -1) (point))))
       (replace-regexp-in-string
        "[\"']" ""
        (buffer-substring-no-properties beg end))))))

(defun js3-mode-forward-sibling ()
  "Move to the end of the sibling following point in parent.
Returns non-nil if successful, or nil if there was no following sibling."
  (let* ((node (js3-node-at-point))
         (parent (js3-mode-find-enclosing-fn node))
         sib)
    (when (setq sib (js3-node-find-child-after (point) parent))
      (goto-char (+ (js3-node-abs-pos sib)
                    (js3-node-len sib))))))

(defun js3-mode-backward-sibling ()
  "Move to the beginning of the sibling node preceding point in parent.
Parent is defined as the enclosing script or function."
  (let* ((node (js3-node-at-point))
         (parent (js3-mode-find-enclosing-fn node))
         sib)
    (when (setq sib (js3-node-find-child-before (point) parent))
      (goto-char (js3-node-abs-pos sib)))))

(defun js3-beginning-of-defun ()
  "Go to line on which current function starts, and return non-nil.
If we're not in a function, go to beginning of previous script-level element."
  (interactive)
  (let ((parent (js3-node-parent-script-or-fn (js3-node-at-point)))
        pos sib)
    (cond
     ((and (js3-function-node-p parent)
           (not (eq (point) (setq pos (js3-node-abs-pos parent)))))
      (goto-char pos))
     (t
      (js3-mode-backward-sibling)))))

(defun js3-end-of-defun ()
  "Go to the char after the last position of the current function.
If we're not in a function, skips over the next script-level element."
  (interactive)
  (let ((parent (js3-node-parent-script-or-fn (js3-node-at-point))))
    (if (not (js3-function-node-p parent))
        ;; punt:  skip over next script-level element beyond point
        (js3-mode-forward-sibling)
      (goto-char (+ 1 (+ (js3-node-abs-pos parent)
                         (js3-node-len parent)))))))

(defun js3-mark-defun (&optional allow-extend)
  "Put mark at end of this function, point at beginning.
The function marked is the one that contains point.

Interactively, if this command is repeated,
or (in Transient Mark mode) if the mark is active,
it marks the next defun after the ones already marked."
  (interactive "p")
  (let (extended)
    (when (and allow-extend
               (or (and (eq last-command this-command) (mark t))
                   (and transient-mark-mode mark-active)))
      (let ((sib (save-excursion
                   (goto-char (mark))
                   (if (js3-mode-forward-sibling)
                       (point))))
            node)
        (if sib
            (progn
              (set-mark sib)
              (setq extended t))
          ;; no more siblings - try extending to enclosing node
          (goto-char (mark t)))))
    (when (not extended)
      (let ((node (js3-node-at-point (point) t)) ; skip comments
            ast fn stmt parent beg end)
        (when (js3-ast-root-p node)
          (setq ast node
                node (or (js3-node-find-child-after (point) node)
                         (js3-node-find-child-before (point) node))))
        ;; only mark whole buffer if we can't find any children
        (if (null node)
            (setq node ast))
        (if (js3-function-node-p node)
            (setq parent node)
          (setq fn (js3-mode-find-enclosing-fn node)
                stmt (if (or (null fn)
                             (js3-ast-root-p fn))
                         (js3-mode-find-first-stmt node))
                parent (or stmt fn)))
        (setq beg (js3-node-abs-pos parent)
              end (+ beg (js3-node-len parent)))
        (push-mark beg)
        (goto-char end)
        (exchange-point-and-mark)))))

(defun js3-narrow-to-defun ()
  "Narrow to the function enclosing point."
  (interactive)
  (let* ((node (js3-node-at-point (point) t))  ; skip comments
         (fn (if (js3-script-node-p node)
                 node
               (js3-mode-find-enclosing-fn node)))
         (beg (js3-node-abs-pos fn)))
    (unless (js3-ast-root-p fn)
      (narrow-to-region beg (+ beg (js3-node-len fn))))))

(defun js3-add-to-globals ()
  (interactive)
  (let ((var (word-at-point)))
    (when (not (member var js3-declared-globals))
      (save-excursion
        (goto-char 0)
        (when (not (looking-at "^/\\*\\s-*globals? "))
          (newline 1)
          (forward-line -1)
          (insert "/*global*/")
          (goto-char 0))
        (if (not (re-search-forward "[*]/" nil t))
            (message "Invalid global declaration")
          (delete-char -2)
          (when (not (looking-back " " nil))
            (insert " "))
          (insert (concat var " */")))))))

(defalias 'js3r 'js3-mode-reset)

(provide 'js3)
(provide 'js3-mode)

;;; js3-foot.el ends here

;;; js3-mode.el ends here
