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
