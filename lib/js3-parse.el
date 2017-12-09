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
