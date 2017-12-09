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
