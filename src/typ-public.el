;;; -*- lexical-binding: t -*-

(eval-when-compile
  (defmacro typ--combine-parametric (prim t1 t2)
    `(cons ,prim (typ-combine (cdr ,t1)
                              (cdr ,t2))))
  (defmacro typ--combine-bool-vector (prim t1)
    `(cons ,prim (typ-combine (cdr ,t1) :boolean)))
  (defmacro typ--combine-string (prim t1)
    `(cons ,prim (typ-combine (cdr ,t1) :integer)))
  )

(defun typ-annotate (fn type)
  "Set FN function return value type to TYPE.
Only applicable for functions that return specific type
in all cases, with any arguments.
Used in `typ-infer-call' to discover FN return type."
  (unless (symbolp fn)
    (error "FN must be a symbol, %S (%s) given" fn (type-of fn)))
  (unless (symbolp type)
    (error "TYPE must be a symbol, %S (%s) given" type (type-of type)))
  (puthash fn type typ--funcs-db))

(defun typ-annotate-mixed (fn handler)
  "Register FN function type inference callback HANDLER.
When `typ-infer-call' is called for list that head is `eq'
to FN, HANDLER is called with that list `cdr'.
In other words, HANDLER is called with FN invocation arguments.
HANDLER must return a type based on the input arguments.

If it is impossible to give precise type information,
handler *must* return nil."
  (unless (symbolp fn)
    (error "FN must be a symbol, %S (%s) given" fn (type-of fn)))
  (unless (functionp handler)
    (error "HANDLER must be a function, %S (%s) given" handler (type-of handler)))
  (puthash fn handler typ--funcs-db))

(defun typ-default-annotations-loaded-p ()
  "Return non-nil if default annotations are loaded."
  (not (not (gethash '+ typ--funcs-db))))

(defun typ-default-annotations-load ()
  "Ensure that type information for builtin functions is set.
When `typ-default-annotations-loaded-p' returns non-nil, does nothing."
  (unless (typ-default-annotations-loaded-p)
    (typ--default-annotations-load)))

(defsubst typ-tag (type)
  "Return tag (keyword) for TYPE."
  (or (car-safe type)
      type))

(defun typ-elt (type)
  "Return TYPE element type if it is sequence (nil otherwise)."
  (pcase (typ-tag type)
    (`:string :integer)
    (`:bool-vector :boolean)
    (_ (cdr-safe type))))

;; Abstract type predicates.

(defsubst typ-number? (type)
  "Return non-nil for TYPE that implements `:number'."
  (memq type '(:integer :float :number)))

(defsubst typ-sequence? (type)
  "Return non-nil for TYPE that implements `:sequence'."
  (memq (typ-tag type) '(:list :string :vector :array :sequence)))

(defsubst typ-array? (type)
  "Return non-nil for TYPE that implements `:array'."
  (memq (typ-tag type) '(:string :vector :array)))

;; Parametric type predicates.

(defsubst typ-list? (type)
  "Return true for TYPE which is (:list . T)."
  (eq :list (car-safe type)))

(defsubst typ-vector? (type)
  "Return true for TYPE which is (:vector . T)."
  (eq :vector (car-safe type)))

;; Other predicates.

(defsubst typ-noreturn? (fn)
  "Return non-nil if FN is marked with `noreturn'."
  (memq fn typ--noreturn-funcs))

;; Type inference.

(defun typ-combine (t1 t2)
  (if (equal t1 t2)
      t1
    (pcase (typ-tag t1)
      (`:number
       (if (memq t2 '(:integer :float))
           :number
         nil))
      (`:integer
       (if (memq t2 '(:float :number))
           :number
         nil))
      (`:float
       (if (memq t2 '(:integer :number))
           :number
         nil))
      (`:sequence
       (pcase (typ-tag t2)
         (`:sequence (typ--combine-parametric :sequence t1 t2))
         (`:list (typ--combine-parametric :sequence t1 t2))
         (`:array (typ--combine-parametric :sequence t1 t2))
         (`:bool-vector (typ--combine-bool-vector :sequence t1))
         (`:string (typ--combine-string :sequence t1))
         (`:vector (typ--combine-parametric :sequence t1 t2))
         (_ nil)))
      (`:list
       (pcase (typ-tag t2)
         (`:sequence (typ--combine-parametric :sequence t1 t2))
         (`:list (typ--combine-parametric :list t1 t2))
         (`:array (typ--combine-parametric :sequence t1 t2))
         (`:bool-vector (typ--combine-bool-vector :sequence t1))
         (`:string (typ--combine-string :sequence t1))
         (`:vector (typ--combine-parametric :sequence t1 t2))
         (_ nil)))
      (`:array
       (pcase (typ-tag t2)
         (`:sequence (typ--combine-parametric :sequence t1 t2))
         (`:list (typ--combine-parametric :sequence t1 t2))
         (`:array (typ--combine-parametric :array t1 t2))
         (`:bool-vector (typ--combine-bool-vector :array t1))
         (`:string (typ--combine-string :array t1))
         (`:vector (typ--combine-parametric :array t1 t2))
         (_ nil)))
      (`:bool-vector
       (pcase (typ-tag t2)
         (`:sequence (typ--combine-bool-vector :sequence t2))
         (`:list (typ--combine-bool-vector :sequence t2))
         (`:array (typ--combine-bool-vector :array t2))
         (`:string typ--harray)
         (`:vector (typ--combine-bool-vector :array t2))
         (_ nil)))
      (`:string
       (pcase (typ-tag t2)
         (`:sequence (typ--combine-string :sequence t2))
         (`:list (typ--combine-string :sequence t2))
         (`:array (typ--combine-string :array t2))
         (`:bool-vector typ--harray)
         (`:vector (typ--combine-string :array t2))
         (_ nil)))
      (`:vector
       (pcase (typ-tag t2)
         (`:sequence (typ--combine-parametric :sequence t1 t2))
         (`:list (typ--combine-parametric :sequence t1 t2))
         (`:array (typ--combine-parametric :array t1 t2))
         (`:bool-vector (typ--combine-bool-vector :array t1))
         (`:string (typ--combine-string :array t1))
         (`:vector (typ--combine-parametric :vector t1 t2))
         (_ nil)))
      (_ nil))))

(defsubst typ-infer-elt (expr &optional quoted)
  "If EXPR is of any sequence types, returns it's element type."
  (typ-elt (typ-infer expr quoted)))

(defun typ-infer (expr &optional quoted)
  "Return result type of EXPR evaluation or nil, if inference fail.
When QUOTED is non-nil, lists handled with `typ-infer-list',
otherwise `typ-infer-call' is used."
  (cond ((listp expr)
         (if quoted
             (typ-infer-list expr)
           (typ-infer-call expr)))
        ((numberp expr)
         (if (integerp expr)
             :integer
           :float))
        ((arrayp expr)
         (if (stringp expr)
             :string
           (typ-infer-vector expr)))
        ((eq t expr) :boolean)
        ((symbolp expr)
         (if (or quoted
                 (keywordp expr))
             :symbol
           nil))
        ((hash-table-p expr) :hash-table)
        (t nil)))

(defun typ-infer-call (call-expr)
  "Return result type of CALL-EXPR invocation or nil, if inference fail.
Non-quoted context implied."
  (let* ((fn (car call-expr))
         (info (gethash fn typ--funcs-db)))
    (cond ((keywordp (typ-tag info)) info)
          (info (let ((args (cdr call-expr)))
                  (funcall info args)))
          (t nil))))

(defun typ-infer-list (xs)
  "Return XS list type or nil, if inference fail.
Quoted context implied."
  (if xs
      (let ((type (typ-infer (pop xs) t)))
        (while (and type
                    xs)
          (setq type (typ-combine type (typ-infer (pop xs) t))))
        (if type
            (cons :list type)
          typ--hlist))
    :nil))

(defun typ-infer-vector (xs)
  "Return XS vector type or nil, if inference fail.
Quoted context implied."
  (if (> (length xs) 0)
      (let ((i 1)
            (xs-count (length xs))
            (type (typ-infer (aref xs 0) t)))
        (while (and type
                    (< i xs-count))
          (setq type (typ-combine type (typ-infer (aref xs i) t))
                i (1+ i)))
        (if type
            (cons :vector type)
          typ--hvector))
    typ--hvector))

;; Type inference + predicate.

(defsubst typ-infer-integer? (expr &optional quoted)
  "Return non-nil if (typ-infer EXPR QUOTED) returned `:integer'."
  (eq :integer (typ-infer expr quoted)))

(defsubst typ-infer-float? (expr &optional quoted)
  "Return non-nil if (typ-infer EXPR QUOTED) returned `:float'."
  (eq :float (typ-infer expr quoted)))

(defsubst typ-infer-string? (expr &optional quoted)
  "Return non-nil if (typ-infer EXPR QUOTED) returned `:string'."
  (eq :string (typ-infer expr quoted)))

(defsubst typ-infer-hash-table? (expr &optional quoted)
  "Return non-nil if (typ-infer EXPR QUOTED) returned `:hash-table'."
  (eq :hash-table (typ-infer expr quoted)))

(defsubst typ-infer-symbol? (expr &optional quoted)
  "Return non-nil if (typ-infer EXPR QUOTED) returned `:symbol'."
  (eq :symbol (typ-infer expr quoted)))

(defsubst typ-infer-boolean? (expr &optional quoted)
  "Return non-nil if (typ-infer EXPR QUOTED) returned `:boolean'."
  (eq :boolean (typ-infer expr quoted)))

(defsubst typ-infer-number? (expr &optional quoted)
  "Return non-nil if (typ-infer EXPR QUOTED) returned `:number' or any type that implements it."
  (typ-number? (typ-infer expr quoted)))

(defsubst typ-infer-sequence? (expr &optional quoted)
  "Return non-nil if (typ-infer EXPR QUOTED) returned `:sequence' or any type that implements it."
  (typ-sequence? (typ-infer expr quoted)))

(defsubst typ-infer-array? (expr &optional quoted)
  "Return non-nil if (typ-infer EXPR QUOTED) returned `:array' or any type that implements it."
  (typ-array? (typ-infer expr quoted)))
