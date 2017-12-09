;;; -*- lexical-binding: t -*-

(defvar typ--funcs-db (make-hash-table :test 'eq)
  "Maps function name (symbol) to it's return value type.

There are two possible value kinds:
  - callable objects (lambdas, closures, ...)
  - type itself (any one of):
    - simple type
    - abstract type
    - parametrized type

If key contains callable value, it is called with
unevaluated function arguments.
See `typ-annotate-mixed' for more details.")

(defvar typ--noreturn-funcs '(noreturn
                              throw
                              user-error
                              error
                              signal)
  "List of functions that never return normally.
Extending this list is not recommended.")

;; These exist to avoid unnecessary allocations.
(defconst typ--hlist (cons :list nil)
  "Heterogeneous list.  Values can have any type.")
(defconst typ--hvector (cons :vector nil)
  "Heterogeneous vector.  Values can have any type.")
(defconst typ--harray (cons :array nil)
  "Heterogeneous array.  Values can have any type.")
