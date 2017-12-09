;;; asoc.el --- alist functions and macros   -*- lexical-binding: t -*-

;; Copyright (C) 2016 Troy Pracy

;; Author: Troy Pracy <troyp7@gmail.com>
;; Maintainer: Troy Pracy <troyp7@gmail.com>
;; Keywords: alist data-types
;; Version: 0.6.1
;; URL: https://github.com/troyp/asoc.el

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 2 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; Emacs Lisp provides only minimal facilities for dealing with alists, and
;; processing them using standard list functions is awkward and tedious. `asoc`
;; provides a complete API for handling association lists. In addition to basic
;; functions for creating, accessing and modifying alists, it provides mapping,
;; filtering and folding facilities in both regular and anaphoric variants, a
;; looping construct analogous to `dolist`, and a special variable for
;; configuring the equality predicate used by `asoc` operations.

;;

;;; Code:
(require 'cl-macs)


;; ,-----------,
;; | Variables |
;; '-----------'

(defvar asoc-compare-fn nil
  "Special variable holding the equality predicate used in asoc functions.

May take the values `equalp' (or `cl-equalp'), `equal', `eql', `eq'. When unset,
functions default to using `equal'.

This variable may be passed to asoc functions dynamically in a let binding.")

;; ,-------------------,
;; | Private Functions |
;; '-------------------'

(defun asoc---compare (x y)
  "Compare X and Y using `asoc-compare-fn'."
  (funcall (or asoc-compare-fn #'equal) x y))

(defun asoc---assoc (key alist)
  "Return the first association in ALIST matching KEY, or else nil.

The equality test to be used is determined by `asoc-compare-fn'."
  (cl-case asoc-compare-fn
    ('eq          (assq  key alist))
    ((equal nil)  (assoc key alist))
    (t (progn
         (while (and alist
                     (not (funcall asoc-compare-fn (caar alist) key)))
           (setf alist (cdr alist)))
         (car alist)))))

(defun asoc---uniq (alist)
  "Return a copy of ALIST with duplicate keys removed.

The first pair with a given key is kept, later pairs are omitted. Key equality
is determined using `asoc-compare-fn'."
  (let ( result
         (rest alist) )
    (while rest
      (let* ((pair  (car rest))
             (key   (car pair)))
        (unless (asoc---assoc key result)
          (push pair result)))
      (setq rest (cdr rest)))
    (nreverse result)))

(defun asoc---list-member (key list)
  "Return non-nil if KEY is a member of LIST.

Similar to `member', `memq' and `memql', but the equality test to used is
determined by `asoc-compare-fn'."
  (cond ((null list) nil)
        ((funcall (or asoc-compare-fn #'equal) key (car list)) list)
        ((asoc---list-member key (cdr list)))))

(defun asoc---list-filter (pred list)
  (let ((DELMARKER (make-symbol "DEL")))
    (delq
     DELMARKER
     (mapcar (lambda (x) (if (funcall pred x) x DELMARKER))
             list))))

(defun asoc---list-remove (pred list)
      (let ((DELMARKER (make-symbol "DEL")))
        (delq
        DELMARKER
        (mapcar (lambda (x) (if (funcall pred x) DELMARKER x))
                list))))

(defun asoc---list-take (n list)
  "Return the first N elements of LIST.

If there are insufficient elements, return LIST."
  (let ( result
         (i 0)
         (rest list) )
    (while (and (< i n)
                rest)
      (push (car rest) result)
      (setq rest (cdr rest))
      (setq i (1+ i)))
    (nreverse result)))

;; ,----------------------------------,
;; | Constructor and Filter Functions |
;; '----------------------------------'

(defun asoc-make (&optional keys default)
  "Return an alist with KEYS each initialized to value nil."
  (asoc-zip keys (make-list (length keys) default)))

(defalias 'asoc-copy 'copy-sequence "Return a shallow copy of ALIST.")

(defun asoc-uniq (alist)
  "Return a copy of ALIST with duplicate keys removed.

The first occurrence of each key is retained.

Example:

    (asoc-uniq '((a 1) (b 2) (b 3) (c 4) (a 5)))
    ;; ((a 1) (b 2) (c 4))"
  (declare (indent 1))
  (asoc---uniq alist))

(defun asoc-merge (&rest alists)
  "Return an alist with unique keys resulting from merging ALISTS.

When identical keys occur in two alists, the latter alist takes precedence.
When identical keys occur within a single alist, the foremost takes precedence
(as usual).

With a single argument, equivalent to `asoc-uniq'.

Example:

    (asoc-merge '((a . 1) (b . 2) (a . 4))
                '((a . 4) (c . 5) (c . 6)))
    ;; ((a . 4) (c . 5) (b . 2))"
  (asoc---uniq (apply #'append (nreverse alists))))

(defun asoc-sort-keys (alist &optional comparator)
  "Return a copy of ALIST sorted by keys.

The keys are sorted stably using COMPARATOR, or `string<' if none is provided.
Note that `string<' is only applicable to symbols and strings. For other types
of key, a comparator argument is mandatory.

Example:

    (let ((a '((b . 2) (a . 1) (e . 5) (d . 4) (c . 3))))
      (asoc-sort-keys a))
    ;; ((a . 1) (b . 2) (c . 3) (d . 4) (e . 5))"
  (sort (copy-sequence alist)
        (lambda (pair1 pair2)
          (funcall (or comparator #'string<) (car pair1) (car pair2)))))

(defun asoc-filter (predicate alist)
  "Return a copy of ALIST with key-value pairs failing PREDICATE removed.

PREDICATE should take two arguments, KEY and VALUE.

Example: filter for pairs where KEY > VALUE

    (let ((fib '((1 . 1)  (2 . 1)  (3 . 2)  (4 . 3)
                 (5 . 5)  (6 . 8)  (7 . 13)  (8 . 21))))
      (asoc-filter #'> fib))
    ;; ((2 . 1) (3 . 2) (4 . 3))"
  (asoc---list-filter (lambda (pair) (funcall predicate (car pair) (cdr pair)))
                      alist))

(defmacro asoc--filter (form alist)
  "Anaphoric variant of `asoc-filter'.

Return a list of those ALIST elements for which FORM evaluates t.

The included elements remain in their original order. The anaphoric variables
'key and 'value are available for use in FORM.

Examples:

    ;; remove nodes where the key is associated with itself
    (asoc--filter (not (eq key value))
      '((a . b) (b . c) (c . c) (d . a) (e . e)))
    ;; ((a . b) (b . c) (d . a))"
  (declare (debug (form sexp))
           (indent 1))
  `(asoc-filter (lambda (key value) ,form) ,alist))

(defun asoc-filter-keys (predicate alist)
  "Return a copy of ALIST with keys failing PREDICATE removed.

Example: filter for pairs where KEY <= 3

    (let ((fib '((1 . 1)  (2 . 1)  (3 . 2)  (4 . 3)
                 (5 . 5)  (6 . 8)  (7 . 13)  (8 . 21))))
      (asoc-filter-keys (lambda (k) (<= k 3)) fib))
    ;; ((1 . 1) (2 . 1) (3 . 2))"
  (asoc---list-filter (lambda (pair) (funcall predicate (car pair))) alist))

(defun asoc-filter-values (predicate alist)
  "Return a copy of ALIST with pairs whose value fails PREDICATE removed.

Example: filter for pairs where VALUE <= 3

    (let ((fib '((1 . 1)  (2 . 1)  (3 . 2)  (4 . 3)
                 (5 . 5)  (6 . 8)  (7 . 13)  (8 . 21))))
      (asoc-filter-values (lambda (v) (<= v 3)) fib))
    ;; ((1 . 1) (2 . 1) (3 . 2) (4 . 3))"
  (asoc---list-filter (lambda (pair) (funcall predicate (cdr pair))) alist))

(defun asoc-remove (predicate alist)
  "Return a copy of ALIST with key-value pairs satisfying PREDICATE removed.

PREDICATE should take two arguments, KEY and VALUE.

Alias: `asoc-reject'

Equivalent to `asoc-filter' with inverted PREDICATE.

Example: filter out pairs where KEY > VALUE

    (let ((fib '((1 . 1)  (2 . 1)  (3 . 2)  (4 . 3)
                 (5 . 5)  (6 . 8)  (7 . 13)  (8 . 21))))
      (asoc-remove #'> fib))
    ;; ((1 . 1) (5 . 5) (6 . 8) (7 . 13) (8 . 21))"
  (asoc---list-remove (lambda (pair) (funcall predicate (car pair) (cdr pair)))
                      alist))

(defun asoc-remove-keys (predicate alist)
  "Return a copy of ALIST with keys satisfying PREDICATE removed.

Alias: `asoc-reject-keys'

Equivalent to `asoc-filter-keys' with inverted PREDICATE.

Example: filter out pairs where KEY <= 3

    (let ((fib '((1 . 1)  (2 . 1)  (3 . 2)  (4 . 3)
                 (5 . 5)  (6 . 8)  (7 . 13)  (8 . 21))))
      (asoc-remove-keys (lambda (k) (<= k 3)) fib))
    ;; ((4 . 3) (5 . 5) (6 . 8) (7 . 13) (8 . 21))"
  (asoc---list-remove (lambda (pair) (funcall predicate (car pair))) alist))

(defun asoc-remove-values (predicate alist)
  "Return a copy of ALIST with pairs whose value satisfying PREDICATE removed.

Alias: `asoc-reject-values'

Equivalent to `asoc-filter-values' with inverted PREDICATE.

Example: filter out pairs where VALUE <= 3

    (let ((fib '((1 . 1)  (2 . 1)  (3 . 2)  (4 . 3)
                 (5 . 5)  (6 . 8)  (7 . 13)  (8 . 21))))
      (asoc-remove-values (lambda (v) (<= v 3)) fib))
    ;; ((5 . 5) (6 . 8) (7 . 13) (8 . 21))"
  (asoc---list-remove (lambda (pair) (funcall predicate (cdr pair))) alist))

(defalias 'asoc-reject 'asoc-remove)
(defalias 'asoc-reject-keys 'asoc-remove-keys)
(defalias 'asoc-reject-values 'asoc-remove-values)

(defun asoc-partition (flatlist)
  "Return an alist whose keys and values are taken alternately from FLATLIST.

Example:
    (asoc-partition '(a 1 b 2 c 3 d 4 e 5 f 6))
    ;; ((a . 1) (b . 2) (c . 3) (d . 4) (e . 5) (f . 6))"
  (let ( alist
         (rest flatlist) )
    (while rest
      (let (key value)
        (setq key   (car rest))
        (setq value (cadr rest))
        (setq rest  (cddr rest))
        (push (cons key value) alist)))
    (nreverse alist)))

;; ,------------,
;; | Predicates |
;; '------------'

(defun asoc-contains-key? (alist key)
  "Return t if ALIST contains an item with key KEY, nil otherwise."
  (when (asoc---assoc key alist) t))

(defun asoc-contains-pair? (alist key value)
  "Return t if ALIST contains an item (KEY . VALUE), nil otherwise."
  (let ( result
         (rest alist) )
    (while rest
      (let ((pair (car rest)))
        (if (and (asoc---compare (car pair) key)
                 (asoc---compare (cdr pair) value))
            (progn
              (setq result t)))
        (setq rest (cdr rest))))
    result))

(defalias 'asoc-contains-key-p 'asoc-contains-key?)
(defalias 'asoc-contains-pair-p 'asoc-contains-pair?)

;; ,------------------,
;; | Access Functions |
;; '------------------'

(defun asoc-get (alist key &optional default)
  "Return the value associated with KEY in ALIST, or DEFAULT if missing."
  (or (cdr (asoc---assoc key alist)) default))

(defmacro asoc-put! (alist key value &optional replace)
  "Associate KEY with VALUE in ALIST.

When KEY already exists, if REPLACE is non-nil, previous entries with that key
are removed. Otherwise, the pair is simply consed on the front of the alist."
  (declare (debug (sexp sexp sexp &optional sexp)))
  `(progn
     (when ,replace
       (setq ,alist (asoc---list-filter
                     (lambda (pair)
                       (not (asoc---compare (car pair) ,key)))
                     ,alist)))
     (push (cons ,key ,value) ,alist)))
     ;; (setq ,alist (cons (cons ,key ,value) ,alist))))

(defun asoc-dissoc (alist &rest keys)
  "Return a modified list excluding all pairs with a key in KEYS"
  (let (result)
    (dolist (assn alist result)
      (unless (asoc---list-member (car assn) keys)
        (push assn result)))
    (reverse result)))

(defmacro asoc-pop! (alist key)
  "Return the first association containing KEY and remove it from ALIST."
  `(let* (preceding
          (rest ,alist)
          (assn (car rest)))
     (while (and rest (not (asoc---compare ,key (car assn))))
       (push assn preceding)
       (setq rest (cdr rest))
       (setq assn (car rest)))
     ;; we've found the association or the end of the list
     (setq rest (cdr rest))
     (dolist (assn preceding rest)
       (push assn rest))
     (setq ,alist rest)
     assn))

(defun asoc-find (predicate alist)
  "Return the first ALIST association satisfying PREDICATE.

PREDICATE should take two arguments, KEY and VALUE.

For all associations satisfying PREDICATE, use `asoc-filter'."
  (while (and alist
              (not (funcall predicate (caar alist) (cdar alist))))
    (setf alist (cdr alist)))
  (car alist))

(defmacro asoc--find (form alist)
    "Anaphoric variant of `asoc-find'.

Return the first ALIST association for which FORM evaluates t.

The anaphoric variables 'key and 'value are available for use in FORM.

For all associations satisfying FORM, use `asoc--filter'"
    (declare (debug (form sexp))
             (indent 1))
    `(asoc-find (lambda (key value) ,form) ,alist))

(defun asoc-find-key (key alist)
    "Return the first association of ALIST with KEY, or nil if none match.

For all associations with KEY, use `asoc-filter-keys'."
    (asoc---assoc key alist))

(defun asoc-keys (alist)
  "Return a list of unique keys in ALIST.

For a list of all keys in order, with duplicates, use `mapcar' with `car' over
ALIST."
  (let ( result
         (rest alist) )
    (while rest
      (let ((pair (car rest)))
        (unless (asoc---list-member (car pair) result)
          (push (car pair) result))
        (setq rest (cdr rest))))
    (reverse result)))

(defun asoc-values (alist &optional ignore-shadowed)
  "Return a list of unique values in ALIST.

If IGNORE-SHADOWED is non-nil, only show include associated with the first
occurrence of each key.

For a list of all values in order, with duplicate values (and values of shadowed
keys), use `mapcar' with `cdr' over ALIST."
  (let ( result
         keys-seen
         (rest alist) )
    (if ignore-shadowed
        (while rest
          (let ((pair (car rest)))
            (unless (or (asoc---list-member (car pair) keys-seen)
                        (asoc---list-member (cdr pair) result))
              (push (cdr pair) result))
            (push (car pair) keys-seen))
          (setq rest (cdr rest)))
      (while rest
        (let ((pair (car rest)))
          (unless (asoc---list-member (cdr pair) result)
            (push (cdr pair) result))
          (setq rest (cdr rest)))))
    (reverse result)))

(defun asoc-unzip (alist)
  "Return a list of all keys and a list of all values in ALIST.

Returns '(KEYLIST VALUELIST) where KEYLIST and VALUELIST contain all the keys
and values in ALIST in order, including repeats. The original alist can be
reconstructed with

    (asoc-zip KEYLIST VALUELIST).

asoc-unzip will also reverse `asoc-zip' as long as the original arguments of
`asoc-zip' were both lists and were of equal length."
  (let ( keylist
         valuelist
         (rest      (reverse alist)) )
    (while rest
      (let ((pair (car rest)))
        (push (car pair) keylist)
        (push (cdr pair) valuelist)
        (setq rest (cdr rest))))
    (list keylist valuelist)))

;; ,--------------------,
;; | Looping Constructs |
;; '--------------------'

(defmacro asoc-do (spec &rest body)
  "Iterate through ALIST, executing BODY for each key-value pair.

For each iteration, KEYVAR is bound to the key and VALUEVAR is bound to the
value.

The return value is obtained by evaluating RESULT.

Example:

  (asoc-do ((k v) a)
    (insert (format \"%S\t%S\\n\" k v)))
  ;; print keys and values

  (let ((sum 0))
    (asoc-do ((key value) a sum)
      (when (symbolp key)
        (setf sum (+ sum value)))))
  ;; add values associated with all keys that are symbols.

\(fn ((KEYVAR VALUEVAR) ALIST [RESULT]) BODY...)"
  (declare (debug (((sexp sexp) form [&optional sexp]) body))
           (indent 1))
  (let* ((vars    (car spec))
         (kvar    (car vars))
         (vvar    (cadr vars))
         (alist   (cadr spec))
         (result  (car (cddr spec)))
         (pairsym (make-symbol "pair")))
    (if result
        `(progn
           (mapcar (lambda (pair)
                     (let ((,kvar (car pair))
                           (,vvar (cdr pair)))
                       ,@body))
                   ,alist)
           ,result)
      `(progn
         (mapcar (lambda (,pairsym)
                   (let ((,kvar (car ,pairsym))
                         (,vvar (cdr ,pairsym)))
                     ,@body))
                 ,alist)
         nil))))

(defmacro asoc--do (alist &rest body)
  "Anaphoric variant of `asoc-do'.

Iterate through ALIST, executing BODY for each key-value pair. For each
iteration, the anaphoric variables 'key and 'value are bound to they current
key and value. The macro returns the value of the anaphoric variable 'result,
which is initially nil.

Optionally, initialization code can be included prior to the main body using
the syntax (:initially INITCODE...).

Example:

    (let ((a '((one . 1) (two . 4) (3 . 9) (4 . 16) (five . 25) (6 . 36))))
      (asoc--do a
        (when (symbolp key)
          (setf result (+ (or result 0) value)))))
    ;; 30

    (let ((a '((one . 1) (two . 4) (3 . 9) (4 . 16) (five . 25) (6 . 36))))
      (asoc--do a
        (:initially (setf result 0))
        (when (symbolp key)
          (setf result (+ result value)))))
    ;; 30

\(fn (ALIST [(:initially INITCODE...)] BODY...)"
  (declare (debug (sexp body))
           (indent 1))
  (let ((first-sexp (car body)))
    (if (and (listp first-sexp)
             (eq (car first-sexp) :initially))
        ;; with :initially form
        (let ((init (cdr first-sexp))
              (body (cdr body)))
          `(let ( result )
             ,@init
             (asoc-do ((key value) ,alist result) ,@body)))
      ;; no :initially form
      `(let ( result )
         (asoc-do ((key value) ,alist result) ,@body)))))

;; ,-------------------,
;; | Mapping Functions |
;; '-------------------'

(defun asoc-map (func alist)
  "Apply FUNC to each element of ALIST and return the resulting list.

FUNCTION should be a function of two arguments (KEY VALUE).

Examples:

    ;; map value to nil when key is not a symbol...
    (asoc-map (lambda (k v) (cons k (when (symbolp k) v)))
              '((one . 1) (two . 4) (3 . 9) (4 . 16) (five . 25) (6 . 36)))
    ;; ((one . 1) (two . 4) (3 . nil) (4 . nil) (five . 25) (6 . nil))

    ;; list of values for symbol keys (nil for other keys)
    (asoc-map (lambda (k v) (when (symbolp k) v))
              '((one . 1) (two . 4) (3 . 9) (4 . 16) (five . 25) (6 . 36)))
    ;; (1 4 nil nil 25 nil)"
  (mapcar (lambda (k.v)
            (let ((key   (car k.v))
                  (value (cdr k.v)))
              (funcall func key value)))
          alist))

(defmacro asoc--map (form alist)
  "Anaphoric variant of `asoc-map'.

Evaluate FORM for each element of ALIST and return the resulting list.
The anaphoric variables 'key and 'value are available for use in FORM.

Examples:

    (asoc--map
        (cons (intern (concat (symbol-name key) \"-squared\"))
              (* value value))
      '((one . 1) (two . 2) (three . 3) (four . 4)))
    ;; ((one-squared . 1) (two-squared . 4)
    ;;  (three-squared . 9) (four-squared . 16))

    (asoc--map (cons (intern key) value)
      '((\"one\" . 1) (\"two\" . 2) (\"three\" . 3)))
    ((one . 1) (two . 2) (three . 3))

    (asoc--map (format \"%s=%d;\" key value)
      '((one . 1) (two . 2) (three . 3) (four . 4)))
    (\"one=1;\" \"two=2;\" \"three=3;\" \"four=4;\")"
  (declare (debug (form sexp))
           (indent 1))
  `(asoc-map (lambda (key value) ,form) ,alist))

(defun asoc-map-keys (func alist)
  "Return a modified copy of alist with keys transformed by FUNC.

Example: convert symbolic keys to strings

    (asoc-map-keys #'symbol-name
                  '((one . 1) (two . 4) (three . 9) (four . 16)))
    ;; ((\"one\" . 1) (\"two\" . 4) (\"three\" . 9) (\"four\" . 16))"
  (mapcar (lambda (k.v)
            (let ((k (car k.v))
                  (v (cdr k.v)))
              (cons (funcall func k) v)))
          alist))

(defun asoc-map-values (func alist)
  "Return a modified copy of alist with values transformed by FUNC.

Example: convert alist to nested list

    (let ((a '((1 . 1) (2 . 4) (3 . 9) (4 . 16) (5 . 25))))
      (asoc-map-values #'list a))
    ;; ((1 1) (2 4) (3 9) (4 16) (5 25))"
  (mapcar (lambda (k.v)
            (let ((k (car k.v))
                  (v (cdr k.v)))
              (cons k (funcall func v))))
          alist))

(defun asoc-zip (keys values)
  "Return an alist associating KEYS with corresponding VALUES.
If KEYS is longer than VALUES, the excess keys have value nil."
  (when (> (length values) (length keys))
    (error "More keys than values."))
  (let* ((n (- (length keys)
               (length values)))
         (values (append values (make-list n nil)))
         (result nil))
    (while keys
      (let ((key   (pop keys))
            (value (pop values)))
        (push (cons key value) result)))
    (reverse result)))

;; ,-------,
;; | Folds |
;; '-------'

(defun asoc-fold (func alist init)
  "Reduce ALIST using FUNC on the values, starting with value INIT.

FUNC should take a key, a value and the accumulated result and return
an updated result.

Example: list of keys with value of 0

    (let ((a '((1 . 0) (2 . 0) (3 . 0) (4 . 1) (5 . 0)
               (6 . 2) (7 . 7) (8 . 3) (9 . 2) (10 . 0))))
      (asoc-fold (lambda (k v acc) (if (zerop v) (cons k acc) acc))
                 (reverse a) nil))
    ;; (1 2 3 5 10)"
  (let ((result init))
    (asoc-do
        ((key value) alist)
      (setq result (funcall func key value result)))
    result))

(defmacro asoc--fold (form alist init)
  "Anaphoric variant of `asoc-fold'.

  Reduce ALIST using FORM on each value, starting from INIT.

The anaphoric variables 'key, 'value and 'acc represent the current
key, value and accumulated value, respectively.

The return value is the value of 'acc after the last element has
been processed.

Example: list of keys with value of 0

    (let ((a '((1 . 0) (2 . 0) (3 . 0) (4 . 1) (5 . 0)
              (6 . 2) (7 . 7) (8 . 3) (9 . 2) (10 . 0))))
      (asoc--fold (if (zerop value) (cons key acc) acc)
        (reverse a) nil))
    ;; (1 2 3 5 10)"
  (declare (debug (form sexp sexp))
           (indent 1))
  `(asoc-fold (lambda (key value acc) ,form)
              ,alist ,init))

(defun asoc-merge-values (&rest alists)
  "Return an alist merging multiple occurrences of each key in ALISTS.

Each key is associated with a list containing all values in ALISTS which were
associated with the key, in order.

Example:

    (let ( (a '((a . 1) (b . 2) (a . 3) (a . 1)))
           (b '((a . 5) (b . 2) (c . 3))) )
      (asoc-merge-values a b))
    ;; ((a 1 3 1 5) (b 2 2) (c 3))
    ;; ie.  ((a . (1 3 1 5)) (b . (2 2)) (c . (3)))"
  (let ( result
         (rest (reverse (apply #'append alists))) )
    (while rest
      (let* ((assoc        (car rest))
             (key          (car assoc))
             (value        (cdr assoc))
             (accum-value  (asoc-get result key))
             (new-value    (cons value accum-value)))
        (push (cons key new-value) result))
      (setq rest (cdr rest)))
    (asoc-uniq result)))

(defun asoc-merge-values-no-dups (&rest alists)
  "Return an alist merging multiple unique values for each key in ALISTS.

Each key is associated with a list containing all unique values in ALISTS which
were associated with the key, in order.

Example:

    (let ( (a '((a . 1) (b . 2) (a . 3) (a . 1)))
           (b '((a . 5) (b . 2) (c . 3))) )
      (asoc-merge-values-no-dups a b))
      ;; ((a 1 3 5) (b 2) (c 3))
      ;; ie.  ((a . (1 3 5)) (b . (2)) (c . (3)))"
  (asoc-map-values #'delete-dups (apply #'asoc-merge-values alists)))


(provide 'asoc)

;;; asoc ends here
