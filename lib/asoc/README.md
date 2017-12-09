# asoc.el -- Association List Library for Emacs Lisp.


`asoc.el` provides a complete API for handling association lists (alists). In
addition to basic functions for creating, accessing and modifying alists, it
provides mapping, filtering and folding facilities in both regular and anaphoric
variants, a looping construct analogous to `dolist` (also with anaphoric
variant), and a special variable for configuring the equality predicate used by
`asoc` operations.

## Table of Contents

### [API](#api-1)

[A note on builtin list functions](#a-note-on-builtin-list-functions)

[Conventions](#conventions)

#### [Variables](#variables-1)
* [asoc-compare-fn](#asoc-compare-fn-nil)

#### [Constructor and Filter Functions](#constructor-and-filter-functions-1)
* [asoc-make](#asoc-make-optional-keys-default) `(&optional keys default)`
* [asoc-copy](#asoc-copy-alist) `(alist)`
* [asoc-zip](#asoc-zip-keys-values) `(keys values)`
* [asoc-uniq](#asoc-uniq-alist) `(alist)`
* [asoc-merge](#asoc-merge-rest-alists) `(&rest alists)`
* [asoc-sort-keys](#asoc-sort-keys-alist-optional-comparator)
  `(alist &optional comparator)`
* [asoc-filter](#asoc-filter-predicate-alist) `(predicate alist)`
* [asoc--filter](#asoc--filter-form-alist) `(form alist)`
* [asoc-filter-keys](#asoc-filter-keys-predicate-alist) `(predicate alist)`
* [asoc-filter-values](#asoc-filter-values-predicate-alist) `(predicate alist)`
* [asoc-remove](#asoc-remove-predicate-alist) `(predicate alist)`
* [asoc-remove-keys](#asoc-remove-keys-predicate-alist) `(predicate alist)`
* [asoc-remove-values](#asoc-remove-values-predicate-alist) `(predicate alist)`
* [asoc-partition](#asoc-partition-flatlist) `(flatlist)`

#### [Predicates](#predicates-1)
* [asoc-contains-key?](#asoc-contains-key-alist-key) `(alist key)`
* [asoc-contains-pair?](#asoc-contains-pair-alist-key-value) `(alist key value)`

#### [Access Functions](#access-functions-1)
* [asoc-get](#asoc-get-alist-key-optional-default)
  `(alist key &optional default)`
* [asoc-put!](#asoc-put-alist-key-value-optional-replace)
  `(alist key value &optional replace)`
* [asoc-dissoc](#asoc-dissoc-alist-rest-keys) `(alist &rest keys)`
* [asoc-pop!](#asoc-pop-alist-key) `(alist key)`
* [asoc-find](#asoc-find-predicate-alist) `(predicate alist)`
* [asoc--find](#asoc--find-form-alist) `(form alist)`
* [asoc-find-key](#asoc-find-key-key-alist) `(key alist)`
* [asoc-keys](#asoc-keys-alist) `(alist)`
* [asoc-values](#asoc-values-alist-optional-ignore-shadowed)
  `(alist &optional ignore-shadowed)`
* [asoc-unzip](#asoc-unzip-alist) `(alist)`

#### [Looping Constructs](#looping-constructs-1)
* [asoc-do](#asoc-do-spec-rest-body) `(spec &rest body)`
* [asoc--do](#asoc--do-alist-rest-body) `(alist &rest body)`

#### [Mapping Functions](#mapping-functions-1)
* [asoc-map](#asoc-map-function-alist) `(function alist)`
* [asoc--map](#asoc--map-form-alist) `(form alist)`
* [asoc-map-keys](#asoc-map-keys-func-alist) `(func alist)`
* [asoc-map-values](#asoc-map-values-func-alist) `(func alist)`

#### [Folds](#folds-1)
* [asoc-fold](#asoc-fold-func-alist-init) `(func alist init)`
* [asoc--fold](#asoc--fold-form-alist-init) `(form alist init)`
* [asoc-merge-values](#asoc-merge-values-rest-alists) `(&rest alists)`
* [asoc-merge-values-no-dups](#asoc-merge-values-no-dups-rest-alists)
  `(&rest alists)`
  
### [Notes](#notes-1)

#### [Handling Alist Variants](#handling-alist-variants-1)
* [List of duples](#list-of-duples)
* [Flat key-value list / Property list](#flat-key-value-list--property-list)
* [Multi-valued alist](#multi-valued-alist)

#### [Representation of Alists](#representation-of-alists-1)
* [List-valued alists](#list-valued-alists)
* [Cons-valued alist](#cons-valued-alist)
* [Null values](#null-values)

#### [Other Packages](#other-packages-1)

-------------------------------------------------------------------------------

## API

### A note on builtin list functions

For some operations, no distinction need be made between alists and general
lists. `asoc` does not provide functions for such operations, since regular list
functions may be used. For instance, `cons`, `car`, `cdr`, `push`, `pop`,
`append` should be used for assembling and disassembling alists.

-------------------------------------------------------------------------------

### Conventions

Where appropriate, the `asoc` API follows established conventions for naming,
argument order, etc. In particular, it follows the prefix conventions of
[`dash.el`](https://github.com/magnars/dash.el):

* __`asoc-`__:   prefix for regular functions, macros and variables
* __`asoc--`__:  prefix for anaphoric macros
* __`asoc---`__: prefix for private functions, macros and variables

The following suffixes are used:

* __`?`__ or __`-p`__:  marks a predicate function
* __`!`__:          marks a function which may modify its alist argument

`asoc` also follows `dash` in using a special variable to set the predicate used
in equality tests. To control the predicate used for a given call,
`asoc-compare-fn` may be set within a dynamically-scoped let-block containing
the function call.

-------------------------------------------------------------------------------

### Variables

#### asoc-compare-fn `nil`

Special variable holding the equality predicate used in asoc functions.

May take the values `equalp` (or `cl-equalp`), `equal`, `eql`, `eq`. When unset,
functions default to using `equal`.

This variable may be passed to asoc functions dynamically in a let binding.

-------------------------------------------------------------------------------

### Constructor and Filter Functions

#### asoc-make `(&optional keys default)`

Return an alist with __keys__ each initialized to value nil.

#### asoc-copy `(alist)`
_alias of `copy-sequence`._

Return a shallow copy of __alist__.

#### asoc-zip `(keys values)`

Return an alist associating __keys__ with corresponding __values__.
If __keys__ is longer than __values__, the excess __keys__ have value nil.

#### asoc-uniq `(alist)`

Return a copy of __alist__ with duplicate keys removed.

The first occurrence of each key is retained.

    (asoc-uniq `((a 1) (b 2) (b 3) (c 4) (a 5)))
    ;; ((a 1) (b 2) (c 4))

#### asoc-merge `(&rest alists)`

Return an alist with unique keys resulting from merging __alists__.

When identical keys occur in two alists, the latter alist takes precedence.
When identical keys occur within a single alist, the foremost takes precedence
(as usual).

With a single argument, equivalent to __asoc-uniq__.

#### asoc-sort-keys `(alist &optional comparator)`

Return a copy of __alist__ sorted by keys.

The keys are sorted stably using __comparator__, or `string<` if none is
provided. Note that `string<` is only applicable to symbols and strings. For
other types of key, a comparator argument is mandatory.

    (let ((a '((b . 2) (a . 1) (e . 5) (d . 4) (c . 3))))
      (asoc-sort-keys a))
    ;; ((a . 1) (b . 2) (c . 3) (d . 4) (e . 5))

#### asoc-filter `(predicate alist)`

Return a copy of __alist__ with key-value pairs failing __predicate__ removed.

__predicate__ should take two arguments, __key__ and __value__.

    ;; filter for pairs where KEY > VALUE
    (let ((fib `((1 . 1)  (2 . 1)  (3 . 2)  (4 . 3)  (5 . 5)  (6 . 8)  (7 . 13)  (8 . 21))))
      (asoc-filter #'> fib))
    ;; ((2 . 1) (3 . 2) (4 . 3))

#### asoc--filter `(form alist)`

Anaphoric variant of `asoc-filter`.

Return a list of those __alist__ elements for which __form__ evaluates t.

The included elements remain in their original order. The anaphoric variables
`key` and `value` are available for use in __form__.

    ;; remove nodes where the key is associated with itself
    (asoc--filter (not (eq key value))
      `((a . b) (b . c) (c . c) (d . a) (e . e)))
    ;; ((a . b) (b . c) (d . a))

#### asoc-filter-keys `(predicate alist)`

Return a copy of __alist__ with keys failing __predicate__ removed.

    ;; filter for pairs where KEY <= 3
    (let ((fib `((1 . 1)  (2 . 1)  (3 . 2)  (4 . 3)
          (5 . 5)  (6 . 8)  (7 . 13)  (8 . 21))))
      (asoc-filter-keys (lambda (k) (<= k 3)) fib))
    ;; ((1 . 1) (2 . 1) (3 . 2))

#### asoc-filter-values `(predicate alist)`

Return a copy of __alist__ with pairs whose value fails __predicate__ removed.

    ;; filter for pairs where VALUE <= 3
    (let ((fib `((1 . 1)  (2 . 1)  (3 . 2)  (4 . 3)
                 (5 . 5)  (6 . 8)  (7 . 13)  (8 . 21))))
      (asoc-filter-values (lambda (v) (<= v 3)) fib))
    ;; ((1 . 1) (2 . 1) (3 . 2) (4 . 3))

#### asoc-remove `(predicate alist)`
#### asoc-remove-keys `(predicate alist)`
#### asoc-remove-values `(predicate alist)`
_aliases: `asoc-reject`, `asoc-reject-keys`, `asoc-reject-values`_

These are inverse versions of `asoc-filter`, `asoc-filter-keys` and `asoc-filter-values`.
They are equivalent to the corresponding functions with inverted predicates.

    ;; filter out pairs where KEY > VALUE
    (let ((fib '((1 . 1)  (2 . 1)  (3 . 2)  (4 . 3)
                 (5 . 5)  (6 . 8)  (7 . 13)  (8 . 21))))
      (asoc-remove #'> fib))
    ;; ((1 . 1) (5 . 5) (6 . 8) (7 . 13) (8 . 21))

    ;; filter out pairs where KEY <= 3
    (let ((fib '((1 . 1)  (2 . 1)  (3 . 2)  (4 . 3)
                 (5 . 5)  (6 . 8)  (7 . 13)  (8 . 21))))
      (asoc-remove-keys (lambda (k) (<= k 3)) fib))
    ;; ((4 . 3) (5 . 5) (6 . 8) (7 . 13) (8 . 21))

    ;; filter out pairs where VALUE <= 3
    (let ((fib '((1 . 1)  (2 . 1)  (3 . 2)  (4 . 3)
                 (5 . 5)  (6 . 8)  (7 . 13)  (8 . 21))))
      (asoc-remove-values (lambda (v) (<= v 3)) fib))
    ;; ((5 . 5) (6 . 8) (7 . 13) (8 . 21))

#### asoc-partition `(flatlist)`

Return an alist whose keys and values are taken alternately from __flatlist__.

    (asoc-partition `(a 1 b 2 c 3 d 4 e 5 f 6))
    ;; ((a . 1) (b . 2) (c . 3) (d . 4) (e . 5) (f . 6))

-------------------------------------------------------------------------------

### Predicates

#### asoc-contains-key\? `(alist key)`
_alias: `asoc-contains-key-p`_

Return t if __alist__ contains an item with key __key__, nil otherwise.

#### asoc-contains-pair\? `(alist key value)`
_alias: `asoc-contains-pair-p`_

Return t if __alist__ contains an item `(`__`key`__` . `__`value`__`)`, nil
otherwise.

-------------------------------------------------------------------------------

### Access Functions

#### asoc-get `(alist key &optional default)`

Return the value associated with __key__ in __alist__, or __default__ if
missing.

#### asoc-put! `(alist key value &optional replace)`

Associate __key__ with __value__ in __alist__.

When __key__ already exists, if __replace__ is non-nil, previous entries with
that __key__ are removed. Otherwise, the pair is simply consed on the front of
the __alist__. In the latter case, this is equivalent to `acons`.

#### asoc-dissoc `(alist &rest keys)`

Return a modified list excluding all pairs with a key in __keys__

#### asoc-pop! `(alist key)`

Return the first association containing __key__ and remove it from __alist__.

#### asoc-find `(predicate alist)`

Return the first __alist__ association satisfying __predicate__.

__predicate__ should take two arguments, __key__ and __value__.

For all associations satisfying __predicate__, use `asoc-filter`.

#### asoc--find `(form alist)`

Anaphoric variant of `asoc-find`.

Return the first __alist__ association for which __form__ evaluates t.

The anaphoric variables `key` and `value` are available for use in __form__.

For all associations satisfying __form__, use `asoc--filter`

#### asoc-find-key `(key alist)`

Return the first association of __alist__ with __key__, or nil if none match.

For all associations with __key__, use `asoc-filter-keys`.

#### asoc-keys `(alist)`

Return a list of unique keys in __alist__.

For a list of all keys in order, with duplicates, use `mapcar` with `car` over
__alist__.

#### asoc-values `(alist &optional ignore-shadowed)`

Return a list of unique values in __alist__.

If __ignore-shadowed__ is non-nil, only show include associated with the first
occurrence of each key.

For a list of all values in order, with duplicate values (and values of shadowed
keys), use `mapcar` with `cdr` over __alist__.

#### asoc-unzip `(alist)`

Return a list of all keys and a list of all values in __alist__.

Returns `(`__`keylist`__` `__`valuelist`__`)` where __keylist__ and
__valuelist__ contain all the keys and values in __alist__ in order, including
repeats. The original alist can be reconstructed with


    (asoc-zip KEYLIST VALUELIST).

asoc-unzip will also reverse `asoc-zip` as long as the original arguments of
`asoc-zip` were both lists and were of equal length.

-------------------------------------------------------------------------------

### Looping Constructs

#### asoc-do `((keyvar valuevar) alist [result] body...)`

Iterate through __alist__, executing __body__ for each key-value pair.

For each iteration, __keyvar__ is bound to the key and __valuevar__ is bound to
the value.

The return value is obtained by evaluating __result__.

    (asoc-do ((k v) a)
      (insert (format "%S	%S\n" k v)))
    ;; print keys and values

    (let ((sum 0))
      (asoc-do ((key value) a sum)
        (when (symbolp key)
          (setf sum (+ sum value)))))
    ;; add values associated with all keys that are symbols.

#### asoc--do `(alist &rest body)`

Anaphoric variant of `asoc-do`.

Iterate through __alist__, executing __body__ for each key-value pair. For each
iteration, the anaphoric variables `key` and `value` are bound to they current
key and value. The macro returns the value of the anaphoric variable `result`,
which is initially nil.

Optionally, initialization code can be included prior to the main body using
the syntax `(:initially ...)`.

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

-------------------------------------------------------------------------------

### Mapping Functions

#### asoc-map `(function alist)`

Apply __func__ to each element of __alist__ and return the resulting list.

__func__ should be a function of two arguments (__key__ __value__).

    ;; map value to nil when key is not a symbol...
    (asoc-map (lambda (k v) (cons k (when (symbolp k) v)))
              `((one . 1) (two . 4) (3 . 9) (4 . 16) (five . 25) (6 . 36)))
    ;; ((one . 1) (two . 4) (3 . nil) (4 . nil) (five . 25) (6 . nil))

    ;; list of values for symbol keys (nil for other keys)
    (asoc-map (lambda (k v) (when (symbolp k) v))
              '((one . 1) (two . 4) (3 . 9) (4 . 16) (five . 25) (6 . 36)))
    ;; (1 4 nil nil 25 nil)

#### asoc--map `(form alist)`

Anaphoric variant of `asoc-map`.

Evaluate __form__ for each element of __alist__ and return the resulting list.
The anaphoric variables `key` and `value` are available for use in `form`.

    (asoc--map
        (cons (intern (concat (symbol-name key) "-squared"))
              (* value value))
      `((one . 1) (two . 2) (three . 3) (four . 4)))
    ;; ((one-squared . 1) (two-squared . 4)
    ;;  (three-squared . 9) (four-squared . 16))

    (asoc--map (cons (intern key) value)
      '(("one" . 1) ("two" . 2) ("three" . 3)))
    ((one . 1) (two . 2) (three . 3))

    (asoc--map (format "%s=%d;" key value)
      '((one . 1) (two . 2) (three . 3) (four . 4)))
    ("one=1;" "two=2;" "three=3;" "four=4;")

#### asoc-map-keys `(func alist)`

Return a modified copy of __alist__ with keys transformed by __func__.

    ;; convert symbolic keys to strings
    (asoc-map-keys #'symbol-name
                   '((one . 1) (two . 4) (three . 9) (four . 16)))
    ;; (("one" . 1) ("two" . 4) ("three" . 9) ("four" . 16))

#### asoc-map-values `(func alist)`

Return a modified copy of alist with values transformed by __func__.

    ;; convert alist to nested list
    (let ((a `((1 . 1) (2 . 4) (3 . 9) (4 . 16) (5 . 25))))
      (asoc-map-values #'list a))
    ;; ((1 1) (2 4) (3 9) (4 16) (5 25))

-------------------------------------------------------------------------------

### Folds

#### asoc-fold `(func alist init)`

Reduce __alist__ using __func__ on the values, starting with value __init__.

__func__ should take a key, a value and the accumulated result and return
an updated result.

    ;; list of keys with value of 0
    (let ((a `((1 . 0) (2 . 0) (3 . 0) (4 . 1) (5 . 0)
               (6 . 2) (7 . 7) (8 . 3) (9 . 2) (10 . 0))))
      (asoc-fold (lambda (k v acc) (if (zerop v) (cons k acc) acc))
                 (reverse a) nil))
    ;; (1 2 3 5 10)

#### asoc--fold `(form alist init)`

Anaphoric variant of `asoc-fold`.

  Reduce __alist__ using __form__ on each value, starting from __init__.

The anaphoric variables `key`, `value` and `acc` represent the current
key, value and accumulated value, respectively.

The return value is the value of `acc` after the last element has
been processed.

    ;; list of keys with value of 0
    (let ((a '((1 . 0) (2 . 0) (3 . 0) (4 . 1) (5 . 0)
              (6 . 2) (7 . 7) (8 . 3) (9 . 2) (10 . 0))))
      (asoc--fold (if (zerop value) (cons key acc) acc)
        (reverse a) nil))
    ;; (1 2 3 5 10)

#### asoc-merge-values `(&rest alists)`

Return an alist merging multiple occurrences of each key in __alists__.

Each key is associated with a list containing all values in __alists__ which
were associated with the key, in order.

    (let ( (a `((a . 1) (b . 2) (a . 3) (a . 1)))
           (b '((a . 5) (b . 2) (c . 3))) )
      (asoc-merge-values a b))
    ;; ((a 1 3 1 5) (b 2 2) (c 3))
    ;; ie.  ((a . (1 3 1 5)) (b . (2 2)) (c . (3)))

#### asoc-merge-values-no-dups `(&rest alists)`

Return an alist merging multiple unique values for each key in __alists__.

Each key is associated with a list containing all unique values in __alists__
which were associated with the key, in order.

    (let ( (a `((a . 1) (b . 2) (a . 3) (a . 1)))
           (b '((a . 5) (b . 2) (c . 3))) )
      (asoc-merge-values-no-dups a b))
      ;; ((a 1 3 5) (b 2) (c 3))
    ;; ie.  ((a . (1 3 5)) (b . (2)) (c . (3)))

-------------------------------------------------------------------------------

## Notes

### Handling Alist Variants

#### List of duples

__`( (key1 value1) (key2 value2) ... )`__

An alternative format for describing a key-value mapping is a list whose
elements are 2-element `(key value)` sublists, rather than `(key . value)`
cons cells.

A list of this form is equivalent to an alist whose values are all wrapped in
lists.

    ( (key1 . (value1)) (key2 . (value2)) ... )

Although this is pointless, such pseudo-alists are common, perhaps because the
literals are more concise than those of true alists.

Such lists can be processed with alist functions if you remember to wrap and
unwrap the value as needed. Alternatively, you can convert the list to an alist
prior to processing:

    (let (my-alist (asoc-map-values #'car my-duplelist))
      .... )

When converting such a list, be careful to ensure that it strictly associates
one key with one value. Sometimes an alist will legitimately have list values
to allow a key to be associated with multiple values:

    ( (key1 value1) (key2 value2a value2b) ... )
    ;; or equivalently:
    ( (key1 . (value1)) (key2 . (value2a value2b)) ... )

This is a true alist whose values simply happen to be lists.

#### Flat key-value list / Property list

__`(key1 value 1 key2 value2 ...)`__

Another form of key-value list is a flat list with alternating keys and values.

When keys are distinct symbols, such a list is called a plist (property list).
In Emacs Lisp, each symbol has an associated plist specifying its properties.

Such a list can be converted to an alist with `asoc-partition`

    (let ((my-alist (asoc-partition my-flatlist)))
      .... )

#### Multi-valued alist

__`(... (key1 . value1a) ... (key1 . value1b) ...)`__

Normally, an alist may allow multiple associations with the same key, but only
considers the first when accessing a value. This allows the value for a key to
be non-destructively changed ("shadowed") by simply pushing an association onto
the alist, and the change to be reversed by removing that association.

However, sometimes, a list may contain multiple key-value associations, all of
which are relevant, ie. a key has multiple values.

Such a multi-valued alist is best converted into a list-valued alist using
`asoc-merge-values`.

-------------------------------------------------------------------------------

### Representation of Alists

#### List-valued alists

As mentioned above, alists will sometimes have lists as values.

    ( (key1 value1) (key2 value2a value2b) ... )

... is the standard representation of:

    ( ( key1 . (value1) )
      ( key2 . (value2a value2b) )
      ...

Similarly, with an improper-list-valued alist:

    ( (key1 value1a . value1b) (key2 value2a value2b . value2c) ... )

... is the standard representation of:

    ( ( key1 . (value1a . value1b) )
      ( key2 . (value2a value2b . value2c))
      ...

#### Cons-valued alist

A special case (or special interpretation) of improper-list-valued alists is a
cons-valued alist.

For instance, consider an alist where values may be either individual atoms or
cons cells:

    ( (key1 . value1) (key2 value2a . value2b) ... )

... is the standard representation of:

    ( ( key1 . value1 )
      ( key2 . (value2a . value2b) )
      ...

#### Null values

When a value is `nil`, the key-value pair is represented as a list containing
only the key:

    ( (key1 . value1) (key2) ... )

is the standard representation of:

    ( ( key1 . value1 )
      ( key2 . nil )
      ...

-------------------------------------------------------------------------------

### Other Packages

* [`let-alist`](https://elpa.gnu.org/packages/let-alist.html) provides a macro
of the same name, which allows convenient access to alist values when the keys
are symbols.
* [`map`](https://github.com/emacs-mirror/emacs/blob/master/lisp/emacs-lisp/map.el)
provides functions for alists, hash tables and arrays.
* [`kv`](https://github.com/nicferrier/emacs-kv) provides tools for plists,
alists and hash tables.
* [`a`](https://github.com/plexus/a.el) provides functions for alists and hash
tables inspired by Clojure.
