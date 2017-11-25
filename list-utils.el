;;; list-utils.el --- List-manipulation utility functions
;;
;; Copyright (c) 2012-2015 Roland Walker
;;
;; Author: Roland Walker <walker@pobox.com>
;; Homepage: http://github.com/rolandwalker/list-utils
;; URL: http://raw.githubusercontent.com/rolandwalker/list-utils/master/list-utils.el
;; Version: 0.4.4
;; Last-Updated: 14 Apr 2016
;; EmacsWiki: ListUtils
;; Keywords: extensions
;;
;; Simplified BSD License
;;
;;; Commentary:
;;
;; Quickstart
;;
;;     (require 'list-utils)
;;
;;     (list-utils-flatten '(1 2 (3 4 (5 6 7))))
;;     ;; '(1 2 3 4 5 6 7)
;;
;;     (list-utils-depth '(1 2 (3 4 (5 6 7))))
;;     ;; 3
;;
;;     (let ((cyclic-list '(1 2 3 4 5 6 7)))
;;       (nconc cyclic-list (cdr cyclic-list))
;;       (list-utils-make-linear-inplace cyclic-list))
;;     ;; '(1 2 3 4 5 6 7)
;;
;;     (list-utils-cyclic-p '(1 2 3))
;;     ;; nil
;;
;;     (list-utils-plist-del '(:one 1 :two 2 :three 3) :two)
;;     ;; '(:one 1 :three 3)
;;
;; Explanation
;;
;; List-utils is a collection of functions for list manipulation.
;; This library has no user-level interface; it is only useful
;; for programming in Emacs Lisp.
;;
;; Notable functionality includes
;;
;;     * `list-utils-flatten', a robust list-flattener which handles
;;       cyclic lists, non-nil-terminated lists, and preserves nils
;;       when they are found as list elements.
;;
;;     * `tconc', a simple data structure for efficiently appending
;;       to a list
;;
;; The following functions are provided:
;;
;;     `make-tconc'
;;     `tconc-p'
;;     `tconc-list'
;;     `tconc'
;;     `list-utils-cons-cell-p'
;;     `list-utils-cyclic-length'
;;     `list-utils-improper-p'
;;     `list-utils-make-proper-copy'
;;     `list-utils-make-proper-inplace'
;;     `list-utils-make-improper-copy'
;;     `list-utils-make-improper-inplace'
;;     `list-utils-linear-p'
;;     `list-utils-linear-subseq'
;;     `list-utils-cyclic-p'
;;     `list-utils-cyclic-subseq'
;;     `list-utils-make-linear-copy'
;;     `list-utils-make-linear-inplace'
;;     `list-utils-safe-length'
;;     `list-utils-safe-equal'
;;     `list-utils-depth'
;;     `list-utils-flat-length'
;;     `list-utils-flatten'
;;     `list-utils-alist-or-flat-length'
;;     `list-utils-alist-flatten'
;;     `list-utils-insert-before'
;;     `list-utils-insert-after'
;;     `list-utils-insert-before-pos'
;;     `list-utils-insert-after-pos'
;;     `list-utils-and'
;;     `list-utils-not'
;;     `list-utils-xor'
;;     `list-utils-uniq'
;;     `list-utils-dupes'
;;     `list-utils-singlets'
;;     `list-utils-partition-dupes'
;;     `list-utils-plist-reverse'
;;     `list-utils-plist-del'
;;
;; To use list-utils, place the list-utils.el library somewhere
;; Emacs can find it, and add the following to your ~/.emacs file:
;;
;;     (require 'list-utils)
;;
;; Notes
;;
;;     This library includes an implementation of the classic Lisp
;;     `tconc' which is outside the "list-utils-" namespace.
;;
;; Compatibility and Requirements
;;
;;     GNU Emacs version 25.1-devel     : not tested
;;     GNU Emacs version 24.5           : not tested
;;     GNU Emacs version 24.4           : yes
;;     GNU Emacs version 24.3           : yes
;;     GNU Emacs version 23.3           : yes
;;     GNU Emacs version 22.2           : yes, with some limitations
;;     GNU Emacs version 21.x and lower : unknown
;;
;;     No external dependencies
;;
;; Bugs
;;
;; TODO
;;
;;     @@@ spin out hash-table tests into separate library
;;
;;     test cyclic inputs to all
;;     test improper inputs to all
;;     test single-element lists as inputs to all
;;     test cyclic single-element lists as inputs to all
;;
;;     should list-utils-make-improper-inplace accept nil as a special case?
;;
;;     could do -copy/-inplace variants for more functions, consider doing
;;     so for flatten
;;
;;     list* returns a non-list on single elt, our function throws an error
;;
;;; License
;;
;; Simplified BSD License:
;;
;; Redistribution and use in source and binary forms, with or
;; without modification, are permitted provided that the following
;; conditions are met:
;;
;;   1. Redistributions of source code must retain the above
;;      copyright notice, this list of conditions and the following
;;      disclaimer.
;;
;;   2. Redistributions in binary form must reproduce the above
;;      copyright notice, this list of conditions and the following
;;      disclaimer in the documentation and/or other materials
;;      provided with the distribution.
;;
;; This software is provided by Roland Walker "AS IS" and any express
;; or implied warranties, including, but not limited to, the implied
;; warranties of merchantability and fitness for a particular
;; purpose are disclaimed.  In no event shall Roland Walker or
;; contributors be liable for any direct, indirect, incidental,
;; special, exemplary, or consequential damages (including, but not
;; limited to, procurement of substitute goods or services; loss of
;; use, data, or profits; or business interruption) however caused
;; and on any theory of liability, whether in contract, strict
;; liability, or tort (including negligence or otherwise) arising in
;; any way out of the use of this software, even if advised of the
;; possibility of such damage.
;;
;; The views and conclusions contained in the software and
;; documentation are those of the authors and should not be
;; interpreted as representing official policies, either expressed
;; or implied, of Roland Walker.
;;
;;; Code:
;;

;;; requirements

;; for defstruct, assert, setf, callf, loop
(require 'cl)

;;; declarations

(declare-function list-utils-cyclic-length "list-utils.el")
(declare-function string-utils-compress-whitespace "string-utils.el")

;;;###autoload
(defgroup list-utils nil
  "List-manipulation utility functions."
  :version "0.4.4"
  :link '(emacs-commentary-link :tag "Commentary" "list-utils")
  :link '(url-link :tag "GitHub" "http://github.com/rolandwalker/list-utils")
  :link '(url-link :tag "EmacsWiki" "http://emacswiki.org/emacs/ListUtils")
  :prefix "list-utils-"
  :group 'extensions)

;;; compatibility functions

(unless (fboundp 'string-utils-compress-whitespace)
  (defvar string-utils-whitespace
    (concat (apply 'vector (delq nil (mapcar #'(lambda (x) (decode-char 'ucs x)) '(#x00009 #x0000a #x0000b #x0000c #x0000d #x00020 #x00085 #x00088 #x00089 #x0008a #x000a0 #x01680 #x0180e #x02000 #x02001 #x02002 #x02003 #x02004 #x02005 #x02006 #x02007 #x02008 #x02009 #x0200a #x0200b #x02028 #x02029 #x0202f #x0205f #x02060 #x03000 #x0feff #xe0020)))))
    "Definition of whitespace characters used by string-utils.

Includes Unicode whitespace characters.")
  ;; simplified version of function from string-utils
  (defun string-utils-compress-whitespace (str-val &optional whitespace-type separator)
    "Return STR-VAL with all contiguous whitespace compressed to a single space.
WHITESPACE-TYPE is ignored.
SEPARATOR is the string with which to replace any whitespace."
    (callf or separator " ")
    (let ((whitespace-regexp (concat "[" string-utils-whitespace "]")))
      (save-match-data
        (replace-regexp-in-string (concat whitespace-regexp "+") separator
                                  str-val)))))

;;; hash-table tests

(defun list-utils-htt-= (x y)
  "A comparison function in which `=' floats and integers are identical.

Non-numeric arguments are permitted and will be compared by `equal'.

A hash-table-test is defined with the same name."
  (if (and (numberp x)
           (numberp y))
      (= x y)
    ;; else
    (equal x y)))

(define-hash-table-test 'list-utils-htt-=
                        'list-utils-htt-=
                        #'(lambda (x)
                            (sxhash (if (numberp x)
                                        (float x)
                                      ;; else
                                      x))))

(defun list-utils-htt-case-fold-equal (x y)
  "A string comparison function which ignores case.

Non-string arguments are permitted, and will be compared after
stringification by `format'.

A hash-table-test is defined with the same name."
  (eq t (compare-strings (if x (format "%s" x) "") nil nil
                         (if y (format "%s" y) "") nil nil
                         'ignore-case)))

(define-hash-table-test 'list-utils-htt-case-fold-equal
                        'list-utils-htt-case-fold-equal
                        #'(lambda (x)
                            (sxhash (upcase (if x (format "%s" x) "")))))

(defun list-utils-htt-ignore-whitespace-equal (x y)
  "A string comparison function which ignores whitespace.

Non-string arguments are permitted, and will be compared after
stringification by `format'.

A hash-table-test is defined with the same name."
  (string-equal (string-utils-compress-whitespace (if x (format "%s" x) "") nil "")
                (string-utils-compress-whitespace (if y (format "%s" y) "") nil "")))

(define-hash-table-test 'list-utils-htt-ignore-whitespace-equal
                        'list-utils-htt-ignore-whitespace-equal
                        #'(lambda (x)
                            (sxhash (string-utils-compress-whitespace (if x (format "%s" x) "") nil ""))))

;;; tconc - this section of code is in the public domain

;;;###autoload
(progn
  (require 'cl)
  (defstruct tconc head tail))

;;;###autoload
(defun tconc-list (tc list)
  "Efficiently append LIST to TC.

TC is a data structure created by `make-tconc'."
  (assert (tconc-p tc) nil "TC must be created by `make-tconc'.")
  (when list
    (if (null (tconc-tail tc))
        (setf (tconc-head tc) list)
      ;; else
      (setcdr (tconc-tail tc) list))
    (setf (tconc-tail tc) (last list)))
  (tconc-head tc))

;;;###autoload
(defun tconc (tc &rest args)
  "Efficiently append ARGS to TC.

TC is a data structure created by `make-tconc'

Without ARGS, return the list held by TC."
  (tconc-list tc args))

;;; lists

;;;###autoload
(defun list-utils-cons-cell-p (cell)
  "Return non-nil if CELL holds a cons cell rather than a proper list.

A proper list is defined as a series of cons cells in which the
cdr slot of each cons holds a pointer to the next element of the
list, and the cdr slot in the final cons holds nil.

A plain cons cell, for the purpose of this function, is a single
cons in which the cdr holds data rather than a pointer to the
next cons cell, eg

    '(1 . 2)

In addition, a list which is not nil-terminated is not a proper
list and will be recognized by this function as a cons cell.
Such a list is printed using dot notation for the last two
elements, eg

    '(1 2 3 4 . 5)

Such improper lists are produced by `list*'."
  (let ((len (safe-length cell)))
    (when (and (consp cell)
               (> len 0)
               (not (listp (nthcdr len cell))))
      (nthcdr len cell))))

;;;###autoload
(defun list-utils-make-proper-copy (list &optional tree recur-internal)
  "Copy a cons cell or improper LIST into a proper list.

If optional TREE is non-nil, traverse LIST, making proper
copies of any improper lists contained within.

Optional RECUR-INTERNAL is for internal use only.

Improper lists consist of proper lists consed to a final
element, and are produced by `list*'."
  (assert (or recur-internal (listp list)) nil "LIST is not a list")
  (cond
    ((not tree)
     (let ((tail (list-utils-cons-cell-p list)))
       (cond
         (tail
          (append
           (subseq list 0 (safe-length list))
           (list tail)))
         (t
          (copy-sequence list)))))
    ((consp list)
     (mapcar #'(lambda (elt)
                 (list-utils-make-proper-copy elt 'tree 'recur))
             (list-utils-make-proper-copy list nil 'recur)))
    (t
     list)))

;;;###autoload
(defun list-utils-make-proper-inplace (list &optional tree recur-internal)
  "Make a cons cell or improper LIST into a proper list.

Improper lists consist of proper lists consed to a final
element, and are produced by `list*'.

If optional TREE is non-nil, traverse LIST, making any
improper lists contained within into proper lists.

Optional RECUR-INTERNAL is for internal use only.

Modifies LIST and returns the modified value."
  (assert (or recur-internal (listp list)) nil "LIST is not a list")
  (cond
    ((not tree)
     (when (list-utils-cons-cell-p list)
       (callf list (nthcdr (safe-length list) list)))
     list)
    ((consp list)
     (loop for elt in (list-utils-make-proper-inplace list nil 'recur)
           do (list-utils-make-proper-inplace elt 'tree 'recur))
     list)
    (t
     list)))
(define-obsolete-function-alias 'list-utils-make-proper 'list-utils-make-proper-inplace)

;;;###autoload
(defun list-utils-make-improper-copy (list &optional tree recur-internal)
  "Copy a proper LIST into an improper list.

Improper lists consist of proper lists consed to a final
element, and are produced by `list*'.

If optional TREE is non-nil, traverse LIST, making proper
copies of any improper lists contained within.

Optional RECUR-INTERNAL is for internal use only."
  (assert (or recur-internal (listp list)) nil "LIST is not a list")
  (assert (or recur-internal (> (safe-length list) 1)) nil "LIST has only one element")
  (cond
    ((not tree)
     (let ((tail (list-utils-cons-cell-p list)))
       (cond
         (tail
          (copy-list list))
         (t
          (apply 'list* list)))))
    ((and (consp list)
          (> (safe-length list) 1))
     (apply 'list*
            (mapcar #'(lambda (elt)
                        (list-utils-make-improper-copy elt 'tree 'recur))
                    (list-utils-make-proper-copy list nil 'recur))))
    (t
     list)))

;;;###autoload
(defun list-utils-make-improper-inplace (list &optional tree recur-internal)
  "Make proper LIST into an improper list.

Improper lists consist of proper lists consed to a final
element, and are produced by `list*'.

If optional TREE is non-nil, traverse LIST, making any
proper lists contained within into improper lists.

Optional RECUR-INTERNAL is for internal use only.

Modifies LIST and returns the modified value."
  (assert (or recur-internal (listp list)) nil "LIST is not a list")
  (assert (or recur-internal (> (safe-length list) 1)) nil "LIST has only one element")
  (cond
    ((not tree)
     (unless (list-utils-cons-cell-p list)
       (setcdr (last list 2) (car (last list))))
     list)
    ((and (consp list)
          (> (safe-length list) 1))
     (loop for elt in (list-utils-make-improper-inplace list nil 'recur)
           do (list-utils-make-improper-inplace elt 'tree 'recur))
     list)
    (t
     list)))
(define-obsolete-function-alias 'list-utils-make-improper 'list-utils-make-improper-inplace)

;;;###autoload
(defun list-utils-linear-subseq (list &optional cycle-length)
  "Return the linear elements from a partially cyclic LIST.

If there is no cycle in LIST, return LIST.  If all elements of
LIST are included in a cycle, return nil.

As an optimization, CYCLE-LENGTH may be specified if the length
of the cyclic portion is already known.  Otherwise it will be
calculated from LIST."
  (callf or cycle-length (list-utils-cyclic-length list))
  (if (= 0 cycle-length)
      list
    ;; else
    (let ((behind list)
          (ahead (nthcdr cycle-length list))
          (linear-subseq nil))
      (catch 'cycle
        (while behind
          (when (eq ahead behind)
            (throw 'cycle t))
          (push (car behind) linear-subseq)
          (setq ahead (cdr ahead))
          (setq behind (cdr behind))))
      (nreverse linear-subseq))))

;;;###autoload
(defun list-utils-cyclic-subseq (list &optional from-start)
  "Return any cyclic elements from LIST as a circular list.

The first element of the cyclic structure is not guaranteed to be
first element of the return value unless FROM-START is non-nil.

To linearize the return value, use `list-utils-make-linear-inplace'.

If there is no cycle in LIST, return nil."
  (cond
    ((list-utils-cons-cell-p list)
     nil)
    (from-start
     (nthcdr (length (list-utils-linear-subseq list)) list))
    (t
     (let ((fast list)
           (slow list))
       (catch 'cycle
         (while (cdr fast)
           (setq fast (cdr (cdr fast)))
           (setq slow (cdr slow))
           (when (eq slow fast)
             (throw 'cycle slow))))))))

;;;###autoload
(defun list-utils-cyclic-length (list)
  "Return the number of cyclic elements in LIST.

If some portion of LIST is linear, only the cyclic
elements will be counted.

If LIST is completely linear, return 0."
  (if (list-utils-cons-cell-p list)
      0
    ;;else
    (let ((fast list)
          (slow list)
          (counter 0))
      (catch 'cycle
        (while slow
          (incf counter)
          (setq slow (cdr slow))
          (setq fast (cdr (cdr fast)))
          (when (eq slow list)
            (throw 'cycle t))
          (when (eq slow fast)
            (setq list slow)
            (setq counter 0)
            (setq fast nil))))
      counter)))

;;;###autoload
(defun list-utils-cyclic-p (list &optional perfect)
  "Return non-nil if LIST contains any cyclic structures.

If optional PERFECT is set, only return non-nil if LIST is a
perfect non-branching cycle in which the last element points
to the first."
  (let ((cycle (list-utils-cyclic-subseq list)))
    (when (or (not perfect)
              (not (list-utils-linear-subseq list (list-utils-cyclic-length cycle))))
        cycle)))

;;;###autoload
(defun list-utils-linear-p (list)
  "Return non-nil if LIST is linear (no cyclic structure)."
  (not (list-utils-cyclic-subseq list)))

;;;###autoload
(defalias 'list-utils-improper-p 'list-utils-cons-cell-p)

;;;###autoload
(defun list-utils-safe-length (list)
  "Return the number of elements in LIST.

LIST may be linear or cyclic.

If LIST is not really a list, returns 0.

If LIST is an improper list, return the number of proper list
elements, like `safe-length'."
  (if (not (listp list))
      0
    ;; else
    (let ((cycle-length (list-utils-cyclic-length list)))
      (+ cycle-length
         (safe-length (list-utils-linear-subseq list cycle-length))))))

;;;###autoload
(defun list-utils-flat-length (list)
  "Count simple elements from the beginning of LIST.

Stop counting when a cons is reached.  nil is not a cons,
and is considered to be a \"simple\" element.

If the car of LIST is a cons, return 0."
  (let ((counter 0))
    (ignore-errors
        (catch 'saw-depth
          (dolist (elt list)
            (when (consp elt)
              (throw 'saw-depth t))
            (incf counter))))
  counter))

;;;###autoload
(defun list-utils-make-linear-copy (list &optional tree)
  "Return a linearized copy of LIST, which may be cyclic.

If optional TREE is non-nil, traverse LIST, substituting
linearized copies of any cyclic lists contained within."
  (cond
    ((not tree)
     (subseq list 0 (list-utils-safe-length list)))
    ((consp list)
     (mapcar #'(lambda (elt)
                 (list-utils-make-linear-copy elt 'tree))
             (list-utils-make-linear-copy list)))
    (t
     list)))

;;;###autoload
(defun list-utils-make-linear-inplace (list &optional tree)
  "Linearize LIST, which may be cyclic.

Modifies LIST and returns the modified value.

If optional TREE is non-nil, traverse LIST, linearizing any
cyclic lists contained within."
  (cond
    ((not tree)
     (setf (nthcdr (list-utils-safe-length list) list) nil)
     list)
    ((consp list)
     (mapcar #'(lambda (elt)
                 (list-utils-make-linear-inplace elt 'tree))
             (list-utils-make-linear-inplace list)))
    (t
     list)))

;;;###autoload
(defun list-utils-safe-equal (list-1 list-2 &optional test)
  "Compare LIST-1 and LIST-2, which may be cyclic lists.

LIST-1 and LIST-2 may also contain cyclic lists, which are
each traversed and compared.  This function will not infloop
when cyclic lists are encountered.

Non-nil is returned only if the leaves of LIST-1 and LIST-2 are
`equal' and the structure is identical.

Optional TEST specifies a test, defaulting to `equal'.

If LIST-1 and LIST-2 are not actually lists, they are still
compared according to TEST."
  (callf or test 'equal)
  (cond
    ((and (not (listp list-1))
          (not (listp list-2)))
     (funcall test list-1 list-2))
    ((or (not (listp list-1))
         (not (listp list-2)))
     nil)
    (t
     (catch 'match
       (let* ((cyclic-1 (list-utils-make-linear-copy (list-utils-cyclic-subseq list-1 'from-start)))
              (cyclic-2 (list-utils-make-linear-copy (list-utils-cyclic-subseq list-2 'from-start)))
              (clen-1 (list-utils-safe-length cyclic-1))
              (clen-2 (list-utils-safe-length cyclic-2))
              (linear-1 nil)
              (linear-2 nil)
              (last-cdr-1 nil)
              (last-cdr-2 nil))
         (unless (= clen-1 clen-2)
           (throw 'match nil))
         (loop for a in cyclic-1
               for b in cyclic-2
               unless (list-utils-safe-equal a b) do (throw 'match nil))
         (setq linear-1 (list-utils-linear-subseq list-1 clen-1))
         (setq linear-2 (list-utils-linear-subseq list-2 clen-2))
         (unless (= (list-utils-safe-length linear-1) (list-utils-safe-length linear-2))
           (throw 'match nil))
         (loop for a in linear-1
               for b in linear-2
               unless (list-utils-safe-equal a b) do (throw 'match nil))
         (setq last-cdr-1 (list-utils-improper-p linear-1))
         (setq last-cdr-2 (list-utils-improper-p linear-2))
         (when (or (if last-cdr-1 (not last-cdr-2) last-cdr-2)
                   (and last-cdr-1
                        (not (funcall test last-cdr-1 last-cdr-2))))
           (throw 'match nil)))
       t))))

;;;###autoload
(defun list-utils-depth (list)
  "Find the depth of LIST, which may contain other lists.

If LIST is not a list or is an empty list, returns a depth
of 0.

If LIST is a cons cell or a list which does not contain other
lists, returns a depth of 1."
  (cond
    ((or (not (listp list))
         (null list))
     0)
    ((and (listp list)
          (list-utils-cyclic-p list))
     (list-utils-depth (list-utils-make-linear-copy list)))
    ((list-utils-cons-cell-p list)
     (+ 1 (apply 'max (mapcar 'list-utils-depth (list-utils-make-proper-copy list)))))
    (t
     (+ 1 (apply 'max (mapcar 'list-utils-depth list))))))

;;;###autoload
(defun list-utils-flatten (list)
  "Return a flattened copy of LIST, which may contain other lists.

This function flattens cons cells as lists, and
flattens circular list structures."

  (cond

    ((null list)
     nil)

    ((and (listp list)
          (list-utils-cyclic-p list))
     (list-utils-flatten (list-utils-make-linear-copy list)))

    ((and (listp list)
          (consp (car list)))
     (append (list-utils-flatten (car list))
             (list-utils-flatten (cdr list))))

    ((listp list)
     (let ((extent (list-utils-flat-length list)))
       (append (subseq list 0 extent)
               (list-utils-flatten (nthcdr extent list)))))

    (t
     (list list))))

;;;###autoload
(defun list-utils-insert-before (list element new-element &optional test)
  "Look in LIST for ELEMENT and insert NEW-ELEMENT before it.

Optional TEST sets the test used for a matching element, and
defaults to `equal'.

LIST is modified and the new value is returned."
  (callf or test 'equal)
  (let ((improper (list-utils-improper-p list))
        (pos nil))
    (when improper
      (callf list-utils-make-proper-inplace list))
    (setq pos (position element list :test test))
    (assert pos nil "Element not found: %s" element)
    (push new-element (nthcdr pos list))
    (when improper
      (callf list-utils-make-improper-inplace list)))
  list)

;;;###autoload
(defun list-utils-insert-after (list element new-element &optional test)
  "Look in LIST for ELEMENT and insert NEW-ELEMENT after it.

Optional TEST sets the test used for a matching element, and
defaults to `equal'.

LIST is modified and the new value is returned."
  (callf or test 'equal)
  (let ((improper (list-utils-improper-p list))
        (pos nil))
    (when improper
      (callf list-utils-make-proper-inplace list))
    (setq pos (position element list :test test))
    (assert pos nil "Element not found: %s" element)
    (push new-element (cdr (nthcdr pos list)))
    (when improper
      (callf list-utils-make-improper-inplace list)))
  list)

;;;###autoload
(defun list-utils-insert-before-pos (list pos new-element)
  "Look in LIST for position POS, and insert NEW-ELEMENT before.

POS is zero-indexed.

LIST is modified and the new value is returned."
  (let ((improper (list-utils-improper-p list)))
    (when improper
      (callf list-utils-make-proper-inplace list))
    (assert (and (integerp pos)
                 (>= pos 0)
                 (< pos (length list))) nil "No such position %s" pos)
    (push new-element
          (nthcdr pos list))
    (when improper
      (callf list-utils-make-improper-inplace list)))
  list)

;;;###autoload
(defun list-utils-insert-after-pos (list pos new-element)
  "Look in LIST for position POS, and insert NEW-ELEMENT after.

LIST is modified and the new value is returned."
  (let ((improper (list-utils-improper-p list)))
    (when improper
      (callf list-utils-make-proper-inplace list))
    (assert (and (integerp pos)
                 (>= pos 0)
                 (< pos (length list))) nil "No such position %s" pos)
    (push new-element
          (cdr (nthcdr pos list)))
    (when improper
      (callf list-utils-make-improper-inplace list)))
  list)

;;;###autoload
(defun list-utils-and (list1 list2 &optional test hint flip)
  "Return the elements of LIST1 which are present in LIST2.

This is similar to `cl-intersection' (or `intersection') from
the cl library, except that `list-utils-and' preserves order,
does not uniquify the results, and exhibits more predictable
performance for large lists.

Order will follow LIST1.  Duplicates may be present in the result
as in LIST1.

TEST is an optional comparison function in the form of a
hash-table-test.  The default is `equal'.  Other valid values
include `eq' (built-in), `eql' (built-in), `list-utils-htt-='
\(numeric), `list-utils-htt-case-fold-equal' (case-insensitive).
See `define-hash-table-test' to define your own tests.

HINT is an optional micro-optimization, predicting the size of
the list to be hashed (LIST2 unless FLIP is set).

When optional FLIP is set, the sense of the comparison is
reversed.  When FLIP is set, LIST2 will be the guide for the
order of the result, and will determine whether duplicates may
be returned.  Since this function preserves duplicates, setting
FLIP can change the number of elements in the result.

Performance: `list-utils-and' and friends use a general-purpose
hashing approach.  `intersection' and friends use pure iteration.
Iteration can be much faster in a few special cases, especially
when the number of elements is small.  In other scenarios,
iteration can be much slower.  Hashing has no worst-case
performance scenario, although it uses much more memory.  For
heavy-duty list operations, performance may be improved by
`let'ing `gc-cons-threshold' to a high value around sections that
make frequent use of this function."
  (when flip
    (psetq list1 list2 list2 list1))
  (cond
    ((null list1)
     list2)
    ((null list2)
     list1)
    ((equal list1 list2)
     list1)
    (t
     (let ((saw (make-hash-table
                 :test (or test 'equal)
                 :size (or hint (safe-length (if flip list1 list2))))))
       (mapc #'(lambda (elt)
                 (puthash elt t saw))
             list2)
       (delq nil (mapcar #'(lambda (elt)
                             (when (gethash elt saw)
                               elt))
                         list1))))))

;;;###autoload
(defun list-utils-not (list1 list2 &optional test hint flip)
  "Return the elements of LIST1 which are not present in LIST2.

This is similar to `cl-set-difference' (or `set-difference') from
the cl library, except that `list-utils-not' preserves order and
exhibits more predictable performance for large lists.  Order will
follow LIST1.  Duplicates may be present as in LIST1.

TEST is an optional comparison function in the form of a
hash-table-test.  The default is `equal'.  Other valid values
include `eq' (built-in), `eql' (built-in), `list-utils-htt-='
\(numeric), `list-utils-htt-case-fold-equal' (case-insensitive).
See `define-hash-table-test' to define your own tests.

HINT is an optional micro-optimization, predicting the size of
the list to be hashed (LIST2 unless FLIP is set).

When optional FLIP is set, the sense of the comparison is
reversed, returning elements of LIST2 which are not present in
LIST1.  When FLIP is set, LIST2 will be the guide for the order
of the result, and will determine whether duplicates may be
returned.

Performance: see notes under `list-utils-and'."
  (when flip
    (psetq list1 list2 list2 list1))
  (cond
    ((null list1)
     nil)
    ((null list2)
     list1)
    ((equal list1 list2)
     nil)
    ;; Todo, for some cases iteration is faster, but is there any
    ;; heuristic for following this path that isn't itself too
    ;; expensive? Example where iteration is faster:
    ;; list1 is (1 2 3), list2 is (1 2 3 ... 1000)
    ;; ((and nil
    ;;       (setq member-fn (cdr (assq test list-utils-fast-member-fns))))
    ;;  (delq nil (mapcar #'(lambda (elt)
    ;;                        (unless (funcall member-fn elt list2)
    ;;                          elt))
    ;;                    list1)))
    (t
     (let ((saw (make-hash-table
                 :test (or test 'equal)
                 :size (or hint (safe-length list2)))))
       (mapc #'(lambda (elt)
                 (puthash elt t saw))
             list2)
       (delq nil (mapcar #'(lambda (elt)
                             (unless (gethash elt saw)
                               elt))
                         list1))))))

;;;###autoload
(defun list-utils-xor (list1 list2 &optional test hint flip)
  "Return elements which are only present in either LIST1 or LIST2.

This is similar to `cl-set-exclusive-or' (or `set-exclusive-or')
from the cl library, except that `list-utils-xor' preserves order,
and exhibits more predictable performance for large lists.  Order
will follow LIST1, then LIST2.  Duplicates may be present as in
LIST1 or LIST2.

TEST is an optional comparison function in the form of a
hash-table-test.  The default is `equal'.  Other valid values
include `eq' (built-in), `eql' (built-in), `list-utils-htt-='
\(numeric), `list-utils-htt-case-fold-equal' (case-insensitive).
See `define-hash-table-test' to define your own tests.

HINT is an optional micro-optimization, predicting the size of
the list to be hashed (LIST2 unless FLIP is set).

When optional FLIP is set, the sense of the comparison is
reversed, causing order and duplicates to follow LIST2, then
LIST1.

Performance: see notes under `list-utils-and'."
  (append (list-utils-not list1 list2 test hint flip)
          (list-utils-not list2 list1 test nil  flip)))

;;;###autoload
(defun list-utils-uniq (list &optional test hint)
  "Return a uniquified copy of LIST, preserving order.

This is similar to `cl-remove-duplicates' (or `remove-duplicates')
from the cl library, except that `list-utils-uniq' preserves order,
and exhibits more predictable performance for large lists.  Order
will follow LIST.

TEST is an optional comparison function in the form of a
hash-table-test.  The default is `equal'.  Other valid values
include `eq' (built-in), `eql' (built-in), `list-utils-htt-='
\(numeric), `list-utils-htt-case-fold-equal' (case-insensitive).
See `define-hash-table-test' to define your own tests.

HINT is an optional micro-optimization, predicting the size of
LIST.

Performance: see notes under `list-utils-and'."
  (let ((saw (make-hash-table
              :test (or test 'equal)
              :size (or hint (safe-length list)))))
    (delq nil (mapcar #'(lambda (elt)
                          (unless (gethash elt saw)
                            (progn
                              (puthash elt t saw)
                              elt)))
                      list))))

;;;###autoload
(defun list-utils-dupes (list &optional test hint)
  "Return only duplicated elements from LIST, preserving order.

Duplicated elements may still exist in the result: this function
removes singlets.

TEST is an optional comparison function in the form of a
hash-table-test.  The default is `equal'.  Other valid values
include `eq' (built-in), `eql' (built-in), `list-utils-htt-='
\(numeric), `list-utils-htt-case-fold-equal' (case-insensitive).
See `define-hash-table-test' to define your own tests.

HINT is an optional micro-optimization, predicting the size of
LIST.

Performance: see notes under `list-utils-and'."
  (let ((saw (make-hash-table
              :test (or test 'equal)
              :size (or hint (safe-length list)))))
    (mapc #'(lambda (elt)
              (puthash elt (if (gethash elt saw) 2 1) saw))
          list)
    (delq nil (mapcar #'(lambda (elt)
                          (when (> (gethash elt saw) 1)
                            elt))
                      list))))

;;;###autoload
(defun list-utils-singlets (list &optional test hint)
  "Return only singlet elements from LIST, preserving order.

Duplicated elements may not exist in the result.

TEST is an optional comparison function in the form of a
hash-table-test.  The default is `equal'.  Other valid values
include `eq' (built-in), `eql' (built-in), `list-utils-htt-='
\(numeric), `list-utils-htt-case-fold-equal' (case-insensitive).
See `define-hash-table-test' to define your own tests.

HINT is an optional micro-optimization, predicting the size of
LIST.

Performance: see notes under `list-utils-and'."
  (let ((saw (make-hash-table
              :test (or test 'equal)
              :size (or hint (safe-length list)))))
    (mapc #'(lambda (elt)
              (puthash elt (if (gethash elt saw) 2 1) saw))
          list)
    (delq nil (mapcar #'(lambda (elt)
                          (when (= (gethash elt saw) 1)
                            elt))
                      list))))

;;;###autoload
(defun list-utils-partition-dupes (list &optional test hint)
  "Partition LIST into duplicates and singlets, preserving order.

The return value is an alist with two keys: 'dupes and 'singlets.
The two values of the alist are lists which, if combined, comprise
a complete copy of the elements of LIST.

Duplicated elements may still exist in the 'dupes partition.

TEST is an optional comparison function in the form of a
hash-table-test.  The default is `equal'.  Other valid values
include `eq' (built-in), `eql' (built-in), `list-utils-htt-='
\(numeric), `list-utils-htt-case-fold-equal' (case-insensitive).
See `define-hash-table-test' to define your own tests.

HINT is an optional micro-optimization, predicting the size of
LIST.

Performance: see notes under `list-utils-and'."
  (let ((saw (make-hash-table
              :test (or test 'equal)
              :size (or hint (safe-length list)))))
    (mapc #'(lambda (elt)
              (puthash elt (if (gethash elt saw) 2 1) saw))
          list)
    (list (cons 'dupes
                (delq nil (mapcar #'(lambda (elt)
                                      (when (> (gethash elt saw) 1)
                                        elt))
                                  list)))
          (cons 'singlets
                (delq nil (mapcar #'(lambda (elt)
                                      (when (= (gethash elt saw) 1)
                                        elt))
                                  list))))))

;;; alists

;;;###autoload
(defun list-utils-alist-or-flat-length (list)
  "Count simple or cons-cell elements from the beginning of LIST.

Stop counting when a proper list of non-zero length is reached.

If the car of LIST is a list, return 0."
  (let ((counter 0))
    (ignore-errors
        (catch 'saw-depth
          (dolist (elt list)
            (when (and (consp elt)
                       (not (list-utils-cons-cell-p elt)))
              (throw 'saw-depth t))
            (incf counter))))
  counter))

;;;###autoload
(defun list-utils-alist-flatten (list)
  "Flatten LIST, which may contain other lists.  Do not flatten cons cells.

It is not guaranteed that the result contains *only* cons cells.
The result could contain other data types present in LIST.

This function simply avoids flattening single conses or improper
lists where the last two elements would be expressed as a dotted
pair."

  (cond

    ((null list)
     nil)

    ((and (listp list)
          (list-utils-cyclic-p list))
     (list-utils-alist-flatten (list-utils-make-linear-copy list)))

    ((list-utils-cons-cell-p list)
     list)

    ((and (listp list)
          (consp (car list))
          (not (list-utils-cons-cell-p (car list))))
     (append (list-utils-alist-flatten (car list))
             (list-utils-alist-flatten (cdr list))))

    ((listp list)
     (let ((extent (list-utils-alist-or-flat-length list)))
       (append (subseq list 0 extent)
               (list-utils-alist-flatten (nthcdr extent list)))))

    (t
     (list list))))

;;; plists

;;;###autoload
(defun list-utils-plist-reverse (plist)
  "Return reversed copy of property-list PLIST, maintaining pair associations."
  (assert (= 0 (% (length plist) 2)) nil "Not a PLIST")
  (loop for (a b) on (reverse plist) by 'cddr
        collect b
        collect a))

;;;###autoload
(defun list-utils-plist-del (plist prop)
  "Delete from PLIST the property PROP and its associated value.

When PROP is not present in PLIST, there is no effect.

The new plist is returned; use `(setq x (list-utils-plist-del x prop))'
to be sure to use the new value.

This functionality overlaps with the undocumented `cl-do-remf'."
  (let ((prop-pos (position prop plist)))
    (when (and prop-pos
               (= 0 (% prop-pos 2)))
      (callf cddr (nthcdr prop-pos plist))))
  plist)

(provide 'list-utils)

;;
;; Emacs
;;
;; Local Variables:
;; indent-tabs-mode: nil
;; mangle-whitespace: t
;; require-final-newline: t
;; coding: utf-8
;; byte-compile-warnings: (not cl-functions redefine)
;; End:
;;
;; LocalWords: ListUtils ARGS alist utils nconc tconc defstruct setf
;; LocalWords: plists PLIST setq autoloading plist callf alists
;; LocalWords: inplace
;;

;;; list-utils.el ends here
