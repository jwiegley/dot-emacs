;; -*- lexical-binding: t; -*-
;;; heap.el --- Heap (a.k.a. priority queue) data structure

;; Copyright (C) 2004-2006, 2008, 2012-2013, 2017  Free Software Foundation, Inc

;; Author: Toby Cubitt <toby-predictive@dr-qubit.org>
;; Version: 0.5
;; Keywords: extensions, data structures, heap, priority queue
;; URL: http://www.dr-qubit.org/emacs.php
;; Repository: http://www.dr-qubit.org/git/predictive.git

;; This file is part of Emacs.
;;
;; GNU Emacs is free software: you can redistribute it and/or modify it under
;; the terms of the GNU General Public License as published by the Free
;; Software Foundation, either version 3 of the License, or (at your option)
;; any later version.
;;
;; GNU Emacs is distributed in the hope that it will be useful, but WITHOUT
;; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
;; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
;; more details.
;;
;; You should have received a copy of the GNU General Public License along
;; with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.


;;; Commentary:
;;
;; A heap is a form of efficient self-sorting tree. In particular, the root
;; node is guaranteed to be the highest-ranked entry in the tree. (The
;; comparison function used for ranking the data can, of course, be freely
;; defined). Therefore repeatedly removing the root node will return the data
;; in order of increasing rank. They are often used as priority queues, for
;; scheduling tasks in order of importance.
;;
;; This package implements ternary heaps, since they are about 12% more
;; efficient than binary heaps for heaps containing more than about 10
;; elements, and for very small heaps the difference is negligible. The
;; asymptotic complexity of ternary heap operations is the same as for a
;; binary heap: 'add', 'delete-root' and 'modify' operations are all O(log n)
;; on a heap containing n elements.
;;
;; Note that this package implements a heap as an implicit data structure on a
;; vector. Therefore, the maximum size of the heap has to be specified in
;; advance. Although the heap will grow dynamically if it becomes full, this
;; requires copying the entire heap, so insertion has worst-case complexity
;; O(n) instead of O(log n), though the amortized complexity is still
;; O(log n). (For applications where the maximum size of the heap is not known
;; in advance, an implementation based on binary trees might be more suitable,
;; but is not currently implemented in this package.)
;;
;; You create a heap using `make-heap', add elements to it using `heap-add',
;; delete and return the root of the heap using `heap-delete-root', and modify
;; an element of the heap using `heap-modify'. A number of other heap
;; convenience functions are also provided, all with the prefix
;; `heap-'. Functions with prefix `heap--' are for internal use only, and
;; should never be used outside this package.


;;; Code:

(eval-when-compile (require 'cl))

(defmacro heap--when-generators (then)
  "Evaluate THEN if `generator' library is available."
  (declare (debug t))
  (if (require 'generator nil 'noerror) then))


;;; ================================================================
;;;        Internal functions for use in the heap package

(defstruct (heap-
	    :named
	    (:constructor nil)
	    (:constructor heap--create
			  (cmpfun &optional (size 10) (resize 2)
			   &aux
			   (vect (make-vector size nil))
			   (count 0)))
	    (:copier nil))
  vect cmpfun count size resize)


(defun heap--child (heap i)    ; INTERNAL USE ONLY
  ;; Compare the 3 children of element I, and return element reference
  ;; of the smallest/largest (depending on whethen it's a min- or
  ;; max-heap).
  (let* ((vect (heap--vect heap))
	 (cmpfun (heap--cmpfun heap))
	 (count (heap--count heap))
	 (j nil) (k (* 3 i)))
    ;; Lots of if's in case I has less than three children.
    (if (>= (1+ k) count) nil
      (if (>= (+ 2 k) count) (1+ k)
	(setq j (if (funcall cmpfun (aref vect (1+ k))
			     (aref vect (+ 2 k)))
		    (1+ k) (+ 2 k)))
	(if (>= (+ 3 k) count) j
	  (if (funcall cmpfun (aref vect j) (aref vect (+ 3 k)))
	      j (+ 3 k)))))))


(defsubst heap--vswap (vect i j)   ; INTERNAL USE ONLY
  ;; Swap elements I and J of vector VECT.
  (let ((tmp (aref vect i)))
    (aset vect i (aref vect j))
    (aset vect j tmp) vect))


(defun heap--sift-up (heap n)   ; INTERNAL USE ONLY
  ;; Sift-up starting from element N of vector belonging to HEAP.
  (let* ((i n) (j nil) (vect (heap--vect heap)) (v (aref vect n)))
    ;; Keep moving element up until it reaches top or is smaller/bigger
    ;; than its parent.
    (while (and (> i 0)
		(funcall (heap--cmpfun heap) v
			 (aref vect (setq j (/ (1- i) 3)))))
      (heap--vswap vect i j)
      (setq i j))))


(defun heap--sift-down (heap n)   ; INTERNAL USE ONLY
  ;; Sift-down from element N of the heap vector belonging HEAP.
  (let* ((vect (heap--vect heap))
	(cmpfun (heap--cmpfun heap))
	(i n) (j (heap--child heap i))
	(v (aref vect n)))
    ;; Keep moving the element down until it reaches the bottom of the
    ;; tree or reaches a position where it is bigger/smaller than all
    ;; its children.
    (while (and j (funcall cmpfun (aref vect j) v))
      (heap--vswap vect i j)
      (setq i j)
      (setq j (heap--child heap i)))))



;;; ================================================================
;;;          The public functions which operate on heaps.

;;;###autoload
(defun make-heap
  (compare-function &optional initial-size resize-factor)
  "Create an empty heap with comparison function COMPARE-FUNCTION.

COMPARE-FUNCTION takes two arguments, A and B, and returns
non-nil or nil. To implement a max-heap, it should return non-nil
if A is greater than B. To implemenet a min-heap, it should
return non-nil if A is less than B.

Optional argument INITIAL-SIZE sets the initial size of the heap,
defaulting to 10. Optional argument RESIZE-FACTOR sets the factor
by which the heap's size is increased if it runs out of space,
defaulting to 2."
  ;; sadly, passing null values over-rides the defaults in the defstruct
  ;; `heap--create', so we have to explicitly set the defaults again
  ;; here
  (or initial-size (setq initial-size 10))
  (or resize-factor (setq resize-factor 2))
  (heap--create compare-function initial-size resize-factor))


;;;###autoload
(defalias 'heap-create 'make-heap)


(defun heap-copy (heap)
 "Return a copy of heap HEAP."
 (let ((newheap (heap--create (heap--cmpfun heap) (heap--size heap)
			      (heap--resize heap))))
   (setf (heap--vect newheap) (vconcat (heap--vect heap))
	 (heap--count newheap) (heap--count heap))
   newheap))


(defun heap-empty (heap)
  "Return t if the heap is empty, nil otherwise."
  (= 0 (heap--count heap)))


(defun heap-size (heap)
  "Return the number of entries in the heap."
  (heap--count heap))


(defun heap-compare-function (heap)
  "Return the comparison function for the heap HEAP."
  (heap--cmpfun heap))


(defun heap-add (heap data)
  "Add DATA to the heap, and return DATA."
  ;; Add data to bottom of heap and sift-up from bottom.
  (let ((count (heap--count heap))
	(size (heap--size heap))
	(vect (heap--vect heap)))
    ;; if there's no space left, grow the heap
    (if (< count size)
	(aset vect count data)
      (setf (heap--vect heap)
	    (vconcat (heap--vect heap) (vector data)
		     (make-vector
		      (1- (ceiling (* size (1- (heap--resize heap)))))
		      nil))
	    (heap--size heap)
	    (ceiling (* size (heap--resize heap)))))
    (setq count (setf (heap--count heap) (1+ (heap--count heap))))
    (heap--sift-up heap (1- count)))
  ;; return inserted data
  data)


(defun heap-root (heap)
  "Return the root of the heap, without removing it"
  (if (= (heap--count heap) 0) nil (aref (heap--vect heap) 0)))


(defun heap-delete-root (heap)
  "Return the root of the heap and delete it from the heap."
  (let ((vect (heap--vect heap))
	root count)
    ;; deal with empty heaps and heaps with just one element
    (if (= 0 (heap--count heap)) nil
      (setq root (aref vect 0)
	    count (decf (heap--count heap)))
      (if (= 0 count)
	  (setf (heap--vect heap) (make-vector 10 nil))
	;; delete root, swap last element to top, and sift-down from top
	(aset vect 0 (aref vect count))
	(aset vect count nil)
	(heap--sift-down heap 0))
      root)))


(defun heap-modify (heap match-function data)
  "Replace the first heap entry identified by MATCH-FUNCTION
with DATA, if a match exists. Return t if there was a match, nil
otherwise.

The function MATCH-FUNCTION should take one argument of the type
stored in the heap, and return non-nil if it should be modified,
nil otherwise.

Note that only the match highest up the heap is modified."
  (let ((vect (heap--vect heap))
	(count (heap--count heap))
	(i 0))
    ;; search vector for the first match
    (while (and (< i count)
		(not (funcall match-function (aref vect i))))
      (setq i (1+ i)))
    ;; if a match was found, modify it
    (if (< i count)
	(let ((olddata (aref vect i)))
	  (aset vect i data)
	  ;; if the new data is greater than old data, sift-up,
	  ;; otherwise sift-down
	  (if (funcall (heap--cmpfun heap) data olddata)
	      (heap--sift-up heap i)
	    (heap--sift-down heap i))
	  t)  ; return t if the match was successfully modified
      nil)))  ; return nil if no match was found


(defun heap-build (compare-function vec &optional resize-factor)
  "Build a heap from vector VEC with COMPARE-FUNCTION
as the comparison function.

Note that VEC is modified, and becomes part of the heap data
structure. If you don't want this, copy the vector first and pass
the copy in VEC.

COMPARE-FUNCTION takes two arguments, A and B, and returns
non-nil or nil. To implement a max-heap, it should return non-nil
if A is greater than B. To implemenet a min-heap, it should
return non-nil if A is less than B.

RESIZE-FACTOR sets the factor by which the heap's size is
increased if it runs out of space, defaulting to 2."
  (or resize-factor (setq resize-factor 2))
  (let ((heap (heap--create compare-function (length vec) resize-factor))
	(i (ceiling
	    (1- (expt 3 (ceiling (1- (log (1+ (* 2 (length vec))) 3))))) 2)))
    (setf (heap--vect heap) vec
	  (heap--count heap) (length vec))
    (while (>= (decf i) 0) (heap--sift-down heap i))
    heap))


(defun heap-merge (heap &rest heaps)
  "Merge HEAP with remaining HEAPS.

The merged heap takes the comparison function and resize-fector
of the first HEAP argument.

\(Note that in this heap implementation, the merge operation is
not very efficient, taking O(n) time for combined heap size n\)."
  (setq heaps (mapcar #'heap--vect heaps))
  (heap-build (heap--cmpfun heap)
	      (apply #'vconcat (heap--vect heap) heaps)
	      (heap--resize heap)))


(defun heap-clear (heap)
  "Remove all entries from HEAP.

Return number of entries removed."
  (prog1
      (heap--count heap)
    (setf (heap--vect heap) (make-vector (length (heap--vect heap)) nil)
          (heap--count heap) 0)))


(heap--when-generators
 (iter-defun heap-iter (heap)
   "Return a heap iterator object.

Calling `iter-next' on this object will retrieve the next element
from the heap. The heap itself is not modified.

\(Note that in this heap implementation, constructing a heap
iterator is not very efficient, taking O(n) time for a heap of
size n. Each call to `iter-next' on the other hand *is*
efficient, taking O(log n) time.\)"
   (let ((heap (heap-copy heap)))
     (while (not (heap-empty heap))
       (iter-yield (heap-delete-root heap))))))


(provide 'heap)

;;; heap.el ends here
