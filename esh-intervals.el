;;; esh-intervals.el --- Collections of intervals: trees, bags, and document trees  -*- lexical-binding: t; -*-

;; Copyright (C) 2017  Clément Pit-Claudel

;; Author: Clément Pit-Claudel <clement.pitclaudel@live.com>
;; Keywords: data, internal

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; This file implements a successor to esh-interval-trees.el.  Roughly, the
;; history of ESH solutions to conflicting ranges is as follows (two ranges
;; conflict if they overlap and none of them is a subset of the other):
;;
;; * The very first releast did not construct a document tree: instead, it
;;   segmented text into ranges with consistent text properties, and rendered
;;   each range separately.  In this approach, there's no nesting: just a flat
;;   sequence of annotated segments.  This is very simple to implement, but it
;;   breaks e.g. boxes: that is, it renders <box>a<bold>b</bold></box> as
;;   <box>a</box<box+bold>b</box+bold>.  Unfortunately, that doesn't look right
;;   at all (it has two boxes instead of one).
;;
;; * The second release tried to tackle this by detecting conflicts using a
;;   doubly-linked list of <begin …> and <end …> events as a stack, and
;;   recording all conflicts by scanning from each <close> tag back to the
;;   corresponding <begin> tag.  Conflicts were then resolved one by one,
;;   according to a user-provided priority order.  Unfortunately, this approach
;;   ran into issues with conflicting intervals that started or ended at the
;;   same point.  The argument for its correctness wasn't very clear, either.
;;
;; * The third release introduced document trees (binary trees whose nodes
;;   contained annotations (property-value pairs) and whose leaves were text
;;   ranges).  Document trees were furthermore extended to include the leftmost
;;   and rightmost point covered by each node, allowing for easy splitting.
;;
;;   The algorithm proceeded by inserting each interval into the tree, starting
;;   with low-priority ones.  Most intervals would fit in the tree (either
;;   because they exactly subsumed an existing subtree, or because they were
;;   subsets of an existing interval with no conflicting children), but when an
;;   interval didn't fit the tree could be split into three parts, and the
;;   annotation of the newly added interval was applied to the middle part.
;;   Unfortunately, this still created spurious splits: a pathological case is
;;   described below:
;;
;;     > Suppose there's one interval a:5-15. Insert b:1-10, which splits a into
;;     > a1:5-10 and a2:10-15.  Then insert c:1-8, which splits a1 into a11:5-8
;;     > and a12:8-10, and b into b1:1-8 and b2:8-10.  But now b2 fits into a12,
;;     > and a11 fits in b1.  The trick is that inserting b1 and b2 into a1':5-8
;;     > a2':8-15 would not have required further splits.  In other words,
;;     > cutting a to accommodate b wasn't right, since b was going to be cut
;;     > later on, rendering the original cut useless.
;;
;; * This file (the 4th release) works somewhat differently.  At first, all
;;   intervals are collected in one large interval tree (implemented using an
;;   augmented binary tree).  This augmented tree is paired with an alternate
;;   representation of the same intervals — namely, a bag of intervals indexed
;;   by priority and starting position (note that there is at most one interval
;;   of each priority at each position).
;;
;;   In addition to insertion, the interval tree supports a “split” operation.
;;   Given an interval I, “split” finds all lower-priority intervals that
;;   conflict with I, and splits them to resolve conflicts.  Splitting can
;;   happen in-place: the left half of each split interval replaces the original
;;   interval, and the right part is accumulated into a list of new intervals
;;   (interestingly, these new intervals cannot themselves conflict with I —
;;   this is because any interval can have at most one conflict with any other
;;   interval).  The list of new intervals is then added to both the bag and the tree.
;;
;;   The bag's main purpose is to make it easy (and quick) to find all intervals
;;   of a given priority (the bag is implemented with one bucket per priority
;;   level, which is much simpler than maintaining a separate set of intervals
;;   ordered by priority).  This operation is crucial, because the algorithm
;;   proceeds by iterating over each priority bucket, and splitting the tree
;;   along each interval, in decreasing order of priority.  When this operation
;;   completes, the tree contains a set of properly nesting intervals, with no
;;   conflicts left.
;;
;;   The last step is to build a document tree from the list of all intervals.
;;   This is done by keeping a stack of intervals, and inserting each interval
;;   into the previous one, unless it doesn't fit in there.  If not, intervals
;;   are repeatedly popped from the stack, until one in which the current
;;   interval fits is found (intervals with no annotations are added as
;;   appropriate to ensure that all text ranges are covered by at least one
;;   children-less interval.  This process relies crucially on the order in
;;   which intervals are inserted, and since this order (start point, length,
;;   -priority) is a refinement of the order needed in the interval tree there
;;   is in fact no need for re-sorting (the tree itself is sorted according to
;;   that order).

;;; Code:

(require 'esh-assert)

(cl-declaim (optimize (speed 3) (safety 0)))

;;; Compatibility

(defun esh-intervals--< (&rest args) ;; FIXME remove this when 24.3 goes out of fashion
  "Emulation of (< ARGS...) for Emacs 24.3."
  (while (and (cdr args) (< (car args) (cadr args)))
    (pop args))
  (null (cdr args)))

(defun esh-intervals--<= (&rest args)
  "Emulation of (<= ARGS...) for Emacs 24.3."
  (while (and (cdr args) (<= (car args) (cadr args)))
    (pop args))
  (null (cdr args)))

;;; Intervals

(cl-defstruct
    (esh-intervals-int
     (:constructor nil)
     (:constructor esh-intervals-int (l r priority annot &aux (children nil))))
  l r priority annot children)

(defsubst esh-intervals--int-length-rev (int)
  "Compute the opposite of INT's length."
  (- (esh-intervals-int-l int) (esh-intervals-int-r int)))

(defsubst esh-intervals--int-priority-rev (int)
  "Compute the opposite of INT's priority."
  (- (esh-intervals-int-priority int)))

(defun esh-intervals--int-split (int x)
  "Truncate INT to X and return the second half."
  (prog1 (esh-intervals-int x (esh-intervals-int-r int) (esh-intervals-int-priority int) (esh-intervals-int-annot int))
    (setf (esh-intervals-int-r int) x)))

(defun esh-intervals--int-cut (to-cut ref)
  "Cut interval TO-CUT around interval REF."
  (cond
   ((esh-intervals--< (esh-intervals-int-l to-cut) (esh-intervals-int-l ref) (esh-intervals-int-r to-cut) (esh-intervals-int-r ref))
    (esh-intervals--int-split to-cut (esh-intervals-int-l ref)))
   ((esh-intervals--< (esh-intervals-int-l ref) (esh-intervals-int-l to-cut) (esh-intervals-int-r ref) (esh-intervals-int-r to-cut))
    (esh-intervals--int-split to-cut (esh-intervals-int-r ref)))
   (t nil)))

(defun esh-intervals-int-map-annots (filter annots)
  "Apply FILTER to each annotation pair in ANNOTS.
If FILTER returns NIL, the annotation is dropped from ANNOTS."
  (cond
   ((consp (car annots)) (delq nil (mapcar filter annots)))
   (annots (funcall filter annots))))

(eval-and-compile
  (defun esh-intervals--lexicographic-<-1 (x1 x2 getters)
    "Like `esh-intervals--lexicographic-<', but assume X1 and X2 are symbols.
GETTERS: See `esh-intervals--lexicographic-<'."
    (if (null getters) nil
      (let ((xx1 (make-symbol "xx1"))
            (xx2 (make-symbol "xx2")))
        `(let ((,xx1 (funcall ,(car getters) ,x1))
               (,xx2 (funcall ,(car getters) ,x2)))
           (or (< ,xx1 ,xx2)
               (and (= ,xx1 ,xx2)
                    ,(esh-intervals--lexicographic-<-1 x1 x2 (cdr getters)))))))))

(defmacro esh-intervals--lexicographic-< (x1 x2 &rest getters)
  "Compare X1 and X2 by each function in GETTERS.
These functions should return integers."
  (let ((s1 (make-symbol "x1"))
        (s2 (make-symbol "x2")))
    `(let ((,s1 ,x1)
           (,s2 ,x2))
       ,(esh-intervals--lexicographic-<-1 s1 s2 getters))))

(defun esh-intervals--int-< (int1 int2)
  "Compare INT1 and INT2.
Intervals are ordered by starting point (ascending),
length (ascending), and priority (descending)."
  (esh-intervals--lexicographic-< int1 int2 #'esh-intervals-int-l #'esh-intervals--int-length-rev #'esh-intervals--int-priority-rev))

;;; Documents trees
;; Documents trees are nested intervals (intervals with non-nil `children' lists).

(defun esh-intervals--doctree-fill-final-gap (doctree)
  "Ensure full coverage of DOCTREES range by its children.
This assumes that children of DOCTREE are in reverse order or
buffer position, and adds a text node if needed."
  (let ((children (esh-intervals-int-children doctree)))
    (when children
      (let* ((fill-from (esh-intervals-int-r (car children)))
             (fill-to (esh-intervals-int-r doctree)))
        (unless (= fill-from fill-to)
          (push (esh-intervals-int fill-from fill-to -1 nil) (esh-intervals-int-children doctree)))))))

(defun esh-intervals--doctree-add-child (doctree int)
  "Add INT to DOCTREE's children.
This also adds an intermediate text node if needed, to ensure
that DOCTREE's children are contiguous.  This assumes that
DOCTREE's children are stored in reverse order of buffer
position."
  (let* ((int-l (esh-intervals-int-l int))
         (last-child (car (esh-intervals-int-children doctree)))
         (doctree-rmost (if last-child (esh-intervals-int-r last-child) (esh-intervals-int-l doctree))))
    (unless (= doctree-rmost int-l)
      (push (esh-intervals-int doctree-rmost int-l -1 nil) (esh-intervals-int-children doctree)))
    (push int (esh-intervals-int-children doctree))))

(defun esh-intervals--doctree-nreverse-children (doctree)
  "Apply `nreverse' to all lists of children in DOCTREE."
  (dolist (child (cl-callf nreverse (esh-intervals-int-children doctree)))
    (esh-intervals--doctree-nreverse-children child)))

(defun esh-intervals--doctree-nreverse-annots (doctree)
  "Apply `nreverse' to all annotations in DOCTREE."
  (cl-callf nreverse (esh-intervals-int-annot doctree))
  (dolist (child (esh-intervals-int-children doctree))
    (esh-intervals--doctree-nreverse-annots child)))

(defun esh-intervals-doctree-map-annots (filter doctree)
  "Apply FILTER to attributes of each tag node in DOCTREE.
FILTER should not mutate annotations: they can be physically
shared between subtrees, and thus FILTER could end up being
called on already-processed annotations."
  (when doctree
    (dolist (tr (esh-intervals-int-children doctree))
      (esh-intervals-doctree-map-annots filter tr))
    (setf (esh-intervals-int-annot doctree)
          (esh-intervals-int-map-annots filter (esh-intervals-int-annot doctree)))))

;;; Bags of intervals

;; A bag of intervals is a vector of hashtables.  The vector is indexed by
;; priority.  The hashtables are indexed by left position.

(defsubst esh-intervals--bag-put-bucket (bucket int)
  "Insert INT into BUCKET."
  (puthash (esh-intervals-int-l int) int bucket))

(defsubst esh-intervals--bag-put (bag int)
  "Insert INT into BAG."
  (esh-intervals--bag-put-bucket (aref bag (esh-intervals-int-priority int)) int))

(defun esh-intervals--bag-from-intervals (intss)
  "Construct a bag from INTSS, a list of vectors of intervals."
  (let* ((priority 0)
         (nb-priorities (length intss))
         (bag (make-vector nb-priorities nil)))
    (dolist (ints intss)
      (let* ((nb-ints (length ints))
             (hashtbl (make-hash-table :test #'eq :size nb-ints)))
        (dotimes (int-idx nb-ints)
          (esh-intervals--bag-put-bucket hashtbl (aref ints int-idx)))
        (aset bag priority hashtbl))
      (cl-incf priority))
    bag))

;;; Trees of intervals

(cl-defstruct
    (esh-intervals-tree
     (:constructor nil)
     (:constructor esh-intervals-tree (int maxr l r)))
  int maxr l r)

(defmacro esh-intervals-tree-insert (tree int)
  "Insert INT into TREE (mutably)."
  (macroexp-let2 macroexp-copyable-p v int
    (gv-letplace (getter setter) tree
      (funcall setter `(esh-intervals--tree-insert-1 ,getter ,v)))))

(defun esh-intervals--tree-insert-1 (tree int)
  "Insert INT into TREE and return TREE."
  (if (null tree)
      (esh-intervals-tree int (esh-intervals-int-r int) nil nil)
    (setf (esh-intervals-tree-maxr tree) (max (esh-intervals-tree-maxr tree) (esh-intervals-int-r int)))
    (if (esh-intervals--int-< int (esh-intervals-tree-int tree))
        (esh-intervals-tree-insert (esh-intervals-tree-l tree) int)
      (esh-intervals-tree-insert (esh-intervals-tree-r tree) int))
    tree))

(defsubst esh-intervals--tree-compute-maxr (int l r)
  "Compute value of maxr field from INT, L, and R."
  (max (esh-intervals-int-r int)
       (if l (esh-intervals-tree-maxr l) most-negative-fixnum)
       (if r (esh-intervals-tree-maxr r) most-negative-fixnum)))

(defsubst esh-intervals--tree-update-maxr (tree)
  "Recompute TREE's `maxr' field."
  (setf (esh-intervals-tree-maxr tree)
        (esh-intervals--tree-compute-maxr (esh-intervals-tree-int tree) (esh-intervals-tree-l tree) (esh-intervals-tree-r tree))))

(defun esh-intervals--tree-from-sorted-intervals (ints beg end)
  "Make an interval tree from slice BEG .. END of sorted vector INTS."
  (when (< beg end)
    (let* ((mid (+ beg (/ (- end beg) 2)))
           (int (aref ints mid))
           (l (esh-intervals--tree-from-sorted-intervals ints beg mid))
           (r (esh-intervals--tree-from-sorted-intervals ints (1+ mid) end))
           (maxr (esh-intervals--tree-compute-maxr int l r)))
      (esh-intervals-tree int maxr l r))))

(defun esh-intervals--tree-from-intervals (ints)
  "Make an interval tree from INTS, a vector of intervals."
  (if (< emacs-major-version 25)
      (setq ints (vconcat (sort (append ints nil) #'esh-intervals--int-<)))
    (sort ints #'esh-intervals--int-<))
  (esh-intervals--tree-from-sorted-intervals ints 0 (length ints)))

(defun esh-intervals--tree-split-1 (tree bag int acc)
  "Cut intervals in TREE and BAG that conflict with INT.
ACC is a list of newly created intervals, augmented while
splitting TREE and finally returned.  It's OK to do this in two
phases, because a single interval can't conflict with with INT
twice (otherwise, it's be included in INT, or it would include
it.  Thus, the newly cut intervals can't conflict with INT."
  (when tree
    (unless (<= (esh-intervals-tree-maxr tree) (esh-intervals-int-l int))
      (setq acc (esh-intervals--tree-split-1 (esh-intervals-tree-l tree) bag int acc))
      (unless (<= (esh-intervals-int-r int) (esh-intervals-int-l (esh-intervals-tree-int tree)))
        (setq acc (esh-intervals--tree-split-1 (esh-intervals-tree-r tree) bag int acc)))
      (esh-intervals--tree-update-maxr tree))
    (when (< (esh-intervals-int-priority (esh-intervals-tree-int tree)) (esh-intervals-int-priority int))
      (let ((cut (esh-intervals--int-cut (esh-intervals-tree-int tree) int)))
        (when cut
          (push cut acc)))))
  acc)

(defun esh-intervals--tree-split (tree bag int)
  "Split lower-priority intervals of TREE and BAG that conflict with INT."
  (let ((added (esh-intervals--tree-split-1 tree bag int nil)))
    (dolist (int added)
      (esh-intervals--bag-put bag int)
      (esh-intervals-tree-insert tree int))))

(defun esh-intervals--tree-flatten-1 (tree acc)
  "Flatten TREE onto ACC."
  (if (null tree) acc
    (esh-intervals--tree-flatten-1 (esh-intervals-tree-l tree)
                      (cons (esh-intervals-tree-int tree)
                            (esh-intervals--tree-flatten-1 (esh-intervals-tree-r tree) acc)))))

(defun esh-intervals--tree-flatten (tree)
  "Flatten TREE."
  (esh-intervals--tree-flatten-1 tree nil))

;; Putting it all together

(defun esh-intervals--hash-table-values (table)
  "Accumulate all values of TABLE in a vector."
  (let ((offset -1)
        (vec (make-vector (hash-table-count table) nil)))
    (maphash (lambda (_ v) (aset vec (cl-incf offset) v)) table)
    vec))

(defun esh-intervals--shuffle (v)
  "Shuffle vector V (in place)."
  (let ((pos (1- (length v))))
    (while (> pos 0)
      (let ((target (random pos)))
        (cl-psetf (aref v pos) (aref v target)
                  (aref v target) (aref v pos)))
      (setq pos (1- pos))))
  v)

(defun esh-intervals--resolve-conflicts (tree bag)
  "Split intervals in TREE and BAG to resolve conflicts.
Conflicts happen when two intervals overlap and neither is
included in the other."
  (dotimes (n (length bag))
    ;; Iteration happens in reverse order of priority
    (let* ((ints-table (aref bag (- (length bag) n 1)))
           (ints (esh-intervals--shuffle (esh-intervals--hash-table-values ints-table))))
      (dotimes (pos (length ints))
        (esh-intervals--tree-split tree bag (aref ints pos))))))

(defun esh-intervals--reconstruct-doctree (intervals minl maxr merge-annots)
  "Reconstruct a tree from INTERVALS.
MINL .. MAXR is the range that all intervals are contained in.
INTERVALS is assumed to describe properly parenthesized
intervals; that is, there must not be conflicts between the
intervals.  It is also assumed to be sorted according to
`esh-intervals--int-<'.  When MERGE-ANNOTS is non-nil, intervals
that cover exactly the same ranges are merged (thus interval
annotations are in fact lists of annotations).  Otherwise, each
interval contains a single annotation."
  (let* ((root (esh-intervals-int minl maxr -1 nil))
         (stack (list root)))
    (dolist (int intervals)
      (let ((int-l (esh-intervals-int-l int))
            (int-r (esh-intervals-int-r int)))
        (while (<= (esh-intervals-int-r (car stack)) int-l)
          (esh-intervals--doctree-fill-final-gap (pop stack)))
        (let* ((top (car stack))
               (top-l (esh-intervals-int-l top))
               (top-r (esh-intervals-int-r top)))
          (if (and merge-annots (= int-l top-l) (= int-r top-r))
              ;; Same area covered: merge with parent (will be nreversed later)
              (push (esh-intervals-int-annot int) (esh-intervals-int-annot top))
            ;; Strict inclusion (and no conflicts)
            (esh-assert (esh-intervals--<= top-l int-l int-r top-r))
            (when merge-annots
              (cl-callf list (esh-intervals-int-annot int)))
            (esh-intervals--doctree-add-child top int)
            (push int stack)))))
    (while stack
      (esh-intervals--doctree-fill-final-gap (pop stack)))
    (when merge-annots
      (esh-intervals--doctree-nreverse-annots root))
    (esh-intervals--doctree-nreverse-children root)
    root))

(defun esh-intervals--make-int-vecs (intss)
  "Translate lists of intervals in INTSS to vectors of intervals.
Each source interval should be in the format (FROM TO (K . V))."
  (let ((priority 0)
        (int-vecs nil))
    (dolist (ints intss)
      (let ((ints-vec (vconcat ints)))
        (dotimes (int-idx (length ints-vec))
          (pcase-let ((`(,from ,to . ,annot) (aref ints-vec int-idx)))
            (aset ints-vec int-idx (esh-intervals-int from to priority annot))))
        (push ints-vec int-vecs))
      (cl-incf priority))
    (nreverse int-vecs)))

(defun esh-intervals--make-bag-and-tree (int-vecs)
  "Construct a tree and a bag from INT-VECS.
INT-VECT is a list of vectors of intervals, with one vector per
priority (that is, all intervals in the Nth vector of INT-VECS
are considered to have priority N)."
  (cons (esh-intervals--bag-from-intervals int-vecs)
        (esh-intervals--tree-from-intervals (apply #'vconcat int-vecs))))

(defun esh-intervals-make-doctree (intss minl maxr merge-annots)
  "Construct a document (a tree of tags) from INTSS.
MINL .. MAXR is the range that all intervals are contained in.
INTSS is a list of list of lists, (one list per priority, with
each sublist in the format (FORM TO (K . V))).  Conflicts in INTS
are resolved according to priority order implied by INTSS:
interval in earlier lists are broken to accommodate intervals in
later lists.  MERGE-ANNOTS determines how annotations are
rendered in the final document tree.  When non-nil, nodes contain
lists of annotations.  Otherwise, each node contains a single
annotation"
  (pcase-let ((`(,bag . ,tree) (esh-intervals--make-bag-and-tree (esh-intervals--make-int-vecs intss))))
    (esh-intervals--resolve-conflicts tree bag)
    (esh-intervals--reconstruct-doctree (esh-intervals--tree-flatten tree) minl maxr merge-annots)))

(provide 'esh-intervals)
;;; esh-intervals.el ends here
