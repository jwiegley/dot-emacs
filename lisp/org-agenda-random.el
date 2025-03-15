;;; -*- lexical-binding: t; -*-

;;; This code is by Aaron Harris from:
;;; https://emacs.stackexchange.com/questions/24270/org-mode-pick-random-task-from-custom-agenda-view
;;;
;;; Example use:
;;;
;;; '("d" "daily start"
;;;   ((agenda ""
;;;            ((org-agenda-span             'day)
;;;             (org-agenda-skip-function
;;;              '(org-agenda-skip-entry-if  'notregexp ":start:"))
;;;             (org-agenda-max-entries      5)
;;;             (org-agenda-cmp-user-defined (org-compare-randomly))
;;;             (org-compare-random-refresh  t)
;;;             (org-agenda-sorting-strategy '(user-defined-up))))))

(defun org-compare--get-marker (entry)
  "Return the marker for ENTRY.

This marker points to the location of the headline referenced by
ENTRY."
  (get-text-property 1 'org-marker entry))

(defvar org-compare-random-refresh nil
  "Whether `org-compare-randomly' should refresh its keys.

See the docs for `org-compare-randomly' for more information.")

(defun org-compare-randomly--update-sort-key (entry table generator)
  "Return sort key for ENTRY in TABLE, generating it if necessary.
For internal use by `org-compare-randomly-by'."
  (let* ((marker    (org-compare--get-marker entry))
         (hash-key  `(,(marker-buffer marker) . ,(marker-position marker))))
    (or (gethash hash-key table)
        (puthash hash-key (funcall generator entry) table))))

(defun org-compare-randomly-by (generator)
  "Return a random comparator using GENERATOR.

The comparator returned is like `org-compare-randomly', except
the distribution of random keys is controlled by GENERATOR and
may thus be non-uniform.

The function GENERATOR is called with a single argument, an
agenda entry, when that entry lacks a sort key.  It should return
a number, which is then used for all comparisons until the key
list is cleared; see `org-compare-randomly' for more details on
this.

Subsequent calls to `org-compare-randomly-by' produce comparators
with independent sets of sort keys."
  (let ((table (make-hash-table :test #'equal)))
    (lambda (x y)
      (when org-compare-random-refresh
        (clrhash table)
        (setq org-compare-random-refresh nil))
      (let ((x-val (org-compare-randomly--update-sort-key x table generator))
            (y-val (org-compare-randomly--update-sort-key y table generator)))
        (cond
         ((= x-val y-val)  nil)
         ((< x-val y-val)   -1)
         ((> x-val y-val)   +1))))))

(defun org-compare-randomly ()
  "Return a comparator implementing a random shuffle.

When given distinct agenda entries X and Y, the resulting
comparator has an equal chance of returning +1 and -1 (and a
miniscule chance of returning nil).  Subsequent calls will produce
results consistent with a total ordering.

To accomplish this, a hash table of randomly-generated sort keys
is maintained.  This table will persist until the comparator is
called when the variable `org-compare-random-refresh' is non-nil.
This means that setting this variable as part of a custom agenda
command using this comparator as `org-agenda-cmp-user-defined'
will cause the sort order to change whenever the agenda is
refreshed; otherwise, it will persist until Emacs is restarted.

Note that if you don't want the sort order to change on refresh,
you need to be careful that the comparator is created when the
custom agenda command is defined, not when it's called, e.g.

    (add-to-list
     'org-agenda-custom-commands
     `(\"y\" \"Example Agenda\"
       ((todo
         \"\"
         ((org-agenda-cmp-user-defined ',(org-compare-randomly))
          (org-agenda-sorting-strategy '(user-defined-up)))))))

\(Notice the use of backquote.)

Comparators resulting from different calls to this function have
independent key tables."
  (org-compare-randomly-by (lambda (_) (random))))

(provide 'org-agenda-random)
