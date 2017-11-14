;;; orgtbl-aggregate.el --- Create an aggregated Org table from another one

;; Copyright (C) 2013-2014  Thierry Banel

;; Author: Thierry Banel tbanelwebmin at free dot fr
;; Contributors: Michael Brand, Eric Abrahamsen
;; Version: 0.1
;; Keywords: org, table, aggregation, filtering

;; orgtbl-aggregate is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; orgtbl-aggregate is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:
;;
;; A new org-mode table is automatically updated,
;; based on another table acting as a data source
;; and user-given specifications for how to perform aggregation.
;;
;; Example:
;; Starting from a source table of activities and quantities
;; (whatever they are) over several days,
;; 
;; #+TBLNAME: original
;; | Day       | Color | Level | Quantity |
;; |-----------+-------+-------+----------|
;; | Monday    | Red   |    30 |       11 |
;; | Monday    | Blue  |    25 |        3 |
;; | Thuesday  | Red   |    51 |       12 |
;; | Thuesday  | Red   |    45 |       15 |
;; | Thuesday  | Blue  |    33 |       18 |
;; | Wednesday | Red   |    27 |       23 |
;; | Wednesday | Blue  |    12 |       16 |
;; | Wednesday | Blue  |    15 |       15 |
;; | Turdsday  | Red   |    39 |       24 |
;; | Turdsday  | Red   |    41 |       29 |
;; | Turdsday  | Red   |    49 |       30 |
;; | Friday    | Blue  |     7 |        5 |
;; | Friday    | Blue  |     6 |        8 |
;; | Friday    | Blue  |    11 |        9 |
;; 
;; an aggregation is built for each day (because several rows
;; exist for each day), typing C-c C-c
;; 
;; #+BEGIN: aggregate :table original :cols "Day mean(Level) sum(Quantity)"
;; | Day       | mean(Level) | sum(Quantity) |
;; |-----------+-------------+---------------|
;; | Monday    |        27.5 |            14 |
;; | Thuesday  |          43 |            45 |
;; | Wednesday |          18 |            54 |
;; | Turdsday  |          43 |            83 |
;; | Friday    |           8 |            22 |
;; #+END
;;
;; A wizard can be used:
;; M-x org-insert-dblock:aggregate
;;
;; Full documentation here:
;;   https://github.com/tbanel/orgaggregate/blob/master/README.org

;;; Requires:
(require 'calc-ext)
(require 'org-table)
(eval-when-compile (require 'cl-lib) (require 'cl))

;;; Code:

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Here is a bunch of useful utilities,
;; generic enough to be detached from the orgtbl-aggregate package.
;; For the time being, they are here.

(defun orgtbl-list-local-tables ()
  "Search for available tables in the current file."
  (interactive)
  (let ((tables))
    (save-excursion
      (save-restriction
	(widen)
	(goto-char (point-min))
	(while (re-search-forward "^[ \t]*#\\+tblname:[ \t]*\\(.*\\)" nil t)
	  (let ((text (match-string 1)))
	    (set-text-properties 0 (length text) () text)
	    (setq tables (cons text tables))))))
    tables))

(defun orgtbl-get-distant-table (name-or-id)
  "Find a table in the current buffer named NAME-OR-ID
and returns it as a lisp list of lists.
An horizontal line is translated as the special symbol `hline'."
  (unless (stringp name-or-id)
    (setq name-or-id (format "%s" name-or-id)))
  (let (buffer loc id-loc tbeg form)
    (save-excursion
      (save-restriction
	(widen)
	(save-excursion
	  (goto-char (point-min))
	  (if (re-search-forward
	       (concat "^[ \t]*#\\+tblname:[ \t]*"
		       (regexp-quote name-or-id)
		       "[ \t]*$")
	       nil t)
	      (setq buffer (current-buffer) loc (match-beginning 0))
	    (setq id-loc (org-id-find name-or-id 'marker))
	    (unless (and id-loc (markerp id-loc))
	      (error "Can't find remote table \"%s\"" name-or-id))
	    (setq buffer (marker-buffer id-loc)
		  loc (marker-position id-loc))
	    (move-marker id-loc nil)))
	(with-current-buffer buffer
	  (save-excursion
	    (save-restriction
	      (widen)
	      (goto-char loc)
	      (forward-char 1)
	      (unless (and (re-search-forward "^\\(\\*+ \\)\\|[ \t]*|" nil t)
			   (not (match-beginning 1)))
		(user-error "Cannot find a table at NAME or ID %s" name-or-id))
	      (setq tbeg (point-at-bol))
	      (org-table-to-lisp))))))))

(defun orgtbl-get-header-distant-table (table)
"Return the header of TABLE as a list.
TABLE names a table in the same buffer.
The function takes care of possibly missing headers,
and in this case returns a list of $1, $2, $3... column names"
  (setq table (orgtbl-get-distant-table table))
  (while (eq 'hline (car table))
    (setq table (cdr table)))
  (if (memq 'hline table)
      (car table)
    (let ((i 0))
      (mapcar (lambda (x)
		(setq i (1+ i))
		(format "$%s" i))
	      (car table)))))

(defun orgtbl-insert-elisp-table (table)
  "Insert TABLE, which is a lisp list of lists,
into the current buffer, at the point location.
The list may contain the special symbol 'hline
to mean an horizontal line."
  (mapc (lambda (row)
	  (cond ((consp row)
		 (mapc (lambda (field)
			 (insert "| ")
			 (insert field))
		       row))
		((eq row 'hline)
		 (insert "|-"))
		(t (error "bad row in elisp table")))
	  (insert "\n"))
	table)
  (delete-char -1)
  (org-table-align))

(defun org-time-string-to-calc (orgdate)
  "Convert a string in Org-date format to Calc internal representation
Returns nil if parameter is not a date."
  (and (string-match org-ts-regexp0 orgdate)
       (math-parse-date (replace-regexp-in-string " *[a-z]*[.] *" " " orgdate))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The venerable Calc is used thoroughly by the Aggregate package.
;; A few bugs were found.
;; The fixes are here for the time being

(require 'calc-arith)

(defun math-max-list (a b)
  (if b
      (if (or (Math-anglep (car b)) (eq (caar b) 'date)
	      (and (eq (car (car b)) 'intv) (math-intv-constp (car b)))
	      (math-infinitep (car b)))
	  (math-max-list (math-max a (car b)) (cdr b))
	(math-reject-arg (car b) 'anglep))
    a))

(defun math-min-list (a b)
  (if b
      (if (or (Math-anglep (car b)) (eq (caar b) 'date)
	      (and (eq (car (car b)) 'intv) (math-intv-constp (car b)))
	      (math-infinitep (car b)))
	  (math-min-list (math-min a (car b)) (cdr b))
	(math-reject-arg (car b) 'anglep))
    a))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The Aggregation package

;; this variable becomes true if there is at least one column
;; which is designated with a true name,
;; other than $1, $2, $3 ...
(defvar orgtbl-to-aggregated-table-has-header)

(defun orgtbl-to-aggregated-table-colname-to-int (colname table &optional err)
  "Convert the column name into an integer (first column is numbered 1)
COLNAME may be:
- a dollar form, like $5 which is converted to 5
- an alphanumeric name which appears in the column header (if any)
- the special symbol `hline' which is converted into 0
When COLNAME does not match any actual column,
an error is generated if ERR optional parameter is true
otherwise nil is returned.
Side-effect: the `ORGTBL-TO-AGGREGATED-TABLE-HAS-HEADER' variable is set
to true if COLNAME looks like the name of a column in the table 1st row.
"
  (if (symbolp colname)
      (setq colname (symbol-name colname)))
  ;; skip first hlines if any
  (while (not (listp (car table)))
    (setq table (cdr table)))
  (cond ((equal colname "hline")
	 0)
	((string-match "^\\$\\([0-9]+\\)$" colname)
	 (let ((n (string-to-number (match-string 1 colname))))
	   (if (<= n (length (car table)))
	       n
	     (if err
		 (user-error "Column %s outside table" colname)
	       nil))))
	(t
	 (setq orgtbl-to-aggregated-table-has-header t)
	 ;; orgtbl-to-aggregated-table-has-header set to true
	 ;; because of a column name other than $N
	 (let ((i 0)
	       (j ()))
	   (mapc (lambda (h)
		   (setq i (1+ i))
		   (if (equal h colname)
		       (setq j i)))
		 (car table))
	   (and
	    (not j)
	    err
	    (user-error "Column %s not found in table" colname))
	   j))))

(defun orgtbl-to-aggregated-replace-colnames (table expression)
  "Replace occurrences of column names in EXPRESSION
with forms like (nth N row), N being the numbering of columns.
Doing so, the EXPRESSION is ready to be computed against a table row."
  (cond
   ((listp expression)
    (cons (car expression)
	  (mapcar (lambda (x)
		    (orgtbl-to-aggregated-replace-colnames table x))
		  (cdr expression))))
   ((numberp expression)
    expression)
   (t
    (let ((n (orgtbl-to-aggregated-table-colname-to-int expression table)))
      (if n
	  (list 'nth n 'row)
	expression)))))

(defun orgtbl-to-aggregated-table-parse-spec (column table)
  "Parse a COLUMN specification for valid aggregation forms.
In the process, replace source column names with numbers starting from 1,
or 0 for the special 'hline column."
  (let ((validid1
	 '(sum mean meane gmean hmean sdev pvar psdev min max median prod list))
	(validid2
	 '(sum mean meane gmean hmean sdev pvar psdev min max median cov pcov corr))
	id)
    (cond
     ((string-match "^count()$" column)
      'count)
     ((string-match "^\\([[:word:]]+\\)(\\([[:word:]0-9_$]+\\))$" column)
      (setq id (intern (match-string 1 column)))
      (unless (memq id validid1)
	(error
	 "Bad column specification in orgtbl-to-aggregated-table : %s"
	 column))
      (list id
	    (orgtbl-to-aggregated-table-colname-to-int
	     (match-string 2 column)
	     table
	     t)))
     ((string-match
       "^\\([[:word:]]+\\)(\\([[:word:]0-9_$]+\\)[*,]\\([[:word:]0-9_$]+\\))$"
       column)
      (setq id (intern (match-string 1 column)))
      (unless (memq id validid2)
	(error
	 "Bad column specification in orgtbl-to-aggregated-table : %s"
	 column))
      (let ((a (match-string 2 column))	; save matches in a & b
	    (b (match-string 3 column))); because (...-to-int ..) destroys them
	(list id
	      (orgtbl-to-aggregated-table-colname-to-int a table t)
	      (orgtbl-to-aggregated-table-colname-to-int b table t))))
     ((string-match "^\\([[:word:]0-9_$]+\\)$" column)
      (orgtbl-to-aggregated-table-colname-to-int
       (match-string 1 column)
       table
       t))
     (t (error
	 "Bad column specification in orgtbl-to-aggregated-table : %s"
	 column)))))

(defun orgtbl-to-aggregated-table-compare-rows (row1 row2 aggcols)
  "Are two rows from the source table equal
regarding the aggregation columns ?"
  (let ((ok t))
    (mapc (lambda (i)
	    (unless (or
		     (not (integerp i))
		     (equal (nth i row1) (nth i row2))
		     (setq ok nil))))
	  aggcols)
    ok))

(defun orgtbl-to-aggregated-table-add-group (groups row aggcols aggcond)
  "Add the source ROW to the GROUPS of rows.
If ROW fits a group within GROUPS, then it is added at the end
of this group. Otherwise a new group is added at the end of GROUPS,
containing this single ROW."
  (if (or (not aggcond)
	  (eval aggcond)) ;; this eval need the variable 'row to have a value
      (let ((found ()))
	(mapc (lambda (g)
		(when (orgtbl-to-aggregated-table-compare-rows
		       (car g)
		       row
		       aggcols)
		  (nconc g (list row))
		  (setq found t)))
	      (cdr groups))
	(unless found
	  (nconc groups (list (list row)))))))

(defun orgtbl-aggregate-read-calc-expr (expr)
  "Interpret a string as either an org date or a calc expression"
  (or (org-time-string-to-calc expr)
      (if (equal expr "") 'EMPTY)
      (let ((x (math-read-exprs expr)))
	  (unless (consp x) (error "not consp ?"))
	  (if (eq (car x) 'error)
	      (math-read-exprs "INPUT_ERROR")
	    (car x)))))

(defun orgtbl-aggregate-apply-calc-1arg-function (fun data)
  "Convert DATA, a lisp list of mathematical values, to a Calc
vector.  In the process, empty values are removed (rather than
interpreted as zero).  Then apply the Calc FUN the vectors.
Empty value is returned when not enough non-empty input is
available."
  (let ((vec))
    (mapc (lambda (x)
	    (unless (eq x 'EMPTY)
	      (push x vec)))
	  data)
    (push 'vec vec)
    (case fun
      (mean   (if (cdr  vec) (calcFunc-vmean   vec) ""))
      (meane  (if (cddr vec) (calcFunc-vmeane  vec) ""))
      (gmean  (if (cdr  vec) (calcFunc-vgmean  vec) ""))
      (hmean  (if (cdr  vec) (calcFunc-vhmean  vec) ""))
      (median (if (cdr  vec) (calcFunc-vmedian vec) ""))
      (sum                   (calcFunc-vsum    vec))
      (min                   (calcFunc-vmin    vec))
      (max                   (calcFunc-vmax    vec))
      (prod                  (calcFunc-vprod   vec))
      (pvar   (if (cdr  vec) (calcFunc-vpvar   vec) ""))
      (sdev   (if (cddr vec) (calcFunc-vsdev   vec) ""))
      (psdev  (if (cdr  vec) (calcFunc-vpsdev  vec) "")))))

(defun orgtbl-aggregate-apply-calc-2args-function (fun data)
  "Convert DATA, a lisp list of mathematical values pairs, to two
Calc vectors.  In the process, pairs of empty values are
removed (rather than interpreted as zero).  If only one value in
a pair is empty, it is replaced by zero.  The resulting Calc
vectors have the same length.  Then apply the Calc FUN to those
two vectors.  Empty value is returned when there is not enough
non-empty input."
  (let ((veca)
	(vecb))
    (mapc (lambda (pair)
	    (if (and (eq (car pair) 'EMPTY)
		     (eq (cdr pair) 'EMPTY))
		nil
	      (push (if (eq (car pair) 'EMPTY) 0 (car pair)) veca)
	      (push (if (eq (cdr pair) 'EMPTY) 0 (cdr pair)) vecb)))
	  data)
    (push 'vec veca)
    (push 'vec vecb)
    (case fun
      (corr
       (if (cddr veca) ;; at least two non-empty value?
	   (calcFunc-vcorr veca vecb)
	 ""))
      (cov
       (if (cddr veca) ;; at least two non-empty value?
	   (calcFunc-vcov veca vecb)
	 ""))
      (pcov
       (if (cdr veca) ;; at least one non-empty value?
	   (calcFunc-vpcov veca vecb)
	 "")))))

(defun orgtbl-to-aggregated-table-do-sums (group aggcols)
  "Iterate over the rows in the GROUP
in order to apply the summations.
The result is a row compliant with the AGGCOLS columns specifications."
  (let ((sums (make-vector (length aggcols) ()))
	(i)
	(sum))
    (mapc
     (lambda (row)
       (setq i 0)
       (mapc
	(lambda (sc)
	  (if (consp sc)
	      (case (car sc)
		((mean meane gmean hmean median
		       sum min max prod
		       sdev pvar psdev
		       cov pcov corr)
		 (aset
		  sums
		  i
		  (cons 
		   (cond
		    ((null (cddr sc))
		     (orgtbl-aggregate-read-calc-expr (nth (cadr sc) row)))
		    ((memq (car sc) '(cov pcov corr))
		     (cons
		      (orgtbl-aggregate-read-calc-expr (nth (cadr  sc) row))
		      (orgtbl-aggregate-read-calc-expr (nth (caddr sc) row))))
		    (t
		     (math-mul
		      (orgtbl-aggregate-read-calc-expr (nth (cadr  sc) row))
		      (orgtbl-aggregate-read-calc-expr (nth (caddr sc) row)))))
		   (elt sums i))))
		(list
		 (aset sums i (cons (nth (cadr sc) row) (elt sums i))))
		(t (error "bad aggregation specification")))) ;; cannot happen
	  (setq i (1+ i)))
	aggcols))
     group)
    (setq i 0)
    (mapcar
     (lambda (sc)
       (setq sum (aref sums i))
       (setq i (1+ i))
       (let ((aggr
	      (cond
	       ((integerp sc)  (nth sc (car group)))
	       ((eq sc 'count) (number-to-string (length group)))
	       ((consp sc)
		(case (car sc)
		  ((mean meane gmean hmean median sum min max prod sdev pvar psdev)
		   (orgtbl-aggregate-apply-calc-1arg-function (car sc) sum))
		  ((cov pcov corr)  
		   (orgtbl-aggregate-apply-calc-2args-function (car sc) sum))
		  (list (format "%S" (reverse sum))))))))
	 (when (consp sc)
	   (unless (eq (car sc) 'corr) ; sometimes infinite loop on vcorr
	     (setq aggr (math-simplify (calcFunc-expand aggr))))
	   (case (car sc)
	     ((mean meane gmean hmean median
		    sum min max prod
		    sdev pvar psdev
		    cov pcov corr)
	      (let ((calc-date-format
		     '((YYYY "-" MM "-" DD " " www ". " hh ":" mm ":" ss))))
		(setq aggr (math-format-value aggr))))))
	 aggr))
     aggcols)))

(defun orgtbl-create-table-aggregated (table aggcolsorig aggcond)
  "Convert the source TABLE, which is a list of lists of cells,
into an aggregated table compliant with the AGGCOLSORIG columns specifications,
ignoring source rows which do not pass the AGGCOND."
  (if (stringp aggcolsorig)
      (setq aggcolsorig (split-string aggcolsorig)))
  (when aggcond
    (if (stringp aggcond)
	(setq aggcond (read aggcond)))
    (setq aggcond (orgtbl-to-aggregated-replace-colnames table aggcond)))
  ;; set to t by orgtbl-to-aggregated-table-colname-to-int
  (setq orgtbl-to-aggregated-table-has-header nil)
  (let* ((groups (list t)) ;; a single group is (t row1 row2 row3 ...)
	 (aggcols
	  (mapcar
	   (lambda (column)
	     (orgtbl-to-aggregated-table-parse-spec column table))
	   aggcolsorig))
	 (b 0)
	 (newtable))
    (when orgtbl-to-aggregated-table-has-header
      (pop table) ;; remove headers
      (if (and table (equal (car table) 'hline))
	  (pop table)))
    (mapc (lambda (row)
	    (cond ((equal row 'hline)
		   (setq b (1+ b)))
		  ((listp row)
		   (orgtbl-to-aggregated-table-add-group
		    groups
		    (cons (number-to-string b) row)
		    aggcols
		    aggcond))))
	  table)
    (setq newtable
	  (mapcar
	   (lambda (group)
	     (orgtbl-to-aggregated-table-do-sums group aggcols))
	   (cdr groups)))
    (cons aggcolsorig (cons 'hline newtable))))

;; aggregation in Push mode

;;;###autoload
(defun orgtbl-to-aggregated-table (table params)
  "Convert the orgtbl-mode TABLE to another orgtbl-mode table
with material aggregated.
Grouping of rows is done for identical values of grouping columns.
For each group, aggregation (sum, mean, etc.) is done for other columns.
  
The source table must contain sending directives with the following format:
#+ORGTBL: SEND destination orgtbl-to-aggregated-table :cols ... :cond ...

The destination must be specified somewhere in the same file
with a bloc like this:
  #+BEGIN RECEIVE ORGTBL destination
  #+END RECEIVE ORGTBL destination

:cols     gives the specifications of the resulting columns.
          It is a space-separated list of column specifications.
          Example:
             P Q sum(X) max(X) mean(Y)
          Which means:
             group rows with similar values in columns P and Q,
             and for each group, compute the sum of elements in
             column X, etc.

          The specification for a resulting column may be:
             COL              the name of a grouping column in the source table
             hline            a special name for grouping rows separated
                              by horizontal lines
             count()          give the number of rows in each group
             list(COL)        list the values of the column for each group
             sum(COL)         compute the sum of the column for each group
             sum(COL1*COL2)   compute the sum of the product of two columns
                              for each group
             mean(COL)        compute the average of the column for each group
             mean(COL1*COL2)  compute the average of the product of two columns
                              for each group
             meane(COL)       compute the average along with the estimated error
             hmean(COL)       compute the harmonic average
             gmean(COL)       compute the geometric average
             median(COL)      give the middle element after sorting them
             max(COL)         gives the largest element of each group
             min(COL)         gives the smallest element of each group
             sdev(COL)        compute the standard deviation (divide by N-1)
             psdev(COL)       compute the population standard deviation (divide by N)
             pvar(COL)        compute the variance
             prod(COL)        compute the product
             cov(COL1,COL2)   compute the covariance of two columns
                              for each group (divide by N-1)
             pcov(COL1,COL2)  compute the population covariance of two columns
                              for each group (/N)
             corr(COL1,COL2)  compute the linear correlation of two columns

:cond     optional
          a lisp expression to filter out rows in the source table
          when the expression evaluate to nil for a given row of the source table,
          then this row is discarded in the resulting table
          Example:
             (equal Q \"b\")
          Which means: keep only source rows for which the column Q has the value b

Columns in the source table may be in the dollar form,
for example $3 to name the 3th column,
or by its name if the source table have a header.
If all column names are in the dollar form,
the table is supposed not to have a header.
The special column name \"hline\" takes values from zero and up
and is incremented by one for each horizontal line.

Example:
add a line like this one before your table
,#+ORGTBL: SEND aggregatedtable orgtbl-to-aggregated-table :cols \"sum(X) q sum(Y) mean(Z) sum(X*X)\"
then add somewhere in the same file the following lines:
,#+BEGIN RECEIVE ORGTBL aggregatedtable
,#+END RECEIVE ORGTBL aggregatedtable
Type C-c C-c into your source table

Note:
 This is the 'push' mode for aggregating a table.
 To use the 'pull' mode, look at the org-dblock-write:aggregate function.
"
  (interactive)
  (orgtbl-to-generic
   (orgtbl-create-table-aggregated
    table
    (plist-get params :cols)
    (plist-get params :cond))
   (org-combine-plists
    (list :sep "|" :hline "|-" :lstart "|" :lend "|")
    params)))

;; aggregation in Pull mode

;;;###autoload
(defun org-dblock-write:aggregate (params)
  "Creates a table which is the aggregation of material from another table.
Grouping of rows is done for identical values of grouping columns.
For each group, aggregation (sum, mean, etc.) is done for other columns.

:table    name of the source table

:cols     gives the specifications of the resulting columns.
          It is a space-separated list of column specifications.
          Example:
             \"P Q sum(X) max(X) mean(Y)\"
          Which means:
             group rows with similar values in columns P and Q,
             and for each group, compute the sum of elements in
             column X, etc.

          The specification for a resulting column may be:
             COL              the name of a grouping column in the source table
             hline            a special name for grouping rows separated
                              by horizontal lines
             count()          give the number of rows in each group
             list(COL)        list the values of the column for each group
             sum(COL)         compute the sum of the column for each group
             sum(COL1*COL2)   compute the sum of the product of two columns
                              for each group
             mean(COL)        compute the average of the column for each group
             mean(COL1*COL2)  compute the average of the product of two columns
                              for each group
             meane(COL)       compute the average along with the estimated error
             hmean(COL)       compute the harmonic average
             gmean(COL)       compute the geometric average
             median(COL)      give the middle element after sorting them
             max(COL)         gives the largest element of each group
             min(COL)         gives the smallest element of each group
             sdev(COL)        compute the standard deviation (divide by N-1)
             psdev(COL)       compute the population standard deviation (divide by N)
             pvar(COL)        compute the variance
             prod(COL)        compute the product
             cov(COL1,COL2)   compute the covariance of two columns
                              for each group (divide by N-1)
             pcov(COL1,COL2)  compute the population covariance of two columns
                              for each group (/N)
             corr(COL1,COL2)  compute the linear correlation of two columns

:cond     optional
          a lisp expression to filter out rows in the source table
          when the expression evaluate to nil for a given row of the source table,
          then this row is discarded in the resulting table
          Example:
             (equal Q \"b\")
          Which means: keep only source rows for which the column Q has the value b

Columns in the source table may be in the dollar form,
for example $3 to name the 3th column,
or by its name if the source table have a header.
If all column names are in the dollar form,
the table is supposed not to have a header.
The special column name \"hline\" takes values from zero and up
and is incremented by one for each horizontal line.

Example:
- Create an empty dynamic block like this:
  #+BEGIN: aggregate :table originaltable :cols \"sum(X) Q sum(Y) mean(Z) sum(X*X)\"
  #+END
- Type C-c C-c over the BEGIN line
  this fills in the block with an aggregated table

Note:
 This is the 'pull' mode for aggregating a table.
 To use the 'push' mode, look at the orgtbl-to-aggregated-table function.
"
  (interactive)
  (orgtbl-insert-elisp-table
   (orgtbl-create-table-aggregated
    (orgtbl-get-distant-table (plist-get params :table))
    (plist-get params :cols)
    (plist-get params :cond)))
  (let ((formula (plist-get params :formula))
	(content (plist-get params :content))
	(recalc nil))
    (cond ((stringp formula)
	   (setq recalc t)
	   (end-of-line)
	   (insert "\n#+TBLFM: " formula))
	  ((and content
		(string-match "^\\([ \t]*#\\+tblfm:.*\\)" content))
	   (setq recalc t)
	   (end-of-line)
	   (insert "\n" (match-string 1 content))))
    (when recalc
      (forward-line -1)
      (org-table-recalculate 'all))))

(defvar orgtbl-aggregate-history-cols ())

;;;###autoload
(defun org-insert-dblock:aggregate ()
  "Wizard to interactively insert an aggregate dynamic block."
  (interactive)
  (let* ((table
	  (org-icompleting-read "Table name: " (orgtbl-list-local-tables)))
	 (header (orgtbl-get-header-distant-table table))
	 (aggcols
	  (read-string
	   (format
	    "columns %s: "
	    header)
	   nil 'orgtbl-aggregate-history-cols))
	 (aggcond
	  (read-string
	   (format
	    "condition (optional lisp function operating on %s): "
	    header)
	   nil 'orgtbl-aggregate-history-cols))
	 (params (list :name "aggregate" :table table :cols aggcols)))
    (unless (equal aggcond "")
      (nconc params (list :cond (read aggcond))))
    (org-create-dblock params)
    (org-update-dblock)))
  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The Transposition package

(defun orgtbl-create-table-transposed (table cols aggcond)
  "Convert the source TABLE, which is a list of lists of cells,
into a transposed table compliant with the COLS source columns list,
ignoring source rows which do not pass the AGGCOND.
If COLS is nil, all source columns are taken.
If AGGCOND is nil, all source rows are taken"
  (setq cols
        (if cols
            (mapcar
             (lambda (column)
	       (orgtbl-to-aggregated-table-colname-to-int column table t))
             cols)
          (let ((n 0))
            (mapcar
	     (lambda (x) (setq n (1+ n)))
	     (car table)))))
  (if aggcond
      (setq aggcond (orgtbl-to-aggregated-replace-colnames table aggcond)))
  (let ((result (mapcar (lambda (x) (list t)) cols))
        (nhline 0))
    (mapc
     (lambda (row)
       (if (eq row 'hline)
	   (setq nhline (1+ nhline))
	 (setq row (cons nhline row)))
       (when (or (eq row 'hline) (not aggcond) (eval aggcond))
	 (let ((r result))
	   (mapc
	    (lambda (spec)
	      (nconc (pop r) (list (if (eq row 'hline) "" (nth spec row)))))
	    cols))))
     table)
    (mapcar
     (lambda (row)
       (pop row)
       (let ((empty t))
         (mapc
	  (lambda (x) (if (equal "" x) () (setq empty nil)))
	  row)
         (if empty 'hline row)))
     result)))

;;;###autoload
(defun orgtbl-to-transposed-table (table params)
  "Convert the orgtbl-mode TABLE to a transposed version.
Rows become columns, columns become rows.

The source table must contain sending directives with the following format:
#+ORGTBL: SEND destination orgtbl-to-transposed-table :cols ... :cond ...

The destination must be specified somewhere in the same file
with a bloc like this:
  #+BEGIN RECEIVE ORGTBL destination
  #+END RECEIVE ORGTBL destination

:cols     optional, if omitted all source columns are taken.
          Columns specified here will become rows in the result.
          Valid specifications are
          - names as they appear in the first row of the source table
          - $N forms, starting from $1
          - the special hline column which is the numbering of
            blocks separated by horizontal lines in the source table

:cond     optional
          a lisp expression to filter out rows in the source table
          when the expression evaluate to nil for a given row of the source table,
          then this row is discarded in the resulting table
          Example:
             (equal Q \"b\")
          Which means: keep only source rows for which the column Q has the value b

Columns in the source table may be in the dollar form,
for example $3 to name the 3th column,
or by its name if the source table have a header.
If all column names are in the dollar form,
the table is supposed not to have a header.
The special column name \"hline\" takes values from zero and up
and is incremented by one for each horizontal line.

Horizontal lines are converted to empty columns,
and the other way around.

The destination must be specified somewhere in the same file
with a block like this:
  #+BEGIN RECEIVE ORGTBL destination_table_name
  #+END RECEIVE ORGTBL destination_table_name

Type C-c C-c in the source table to re-create the transposed version.

Note:
 This is the 'push' mode for transposing a table.
 To use the 'pull' mode, look at the org-dblock-write:transpose function.
"
  (interactive)
  (orgtbl-to-generic
   (orgtbl-create-table-transposed
    table
    (plist-get params :cols)
    (plist-get params :cond))
   (org-combine-plists
    (list :sep "|" :hline "|-" :lstart "|" :lend "|")
    params)))

;;;###autoload
(defun org-dblock-write:transpose (params)
  "Create a transposed version of the orgtbl TABLE
Rows become columns, columns become rows.

:table    names the source table

:cols     optional, if omitted all source columns are taken.
          Columns specified here will become rows in the result.
          Valid specifications are
          - names as they appear in the first row of the source table
          - $N forms, starting from $1
          - the special hline column which is the numbering of
            blocks separated by horizontal lines in the source table

:cond     optional
          a lisp expression to filter out rows in the source table
          when the expression evaluate to nil for a given row of the source table,
          then this row is discarded in the resulting table
          Example:
             (equal q \"b\")
          Which means: keep only source rows for which the column q has the value b

Columns in the source table may be in the dollar form,
for example $3 to name the 3th column,
or by its name if the source table have a header.
If all column names are in the dollar form,
the table is supposed not to have a header.
The special column name \"hline\" takes values from zero and up
and is incremented by one for each horizontal line.

Horizontal lines are converted to empty columns,
and the other way around.

- Create an empty dynamic block like this:
  #+BEGIN: aggregate :table originaltable
  #+END
- Type C-c C-c over the BEGIN line
  this fills in the block with the transposed table

Note:
 This is the 'pull' mode for transposing a table.
 To use the 'push' mode, look at the orgtbl-to-transposed-table function.
"
  (interactive)
  (orgtbl-insert-elisp-table
   (orgtbl-create-table-transposed
    (orgtbl-get-distant-table (plist-get params :table))
    (plist-get params :cols)
    (plist-get params :cond)))
  (let ((formula (plist-get params :formula))
	(content (plist-get params :content))
	(recalc nil))
    (cond ((stringp formula)
	   (setq recalc t)
	   (end-of-line)
	   (insert "\n#+TBLFM: " formula))
	  ((and content
		(string-match "^\\([ \t]*#\\+tblfm:.*\\)" content))
	   (setq recalc t)
	   (end-of-line)
	   (insert "\n" (match-string 1 content))))
    (when recalc
      (forward-line -1)
      (org-table-recalculate 'all))))

;;;###autoload
(defun org-insert-dblock:transpose ()
  "Wizard to interactively insert a transpose dynamic block."
  (interactive)
  (let* ((table
	  (org-icompleting-read "Table name: " (orgtbl-list-local-tables)))
         (header (orgtbl-get-header-distant-table table))
	 (aggcols
	  (read-string
	   (format
	    "columns (or empty for all) (source columns are %s): "
	    header)
	   nil 'orgtbl-aggregate-history-cols))
	 (aggcond
	  (read-string
	   (format
	    "condition (optional lisp function) (source columns %s): "
	    header)
	   nil 'orgtbl-aggregate-history-cols))
	 (params (list :name "transpose" :table table)))
    (unless (equal aggcols "")
      (nconc params (list :cols (read (format "(%s)" aggcols)))))
    (unless (equal aggcond "")
      (nconc params (list :cond (read aggcond))))
    (org-create-dblock params)
    (org-update-dblock)))

(provide 'orgtbl-aggregate)
;;; orgtbl-aggregate.el ends here
