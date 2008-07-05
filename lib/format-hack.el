
    (rear-nonsticky	(t	"idsubscript1")
			(t	"subscript1")
			(t	"superscript1"))))

(defun format-deannotate-region (from to translations next-fn)
  "Translate annotations in the region into text properties.
This sets text properties between FROM to TO as directed by the
TRANSLATIONS and NEXT-FN arguments.

NEXT-FN is a function that searches forward from point for an annotation.
It should return a list of 4 elements: \(BEGIN END NAME POSITIVE).  BEGIN and
END are buffer positions bounding the annotation, NAME is the name searched
for in TRANSLATIONS, and POSITIVE should be non-nil if this annotation marks
the beginning of a region with some property, or nil if it ends the region.
NEXT-FN should return nil if there are no annotations after point.

The basic format of the TRANSLATIONS argument is described in the
documentation for the `format-annotate-region' function.  There are some
additional things to keep in mind for decoding, though:

When an annotation is found, the TRANSLATIONS list is searched for a
text-property name and value that corresponds to that annotation.  If the
text-property has several annotations associated with it, it will be used only
if the other annotations are also in effect at that point.  The first match
found whose annotations are all present is used.

The text property thus determined is set to the value over the region between
the opening and closing annotations.  However, if the text-property name has a
non-nil `format-list-valued' property, then the value will be consed onto the
surrounding value of the property, rather than replacing that value.

There are some special symbols that can be used in the \"property\" slot of
the TRANSLATIONS list: PARAMETER and FUNCTION \(spelled in uppercase).
Annotations listed under the pseudo-property PARAMETER are considered to be
arguments of the immediately surrounding annotation; the text between the
opening and closing parameter annotations is deleted from the buffer but saved
as a string.

The surrounding annotation should be listed under the pseudo-property
FUNCTION.  Instead of inserting a text-property for this annotation,
the function listed in the VALUE slot is called to make whatever
changes are appropriate.  It can also return a list of the form
\(START LOC PROP VALUE) which specifies a property to put on.  The
function's first two arguments are the START and END locations, and
the rest of the arguments are any PARAMETERs found in that region.

Any annotations that are found by NEXT-FN but not defined by TRANSLATIONS
are saved as values of the `unknown' text-property \(which is list-valued).
The TRANSLATIONS list should usually contain an entry of the form
    \(unknown \(nil format-annotate-value))
to write these unknown annotations back into the file."
  (save-excursion
    (save-restriction
      (narrow-to-region (point-min) to)
      (goto-char from)
      (let (next open-ans todo loc unknown-ans)
	(while (setq next (funcall next-fn))
	  (let* ((loc      (nth 0 next))
		 (end      (nth 1 next))
		 (name     (nth 2 next))
		 (positive (nth 3 next))
		 (found    nil))

	    ;; Delete the annotation
	    (delete-region loc end)
	    (cond
	     ;; Positive annotations are stacked, remembering location
	     (positive (push `(,name ((,loc . nil))) open-ans))
	     ;; It is a negative annotation:
	     ;; Close the top annotation & add its text property.
	     ;; If the file's nesting is messed up, the close might not match
	     ;; the top thing on the open-annotations stack.
	     ;; If no matching annotation is open, just ignore the close.
	     ((not (assoc name open-ans))
	      (message "Extra closing annotation (%s) in file" name))
	     ;; If one is open, but not on the top of the stack, close
	     ;; the things in between as well.  Set `found' when the real
	     ;; one is closed.
	     (t
	      (while (not found)
		(let* ((top (car open-ans))	; first on stack: should match.
		       (top-name (car top))	; text property name
		       (top-extents (nth 1 top)) ; property regions
		       (params (cdr (cdr top)))	; parameters
		       (aalist translations)
		       (matched nil))
		  (if (equal name top-name)
		      (setq found t)
		    (message "Improper nesting in file."))
		  ;; Look through property names in TRANSLATIONS
		  (while aalist
		    (let ((prop (car (car aalist)))
			  (alist (cdr (car aalist))))
		      ;; And look through values for each property
		      (while alist
			(let ((value (car (car alist)))
			      (ans (cdr (car alist))))
			  (if (member top-name ans)
			      ;; This annotation is listed, but still have to
			      ;; check if multiple annotations are satisfied
			      (if (member nil (mapcar (lambda (r)
							(assoc r open-ans))
						      ans))
				  nil	; multiple ans not satisfied
				;; If there are multiple annotations going
				;; into one text property, split up the other
				;; annotations so they apply individually to
				;; the other regions.
				(setcdr (car top-extents) loc)
				(let ((to-split ans) this-one extents)
				  (while to-split
				    (setq this-one
					  (assoc (car to-split) open-ans)
					  extents (nth 1 this-one))
				    (if (not (eq this-one top))
					(setcar (cdr this-one)
						(format-subtract-regions
						 extents top-extents)))
				    (setq to-split (cdr to-split))))
				;; Set loop variables to nil so loop
				;; will exit.
				(setq alist nil aalist nil matched t
				      ;; pop annotation off stack.
				      open-ans (cdr open-ans))
				(let ((extents top-extents)
				      (start (car (car top-extents)))
				      (loc (cdr (car top-extents))))
				  (while extents
				    (cond
				     ;; Check for pseudo-properties
				     ((eq prop 'PARAMETER)
				      ;; A parameter of the top open ann:
				      ;; delete text and use as arg.
				      (if open-ans
					  ;; (If nothing open, discard).
					  (setq open-ans
						(cons
						 (append (car open-ans)
							 (list
							  (buffer-substring
							   start loc)))
						 (cdr open-ans))))
				      (delete-region start loc))
				     ((eq prop 'FUNCTION)
				      ;; Not a property, but a function.
				      (let ((rtn
					     (apply value start loc params)))
					(if rtn (push rtn todo))))
				     (t
				      ;; Normal property/value pair
				      (setq todo
					    (cons (list start loc prop value)
						  todo))))
				    (setq extents (cdr extents)
					  start (car (car extents))
					  loc (cdr (car extents))))))))
			(setq alist (cdr alist))))
		    (setq aalist (cdr aalist)))
		  (if (not matched)
		      ;; Didn't find any match for the annotation:
		      ;; Store as value of text-property `unknown'.
		      (let ((extents top-extents)
			    (start (car (car top-extents)))
			    (loc (or (cdr (car top-extents)) loc)))
			(while extents
			  (setq open-ans (cdr open-ans)
				todo (cons (list start loc 'unknown top-name)
					   todo)
				unknown-ans (cons name unknown-ans)
				extents (cdr extents)
				start (car (car extents))
				loc (cdr (car extents))))))))))))

	;; Once entire file has been scanned, add the properties.
	(while todo
	  (let* ((item (car todo))
		 (from (nth 0 item))
		 (to   (nth 1 item))
		 (prop (nth 2 item))
		 (val  (nth 3 item)))

	    (if (numberp val)	; add to ambient value if numeric
		(format-property-increment-region from to prop val 0)
	      (put-text-property
	       from to prop
	       (cond ((get prop 'format-list-valued) ; value gets consed onto
						     ; list-valued properties
		      (let ((prev (get-text-property from prop)))
			(cons val (if (listp prev) prev (list prev)))))
		     (t val))))) ; normally, just set to val.
	  (setq todo (cdr todo)))

	(if unknown-ans
	    (message "Unknown annotations: %s" unknown-ans))))))
