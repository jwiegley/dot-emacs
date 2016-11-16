;; coq-par-test.el --- tests for parallel compilation
;; Copyright (C) 2016 Hendrik Tews
;; Authors: Hendrik Tews
;; License:     GPL (GNU GENERAL PUBLIC LICENSE)
;; Maintainer: Hendrik Tews <hendrik@askra.de>
;;
;;; Commentary:
;;
;; This file file contains tests for `coq-par-job-needs-compilation'.
;; It specifies for all combinations of `coq-compile-quick', existing
;; files and relative file ages the required result and side effects
;; of `coq-par-job-needs-compilation'.
;;
;; Run the tests with
;; emacs -batch -L . -L ../generic -L ../lib -load coq-par-test.el
;;
;;; TODO:
;;
;; - integrate into PG build and test(?) system
;; - add tests for files with identical time stamps


(require 'coq-par-compile)

(defconst coq-par-job-needs-compilation-tests
  ;; for documentation see the doc string following the init value
  '(
    ;; present files   | compilation? | delete | 'req-obj-file | 'obj-mod-t
    ;; ====================================================================
    ;; all of src dep vo vio present
    ((src dep vo vio)
     (no-quick           nil            nil       vio            vio)
     (quick              nil            nil       vio            vio)
     (ensure-vo          nil            vio       vo             vo))

    ((src dep vio vo)
     (no-quick           nil            nil       vo             vo  )
     (quick              nil            nil       vo             vo  )
     (ensure-vo          nil            vio       vo             vo  ))

    ((src vo dep vio)    
     (no-quick           nil            vo        vio            vio )
     (quick              nil            vo        vio            vio )
     (ensure-vo          t              vio       vo             nil ))

    ((src vo vio dep)
     (no-quick           t              vio       vo             nil )
     (quick              t              vo        vio            nil )
     (ensure-vo          t              vio       vo             nil ))

    ((src vio dep vo)
     (no-quick           nil            vio       vo             vo  )
     (quick              nil            vio       vo             vo  )
     (ensure-vo          nil            vio       vo             vo  ))

    ((src vio vo dep)
     (no-quick           t              vio       vo             nil )
     (quick              t              vo        vio            nil )
     (ensure-vo          t              vio       vo             nil ))

    ;; present files   | compilation? | delete | 'req-obj-file | 'obj-mod-t
    ((dep src vio vo)
     (no-quick           nil            nil       vo             vo  )
     (quick              nil            nil       vo             vo  )
     (ensure-vo          nil            vio       vo             vo  ))

    ((dep src vo vio)
     (no-quick           nil            nil       vio            vio )
     (quick              nil            nil       vio            vio )
     (ensure-vo          nil            vio       vo             vo  ))

    ((dep vo vio src)
     (no-quick           t              vio       vo             nil )
     (quick              t              vo        vio            nil )
     (ensure-vo          t              vio       vo             nil ))

    ((dep vo src vio)
     (no-quick           nil            vo        vio            vio )
     (quick              nil            vo        vio            vio )
     (ensure-vo          t              vio       vo             nil ))

    ((dep vio vo src)
     (no-quick           t              vio       vo             nil )
     (quick              t              vo        vio            nil )
     (ensure-vo          t              vio       vo             nil  ))

    ((dep vio src vo)
     (no-quick           nil            vio       vo             vo  )
     (quick              nil            vio       vo             vo  )
     (ensure-vo          nil            vio       vo             vo  ))

    ((vo src dep vio)
     (no-quick           nil            vo        vio            vio )
     (quick              nil            vo        vio            vio )
     (ensure-vo          t              vio       vo             nil ))

    ;; present files   | compilation? | delete | 'req-obj-file | 'obj-mod-t
    ((vo src vio dep)
     (no-quick           t              vio       vo             nil )
     (quick              t              vo        vio            nil )
     (ensure-vo          t              vio       vo             nil ))

    ((vo dep src vio)
     (no-quick           nil            vo       vio             vio )
     (quick              nil            vo       vio             vio )
     (ensure-vo          t              vio       vo             nil ))

    ((vo dep vio src)
     (no-quick           t              vio       vo             nil )
     (quick              t              vo        vio            nil )
     (ensure-vo          t              vio       vo             nil ))

    ((vo vio src dep)
     (no-quick           t              vio      vo              nil )
     (quick              t              vo       vio             nil )
     (ensure-vo          t              vio       vo             nil ))

    ((vo vio dep src)
     (no-quick           t              vio      vo              nil )
     (quick              t              vo       vio             nil )
     (ensure-vo          t              vio       vo             nil ))

    ((vio src vo dep)
     (no-quick           t              vio      vo              nil )
     (quick              t              vo       vio             nil )
     (ensure-vo          t              vio       vo             nil ))

    ((vio src dep vo)
     (no-quick           nil            vio      vo              vo  )
     (quick              nil            vio      vo              vo  )
     (ensure-vo          nil            vio       vo             vo  ))

    ((vio dep vo src)
     (no-quick           t              vio      vo              nil )
     (quick              t              vo       vio             nil )
     (ensure-vo          t              vio       vo             nil ))

    ;; present files   | compilation? | delete | 'req-obj-file | 'obj-mod-t
    ((vio dep src vo)
     (no-quick           nil            vio      vo              vo  )
     (quick              nil            vio      vo              vo  )
     (ensure-vo          nil            vio       vo             vo  ))

    ((vio vo dep src)
     (no-quick           t              vio      vo              nil )
     (quick              t              vo       vio             nil )
     (ensure-vo          t              vio       vo             nil ))

    ((vio vo src dep)
     (no-quick           t              vio      vo              nil )
     (quick              t              vo       vio             nil )
     (ensure-vo          t              vio       vo             nil ))


    ;; only src dep vo present
    ((src dep vo)
     (no-quick           nil            nil      vo              vo  )
     (quick              nil            nil      vo              vo  )
     (ensure-vo          nil            nil      vo              vo  ))

    ((src vo dep)
     (no-quick           t              nil      vo              nil )
     (quick              t              vo       vio             nil )
     (ensure-vo          t              nil      vo              nil ))

    ((dep src vo)
     (no-quick           nil            nil      vo              vo  )
     (quick              nil            nil      vo              vo  )
     (ensure-vo          nil            nil      vo              vo  ))

    ((dep vo src)
     (no-quick           t              nil      vo              nil )
     (quick              t              vo       vio             nil )
     (ensure-vo          t              nil      vo              nil ))

    ((vo src dep)
     (no-quick           t              nil      vo              nil )
     (quick              t              vo       vio             nil )
     (ensure-vo          t              nil      vo              nil ))

    ((vo dep src)
     (no-quick           t              nil      vo              nil )
     (quick              t              vo       vio             nil )
     (ensure-vo          t              nil      vo              nil ))


    ;; present files   | compilation? | delete | 'req-obj-file | 'obj-mod-t
    ;; only src dep vio present
    ((src dep vio)
     (no-quick           nil            nil      vio             vio )
     (quick              nil            nil      vio             vio )
     (ensure-vo          t              vio       vo             nil ))

    ((src vio dep)
     (no-quick           t             vio       vo              nil )
     (quick              t             nil       vio             nil )
     (ensure-vo          t              vio       vo             nil ))

    ((dep src vio)
     (no-quick           nil           nil       vio             vio )
     (quick              nil           nil       vio             vio )
     (ensure-vo          t              vio       vo             nil ))

    ((dep vio src)
     (no-quick           t             vio       vo              nil )
     (quick              t             nil       vio             nil )
     (ensure-vo          t              vio       vo             nil ))

    ((vio src dep)
     (no-quick           t             vio       vo              nil )
     (quick              t             nil       vio             nil )
     (ensure-vo          t              vio       vo             nil ))

    ((vio dep src)
     (no-quick           t             vio       vo              nil )
     (quick              t             nil       vio             nil )
     (ensure-vo          t              vio       vo             nil ))


    ;; present files   | compilation? | delete | 'req-obj-file | 'obj-mod-t
    ;; only src vo vio present
    ((src vo vio)
     (no-quick           nil            nil      vio             vio )
     (quick              nil            nil      vio             vio )
     (ensure-vo          nil            vio       vo             vo  ))

    ((src vio vo)
     (no-quick           nil            nil      vo              vo  )
     (quick              nil            nil      vo              vo  )
     (ensure-vo          nil            vio       vo             vo  ))

    ((vo src vio)
     (no-quick           nil            vo       vio             vio )
     (quick              nil            vo       vio             vio )
     (ensure-vo          t              vio       vo             nil ))

    ((vo vio src)
     (no-quick           t              vio      vo              nil )
     (quick              t              vo       vio             nil )
     (ensure-vo          t              vio       vo             nil ))

    ((vio src vo)
     (no-quick           nil            vio      vo              vo  )
     (quick              nil            vio      vo              vo  )
     (ensure-vo          nil            vio      vo              vo  ))

    ((vio vo src)
     (no-quick           t              vio      vo              nil )
     (quick              t              vo       vio             nil )
     (ensure-vo          t              vio       vo             nil ))


    ;; present files   | compilation? | delete | 'req-obj-file | 'obj-mod-t
    ;; only src dep present
    ((src dep)
     (no-quick           t              nil      vo              nil )
     (quick              t              nil      vio             nil )
     (ensure-vo          t              nil      vo              nil ))

    ((dep src)
     (no-quick           t              nil      vo              nil )
     (quick              t              nil      vio             nil )
     (ensure-vo          t              nil      vo              nil ))


    ;; only src vo present
    ((src vo)
     (no-quick           nil            nil      vo              vo  )
     (quick              nil            nil      vo              vo  )
     (ensure-vo          nil            nil      vo              vo  ))

    ((vo src)
     (no-quick           t              nil      vo              nil )
     (quick              t              vo       vio             nil )
     (ensure-vo          t              nil      vo              nil ))


    ;; only src vio present
    ((src vio)
     (no-quick           nil            nil      vio             vio )
     (quick              nil            nil      vio             vio )
     (ensure-vo          t              vio       vo             nil ))

    ((vio src)
     (no-quick           t              vio      vo              nil )
     (quick              t              nil      vio             nil )
     (ensure-vo          t              vio       vo             nil ))


    ;; only src present
    ((src)
     (no-quick           t              nil      vo              nil )
     (quick              t              nil      vio             nil )
     (ensure-vo          t              nil      vo              nil ))
    )
  "Test and result specification for `coq-par-job-needs-compilation'.

List of tests. A test is a list of 4 elements. The first element,
a list, specifies the existing files and their relative age. In
there, `src' stands for the source (x.v) file, `dep' for
a (already compiled) dependency (dep.vo or dep.vio), `vo' for the
.vo file (x.vo) and `vio' for the .vio file (x.vio). A label in
the list denotes an existing file, a missing label a missing
file. The first element is the oldest file, the last element the
newest file.

Elements 2-4 of a test specify the results and side effects of
`coq-par-job-needs-compilation' for all setting of
`coq-compile-quick' on the file configuration described in
element 1. The options `quick-no-vio2vo' and `quick-and-vio2vo'
are specified together with label `quick'. Each result and side
effect specification (also called a variant in the source code
below) is itself a list of 5 elements. Element 1 is the value for
`coq-compile-quick', where `quick' denotes both `quick-no-vio2vo'
and `quick-and-vio2vo'. Element 2 specifies the result of
`coq-par-job-needs-compilation', nil for don't compile, t for do
compile. Elements 3-5 specify side effects. Element 3 which file
must be deleted, where nil means no file must be deleted. Element
4 specifies which file name must be stored in the
`required-obj-file' property of the job. This file will be used
as the compiled module library. In case compilation is
needed (element 2 equals t), this is the target of the
compilation. Element 5 specifies the file whose time stamp must
be stored in the `obj-mod-time' property of the job. A value of
nil there specifies that the `obj-mod-time' property should
contain nil. Element 5 is a bit superfluous, because it must be
set precisely when no compilation is needed (element 2 equals
nil) and then it must equal element 4.

This list contains 1 test for all possible file configuration and
relative ages.")

;; missing test cases for some objects with identical time stamp
;;
;; src-vo-dep-vio
;; 
;; src-vo-dep vio
;; vio src-vo-dep
;; src-vo-vio dep
;; dep src-vo-vio
;; src-dep-vio vo
;; vo src-dep-vio
;; vo-dep-vio src
;; src vo-dep-vio
;; 
;; src-vo dep-vio
;; dep-vio src-vo
;; src-dep vo-vio
;; vo-vio src-dep
;; src-vio vo-dep
;; vo-dep src-vio
;; 
;; src-vo dep vio
;; src-vo vio dep
;; dep src-vo vio
;; dep vio src-vo
;; vio src-vo dep
;; vio dep src-vo
;; 
;; src-dep vo vio
;; src-dep vio vo
;; vo src-dep vio
;; vo vio src-dep
;; vio src-dep vo
;; vio vo src-dep
;; 
;; src-vio vo dep
;; src-vio dep vo
;; vo src-vio dep
;; vo dep src-vio
;; dep src-vio vo
;; dep vo src-vio
;; 
;; vo-dep src vio
;; vo-dep vio src
;; src vo-dep vio
;; src vio vo-dep
;; vio vo-dep src
;; vio src vo-dep
;; 
;; vo-vio src dep
;; vo-vio dep src
;; src vo-vio dep
;; src dep vo-vio
;; dep vo-vio src
;; dep src vo-vio
;; 
;; dep-vio src vo
;; dep-vio vo src
;; src dep-vio vo
;; src vo dep-vio
;; vo dep-vio src
;; vo src dep-vio

(defun test-coq-par-test-data-invarint ()
  "Wellformedness check for the test specifications."
  (mapc
   (lambda (test)
     (let ((test-id (format "%s" (car test))))
       ;; a test is a list of 4 elements and the first element is a list itself
       (assert
	(and
	 (eq (length test) 4)
	 (listp (car test)))
	nil (concat test-id " 1"))
       (mapc
	(lambda (variant)
	  ;; a variant is a list of 5 elements
	  (assert (eq (length variant) 5) nil (concat test-id " 2"))
	  (let ((compilation-result (nth 1 variant))
		(delete-result (nth 2 variant))
		(req-obj-result (nth 3 variant))
		(obj-mod-result (nth 4 variant)))
	    ;; when the obj-mod-time field is set, it must be equal to
	    ;; the required-obj-file field
	    (assert (or (not obj-mod-result)
			(eq req-obj-result obj-mod-result))
		    nil (concat test-id " 3"))
	    (if compilation-result
		;; when compilation is t, obj-mod-time must be set
		(assert (not obj-mod-result) nil (concat test-id " 4"))
	      ;; when compilation? is nil, obj-mod-result must be nil
	      (assert obj-mod-result nil (concat test-id " 5")))
	    ;; the delete field, when set, must be a member of the files list
	    (assert (or (not delete-result)
			(member delete-result (car test)))
		    nil (concat test-id " 6"))))
	  (cdr test))))
   coq-par-job-needs-compilation-tests))

(defun test-coq-par-sym-to-file (dir sym)
  "Convert a test file symbol SYM to a file name in directory DIR."
  (let ((file (cond
	       ((eq sym 'src) "a.v")
	       ((eq sym 'dep) "dep.vo")
	       ((eq sym 'vo) "a.vo")
	       ((eq sym 'vio) "a.vio")
	       (t (assert nil)))))
    (concat dir "/" file)))

(defun test-coq-par-one-test (counter dir files variant dep-just-compiled)
  "Do one test for one specific `coq-compile-quick' value.

This function creates the files in DIR, sets up a job with the
necessary fields, calls `coq-par-job-needs-compilation-tests' and
test the result and side effects wth `assert'."
  (let ((id (format "%s: %s %s%s" counter (car variant) files
		    (if dep-just-compiled " just" "")))
	(job (make-symbol "coq-compile-job-symbol"))
	(module-vo-file (concat dir "/a.vo"))
	(quick-mode (car variant))
	(compilation-result (nth 1 variant))
	(delete-result (nth 2 variant))
	(req-obj-result (nth 3 variant))
	(obj-mod-result (nth 4 variant))
	result non-deleted-files)
    (message "test case %s" id)
    (ignore-errors
      (delete-directory dir t))
    (make-directory dir)
    (setq coq-compile-quick quick-mode)
    (put job 'vo-file module-vo-file)
    (put job 'src-file (coq-library-src-of-vo-file module-vo-file))
    (put job 'youngest-coqc-dependency '(0 0))
    (put job 'name id)
    ;; create files in order
    (mapc
     (lambda (sym)
       (let ((file (test-coq-par-sym-to-file dir sym)))
	 ;;(message "file create for %s: %s" sym file)
	 (with-temp-file file t)
	 (when (eq sym 'dep)
	   (put job 'youngest-coqc-dependency (nth 5 (file-attributes file))))
	 (unless (eq sym delete-result)
	   (push file non-deleted-files))
	 (sleep-for 0 10)
	 ))
     files)
    (when dep-just-compiled
      (put job 'youngest-coqc-dependency 'just-compiled))
    (setq result (coq-par-job-needs-compilation job))
    ;; check result
    (assert (eq result compilation-result)
	    nil (concat id " result"))
    ;; check file deletion
    (assert (or (not delete-result)
		(not (file-attributes
		      (test-coq-par-sym-to-file dir delete-result))))
	    nil (concat id " delete file"))
    ;; check no other file is deleted
    (mapc
     (lambda (f)
       (assert (file-attributes f)
	       nil (concat id " non del file " f)))
     non-deleted-files)
    ;; check value of 'required-obj-file property
    (assert (equal (get job 'required-obj-file)
		   (test-coq-par-sym-to-file dir req-obj-result))
	    nil (concat id " required-obj-file"))
    ;; check 'obj-mod-time property
    (if obj-mod-result
	(assert
	 (equal
	  (get job 'obj-mod-time)
	  (nth 5 (file-attributes
		  (test-coq-par-sym-to-file dir obj-mod-result))))
	 nil (concat id " obj-mod-time non nil"))
      (assert (not (get job 'obj-mod-time))
	      nil (concat id " obj-mod-time nil")))
    ;; check 'use-quick property
    (assert (eq (not (not (and compilation-result (eq req-obj-result 'vio))))
		(get job 'use-quick))
	    nil (concat id " use-quick"))))

(defvar test-coq-par-counter 0
  "Stupid counter.")

(defun test-coq-par-one-spec (dir files variant dep-just-compiled)
  "Run one test for one variant and split it for the 2 quick settings."
  (if (eq (car variant) 'quick)
      (progn
	(test-coq-par-one-test test-coq-par-counter dir files
			       (cons 'quick-no-vio2vo (cdr variant))
			       dep-just-compiled)
	(setq test-coq-par-counter (1+ test-coq-par-counter))
	(test-coq-par-one-test test-coq-par-counter dir files
			       (cons 'quick-and-vio2vo (cdr variant))
			       dep-just-compiled))
    (test-coq-par-one-test test-coq-par-counter dir files variant
			   dep-just-compiled))
  (setq test-coq-par-counter (1+ test-coq-par-counter)))

(defun test-coq-par-job-needs-compilation (dir)
  "Check test date wellformedness and run all the tests."
  (test-coq-par-test-data-invarint)
  (setq test-coq-par-counter 1)
  (mapc
   (lambda (test)
     (mapc
      (lambda (variant)
	(test-coq-par-one-spec dir (car test) variant nil)
	(when (eq (car (last (car test))) 'dep)
	  (test-coq-par-one-spec dir (car test) variant t)))
      (cdr test)))
   coq-par-job-needs-compilation-tests))

(condition-case err
    (progn
      (test-coq-par-job-needs-compilation (make-temp-name "/tmp/coq-par-test"))
      (message "test completed successfully"))
  (error
   (message "test failed with %s" err)
   (kill-emacs 1)))


(provide 'coq-par-test)

;;; coq-par-test.el ends here
