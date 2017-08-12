;;; coq-par-test.el --- tests for parallel compilation

;; This file is part of Proof General.

;; Portions © Copyright 1994-2012  David Aspinall and University of Edinburgh
;; Portions © Copyright 2003, 2012, 2014  Free Software Foundation, Inc.
;; Portions © Copyright 2001-2017  Pierre Courtieu
;; Portions © Copyright 2010, 2016  Erik Martin-Dorel
;; Portions © Copyright 2011-2013, 2016-2017  Hendrik Tews
;; Portions © Copyright 2015-2017  Clément Pit-Claudel

;; Authors: Hendrik Tews
;; Maintainer: Hendrik Tews <hendrik@askra.de>

;; License:     GPL (GNU GENERAL PUBLIC LICENSE)

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

;;; Code:

(require 'coq-par-compile)

(defconst coq--par-job-needs-compilation-tests
  ;; for documentation see the doc string following the init value
  '(
    ;; present files   | compilation? | delete | 'req-obj-file
    ;; ====================================================================
    ;; all of src dep vo vio present
    ((src dep vo vio)
     (no-quick           nil            nil       vo )
     (quick              nil            nil       vo )
     (ensure-vo          nil            vio       vo ))

    ((src dep vio vo)
     (no-quick           nil            nil       vio)
     (quick              nil            nil       vio)
     (ensure-vo          nil            nil       vo ))

    ((src vo dep vio)    
     (no-quick           nil            vo        vio)
     (quick              nil            vo        vio)
     (ensure-vo          t              nil       vo ))

    ((src vo vio dep)
     (no-quick           t              vio       vo )
     (quick              t              vo        vio)
     (ensure-vo          t              vio       vo ))

    ((src vio dep vo)
     (no-quick           nil            vio       vo )
     (quick              nil            vio       vo )
     (ensure-vo          nil            vio       vo ))

    ((src vio vo dep)
     (no-quick           t              vio       vo )
     (quick              t              vo        vio)
     (ensure-vo          t              vio       vo ))

    ;; present files   | compilation? | delete | 'req-obj-file
    ((dep src vio vo)
     (no-quick           nil            nil       vio)
     (quick              nil            nil       vio)
     (ensure-vo          nil            nil       vo ))

    ((dep src vo vio)
     (no-quick           nil            nil       vo )
     (quick              nil            nil       vo )
     (ensure-vo          nil            vio       vo ))

    ((dep vo vio src)
     (no-quick           t              vio       vo )
     (quick              t              vo        vio)
     (ensure-vo          t              vio       vo ))

    ((dep vo src vio)
     (no-quick           nil            vo        vio)
     (quick              nil            vo        vio)
     (ensure-vo          t              nil       vo ))

    ((dep vio vo src)
     (no-quick           t              vio       vo )
     (quick              t              vo        vio)
     (ensure-vo          t              vio       vo ))

    ((dep vio src vo)
     (no-quick           nil            vio       vo )
     (quick              nil            vio       vo )
     (ensure-vo          nil            vio       vo ))

    ((vo src dep vio)
     (no-quick           nil            vo        vio)
     (quick              nil            vo        vio)
     (ensure-vo          t              nil       vo ))

    ;; present files   | compilation? | delete | 'req-obj-file
    ((vo src vio dep)
     (no-quick           t              vio       vo )
     (quick              t              vo        vio)
     (ensure-vo          t              vio       vo ))

    ((vo dep src vio)
     (no-quick           nil            vo       vio )
     (quick              nil            vo       vio )
     (ensure-vo          t              nil       vo ))

    ((vo dep vio src)
     (no-quick           t              vio       vo )
     (quick              t              vo        vio)
     (ensure-vo          t              vio       vo ))

    ((vo vio src dep)
     (no-quick           t              vio      vo  )
     (quick              t              vo       vio )
     (ensure-vo          t              vio       vo ))

    ((vo vio dep src)
     (no-quick           t              vio      vo  )
     (quick              t              vo       vio )
     (ensure-vo          t              vio       vo ))

    ((vio src vo dep)
     (no-quick           t              vio      vo  )
     (quick              t              vo       vio )
     (ensure-vo          t              vio       vo ))

    ((vio src dep vo)
     (no-quick           nil            vio      vo  )
     (quick              nil            vio      vo  )
     (ensure-vo          nil            vio       vo ))

    ((vio dep vo src)
     (no-quick           t              vio      vo  )
     (quick              t              vo       vio )
     (ensure-vo          t              vio       vo ))

    ;; present files   | compilation? | delete | 'req-obj-file
    ((vio dep src vo)
     (no-quick           nil            vio      vo  )
     (quick              nil            vio      vo  )
     (ensure-vo          nil            vio       vo ))

    ((vio vo dep src)
     (no-quick           t              vio      vo  )
     (quick              t              vo       vio )
     (ensure-vo          t              vio       vo ))

    ((vio vo src dep)
     (no-quick           t              vio      vo  )
     (quick              t              vo       vio )
     (ensure-vo          t              vio       vo ))


    ;; only src dep vo present
    ((src dep vo)
     (no-quick           nil            nil      vo  )
     (quick              nil            nil      vo  )
     (ensure-vo          nil            nil      vo  ))

    ((src vo dep)
     (no-quick           t              nil      vo  )
     (quick              t              vo       vio )
     (ensure-vo          t              nil      vo  ))

    ((dep src vo)
     (no-quick           nil            nil      vo  )
     (quick              nil            nil      vo  )
     (ensure-vo          nil            nil      vo  ))

    ((dep vo src)
     (no-quick           t              nil      vo  )
     (quick              t              vo       vio )
     (ensure-vo          t              nil      vo  ))

    ((vo src dep)
     (no-quick           t              nil      vo  )
     (quick              t              vo       vio )
     (ensure-vo          t              nil      vo  ))

    ((vo dep src)
     (no-quick           t              nil      vo  )
     (quick              t              vo       vio )
     (ensure-vo          t              nil      vo  ))


    ;; present files   | compilation? | delete | 'req-obj-file
    ;; only src dep vio present
    ((src dep vio)
     (no-quick           nil            nil      vio )
     (quick              nil            nil      vio )
     (ensure-vo          t              nil       vo ))

    ((src vio dep)
     (no-quick           t             vio       vo  )
     (quick              t             nil       vio )
     (ensure-vo          t              vio       vo ))

    ((dep src vio)
     (no-quick           nil           nil       vio )
     (quick              nil           nil       vio )
     (ensure-vo          t              nil       vo ))

    ((dep vio src)
     (no-quick           t             vio       vo  )
     (quick              t             nil       vio )
     (ensure-vo          t              vio       vo ))

    ((vio src dep)
     (no-quick           t             vio       vo  )
     (quick              t             nil       vio )
     (ensure-vo          t              vio       vo ))

    ((vio dep src)
     (no-quick           t             vio       vo  )
     (quick              t             nil       vio )
     (ensure-vo          t              vio       vo ))


    ;; present files   | compilation? | delete | 'req-obj-file
    ;; only src vo vio present
    ((src vo vio)
     (no-quick           nil            nil       vo )
     (quick              nil            nil       vo )
     (ensure-vo          nil            vio       vo ))

    ((src vio vo)
     (no-quick           nil            nil       vio)
     (quick              nil            nil       vio)
     (ensure-vo          nil            nil       vo ))

    ((vo src vio)
     (no-quick           nil            vo       vio )
     (quick              nil            vo       vio )
     (ensure-vo          t              nil       vo ))

    ((vo vio src)
     (no-quick           t              vio      vo  )
     (quick              t              vo       vio )
     (ensure-vo          t              vio       vo ))

    ((vio src vo)
     (no-quick           nil            vio      vo  )
     (quick              nil            vio      vo  )
     (ensure-vo          nil            vio      vo  ))

    ((vio vo src)
     (no-quick           t              vio      vo  )
     (quick              t              vo       vio )
     (ensure-vo          t              vio       vo ))


    ;; present files   | compilation? | delete | 'req-obj-file
    ;; only src dep present
    ((src dep)
     (no-quick           t              nil      vo  )
     (quick              t              nil      vio )
     (ensure-vo          t              nil      vo  ))

    ((dep src)
     (no-quick           t              nil      vo  )
     (quick              t              nil      vio )
     (ensure-vo          t              nil      vo  ))


    ;; only src vo present
    ((src vo)
     (no-quick           nil            nil      vo  )
     (quick              nil            nil      vo  )
     (ensure-vo          nil            nil      vo  ))

    ((vo src)
     (no-quick           t              nil      vo  )
     (quick              t              vo       vio )
     (ensure-vo          t              nil      vo  ))


    ;; only src vio present
    ((src vio)
     (no-quick           nil            nil      vio )
     (quick              nil            nil      vio )
     (ensure-vo          t              nil       vo ))

    ((vio src)
     (no-quick           t              vio      vo  )
     (quick              t              nil      vio )
     (ensure-vo          t              vio       vo ))


    ;; only src present
    ((src)
     (no-quick           t              nil      vo  )
     (quick              t              nil      vio )
     (ensure-vo          t              nil      vo  ))

    ;; present files   | compilation? | delete | 'req-obj-file
    ;;
    ;; test cases for some objects with identical time stamp
    ;;
    ;; 4 files with same time stamp
    (((src vo dep vio))
     (no-quick           t              vio       vo )
     (quick              t              vo        vio)
     (ensure-vo          t              vio       vo ))

    ;; 3 files with same time stamp
    (((src vo dep) vio)
     (no-quick           nil            vo       vio )
     (quick              nil            vo       vio )
     (ensure-vo          t              nil       vo ))

    ((vio (src vo dep))
     (no-quick           t              vio      vo  )
     (quick              t              vo       vio )
     (ensure-vo          t              vio       vo ))

    (((src vo vio) dep)
     (no-quick           t              vio      vo  )
     (quick              t              vo       vio )
     (ensure-vo          t              vio       vo ))

    ((dep (src vo vio))
     (no-quick           t              vio      vo  )
     (quick              t              vo       vio )
     (ensure-vo          t              vio       vo ))

    (((src dep vio) vo)
     (no-quick           nil            vio      vo  )
     (quick              nil            vio      vo  )
     (ensure-vo          nil            vio       vo ))

    ;; present files   | compilation? | delete | 'req-obj-file
    ((vo (src dep vio))
     (no-quick           t              vio      vo  )
     (quick              t              vo       vio )
     (ensure-vo          t              vio       vo ))

    (((vo dep vio) src)
     (no-quick           t              vio      vo  )
     (quick              t              vo       vio )
     (ensure-vo          t              vio       vo ))

    ((src (vo dep vio))
     (no-quick           t              vio       vo )
     (quick              t              vo        vio)
     (ensure-vo          t              vio       vo ))

    ;; 2 times 2 files with same time stamp
    (((src vo) (dep vio))
     (no-quick           t              vio       vo )
     (quick              t              vo        vio)
     (ensure-vo          t              vio       vo ))

    (((dep vio) (src vo))
     (no-quick           t              vio       vo )
     (quick              t              vo        vio)
     (ensure-vo          t              vio       vo ))

    (((src dep) (vo vio))
     ;; could also use the vio as 'req-obj-file in the first 2 cases here
     (no-quick           nil            nil       vo )
     (quick              nil            nil       vo )
     (ensure-vo          nil            vio       vo ))

    (((vo vio) (src dep))
     (no-quick           t              vio       vo )
     (quick              t              vo        vio)
     (ensure-vo          t              vio       vo ))

    (((src vio) (vo dep))
     (no-quick           t              vio       vo )
     (quick              t              vo        vio)
     (ensure-vo          t              vio       vo ))

    ;; present files   | compilation? | delete | 'req-obj-file
    (((vo dep) (src vio))
     (no-quick           t              vio       vo )
     (quick              t              vo        vio)
     (ensure-vo          t              vio       vo ))

    ;; 2 files with same time stamp
    (((src vo) dep vio)
     (no-quick           nil            vo        vio)
     (quick              nil            vo        vio)
     (ensure-vo          t              nil       vo ))

    (((src vo) vio dep)
     (no-quick           t              vio       vo )
     (quick              t              vo        vio)
     (ensure-vo          t              vio       vo ))

    ((dep (src vo) vio)
     (no-quick           nil            vo        vio)
     (quick              nil            vo        vio)
     (ensure-vo          t              nil       vo ))

    ((dep vio (src vo))
     (no-quick           t              vio       vo )
     (quick              t              vo        vio)
     (ensure-vo          t              vio       vo ))

    ((vio (src vo) dep)
     (no-quick           t              vio       vo )
     (quick              t              vo        vio)
     (ensure-vo          t              vio       vo ))

    ((vio dep (src vo))
     (no-quick           t              vio       vo )
     (quick              t              vo        vio)
     (ensure-vo          t              vio       vo ))

    ;; present files   | compilation? | delete | 'req-obj-file
    (((src dep) vo vio)
     (no-quick           nil            nil       vo )
     (quick              nil            nil       vo )
     (ensure-vo          nil            vio       vo ))

    (((src dep) vio vo)
     (no-quick           nil            nil       vio)
     (quick              nil            nil       vio)
     (ensure-vo          nil            nil       vo ))

    ((vo (src dep) vio)
     (no-quick           nil            vo        vio)
     (quick              nil            vo        vio)
     (ensure-vo          t              nil       vo ))

    ((vo vio (src dep))
     (no-quick           t              vio       vo )
     (quick              t              vo        vio)
     (ensure-vo          t              vio       vo ))

    ((vio (src dep) vo)
     (no-quick           nil            vio      vo  )
     (quick              nil            vio      vo  )
     (ensure-vo          nil            vio       vo ))

    ((vio vo (src dep))
     (no-quick           t              vio       vo )
     (quick              t              vo        vio)
     (ensure-vo          t              vio       vo ))

    (((src vio) vo dep)
     (no-quick           t              vio       vo )
     (quick              t              vo        vio)
     (ensure-vo          t              vio       vo ))

    (((src vio) dep vo)
     (no-quick           nil            vio      vo  )
     (quick              nil            vio      vo  )
     (ensure-vo          nil            vio      vo  ))

    ((vo (src vio) dep)
     (no-quick           t              vio       vo )
     (quick              t              vo        vio)
     (ensure-vo          t              vio       vo ))

    ;; present files   | compilation? | delete | 'req-obj-file
    ((vo dep (src vio))
     (no-quick           t              vio       vo )
     (quick              t              vo        vio)
     (ensure-vo          t              vio       vo ))

    ((dep (src vio) vo)
     (no-quick           nil            vio      vo  )
     (quick              nil            vio      vo  )
     (ensure-vo          nil            vio       vo ))

    ((dep vo (src vio))
     (no-quick           t              vio       vo )
     (quick              t              vo        vio)
     (ensure-vo          t              vio       vo ))

    (((vo dep) src vio)
     (no-quick           nil            vo       vio )
     (quick              nil            vo       vio )
     (ensure-vo          t              nil       vo ))

    (((vo dep) vio src)
     (no-quick           t              vio       vo )
     (quick              t              vo        vio)
     (ensure-vo          t              vio       vo ))

    ((src (vo dep) vio)
     (no-quick           nil            vo        vio)
     (quick              nil            vo        vio)
     (ensure-vo          t              nil       vo ))

    ((src vio (vo dep))
     (no-quick           t              vio       vo )
     (quick              t              vo        vio)
     (ensure-vo          t              vio       vo ))

    ((vio (vo dep) src)
     (no-quick           t              vio       vo )
     (quick              t              vo        vio)
     (ensure-vo          t              vio       vo ))

    ((vio src (vo dep))
     (no-quick           t              vio       vo )
     (quick              t              vo        vio)
     (ensure-vo          t              vio       vo ))

    ;; present files   | compilation? | delete | 'req-obj-file
    (((vo vio) src dep)
     (no-quick           t              vio       vo )
     (quick              t              vo        vio)
     (ensure-vo          t              vio       vo ))

    (((vo vio) dep src)
     (no-quick           t              vio       vo )
     (quick              t              vo        vio)
     (ensure-vo          t              vio       vo ))

    ((src (vo vio) dep)
     (no-quick           t              vio       vo )
     (quick              t              vo        vio)
     (ensure-vo          t              vio       vo ))

    ((src dep (vo vio))
     ;; could also use the vio as 'req-obj-file in the first 2 cases here
     (no-quick           nil            nil       vo )
     (quick              nil            nil       vo )
     (ensure-vo          nil            vio       vo ))

    ((dep (vo vio) src)
     (no-quick           t              vio       vo )
     (quick              t              vo        vio)
     (ensure-vo          t              vio       vo ))

    ((dep src (vo vio))
     ;; could also use the vio as 'req-obj-file in the first 2 cases here
     (no-quick           nil            nil       vo )
     (quick              nil            nil       vo )
     (ensure-vo          nil            vio       vo ))

    (((dep vio) src vo)
     (no-quick           nil            vio      vo  )
     (quick              nil            vio      vo  )
     (ensure-vo          nil            vio       vo ))

    (((dep vio) vo src)
     (no-quick           t              vio       vo )
     (quick              t              vo        vio)
     (ensure-vo          t              vio       vo ))

    ((src (dep vio) vo)
     (no-quick           nil            vio      vo  )
     (quick              nil            vio      vo  )
     (ensure-vo          nil            vio       vo ))

    ;; present files   | compilation? | delete | 'req-obj-file
    ((src vo (dep vio))
     (no-quick           t              vio       vo )
     (quick              t              vo        vio)
     (ensure-vo          t              vio       vo ))

    ((vo (dep vio) src)
     (no-quick           t              vio       vo )
     (quick              t              vo        vio)
     (ensure-vo          t              vio       vo ))

    ((vo src (dep vio))
     (no-quick           t              vio       vo )
     (quick              t              vo        vio)
     (ensure-vo          t              vio       vo ))

    ;; 2 files with the same time stamp out of 3 files
    ;; without vio
    (((src dep vo))
     (no-quick           t              nil       vo )
     (quick              t              vo        vio)
     (ensure-vo          t              nil       vo ))

    (((src dep) vo)
     (no-quick           nil            nil      vo  )
     (quick              nil            nil      vo  )
     (ensure-vo          nil            nil      vo  ))

    ((vo (src dep))
     (no-quick           t              nil       vo )
     (quick              t              vo        vio)
     (ensure-vo          t              nil       vo ))

    (((src vo) dep)
     (no-quick           t              nil       vo )
     (quick              t              vo        vio)
     (ensure-vo          t              nil       vo ))

    ((dep (src vo))
     (no-quick           t              nil       vo )
     (quick              t              vo        vio)
     (ensure-vo          t              nil       vo ))

    (((dep vo) src)
     (no-quick           t              nil       vo )
     (quick              t              vo        vio)
     (ensure-vo          t              nil       vo ))

    ;; present files   | compilation? | delete | 'req-obj-file
    ((src (dep vo))
     (no-quick           t              nil       vo )
     (quick              t              vo        vio)
     (ensure-vo          t              nil       vo ))

    ;; without vo
    (((src dep vio))
     (no-quick           t              vio       vo )
     (quick              t              nil       vio)
     (ensure-vo          t              vio       vo ))

    (((src dep) vio)
     (no-quick           nil           nil       vio )
     (quick              nil           nil       vio )
     (ensure-vo          t              nil       vo ))

    ((vio (src dep))
     (no-quick           t              vio       vo )
     (quick              t              nil       vio)
     (ensure-vo          t              vio       vo ))

    (((src vio) dep)
     (no-quick           t              vio       vo )
     (quick              t              nil       vio)
     (ensure-vo          t              vio       vo ))

    ((dep (src vio))
     (no-quick           t              vio       vo )
     (quick              t              nil       vio)
     (ensure-vo          t              vio       vo ))

    (((dep vio) src)
     (no-quick           t              vio       vo )
     (quick              t              nil       vio)
     (ensure-vo          t              vio       vo ))

    ((src (dep vio))
     (no-quick           t              vio       vo )
     (quick              t              nil       vio)
     (ensure-vo          t              vio       vo ))

    ;; without dep
    (((src vio vo))
     (no-quick           t              vio       vo )
     (quick              t              vo        vio)
     (ensure-vo          t              vio       vo ))

    (((src vio) vo)
     (no-quick           nil            vio      vo  )
     (quick              nil            vio      vo  )
     (ensure-vo          nil            vio      vo  ))

    ((vo (src vio))
     (no-quick           t              vio       vo )
     (quick              t              vo        vio)
     (ensure-vo          t              vio       vo ))

    (((src vo) vio)
     (no-quick           nil            vo       vio )
     (quick              nil            vo       vio )
     (ensure-vo          t              nil       vo ))

    ;; present files   | compilation? | delete | 'req-obj-file
    ((vio (src vo))
     (no-quick           t              vio       vo )
     (quick              t              vo        vio)
     (ensure-vo          t              vio       vo ))

    (((vio vo) src)
     (no-quick           t              vio       vo )
     (quick              t              vo        vio)
     (ensure-vo          t              vio       vo ))

    ((src (vio vo))
     ;; could also use the vio as 'req-obj-file in the first 2 cases here
     (no-quick           nil            nil       vo )
     (quick              nil            nil       vo )
     (ensure-vo          nil            vio       vo ))

    ;; 2 files with identical time stamp out of 2 files
    (((src dep))
     (no-quick           t              nil      vo  )
     (quick              t              nil      vio )
     (ensure-vo          t              nil      vo  ))

    (((src vo))
     (no-quick           t              nil      vo  )
     (quick              t              vo       vio )
     (ensure-vo          t              nil      vo  ))

    (((src vio))
     (no-quick           t              vio      vo  )
     (quick              t              nil      vio )
     (ensure-vo          t              vio      vo  ))
    )
  "Test and result specification for `coq-par-job-needs-compilation'.

List of tests. A test is a list of 4 elements. The first element,
a list, specifies the existing files and their relative age. In
there, `src' stands for the source (x.v) file, `dep' for
a (already compiled) dependency (dep.vo or dep.vio), `vo' for the
.vo file (x.vo) and `vio' for the .vio file (x.vio). A label in
the list denotes an existing file, a missing label a missing
file. The first element is the oldest file, the last element the
newest file. A sublist specifies a set of files with identical
time stamps. For example, ``(src (vo vio) dep)'' specifies source
is older than .vo and .vio, .vo and .vio have identical last
modification time stamps and .vo and .vio are older than the
dependency.

Elements 2-4 of a test specify the results and side effects of
`coq-par-job-needs-compilation' for all setting of
`coq-compile-quick' on the file configuration described in
element 1. The options `quick-no-vio2vo' and `quick-and-vio2vo'
are specified together with label `quick'. Each result and side
effect specification (also called a variant in the source code
below) is itself a list of 4 elements. Element 1 is the value for
`coq-compile-quick', where `quick' denotes both `quick-no-vio2vo'
and `quick-and-vio2vo'. Element 2 specifies the result of
`coq-par-job-needs-compilation', nil for don't compile, t for do
compile. Elements 3-5 specify side effects. Element 3 which file
must be deleted, where nil means no file must be deleted. Element
4 specifies which file name must be stored in the
`required-obj-file' property of the job. This file will be used
as the compiled module library. In case compilation is
needed (element 2 equals t), this is the target of the
compilation.

This list contains 1 test for all possible file configuration and
relative ages.")

(defun coq-par-test-flatten-files (file-descr)
  "Flatten a file description test case list into a list of files."
  (let (result)
    (dolist (f file-descr result)
      (if (listp f)
	  (setq result (append f result))
	(push f result)))))

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
	  ;; a variant is a list of 4 elements
	  (assert (eq (length variant) 4) nil (concat test-id " 2"))
	  (let ((files (coq-par-test-flatten-files (car test)))
		(quick-mode (car variant))
		(compilation-result (nth 1 variant))
		(delete-result (nth 2 variant))
		(req-obj-result (nth 3 variant)))
	    ;; the delete field, when set, must be a member of the files list
	    (assert (or (not delete-result)
			(member delete-result files))
		    nil (concat test-id " 3"))
	    ;; 8.4 compatibility check
	    (when (and (or (eq quick-mode 'no-quick) (eq quick-mode 'ensure-vo))
		       (not (member 'vio files)))
	      (assert (not delete-result)
		      nil (concat test-id " 4"))
	      (assert (eq compilation-result
			  (not (eq (car (last (car test))) 'vo)))
		      nil (concat test-id " 5")))))
	  (cdr test))))
   coq--par-job-needs-compilation-tests))

(defun test-coq-par-sym-to-file (dir sym)
  "Convert a test file symbol SYM to a file name in directory DIR."
  (let ((file (cond
	       ((eq sym 'src) "a.v")
	       ((eq sym 'dep) "dep.vo")
	       ((eq sym 'vo) "a.vo")
	       ((eq sym 'vio) "a.vio")
	       (t (assert nil)))))
    (concat dir "/" file)))

(defun test-coq-par-one-test (counter dir file-descr variant dep-just-compiled)
  "Do one test for one specific `coq-compile-quick' value.

This function creates the files in DIR, sets up a job with the
necessary fields, calls `coq--par-job-needs-compilation-tests' and
test the result and side effects wth `assert'."
  (let ((id (format "%s: %s %s%s" counter (car variant) file-descr
		    (if dep-just-compiled " just" "")))
	(job (make-symbol "coq-compile-job-symbol"))
	(module-vo-file (concat dir "/a.vo"))
	(quick-mode (car variant))
	(compilation-result (nth 1 variant))
	(delete-result (nth 2 variant))
	(req-obj-result (nth 3 variant))
	(different-counter 5)
	(same-counter 5)
	(different-not-ok t)
	(same-not-ok t)
	(last-different-time-stamp '(0 0))
	(file-descr-flattened (coq-par-test-flatten-files file-descr))
	same-time-stamp file-list
	obj-mod-result result)
    (message "test case %s/576: %s %s%s" counter (car variant) file-descr
	     (if dep-just-compiled " just" ""))
    (when (not compilation-result)
      (setq obj-mod-result req-obj-result))
    (ignore-errors
      (delete-directory dir t))
    (make-directory dir)
    (setq coq-compile-quick quick-mode)
    (put job 'vo-file module-vo-file)
    (put job 'src-file (coq-library-src-of-vo-file module-vo-file))
    (put job 'youngest-coqc-dependency '(0 0))
    (put job 'name id)
    ;; create files in order
    (while different-not-ok
      ;; (message "enter different loop %s at %s"
      ;; 	       different-counter (current-time))
      (setq different-not-ok nil)
      (setq different-counter (1- different-counter))
      (assert (> different-counter 0)
	      nil "create files with different time stamps failed")
      (dolist (same-descr file-descr)
	(when (symbolp same-descr)
	  (setq same-descr (list same-descr)))
	(setq file-list
	      (mapcar (lambda (sym) (test-coq-par-sym-to-file dir sym))
		      same-descr))
	;; (message "try %s files %s" same-descr file-list)
	(setq same-counter 5)
	(setq same-not-ok t)
	(while same-not-ok
	  (setq same-counter (1- same-counter))
	  (assert (> same-counter 0)
		  nil "create files with same time stamp filed")
	  (dolist (file file-list)
	    (with-temp-file file t))
	  ;; check now that all the files in file-list have the same time stamp
	  (setq same-not-ok nil)
	  (setq same-time-stamp (nth 5 (file-attributes (car file-list))))
	  ;; (message "got first time stamp %s" same-time-stamp)
	  (dolist (file (cdr file-list))
	    (let ((ots (nth 5 (file-attributes file))))
	      ;; (message "got other time stamp %s" ots)
	      (unless (equal same-time-stamp ots)
		(setq same-not-ok t)))))
	;; (message "successful finished %s" same-descr)
	(when (member 'dep same-descr)
	  (put job 'youngest-coqc-dependency
	       (nth 5 (file-attributes (test-coq-par-sym-to-file dir 'dep)))))
	;; (message "XX %s < %s = %s"
	;; 	 last-different-time-stamp same-time-stamp
	;; 	 (time-less-p last-different-time-stamp same-time-stamp))
	(unless (time-less-p last-different-time-stamp same-time-stamp)
	  ;; error - got the same time stamp
	  ;; (message "unsuccsessful - need different retry")
	  (setq different-not-ok t))
	(setq last-different-time-stamp same-time-stamp)
	(sleep-for 0 15)))
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
    (dolist (f file-descr-flattened)
      (unless (eq f delete-result)
	(assert (file-attributes (test-coq-par-sym-to-file dir f))
		nil (format "%s non del file %s: %s"
			    id f
			    (test-coq-par-sym-to-file dir f)))))
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
	    nil (concat id " use-quick"))
    ;; check vio2vo-needed property
    (assert (eq
	     (and (eq quick-mode 'quick-and-vio2vo)
		  (eq req-obj-result 'vio)
		  (or (eq delete-result 'vo)
		      (not (member 'vo file-descr-flattened))))
	     (get job 'vio2vo-needed))
	    nil (concat id " vio2vo-needed wrong"))
    (ignore-errors
      (delete-directory dir t))))

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
  "Check test data wellformedness and run all the tests."
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
   coq--par-job-needs-compilation-tests))

(condition-case err
    (progn
      (test-coq-par-job-needs-compilation (make-temp-name "/tmp/coq-par-test"))
      (message "test completed successfully"))
  (error
   (message "test failed with %s" err)
   (kill-emacs 1)))


(provide 'coq-par-test)

;;; coq-par-test.el ends here
