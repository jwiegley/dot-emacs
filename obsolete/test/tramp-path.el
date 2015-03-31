;;; tramp-path.el --- Path parsing tests for tramp2

;; Copyright (C) 2001 by Daniel Pittman <daniel@rimspace.net>

;;; Code:
(push "." load-path)
(push "../lisp" load-path)
(load "tramp2.el")

;; Verify the path constructor.
(let ((simple	(make-tramp2-path (list (make-tramp2-connect 'one "one" "one")) "one"))
      (complex  (make-tramp2-path (list (make-tramp2-connect 'one "one" "one")
					(make-tramp2-connect 'two "two" "two")) "two")))
  (Assert (equal (tramp2-path-construct simple)  "/!:one|one@one::one"))
  (Assert (equal (tramp2-path-construct complex) "/!:one|one@one:two|two@two::two")))
  

;; Paths we don't own should signal an error.
(dolist (path '("test.file"
		"/tmp/test.file"
		"/melancholia:test.file"
		"/melancholia.rimspace.net:test.file"
		"/melancholia:/tmp/test.file"
		"/melancholia.rimspace.net:/tmp/test.file"))
  (eval `(Check-Error 'tramp2-file-error (tramp2-path-parse ,path))))


;; Paths with invalid syntax should signal an error.
(dolist (path '("/!::test.file"
		"/!:::test.file"
		"/!:|::test.file"
		"/!:@::test.file"
		"/!:|@::test.file"
		"/!:[]::test.file"
		"/!:[]|::test.file"
		"/!:[]@::test.file"))  
  (eval `(Check-Error 'tramp2-file-error (tramp2-path-parse 'path))))


;; Paths that actually work.
(dolist (data '("/!:melancholia::test.file"
		"/!:root@melancholia::test.file"
		"/!:ssh|melancholia::test.file"
		"/!:ssh|root@::test.file"
		"/!:ssh|root@melancholia::test.file"))
  (eval `(Assert (equal (tramp2-path-construct (tramp2-path-parse ,data)) ,data))))


;; Multi-hop paths.
(dolist (data '("/!:melancholia:melancholia::test.file"
		"/!:root@melancholia:root@melancholia::test.file"
		"/!:ssh|melancholia:ssh|melancholia::test.file"
		"/!:ssh|root@:ssh|root@::test.file"
		"/!:ssh|root@melancholia:ssh|root@melancholia::test.file"))
  (eval `(Assert (equal (tramp2-path-construct (tramp2-path-parse ,data)) ,data))))


;; Ensure that we read connections in the right order.
(Assert (equal (tramp2-path-parse "/!:one:two:three::test.file")
	       (make-tramp2-path (list (make-tramp2-connect nil nil "one")
				       (make-tramp2-connect nil nil "two")
				       (make-tramp2-connect nil nil "three"))
				 "test.file")))


(Assert (equal (tramp2-path-remote-file (tramp2-path-parse "/!:one::file:with:colon"))
	       "file:with:colon"))
