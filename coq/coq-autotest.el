;; coq-autotest.el: tests of Isar Proof General.
;;
;; You can run these by issuing "make devel.test.isar" in PG home dir.
;;
;; $Id$
;;

(require 'pg-autotest)

;; The included test files
(pg-autotest  message "Testing standard examples")
(pg-autotest script-wholefile "coq/example.v")
(pg-autotest script-wholefile "coq/example-x-symbol.v")
(pg-autotest script-wholefile "coq/ex-module.v")

(pg-autotest-quit-prover)
(pg-autotest-finished)


