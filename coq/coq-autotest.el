;; coq-autotest.el: tests of Coq Proof General (in progress).
;;
;; You can run these by issuing "make test.coq" in PG home dir.
;;
;; $Id$
;;

(require 'pg-autotest)

;; The included test files
(unless noninteractive
  (pg-autotest  message "Testing standard examples")
  (pg-autotest script-wholefile "coq/example.v")
  (pg-autotest script-wholefile "coq/example-tokens.v")
  (pg-autotest script-wholefile "coq/ex-module.v")

  (pg-autotest-quit-prover)
  (pg-autotest-finished))

