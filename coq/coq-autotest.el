;; coq-autotest.el: tests of Coq Proof General (in progress).
;;
;; You can run these by issuing "make test.coq" in PG home dir.
;;
;; $Id$
;;

(eval-when-compile
  (require 'cl))

(eval-when (compile)
  (require 'proof-site)
  (proof-ready-for-assistant 'coq))  

(require 'pg-autotest)

;; The included test files
(unless noninteractive
  (pg-autotest remark "Testing standard examples...")
  (pg-autotest script-wholefile "coq/example.v")
  (pg-autotest script-wholefile "coq/example-tokens.v")
  (pg-autotest script-wholefile "coq/ex-module.v")

  (pg-autotest quit-prover)
  (pg-autotest exit))
