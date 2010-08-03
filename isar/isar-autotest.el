;; isar-autotest.el: tests of Isar Proof General.
;;
;; You can run these by issuing "make test.isar" in PG home dir.
;;
;; $Id$
;;

(eval-when-compile
  (require 'cl))

(eval-when (compile)
  (require 'proof-site)
  (proof-ready-for-assistant 'isar))  

(declare-function isar-tracing:auto-quickcheck-toggle "isar.el")
(declare-function isar-tracing:auto-solve-toggle "isar.el")

(require 'pg-autotest)

(unless noninteractive

  (pg-autotest log ".autotest.log")  ; convention

  (pg-autotest timestart 'total)

  (pg-autotest remark "Testing standard Example.thy, Example-Xsym.thy")
  (pg-autotest script-wholefile "isar/Example.thy")
  (pg-autotest script-wholefile "isar/Example-Tokens.thy")

  (pg-autotest remark "Larger files...")
  (pg-autotest eval (isar-tracing:auto-quickcheck-toggle 0))
  (pg-autotest eval (isar-tracing:auto-solve-toggle 0)) ; autosolve hammers this!
  (pg-autotest eval (proof-full-annotation-toggle 0))
  (pg-autotest script-wholefile "etc/isar/AHundredTheorems.thy")
  (pg-autotest script-wholefile "isar/ex/Tarski.thy")

  (pg-autotest remark "Testing random jumps")
  (pg-autotest script-randomjumps "isar/Example.thy" 5)
  (pg-autotest script-randomjumps "isar/ex/Tarski.thy" 10) ; better test?

  (pg-autotest remark "Testing restarting the prover")
  (pg-autotest quit-prover)

  (pg-autotest remark "Now in tokens mode")
  (pg-autotest eval (proof-unicode-tokens-toggle))
  (pg-autotest script-wholefile "isar/Example-Tokens.thy")


  (pg-autotest remark	         "Simple test of multiple file behaviour:")
  (pg-autotest script-wholefile  "etc/isar/multiple/C.thy")
  (pg-autotest assert-processed   "etc/isar/multiple/C.thy")
  (pg-autotest assert-processed   "etc/isar/multiple/A.thy")
  (pg-autotest assert-processed   "etc/isar/multiple/B.thy")
  (pg-autotest retract-file       "etc/isar/multiple/B.thy")
  (pg-autotest assert-unprocessed "etc/isar/multiple/B.thy")
  (pg-autotest assert-unprocessed "etc/isar/multiple/C.thy")
  (pg-autotest assert-processed   "etc/isar/multiple/A.thy")


  (pg-autotest quit-prover)
  
  (pg-autotest timetaken 'total)

  (pg-autotest exit)

  )
