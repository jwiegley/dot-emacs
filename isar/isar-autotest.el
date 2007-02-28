;; isar-autotest.el: tests of Isar Proof General.
;;
;; You can run these by issuing "make test.isar" in PG home dir.
;;
;; $Id$
;;

(require 'pg-autotest)

;; The included test files
(pg-autotest message "Testing standard Example.thy, Example-Xsym.thy")
(pg-autotest script-wholefile "isar/Example.thy")
(pg-autotest script-wholefile "isar/Example-Xsym.thy")

; These require Complex theory
;(pg-autotest script-wholefile "isar/Root2_Isar.thy")
;(pg-autotest script-wholefile "isar/Root2_Tactic.thy")

;; The standard simple multiple file examples

(pg-autotest message	       "Simple test of multiple files...")
(pg-autotest script-wholefile  "etc/isar/multiple/C.thy")
(pg-autotest assert-processed   "etc/isar/multiple/C.thy")
(pg-autotest assert-processed   "etc/isar/multiple/A.thy")
(pg-autotest assert-processed   "etc/isar/multiple/B.thy")
(pg-autotest retract-file      "etc/isar/multiple/B.thy")
(pg-autotest assert-unprocessed "etc/isar/multiple/B.thy")
(pg-autotest assert-unprocessed "etc/isar/multiple/C.thy")
(pg-autotest assert-processed   "etc/isar/multiple/A.thy")


(pg-autotest-quit-prover)
(pg-autotest-finished)


