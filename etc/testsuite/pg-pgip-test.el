;; Tests for pg-pgip.el
;;
;; $Id$

(pg-clear-test-suite "pg-pgip")
(pg-set-test-suite   "pg-pgip")

(pg-test-eval (pg-pgip-interpret-value "true" 'boolean) t)
(pg-test-eval (pg-pgip-interpret-value "false" 'boolean) nil)
(pg-test-eval (pg-pgip-interpret-value "27" 'integer) 27)
(pg-test-eval (pg-pgip-interpret-value "true" (list 'choice 'boolean 'integer)) t)
(pg-test-eval (pg-pgip-interpret-value "27" (list 'choice 'boolean 'integer)) 27)


