;;; Tests for pg-pgip.el

;; This file is part of Proof General.

;; Portions © Copyright 1994-2012  David Aspinall and University of Edinburgh
;; Portions © Copyright 2003, 2012, 2014  Free Software Foundation, Inc.
;; Portions © Copyright 2001-2017  Pierre Courtieu
;; Portions © Copyright 2010, 2016  Erik Martin-Dorel
;; Portions © Copyright 2011-2013, 2016-2017  Hendrik Tews
;; Portions © Copyright 2015-2017  Clément Pit-Claudel

;;; Commentary:
;;

;;; Code:

(pg-clear-test-suite "pg-pgip")
(pg-set-test-suite   "pg-pgip")

(pg-test-eval (pg-pgip-interpret-value "true" 'boolean) t)
(pg-test-eval (pg-pgip-interpret-value "false" 'boolean) nil)
(pg-test-eval (pg-pgip-interpret-value "27" 'integer) 27)
(pg-test-eval (pg-pgip-interpret-value "true" (list 'choice 'boolean 'integer)) t)
(pg-test-eval (pg-pgip-interpret-value "27" (list 'choice 'boolean 'integer)) 27)


(provide 'pg-pgip-test)
;; End of `pg-pgip-test.el'
