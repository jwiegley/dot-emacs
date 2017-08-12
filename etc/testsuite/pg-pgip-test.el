;;; Tests for pg-pgip.el

;; This file is part of Proof General.

;; Portions © Copyright 1994-2012  David Aspinall and University of Edinburgh
;; Portions © Copyright 2003, 2012, 2014  Free Software Foundation, Inc.
;; Portions © Copyright 2001-2017  Pierre Courtieu
;; Portions © Copyright 2010, 2016  Erik Martin-Dorel
;; Portions © Copyright 2011-2013, 2016-2017  Hendrik Tews
;; Portions © Copyright 2015-2017  Clément Pit-Claudel

;; Proof General is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; Proof General is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with Proof General. If not, see <http://www.gnu.org/licenses/>.

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
