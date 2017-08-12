;;; hol-light-autotest.el --- tests of HOL Light Proof General.

;; This file is part of Proof General.

;; Portions © Copyright 1994-2012  David Aspinall and University of Edinburgh
;; Portions © Copyright 2003, 2012, 2014  Free Software Foundation, Inc.
;; Portions © Copyright 2001-2017  Pierre Courtieu
;; Portions © Copyright 2010, 2016  Erik Martin-Dorel
;; Portions © Copyright 2011-2013, 2016-2017  Hendrik Tews
;; Portions © Copyright 2015-2017  Clément Pit-Claudel

;;; Commentary:
;;
;; You can run these by issuing "make test.hol-light" in PG home dir.
;;

;;; Code:

(eval-when-compile
  (require 'cl))

(require 'proof-site)
(proof-ready-for-assistant 'hol-light)

(require 'pg-autotest)

(unless (bound-and-true-p byte-compile-current-file)
  
  (pg-autotest start 'debug)
  (pg-autotest log ".autotest.log")  ; convention

  (pg-autotest timestart 'total)

  (pg-autotest remark "Testing standard examples...")

  (pg-autotest script-wholefile "hol-light/example.ml")

  (proof-shell-wait)


  (pg-autotest remark "Complete.")

  (pg-autotest timetaken 'total)

  (pg-autotest exit))
