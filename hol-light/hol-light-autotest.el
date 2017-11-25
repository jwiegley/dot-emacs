;; hol-light-autotest.el: tests of HOL Light Proof General.
;;
;; You can run these by issuing "make test.hol-light" in PG home dir.
;;
;; $Id$
;;

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
