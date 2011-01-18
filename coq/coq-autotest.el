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

(unless noninteractive
  
  ;; new multiple file handling for Coq gives interactive queries
  ;; continually unless we set this
  (setq proof-auto-action-when-deactivating-scripting 'retract)

  (pg-autotest log ".autotest.log")  ; convention

  (pg-autotest timestart 'total)

  (pg-autotest remark "Testing standard examples...")
  (pg-autotest script-wholefile "coq/example.v")
  (pg-autotest script-wholefile "coq/example-tokens.v")
  (pg-autotest script-wholefile "coq/ex-module.v")

  (pg-autotest remark "Testing prove-as-you-go (not replay)")
  (find-file ".autotest.v")
  (erase-buffer) ; just in case exists
  (setq buffer-file-name nil)
  (pg-autotest eval (proof-electric-terminator-toggle 1))
  (pg-autotest eval (insert "Module test")) ; no \n
  (proof-electric-terminator)
  (proof-shell-wait)
  (pg-autotest eval (insert " Goal forall (A B:Prop),(A /\\ B) -> (B /\\ A)"))
  (proof-electric-terminator)
  (proof-shell-wait)
  (pg-autotest eval (insert "\ntauto."))
  (backward-char)
  (proof-electric-terminator) ; shouldn't insert another or delete present
  (proof-shell-wait)
;; FIXME: next test fails, why?
  (pg-autotest assert-full)
  ;; TODO: test switching active scripting buffer after
  ;; an error (see cvs log for proof-script.el 10.68)
;; FIXME: bug, this causes "region is read only"
;;  (pg-autotest eval (insert " End test"))
;;  (proof-electric-terminator)
  (set-buffer-modified-p nil)
  (kill-buffer ".autotest.v")
  (proof-shell-wait)

  
  (pg-autotest script-wholefile "etc/coq/multiple-plain/a.v")
  (pg-autotest script-wholefile "etc/coq/multiple-plain/b.v")
  (pg-autotest script-wholefile "etc/coq/multiple-plain/c.v")
  ;; FIXME: this is broken: retracting a previously
  ;; processed file doesn't work
  (pg-autotest script-wholefile "etc/coq/multiple-plain/a.v")

  (pg-autotest quit-prover)

  (pg-autotest remark "Complete.")

  (pg-autotest timetaken 'total)

  (pg-autotest exit))
