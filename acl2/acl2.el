;; acl2.el   Basic Proof General instance for ACL2
;;
;; Copyright (C) 2000 LFCS Edinburgh. 
;;
;; Author: David Aspinall <da@dcs.ed.ac.uk>
;;
;; $Id$
;;
;; Needs improvement!
;;
;; See the README file in this directory for information.


(require 'proof-easy-config)            ; easy configure mechanism
(require 'proof-syntax)			; functions for making regexps

(setq auto-mode-alist                   ; ACL2 uses two file extensions
      (cons				; Only grab .lisp extension after 
       (cons "\\.lisp$" 'acl2-mode)	; an acl2 file has been loaded
       auto-mode-alist))	

(proof-easy-config  'acl2 "ACL2" 
 proof-assistant-home-page       "http://www.cs.utexas.edu/users/moore/acl2"
 proof-prog-name		 "acl2"

 proof-script-sexp-commands	 t
 proof-comment-start             ";"
 proof-comment-start             ";"

 proof-shell-annotated-prompt-regexp "ACL2[ !]*>+"

 proof-shell-error-regexp	 "^Error: "  
 proof-shell-interrupt-regexp    "Correctable error: Console interrupt."
 proof-shell-prompt-pattern      "ACL2[ !]*>+"

 proof-shell-quit-cmd            ":q"	 ;; FIXME: followed by C-d.
 proof-shell-restart-cmd	 "#."    ;; FIXME: maybe not?
 proof-info-command		 ":help"

 ;;
 ;; Syntax table entries for proof scripts  (FIXME: incomplete)
 ;;
 proof-script-syntax-table-entries
 '(?\[ "(]  "
   ?\] "([  "
   ?\( "()  " 
   ?\) ")(  "
   ?.  "w" 
   ?_  "w"   
   ?\' "'    "
   ?`  "'    "
   ?,  "'    "
   ?\| "."   
   ?\; "<    "
   ?\n ">    "
   )

 ;; End of easy config.
 )

;; Interrupts and errors enter another loop; break out of it
(add-hook
 'proof-shell-handle-error-or-interrupt-hook
 (lambda () (proof-shell-insert ":q" nil)))



(warn "ACL2 Proof General is incomplete!  Please help improve it!
Read the manual, make improvements and send them to feedback@proofgeneral.org")

(provide 'acl2)
