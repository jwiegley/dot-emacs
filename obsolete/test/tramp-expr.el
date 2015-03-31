;;; tramp-expr.el --- expression parsing tests for tramp2

;;; Code:
(push "." load-path)
(push "../lisp" load-path)
(load "tramp2.el")

(setq tramp2-test-connect (make-tramp2-connect 'protocol "user" "host"))

;; Verify function calling.
(defun test-tramp2-expr-fn (user host)
  "Return \"user host\""
  (format "%s %s" user host))

(Assert (string-equal "user host" (tramp2-expression 'test-tramp2-expr-fn tramp2-test-connect)))


;; Verify lambda evaluation.
(Assert (string-equal "user host"
		      (tramp2-expression (lambda (user host) (format "%s %s" user host))
					 tramp2-test-connect)))


;; Verify list evaluation
(Assert (string-equal "user host"
		      (tramp2-expression (list 'format "%s %s" 'user 'host)
					 tramp2-test-connect)))


;; Verify string substitution.
(Assert (string-equal "user host" (tramp2-expression "%u %h" tramp2-test-connect)))
(Assert (string-equal "host"      (tramp2-expression "%h" tramp2-test-connect)))
(Assert (string-equal "user"      (tramp2-expression "%u" tramp2-test-connect)))
(Assert (string-equal "boo"       (tramp2-expression "boo" tramp2-test-connect)))




(provide 'tramp-expr)

;;; tramp-expr.el ends here
