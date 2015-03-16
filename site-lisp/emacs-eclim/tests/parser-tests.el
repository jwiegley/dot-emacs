
(ert-deftest java-parser-read-complex-signarure()
  (should (equal (eclim--java-parser-read "public Message<?> preSend(org.springframework.integration.Message<?>,org.springframework.integration.MessageChannel)")
                 '(public Message ((\?)) preSend ((org\.springframework\.integration\.Message ((\?))) (org\.springframework\.integration\.MessageChannel))))))

(ert-deftest parse-complex-signature ()
  (should (equal (eclim--java-parse-method-signature "public Message<?> preSend(org.springframework.integration.Message<?>,org.springframework.integration.MessageChannel)")
                 '((:arglist ((:type org\.springframework\.integration\.Message ((\?)))) ((:type org\.springframework\.integration\.MessageChannel))) (:name . preSend) (:return public Message ((\?)))))))

