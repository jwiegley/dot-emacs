(defmacro with-temp-buffer-fix (&rest body)
  "Like `with-temp-buffer' but does not switch buffer with `execute-kbd-macro'."
  `(let ((origin-buffer (current-buffer))
         (buffer-name "*wrap-region-temp*"))
     (switch-to-buffer (get-buffer-create buffer-name))
     (erase-buffer)
     ,@body
     (switch-to-buffer origin-buffer)))


(Then "^key \"\\(.+\\)\" should wrap with \"\\(.+\\)\" and \"\\(.+\\)\"$"
      (lambda (key left right)
        (with-temp-buffer-fix
         (When "I turn on wrap-region")
         (And  "I insert \"%s\"" "This is some text")
         (And  "I select \"%s\"" "is some")
         (And  "I press \"%s\"" key)
         (Then "I should see \"%s\"" (format "This %sis some%s text" left right)))))

(Then "^key \"\\(.+\\)\" should wrap with \"\\(.+\\)\" and \"\\(.+\\)\" in \"\\(.+\\)\"$"
      (lambda (key left right mode)
        (with-temp-buffer-fix
         (When "I turn on %s" mode)
         (And  "I turn on wrap-region")
         (And  "I insert \"%s\"" "This is some text")
         (And  "I select \"%s\"" "is some")
         (And  "I press \"%s\"" key)
         (Then "I should see \"%s\"" (format "This %sis some%s text" left right)))))

(Then "^key \"\\(.+\\)\" should not wrap$"
      (lambda (key)
        (with-temp-buffer-fix
         (When "I turn on wrap-region")
         (And  "I insert \"%s\"" "This is some text")
         (And  "I select \"%s\"" "is some")
         (And  "I press \"%s\"" key)
         (Then "I should see \"%s\"" (format "This %sis some text" key)))))

(Then "^key \"\\(.+\\)\" should not wrap in \"\\(.+\\)\"$"
      (lambda (key mode)
        (with-temp-buffer-fix
         (When "I turn on %s" mode)
         (And  "I turn on wrap-region")
         (And  "I insert \"%s\"" "This is some text")
         (And  "I select \"%s\"" "is some")
         (And  "I press \"%s\"" key)
         (Then "I should see \"%s\"" (format "This %sis some text" key)))))
