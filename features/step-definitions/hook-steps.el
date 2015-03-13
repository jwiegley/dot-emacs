(Given "^I add a mode hook that erases buffer$"
       (lambda ()
         (add-hook 'wrap-region-hook 'erase-buffer)))

(And "I add an after wrap hook that replaces \"\\(.+\\)\" with \"\\(.+\\)\""
     (lambda (from to)
       (add-hook 'wrap-region-after-wrap-hook
                 `(lambda ()
                    (replace-regexp ,from ,to ,nil (point-min) (point-max))))))

(And "I add a before wrap hook that replaces \"\\(.+\\)\" with \"\\(.+\\)\""
     (lambda (from to)
       (add-hook 'wrap-region-before-wrap-hook
                 `(lambda ()
                    (replace-regexp ,from ,to ,nil (mark) (point))))))
