(require 'org-trello-deferred)
(require 'ert)

(ert-deftest test-orgtrello-deferred--compute-deferred-computation ()
  (should (equal
           '(deferred:$
              (deferred:next
                (lambda ()
                  '(1 2)))
              (deferred:nextc it
                (lambda (data)
                  (message "Initial data: %S" data)
                  data))
              (deferred:nextc it
                (lambda(data)
                  (cons (+ (car data) (cadr data)) data)))
              (deferred:nextc it
                (lambda (data) (cons (1+ (car data)) data)))
              (deferred:nextc it
                (lambda (data) (message "result sir: %S" data)))
              (deferred:nextc it
                (orgtrello-controller-log-success "do something..."))
              (deferred:error it
                (orgtrello-controller-log-error "do something..." "Error: %S")))

           (orgtrello-deferred--compute-deferred-computation '(1 2) '((lambda (data) (message "Initial data: %S" data) data)
                                                                      (lambda (data) (cons (+ (car data) (cadr data)) data))
                                                                      (lambda (data) (cons (1+ (car data)) data))
                                                                      (lambda (data) (message "result sir: %S" data)))
                                                             "do something...")))
  (should (equal
           '(deferred:$
              (deferred:next
                (lambda ()
                  '(1 2)))
              (deferred:nextc it
                (lambda (data)
                  (message "Initial data: %S" data)
                  data))
              (deferred:nextc it
                (lambda(data)
                  (cons (+ (car data) (cadr data)) data)))
              (deferred:nextc it
                (lambda (data) (cons (1+ (car data)) data)))
              (deferred:nextc it
                (lambda (data) (message "result sir: %S" data)))
              (deferred:error it
                (orgtrello-controller-log-error "do something..." "Error: %S")))

           (orgtrello-deferred--compute-deferred-computation '(1 2) '((lambda (data) (message "Initial data: %S" data) data)
                                                                      (lambda (data) (cons (+ (car data) (cadr data)) data))
                                                                      (lambda (data) (cons (1+ (car data)) data))
                                                                      (lambda (data) (message "result sir: %S" data)))
                                                             "do something..."
                                                             'no-success-log))))

(ert-deftest test-orgtrello-deferred-eval-computation ()
  (should (eq 3
              (with-mock
                (mock (orgtrello-deferred--compute-deferred-computation :initial-state :fns :log :no-success-log) => '(+ 1 2))
                (orgtrello-deferred-eval-computation :initial-state :fns :log :no-success-log)))))
