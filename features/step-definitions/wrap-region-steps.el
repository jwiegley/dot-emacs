(defun parse-modes (mode-or-modes)
  (let ((mode-split (split-string mode-or-modes ",")))
    (if (> (length mode-split) 1)
        (mapcar 'intern mode-split)
      (intern mode-or-modes))))


(Given "^I turn on wrap-region globally$"
       (lambda ()
         (wrap-region-global-mode 1)))

(Given "^I turn on wrap-region$"
       (lambda ()
         (wrap-region-mode 1)))

(Given "^I turn off wrap-region$"
       (lambda ()
         (wrap-region-mode -1)))

(Given "^I add \"\\(.+\\)\" as an except mode$"
       (lambda (mode)
         (add-to-list 'wrap-region-except-modes (intern mode))))

(Given "^I add wrapper \"\\([^\"]+\\)\"$"
       (lambda (wrapper)
         (apply 'wrap-region-add-wrapper (split-string wrapper "/"))))

(Given "^I remove wrapper \"\\(.\\)\"$"
       (lambda (left)
         (wrap-region-remove-wrapper left)))

(Given "^I require negative prefix to wrap$"
       (lambda ()
         (setq wrap-region-only-with-negative-prefix t)))

(Given "^I require region to remain active after wrapping$"
       (lambda ()
         (setq wrap-region-keep-mark t)))

(Given "^I add wrapper \"\\(.+\\)\" for \"\\(.+\\)\"$"
       (lambda (wrapper mode-or-modes)
         (let* ((modes (parse-modes mode-or-modes))
                (wrapper-split
                 (split-string wrapper "/"))
                (args
                 (append
                  wrapper-split
                  (if (= (length wrapper-split) 2)
                      (list nil modes)
                    (list modes)))))
           (apply 'wrap-region-add-wrapper args))))

(Given "^I remove wrapper \"\\(.+\\)\" from \"\\(.+\\)\"$"
       (lambda (key mode-or-modes)
         (let ((modes (parse-modes mode-or-modes)))
           (wrap-region-remove-wrapper key modes))))

(Given "^I add wrapper these wrappers:$"
       (lambda (table)
         (let ((wrappers (cdr table)))
           (wrap-region-add-wrappers
            (mapcar
             (lambda (wrapper)
               (let* ((left  (pop wrapper))
                      (right (pop wrapper))
                      (key   (pop wrapper))
                      (split (split-string (car wrapper) ","))
                      (modes (mapcar 'intern (delete "" split))))
                 (list left right key modes)))
             wrappers)))))

(Then "^key \"\\(.+\\)\" should be bound to \"\\(.+\\)\"$"
      (lambda (key fn)
        (should
         (equal
          (key-binding (read-kbd-macro key))
          (intern fn)))))
