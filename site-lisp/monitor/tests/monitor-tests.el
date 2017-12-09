;;; monitor-tests.el
;;; Code:

(require 'ert)
(require 'monitor)

(defun monitor--test-build-test-monitor (name &optional parent &rest args)
  "Build a test monitor named NAME."
  (apply 'define-monitor name parent "Test monitor." args))

(defmacro monitor--test-build-get-put-tests (getter putter)
  "Build standard tests for a getter GETTER and putter PUTTER."
  (let* ((monitor-symbol (make-symbol "monitor-symbol"))
         (get-form `(funcall ,getter ,monitor-symbol :test-slot-a))
         (set-form (lambda (to) `(funcall ,putter ,monitor-symbol :test-slot-a ,to))))
    `(let ((,monitor-symbol (make-symbol "monitor--test-build-get-put-tests-tvar")))
       (should-error ,get-form :type '(wrong-type-argument monitorp))
       (should-error ,(funcall set-form "test") :type 'wrong-type-argument)
       (monitor--test-build-test-monitor ,monitor-symbol)
       (should (eq nil ,get-form))
       ,(funcall set-form "test")
       (should (equal "test" (funcall ,getter ,monitor-symbol :test-slot-a)))
       ,(funcall set-form "test2")
       (should (equal "test2" ,get-form)))))

(defmacro monitor--test-with-uninterned-symbols (symbols &rest body)
  "Provide an uninterned version of each symbol in SYMBOLS for use in BODY."
  (declare (indent 1))
  `(let (,@(--map `(,it (make-symbol (symbol-name ',it))) symbols))
     ,@body))

(defun monitor--test-same-instances-p (lista listb)
  "T if LISTA has the same monitor instances as LISTB."
  (let ((-compare-fn 'monitor--instance-equal)) (-same-items-p lista listb)))

(ert-deftest monitor-test-monitorp ()
  "Tests for `monitorp'."
  (monitor--test-with-uninterned-symbols (monitor-symbol)
    ; initially, we don't expect it to be a monitor.
    (should (eq nil (monitorp monitor-symbol)))
    (monitor--test-build-test-monitor monitor-symbol)
    ; now we've created a monitor, it should recognize it as one
    (should (eq t (monitorp monitor-symbol)))
    (monitor--remove-monitor monitor-symbol)
    ; now it is no longer a monitor
    (should (eq nil (monitorp monitor-symbol)))))

(ert-deftest monitor-test-monitor-meta-get-put ()
  "Tests for `monitor--meta-put' and `monitor--meta-get'."
  (monitor--test-build-get-put-tests 'monitor--meta-get 'monitor--meta-put))

(ert-deftest monitor-test-monitor-decl-get-put ()
  "Tests for `monitor--decl-put' and `monitor--decl-get'."
  (monitor--test-build-get-put-tests 'monitor--decl-get 'monitor--decl-put)
  (monitor--test-with-uninterned-symbols (monitor-parent-symbol monitor-child-symbol)
    (monitor--test-build-test-monitor monitor-parent-symbol nil :test-arg-a 'parent-a :test-arg-b 'parent-b)
    (monitor--test-build-test-monitor monitor-child-symbol monitor-parent-symbol :test-arg-b 'child-b)
    ; not defined in child, so fall back to parent
    (should (eq 'parent-a (monitor--decl-get monitor-child-symbol :test-arg-a)))
    ; defined in both parent and child, so use child
    (should (eq 'child-b (monitor--decl-get monitor-child-symbol :test-arg-b)))))

(ert-deftest monitor-test-make-plist ()
  "Tests for `monitor--make-plist'."
  ; all plists should be different
  (should-not (eq (monitor--make-plist) (monitor--make-plist))))

(ert-deftest monitor-test-monitor-enable-disable ()
  "Tests for `monitor-enable' and `monitor-disable'."
  (monitor--test-with-uninterned-symbols (monitor-symbol monitor-child)
    (let ((counter-enabled 0)
          (counter-disabled 0))
      (monitor--test-build-test-monitor monitor-symbol nil
        :enable (lambda (monitor) (setq counter-enabled (1+ counter-enabled)))
        :disable (lambda (monitor) (setq counter-disabled (1+ counter-disabled))))
      (should (= 0 counter-enabled))
      (should (= 0 counter-disabled))
      (should (eq t (monitor--disabled-p monitor-symbol)))
      (monitor-enable monitor-symbol)
      (should (= 1 counter-enabled))
      (should (eq t (monitor--enabled-p monitor-symbol)))
      (monitor-enable monitor-symbol)
      (should (= 1 counter-enabled))
      (monitor-disable monitor-symbol)
      (should (= 1 counter-disabled))
      (should (eq t (monitor--disabled-p monitor-symbol)))
      (monitor-disable monitor-symbol)
      (should (= 1 counter-disabled))
      (monitor--test-build-test-monitor monitor-child monitor-symbol :enable nil)
      (should (= 1 counter-enabled))
      (should (= 1 counter-disabled))
      (monitor-enable monitor-child)
      (should (= 1 counter-enabled))
      (monitor-disable monitor-child)
      (should (= 2 counter-disabled)))))

(ert-deftest monitor-test-monitor-instance-p ()
  "Tests for `monitor--instance-p'."
  (monitor--test-with-uninterned-symbols (monitor-symbol)
    ; monitors aren't instances of themselves
    (monitor--test-build-test-monitor monitor-symbol)
    (should (eq nil (monitor--instance-p monitor-symbol)))
    (let ((instance-a (monitor-instance-create monitor-symbol)))
      ; explicit instance
      (should (eq t (monitor--instance-p instance-a))))))

(ert-deftest monitor-test-monitor-instance-equal ()
  "Tests for `monitor--instance-equal'."
  (monitor--test-with-uninterned-symbols (monitor-symbol monitor-symbol-b)
    (monitor--test-build-test-monitor monitor-symbol)
    (monitor--test-build-test-monitor monitor-symbol-b)
    (let ((instance-a (monitor-instance-create monitor-symbol :a 6 :b 7))
          (instance-b (monitor-instance-create monitor-symbol :a 6 :b 7))
          (instance-c (monitor-instance-create monitor-symbol :b 7 :a 6))
          (instance-d (monitor-instance-create monitor-symbol :a 5 :b 7))
          (instance-e (monitor-instance-create monitor-symbol :a 6 :c 7))
          (instance-f (monitor-instance-create monitor-symbol-b :a 6 :b 7)))
      ; same instance
      (should (eq t (monitor--instance-equal instance-a instance-a)))
      ; same form
      (should (eq t (monitor--instance-equal instance-a instance-b)))
      ; same key-values, different order
      (should (eq t (monitor--instance-equal instance-a instance-c)))
      ; different value for a key
      (should-not (eq t (monitor--instance-equal instance-a instance-d)))
      ; different keys
      (should-not (eq t (monitor--instance-equal instance-a instance-e)))
      ; different monitors
      (should-not (eq t (monitor--instance-equal instance-a instance-f))))))

(ert-deftest monitor-test-monitor-plist-equal-p ()
  "Tests for `monitor--monitor-plist-equal-p'."
  (monitor--test-with-uninterned-symbols (monitor-parent)
    (monitor--test-build-test-monitor monitor-parent)
    (let ((monitor-a (monitor--create-monitor-plist nil "foo" :a 7))
          (monitor-b (monitor--create-monitor-plist nil "foo" :a 7))
          (monitor-c (monitor--create-monitor-plist nil "bar" :a 7))
          (monitor-d (monitor--create-monitor-plist nil "foo" :a 8))
          (monitor-e (monitor--create-monitor-plist monitor-parent "foo" :a 7))
          (monitor-f (monitor--create-monitor-plist nil "foo" :a 7 :b 8))
          (monitor-g (monitor--create-monitor-plist nil "foo" :b 8 :a 7))
          (monitor-h (monitor--create-monitor-plist nil "foo" :b 7)))
    ; same monitor
    (should (eq t (monitor--monitor-plist-equal-p monitor-a monitor-a)))
    ; same form
    (should (eq t (monitor--monitor-plist-equal-p monitor-a monitor-b)))
    ; different parents
    (should (eq nil (monitor--monitor-plist-equal-p monitor-a monitor-e)))
    ; same key-values, different order
    (should (eq t (monitor--monitor-plist-equal-p monitor-f monitor-g)))
    ; different value for a key
    (should-not (eq t (monitor--monitor-plist-equal-p monitor-a monitor-d)))
    ; different keys
    (should-not (eq t (monitor--monitor-plist-equal-p monitor-a monitor-h)))
    ; different docs
    (should (eq nil (monitor--monitor-plist-equal-p monitor-a monitor-c))))))

(ert-deftest monitor-test-monitor-instance-get ()
  "Tests for `monitor--instance-get'."
  (monitor--test-with-uninterned-symbols (monitor-symbol)
    (monitor--test-build-test-monitor monitor-symbol nil :test-arg-a 'ma :test-arg-b 'mb)
    (let ((instance (monitor-instance-create monitor-symbol :test-arg-a 'ia)))
      ; not declared in any
      (should (eq nil (monitor--instance-get instance :test-arg)))
      ; declared in instance
      (should (eq 'ia (monitor--instance-get instance :test-arg-a)))
      ; not in instance, fall back to monitor
      (should (eq 'mb (monitor--instance-get instance :test-arg-b))))))

(ert-deftest monitor-test-monitor-instance-get-arg ()
  "Tests for `monitor--instance-get-arg'."
  (monitor--test-with-uninterned-symbols (monitor-symbol)
    (monitor--test-build-test-monitor monitor-symbol nil :test-arg-a 'ma :test-arg-b 'mb)
    (let ((instance (monitor-instance-create monitor-symbol :test-arg-a 'ia)))
      ; not declared in any
      (should (eq nil (monitor--instance-get-arg instance :test-arg)))
      ; declared in instance
      (should (eq 'ia (monitor--instance-get-arg instance :test-arg-a)))
      ; not in instance (in monitor), but don't fall back
      (should (eq nil (monitor--instance-get-arg instance :test-arg-b))))))

(ert-deftest monitor-test-monitor-instance-get-meta ()
  "Tests for `monitor--instance-get-meta'."
  (monitor--test-with-uninterned-symbols (monitor-symbol)
    (monitor--test-build-test-monitor monitor-symbol nil :test-arg-a 'ma)
    (let ((instance (monitor-instance-create monitor-symbol :test-arg-a 'ia)))
      ;; not a meta property
      (should (eq nil (monitor--instance-get-meta instance :test-arg-a)))
      (monitor--meta-put monitor-symbol :test-a 'foo)
      ;; meta properties don't inherit
      (should (eq nil (monitor--instance-get-meta instance :test-a)))
      (monitor--instance-put-meta instance :test-b 'bar)
      ;; declared in instance
      (should (eq 'bar (monitor--instance-get-meta instance :test-b))))))

(ert-deftest monitor-test-instance-existing-p ()
  "Tests for `monitor--instance-existing-p'."
  (monitor--test-with-uninterned-symbols (monitor-symbol)
    (monitor--test-build-test-monitor monitor-symbol)
    (should-error (monitor--instance-existing-p nil) :type 'wrong-type-argument)
    (let ((instance (monitor-instance-create monitor-symbol)))
      (should (eq t (monitor--instance-existing-p instance)))
      (monitor--instance-destroy instance)
      (should (eq nil (monitor--instance-existing-p instance))))))

(ert-deftest monitor-test-instance-create ()
  "Tests for `monitor-instance-create'."
  (monitor--test-with-uninterned-symbols (monitor-symbol)
    (let (instances (validated 0))
      (monitor--test-build-test-monitor monitor-symbol nil
        :create (lambda (instance)
                  (push instance instances))
        :validate (lambda (instance) (setq validated (1+ validated))))
      (should (equal nil instances))
      (should (= 0 validated))
      (let ((instance (monitor-instance-create monitor-symbol)))
        ;; should have validated
        (should (= 1 validated))
        (should (monitor--test-same-instances-p (list instance) instances))
        (monitor-instance-create monitor-symbol)
        ; already have an exact instance
        (should (monitor--test-same-instances-p (list instance) instances))
        (should (= 1 validated))
        (let ((instance-b (monitor-instance-create monitor-symbol :a 1)))
          (should (monitor--test-same-instances-p (list instance instance-b) instances))
          (should (= 2 validated)))))))

(ert-deftest monitor-test-instance-destroy ()
  "Tests for `monitor--instance-destroy'."
  (monitor--test-with-uninterned-symbols (monitor-symbol)
    (let (instances)
      (monitor--test-build-test-monitor monitor-symbol nil
        :create (lambda (instance)
                  (push instance instances))
        :destroy (lambda (instance)
                   (setq instances (--reject (monitor--instance-equal it instance) instances))))
      (should (equal nil instances))
      (let ((instance (monitor-instance-create monitor-symbol)))
        (should (monitor--test-same-instances-p (list instance) instances))
        (monitor--instance-destroy instance)
        (should (eq nil instances))))))

(ert-deftest monitor-test-define-monitor-basic ()
  "Basic tests for `define-monitor'."
  (monitor--test-with-uninterned-symbols (monitor-symbol monitor-symbol-a monitor-symbol-b)
    (should-error (define-monitor monitor-symbol-a monitor-symbol-b "") :type 'wrong-type-argument)
    (let ((count-disable 0))
      (define-monitor monitor-symbol nil "" :disable (lambda (monitor) (setq count-disable (1+ count-disable))))
      (monitor-enable monitor-symbol)
      (should (= 0 count-disable))
      (define-monitor monitor-symbol nil "" :disable (lambda (monitor) (setq count-disable (1+ count-disable))))
      ; 'same' monitor, so don't overwrite it
      (should (= 0 count-disable))
      (define-monitor monitor-symbol nil "" :enable nil :disable (lambda (monitor) (setq count-disable (1+ count-disable))))
      ; different monitors - so destroy the old one
      (should (= 1 count-disable)))))

(ert-deftest monitor-test-monitor-remove ()
  "Tests for `monitor--remove-monitor'."
  (monitor--test-with-uninterned-symbols (monitor-symbol)
    (let ((count-destroy 0)
          (count-disable 0))
      (monitor--test-build-test-monitor monitor-symbol nil
        :disable (lambda (monitor) (setq count-disable (1+ count-disable)))
        :destroy (lambda (instance) (setq count-destroy (1+ count-destroy))))
      (monitor-enable monitor-symbol)
      (monitor-instance-create monitor-symbol)
      (monitor-instance-create monitor-symbol :a 7)
      (monitor--remove-monitor monitor-symbol)
      ; it should destroy all instances
      (should (= 2 count-destroy))
      ; it should be 'disabled'
      (should (= 1 count-disable)))))

(ert-deftest monitor-test-monitor-fn-run ()
  "Tests for `monitor--fn-run'."
  (let ((fn-a nil)
        (fn-b '1+)
        (fn-c (lambda () "foo"))
        (fn-d '((lambda () "foo") (lambda () "bar")))
        (fn-e '(1+ 1-))
        (bfn-a 1)
        (bfn-b '(1)))
      ; shouldn't error with no function
      (monitor--fn-run fn-a)
      ; function with arguments
      (should (= 8 (monitor--fn-run fn-b 7)))
      ; function with no arguments
      (should (equal "foo" (monitor--fn-run fn-c)))
      ;; multiple functions with no arguments
      (should (equal '("foo" "bar") (monitor--fn-run fn-d)))
      ;; multiple functions with arguments
      (should (equal '(5 3) (monitor--fn-run fn-e 4)))
      ;; wrong type (single element)
      (should-error (monitor--fn-run bfn-a) :type 'wrong-type-argument)
      ;; wrong type (in list)
      (should-error (monitor--fn-run bfn-b) :type 'wrong-type-argument)))

(ert-deftest monitor-test-monitor-instance-run ()
  "Tests for `monitor--instance-run'."
  (monitor--test-with-uninterned-symbols (monitor-symbol)
    (monitor--test-build-test-monitor monitor-symbol nil :test-fn-b (lambda () "bar"))
    (let ((instance-a (monitor-instance-create monitor-symbol :test-fn nil))
          (instance-b (monitor-instance-create monitor-symbol :test-fn '1+)))
      ; shouldn't error with no function
      (monitor--instance-run instance-a :test-fn)
      ; standard function
      (should (= 8 (monitor--instance-run instance-b :test-fn 7)))
      ; don't fall back to monitor
      ; different interpretation for instance functions and monitor functions.
      (should (eq nil (monitor--instance-run instance-a :test-fn-b))))))

(ert-deftest monitor-test-monitor-run-option-with-parents ()
  "Tests for `monitor-run-monitor-option-with-parents'."
  (monitor--test-with-uninterned-symbols (monitor-parent monitor-middle monitor-child)
    (let ((count-parent 0) (count-middle 0) (count-child 0))
      (define-monitor monitor-parent nil "" :test-inc (lambda () (setq count-parent (1+ count-parent))))
      (define-monitor monitor-middle monitor-parent "" :test-inc (lambda () (setq count-middle (1+ count-middle))))
      (define-monitor monitor-child monitor-middle "" :test-inc (lambda () (setq count-child (1+ count-child))))
      ;; no parents
      (monitor-run-monitor-option-with-parents monitor-parent :test-inc)
      (should (= 1 count-parent))
      ;; has parent
      (monitor-run-monitor-option-with-parents monitor-middle :test-inc)
      (should (= 2 count-parent))
      (should (= 1 count-middle))
      ;; parent heirarchy
      (monitor-run-monitor-option-with-parents monitor-child :test-inc)
      (should (= 3 count-parent))
      (should (= 2 count-middle))
      (should (= 1 count-child)))))

(ert-deftest monitor-test-monitor-instance-list ()
  "Tests for monitor instance lists."
  (monitor--test-with-uninterned-symbols (monitor-symbol)
    (define-monitor monitor-symbol nil "")
    (let ((instance-a (monitor monitor-symbol))
          (instance-b (monitor monitor-symbol :a 7))
          ilist)
      (should (eq nil ilist))
      (setq ilist (monitor--instance-list-add-instance ilist instance-a))
      (should (monitor--test-same-instances-p (list instance-a) ilist))
      ;; already in list
      (setq ilist (monitor--instance-list-add-instance ilist instance-a))
      (should (monitor--test-same-instances-p (list instance-a) ilist))
      ;; new instance
      (setq ilist (monitor--instance-list-add-instance ilist instance-b))
      (should (monitor--test-same-instances-p (list instance-a instance-b) ilist))
      ;; cannot add non instances
      (should-error (monitor--instance-list-add-instance ilist 'foo) :type 'wrong-type-argument)
      (setq ilist (monitor--instance-list-remove-instance ilist instance-b))
      (should (monitor--test-same-instances-p (list instance-a) ilist))
      ;; not in list
      (setq ilist (monitor--instance-list-remove-instance ilist instance-b))
      (should (monitor--test-same-instances-p (list instance-a) ilist))
      ;; cannot remove non instances
      (should-error (monitor--instance-list-remove-instance ilist 'foo) :type 'wrong-type-argument))))

(ert-deftest monitor-test-monitor-instance-alist ()
  "Tests for monitor instance alists."
  (monitor--test-with-uninterned-symbols (monitor-symbol)
    (define-monitor monitor-symbol nil "")
    (let ((instance-a (monitor monitor-symbol))
          (instance-b (monitor monitor-symbol :a 7))
          ialist)
      (should (eq nil (monitor--instance-alist-instances ialist 'a)))
      (setq ialist (monitor--instance-alist-add-instance ialist 'a instance-a))
      (should (monitor--test-same-instances-p (list instance-a) (monitor--instance-alist-instances ialist 'a)))
      ;; already in alist at that key
      (setq ialist (monitor--instance-alist-add-instance ialist 'a instance-a))
      (should (monitor--test-same-instances-p (list instance-a) (monitor--instance-alist-instances ialist 'a)))
      ;; can be under multiple keys
      (setq ialist (monitor--instance-alist-add-instance ialist 'b instance-a))
      (should (monitor--test-same-instances-p (list instance-a) (monitor--instance-alist-instances ialist 'b)))
      (should (monitor--test-same-instances-p (list instance-a) (monitor--instance-alist-instances ialist 'a)))
      ;; multiple instances under one key
      (monitor--instance-alist-add-instance ialist 'b instance-b)
      (should (monitor--test-same-instances-p (list instance-a instance-b) (monitor--instance-alist-instances ialist 'b)))
      ;; can remove instances
      (setq ialist (monitor--instance-alist-remove-instance ialist 'b instance-a))
      (should (monitor--test-same-instances-p (list instance-b) (monitor--instance-alist-instances ialist 'b)))
      ;; not in alist
      (setq ialist (monitor--instance-alist-remove-instance ialist 'b instance-a))
      (should (monitor--test-same-instances-p (list instance-b) (monitor--instance-alist-instances ialist 'b)))
      ;; no more instances deletes the entry
      (setq ialist (monitor--instance-alist-remove-instance ialist 'b instance-b))
      (should-not (-contains-p (monitor--instance-alist-keys ialist) 'b)))))

(ert-deftest monitor-test-base-monitor ()
  "Tests for the 'base monitor."
  (monitor--test-with-uninterned-symbols (monitor-symbol)
    ;; we should be able to make children
    (define-monitor monitor-symbol 'base "")
    ;; we don't need any arguments for an instance
    (monitor monitor-symbol)))

(ert-deftest monitor-test-trigger-monitor ()
  "Tests for the 'trigger monitor."
  (monitor--test-with-uninterned-symbols (monitor-symbol)
    ;; we should be able to make children
    (define-monitor monitor-symbol 'trigger "")
    ;; the :trigger option is required
    (should-error (monitor monitor-symbol))
    (let* ((counter-a 0) (counter-b 0)
           (instance (monitor monitor-symbol :trigger '((lambda () (setq counter-a (1+ counter-a)))
                                                        (lambda () (setq counter-b (+ 2 counter-b)))))))
      ;; syntax for running triggers
      (monitor-run-monitor-option monitor-symbol :trigger instance)
      (should (= 1 counter-a))
      (should (= 2 counter-b)))))

(ert-deftest monitor-test-hook-monitor ()
  "Tests for the 'hook monitor."
  (monitor--test-with-uninterned-symbols (monitor-symbol hook-symbol ivar)
    (set ivar nil)
    ;; we should be able to make children
    (define-monitor monitor-symbol 'hook "" :hook-ivar ivar)
    ;; the :hook option is required
    (should-error (monitor monitor-symbol :trigger nil))
    (unwind-protect
        (should (eq nil (symbol-value ivar)))
        (set hook-symbol nil)
        (let* ((counter-a 0) (counter-b 0)
               (instance (monitor monitor-symbol
                           :trigger (lambda () (setq counter-a (1+ counter-a)))
                           :hook hook-symbol)))
          ;; instance should be stored in specified instance variable
          (should (monitor--test-same-instances-p
                   (list instance)
                   (monitor--instance-alist-instances (symbol-value ivar) hook-symbol)))
          (should (= 0 counter-a))
          (should (eq nil (symbol-value hook-symbol)))
          ;; not enabled
          (should (eq nil (monitor--enabled-p monitor-symbol)))
          (run-hooks hook-symbol)
          (should (= 0 counter-a))
          (monitor-enable monitor-symbol)
          (should (= 1 (length (symbol-value hook-symbol))))
          ;; instances trigger when hook runs
          (run-hooks hook-symbol)
          (should (= 1 counter-a))
          (monitor-disable monitor-symbol)
          (should (eq nil (symbol-value hook-symbol))))
      (monitor--remove-monitor monitor-symbol))
    (should (eq nil (monitor--instance-alist-instances monitor--hook-instances hook-symbol)))
    (should (eq nil (symbol-value ivar)))))

(ert-deftest monitor-test-expression-value-monitor ()
  "Tests for the 'expression-value monitor."
  (monitor--test-with-uninterned-symbols (monitor-symbol)
    ;; we should be able to make children
    (define-monitor monitor-symbol 'expression-value "")
    ;; the :expr option is required
    (should-error (monitor monitor-symbol :trigger nil :pred nil))
    ;; the :pred option is required
    (should-error (monitor monitor-symbol :trigger nil :expr nil))
    (unwind-protect
        (let* ((counter-a 0) (counter-b 0)
               (instance (monitor monitor-symbol
                           :trigger (lambda () (setq counter-a (1+ counter-a)))
                           :expr 'counter-b
                           :pred (lambda (old new) (> new old)))))
          (monitor-enable monitor-symbol)
          (should (= 0 counter-a))
          ;; value not yet checked
          (monitor-run-monitor-option monitor-symbol :check instance)
          (should (= 0 counter-a))
          ;; value checked, but same
          (monitor-run-monitor-option monitor-symbol :check instance)
          (should (= 0 counter-a))
          (setq counter-b (1+ counter-b))
          ;; should trigger (value increased)
          (monitor-run-monitor-option monitor-symbol :check instance)
          (should (= 1 counter-a))
      (monitor--remove-monitor monitor-symbol)))))

(provide 'monitor-tests)
;;; monitor-tests.el ends here
