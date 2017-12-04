;;; smart-jump-test.el --- Tests for smart-jump -*- lexical-binding: t -*-
(require 'smart-jump)

(defun smart-jump-set-smart-jump-list-for-matching-mode (mode list)
  "Set `smart-jump-list' with LIST for every buffer that matches MODE."
  (dolist (b (buffer-list))
    (with-current-buffer b
      (when (or (bound-and-true-p mode) ;; `minor-mode'
                (eq major-mode mode)) ;; `major-mode'
        (setq smart-jump-list list)))))

(defun smart-jump-get-smart-jump-list-for-mode (mode)
  (defvar smart-jump-smart-jump-list-result nil)
  (dolist (b (buffer-list) smart-jump-smart-jump-list-result)
    (with-current-buffer b
      (when (eq major-mode mode)
        (setq smart-jump-smart-jump-list-result smart-jump-list)))))

(ert-deftest smart-jump-no-registration-uses-fallbacks ()
  "When mode has not been registered, calling `smart-jump' triggers fallback
functions."
  (defvar smart-jump-jump-counter nil)
  (let* ((counter 0)
         (smart-jump-jump-counter (lambda ()
                                    (interactive)
                                    (setq counter (1+ counter))))
         (smart-jump-list `((
                             :jump-fn ,smart-jump-jump-counter
                             :refs-fn ,smart-jump-jump-counter
                             :should-jump t
                             :heuristic point
                             :async nil
                             :order 0
                             ))))
    (call-interactively #'smart-jump-go)
    (call-interactively #'smart-jump-references)
    (should (equal counter 2))))

(ert-deftest smart-jump-with-errors-uses-fallbacks ()
  "When first to N-1 `smart-jump's throws an error, fallbacks are triggered."
  (defvar smart-jump-jump-counter nil)
  (let* ((counter 0)
         (smart-jump-jump-counter (lambda ()
                                    (interactive)
                                    (setq counter (1+ counter))))
         (smart-jump-list `((
                             :jump-fn (lambda () (interactive) (throw 'error))
                             :refs-fn (lambda () (interactive (throw 'error)))
                             :should-jump t
                             :heuristic error
                             :order 1
                             )
                            (
                             :jump-fn ,smart-jump-jump-counter
                             :refs-fn ,smart-jump-jump-counter
                             :should-jump t
                             :heuristic point
                             :async nil
                             :order 100))))
    (call-interactively #'smart-jump-go)
    (call-interactively #'smart-jump-references)
    (should (equal counter 2))))

(ert-deftest smart-jump-no-errors-no-fallbacks ()
  "When there are no errors, jumps in smart-jump-list are called successfully.
No fallbacks are triggered."
  (defvar smart-jump-fallback-counter nil)
  (defvar smart-jump-jump-counter nil)
  (let* ((counter 0)
         (smart-jump-jump-counter (lambda ()
                                    (interactive)
                                    (setq counter (1+ counter))))
         (smart-jump-fallback-counter (lambda ()
                                        (interactive)
                                        ;; If fallback is called at all, this
                                        ;; test has failed.
                                        (setq counter -1)))
         (smart-jump-list `((
                             :jump-fn ,smart-jump-jump-counter
                             :refs-fn ,smart-jump-jump-counter
                             :should-jump t
                             :heuristic error
                             )
                            (
                             :jump-fn ,smart-jump-fallback-counter
                             :refs-fn ,smart-jump-fallback-counter
                             :should-jump t
                             :heuristic point
                             :async nil
                             :order 100))))
    (call-interactively #'smart-jump-go)
    (call-interactively #'smart-jump-references)
    (should (equal counter 2))))

(ert-deftest smart-jump-:should-jump:-is-false-uses-fallback ()
  "When the 1 -> N-1 jump's :should-jump is false, it should skip that jump
and use the fallback instead."
  (defvar smart-jump-fallback-counter nil)
  (defvar smart-jump-jump-counter nil)
  (let* ((counter 0)
         (smart-jump-jump-counter (lambda ()
                                    (interactive)
                                    ;; Test fails if this is hit.
                                    (setq counter -1)))
         (smart-jump-fallback-counter (lambda ()
                                        (interactive)
                                        (setq counter (1+ counter))))
         (smart-jump-list `((
                             :jump-fn ,smart-jump-jump-counter
                             :refs-fn ,smart-jump-jump-counter
                             :should-jump nil
                             :heuristic error
                             )
                            (
                             :jump-fn ,smart-jump-fallback-counter
                             :refs-fn ,smart-jump-fallback-counter
                             :should-jump t
                             :heuristic point
                             :async nil
                             :order 100
                             ))))
    (call-interactively #'smart-jump-go)
    (call-interactively #'smart-jump-references)
    (should (equal counter 2))))

(ert-deftest smart-jump-:should-jump:-is-function-is-false-uses-fallback ()
  "When the 1 -> N-1 jump's :should-jump is a function and also false, it should
skip that jump and use the fallback instead. This is making sure the
implementation doesn't use the true-ness of the function symbol when determining
whether or not it should jump."
  (defvar smart-jump-fallback-counter nil)
  (defvar smart-jump-jump-counter nil)
  (let* ((counter 0)
         (smart-jump-jump-counter (lambda ()
                                    (interactive)
                                    (message "TEST??")
                                    ;; Test fails if this is hit.
                                    (setq counter -1)))
         (smart-jump-fallback-counter (lambda ()
                                        (interactive)
                                        (setq counter (1+ counter))))
         (smart-jump-list `((
                             :jump-fn ,smart-jump-jump-counter
                             :refs-fn ,smart-jump-jump-counter
                             :should-jump (lambda () nil)
                             :heuristic error
                             )
                            (
                             :jump-fn ,smart-jump-fallback-counter
                             :refs-fn ,smart-jump-fallback-counter
                             :should-jump t
                             :heuristic point
                             :async nil
                             :order 100
                             ))))
    (call-interactively #'smart-jump-go)
    (call-interactively #'smart-jump-references)
    (should (equal counter 2))))

(ert-deftest smart-jump-register-updates-current-mode ()
  "When calling `smart-jump-register', current buffer's `smart-jump-list'
should be updated."
  ;; Keep track of `smart-jump-list' so we can reset the state back
  ;; to normal after the test runs.
  (defvar smart-jump-old-smart-jump-list nil)
  (setq smart-jump-old-smart-jump-list
        (smart-jump-get-smart-jump-list-for-mode 'emacs-lisp-mode))
  (with-temp-buffer
    (let ((major-mode 'emacs-lisp-mode)
          (smart-jump-list '()))
      (smart-jump-register :modes 'emacs-lisp-mode
                           :jump-fn 'dummy)
      (should (equal (plist-get (car smart-jump-list) :jump-fn) 'dummy))
      ;; Reset the state back...
      (smart-jump-set-smart-jump-list-for-matching-mode
       'emacs-lisp-mode smart-jump-old-smart-jump-list))))

(ert-deftest smart-jump-register-adds-hook-only-once ()
  "When calling `smart-jump-register' multiple times, only one hook should
be added."
  ;; Keep track of `smart-jump-list' so we can reset the state back
  ;; to normal after the test runs.
  (defvar smart-jump-old-smart-jump-list nil)
  (setq smart-jump-old-smart-jump-list
        (smart-jump-get-smart-jump-list-for-mode 'emacs-lisp-mode))
  (with-temp-buffer
    (let ((major-mode 'emacs-lisp-mode)
          (emacs-lisp-mode-hook nil))
      (smart-jump-register :modes 'emacs-lisp-mode
                           :jump-fn 'dummy)
      (should (equal (length emacs-lisp-mode-hook) 1))
      (smart-jump-register :modes 'emacs-lisp-mode
                           :jump-fn 'dummy)
      (should (equal (length emacs-lisp-mode-hook) 1))
      (smart-jump-set-smart-jump-list-for-matching-mode
       'emacs-lisp-mode smart-jump-old-smart-jump-list))))

(ert-deftest smart-jump-register-adds-one-hook-per-jump-definition ()
  "Register a `smart-jump' using :jump-fn as the key. A mode can contain many
:jump-fn's."
  ;; Keep track of `smart-jump-list' so we can reset the state back
  ;; to normal after the test runs.
  (defvar smart-jump-old-smart-jump-list nil)
  (setq smart-jump-old-smart-jump-list
        (smart-jump-get-smart-jump-list-for-mode 'emacs-lisp-mode))
  (with-temp-buffer
    (let ((major-mode 'emacs-lisp-mode)
          (smart-jump-list '())
          (emacs-lisp-mode-hook nil))
      (smart-jump-register :modes 'emacs-lisp-mode
                           :jump-fn 'dummy)
      (should (equal (length emacs-lisp-mode-hook) 1))
      (smart-jump-register :modes 'emacs-lisp-mode
                           :jump-fn 'dummy-2)
      (should (equal (length emacs-lisp-mode-hook) 2))
      (smart-jump-set-smart-jump-list-for-matching-mode
       'emacs-lisp-mode smart-jump-old-smart-jump-list))))

(ert-deftest smart-jump-register-registrations-are-sorted ()
  "`smart-jump's registered are sorted according to their :order.
Lower :order numbers should be sorted up front."
  (defvar smart-jump-old-smart-jump-list nil)
  (setq smart-jump-old-smart-jump-list
        (smart-jump-get-smart-jump-list-for-mode 'emacs-lisp-mode))
  (with-temp-buffer
    (let ((major-mode 'emacs-lisp-mode)
          (smart-jump-list '())
          (emacs-lisp-mode-hook nil))
      (smart-jump-register :modes 'emacs-lisp-mode
                           :jump-fn 'dummy
                           :order 2)
      (smart-jump-register :modes 'emacs-lisp-mode
                           :jump-fn 'dummy-2
                           :order 1)
      (should (equal (plist-get (car smart-jump-list) :jump-fn) 'dummy-2))
      (smart-jump-set-smart-jump-list-for-matching-mode
       'emacs-lisp-mode smart-jump-old-smart-jump-list))))

;;; smart-jump-test.el ends here
