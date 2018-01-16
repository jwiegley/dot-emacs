;;; test code for deferred.el  -*- lexical-binding: t; -*-

;; Copyright (C) 2010, 2011  SAKURAI Masashi
;; Author: SAKURAI Masashi <m.sakurai at kiwanami.net>

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; Run tests:
;; $ emacs -batch -l test-deferred.el -f ert-run-tests-batch-and-exit


(require 'ert)
(require 'undercover)
(undercover "deferred.el"
            (:send-report nil)
            (:report-file "/tmp/undercover-report.json"))
(require 'deferred)
(require 'cl-lib)
(require 'pp)

(defmacro should= (a &rest b)
  `(should (equal ,a (progn ,@b)))
  )

(defmacro aand (test &rest rest)
  `(let ((it ,test))
     (if it ,(if rest (macroexpand-all `(aand ,@rest)) 'it))))

(defmacro $ (&rest elements)
  `(let (it)
     ,@(cl-loop for i in elements
                with it = nil
                collect
                `(setq it ,i))
     it))

(defmacro dnew(&rest aforms)
  (if aforms
      `(deferred:new (lambda (x) ,@aforms))
    `(deferred:new)))

(defmacro next(&rest aforms)
  `(deferred:next (lambda (x) ,@aforms)))

(defmacro nextc(d &rest aforms)
  `(deferred:nextc ,d (lambda (x) ,@aforms)))

(defmacro errorc(d &rest aforms)
  `(deferred:error ,d (lambda (e) ,@aforms)))

(defmacro errorf(d formatstr)
  `(deferred:error ,d (lambda (e) (error ,formatstr e))))

(defmacro cancelc(d)
  `(deferred:cancel ,d))

(defmacro wait(msec)
  `(deferred:wait ,msec))

(defmacro dloop(&rest body)
  `(deferred:loop ,@body))

(defmacro parallel(&rest args)
  `(deferred:parallel ,@args))

(defmacro earlier(&rest args)
  `(deferred:earlier ,@args))

(defmacro flush ()
  `(deferred:flush-queue!))

(defmacro clear ()
  `(setq deferred:queue nil))

(defmacro dtest (&rest form)
  `(progn
     (clear)
     (let (last-value)
       (nextc
        ($
         ,@form)
        (setq last-value x))
       (flush)
       last-value)))

(defmacro wtest (time &rest form)
  `(progn
     (clear)
     (let (last-value)
       (nextc
        ($
         ,@form)
        (setq last-value x))
       (while (null last-value)
         (sit-for ,time))
       (flush)
       last-value)))

(defun deferred:setTimeout (f _msec)
  "overrided for test"
  (deferred:call f))

(defun deferred:cancelTimeout (id)
  "overrided for test"
  (when (deferred-p id)
    (deferred:cancel id)))

(defun deferred:run-with-idle-timer (_sec f)
  "overrided for test"
  (deferred:call f))

(defun deferred:not-called-func (&optional m)
  (error "Must not be called!! %s" m))



(ert-deftest deferred-primitive-simple ()
  "> call-lambda simple"
  (should= 1 (deferred:call-lambda (lambda ()  1)))
  (should= 1 (deferred:call-lambda (lambda ()  1) 1))
  (should= 1 (deferred:call-lambda (lambda (_) 1)))
  (should= 1 (deferred:call-lambda (lambda (_) 1) 1))
  (should= 1 (deferred:call-lambda (deferred:lambda () 1)))
  (should= 1 (deferred:call-lambda (deferred:lambda () 1) 1))
  (should= nil (deferred:call-lambda 'car))
  (should= 2 (deferred:call-lambda 'car '(2 1)))
  (should= nil (deferred:call-lambda (symbol-function 'car)))
  (should= 2 (deferred:call-lambda (symbol-function 'car) '(2 1))))

(ert-deftest deferred-primitive-scope ()
  "> call-lambda lexical-scope"
  (should= 3 (let ((st 1))
              (deferred:call-lambda
                (lambda () (+ st 2)))))
  (should= 3  (let ((st 1))
               (deferred:call-lambda
                 (lambda () (+ st 2)) 0)))
  (should= 3 (let ((st 1))
              (deferred:call-lambda
                (lambda (_) (+ st 2)))))
  (should= 3  (let ((st 1))
               (deferred:call-lambda
                 (lambda (_) (+ st 2)) 0))))

(when (version<= "25.0" emacs-version)
  ;; Emacs 24 doesn’t know how to byte-compile closures, so run this test only
  ;; under Emacs 25.
  (ert-deftest deferred-primitive-compile ()
    "> call-lambda byte-compile"
    (should= 1 (deferred:call-lambda (byte-compile (lambda (_) 1))))
    (should= 1 (deferred:call-lambda (byte-compile (lambda (_) 1)) 1))
    (should= 1 (deferred:call-lambda (byte-compile (lambda () 1))))
    (should= 1 (deferred:call-lambda (byte-compile (lambda () 1)) 1))

    (should= 3 (let ((st 1))
                 (deferred:call-lambda
                   (byte-compile (lambda () (+ st 2))))))
    (should= 3  (let ((st 1)) ;ng
                  (deferred:call-lambda
                    (byte-compile (lambda () (+ st 2))) 0)))
    (should= 3 (let ((st 1))
                 (deferred:call-lambda
                   (byte-compile (lambda (_) (+ st 2))))))
    (should= 3  (let ((st 1)) ;ng
                  (deferred:call-lambda
                    (byte-compile (lambda (_) (+ st 2))) 0)))

    (should-error
     (deferred:call-lambda
       (lambda (x) (signal 'wrong-number-of-arguments '("org"))))
     :type 'wrong-number-of-arguments)))

(ert-deftest deferred-basic ()
  "Basic test for deferred functions."
  (should (deferred-p
            ;; function test
            (deferred:new)))
  (should (null
           ;; basic cancel test
           (let ((d (deferred:next 'deferred:not-called-func)))
             (cancelc d)
             (flush))))
  (should (deferred-p
            ;; basic post function test
            (progn
              (clear)
              (let ((d (dnew)))
                (nextc d x)
                (deferred:exec-task d 'ok "ok!")))))
  (should (deferred-p
            ;; basic error post function test
            (progn
              (clear)
              (let ((d (dnew)))
                (deferred:error d (lambda (e) e))
                (deferred:exec-task d 'ng "error"))))))

(ert-deftest deferred-basic-result-propagation ()
  "> result propagation"
  (should= 'ok
          ;; value saving test
          (let ((d (deferred:succeed 1)))
            (deferred:status d)))

  (should= 1
          ;; value saving test
          (let ((d (deferred:succeed 1)))
            (deferred-value d)))

  (should= nil
          ;; value clearing test
          (let ((d (deferred:succeed 1)))
            (deferred:set-next d (dnew))
            (deferred:status d)))

  (should= 1
          ;; value propagating test
          (let ((d (deferred:succeed 1))
                (nd (dnew)))
            (deferred:set-next d nd)
            (deferred-value nd))))

(ert-deftest deferred-basic-error-propagation ()
  "> error propagation"
  (should= 'ok
          ;; value saving test
          (let ((d (deferred:succeed 1)))
            (deferred:status d)))

  (should= 1
          ;; value saving test
          (let ((d (deferred:succeed 1)))
            (deferred-value d)))

  (should= nil
          ;; value clearing test
          (let ((d (deferred:succeed 1)))
            (deferred:set-next d (dnew))
            (deferred:status d)))

  (should= 1
          ;; value propagating test
          (let ((d (deferred:succeed 1))
                (nd (dnew)))
            (deferred:set-next d nd)
            (deferred-value nd))))

(ert-deftest deferred-main-chain ()
  ">>> Main Test / Chaining"

  (should= '(2 1 0)
          ;; basic deferred chain test
          (clear)
          (let (vs)
            ($ (next (push 1 vs))
               (nextc it (push 2 vs)))
            (push 0 vs)
            (flush)
            vs))

  (should= "errorback called"
          ;; basic errorback test
          (dtest (next (error "errorback"))
                 (errorc it (concat (cadr e) " called"))))

  (should= "next callback called"
          ;; error recovery test
          (dtest
           (next (error "callback called"))
           (errorc it (cadr e))
           (nextc it (concat "next " x))))

  (should= '(error "second errorback called")
          ;; error recovery test 2
          (dtest
           (next (error "callback called"))
           (nextc it (deferred:not-called-func "second errorback1"))
           (errorc it e)
           (errorc it (deferred:not-called-func "second errorback2"))
           (nextc it (error "second errorback called"))
           (nextc it "skipped")
           (errorc it e)))

  (should= "start errorback ok1"
          ;; start errorback test1
           (let (message-log-max)
             (cl-letf (((symbol-function 'message) (lambda (&rest args) args)))
            (let ((d (dnew)))
              (dtest
               (progn
                 (deferred:errorback d "start errorback") d)
               (nextc it (deferred:not-called-func "ERROR : start errorback"))
               (errorc it (cadr e))
               (nextc it (concat x " ok1")))))))

  (should= "post errorback ok2"
          ;; start errorback test1
          (let ((d (dnew)))
            (dtest
             (progn (deferred:errorback-post d "post errorback") d)
             (nextc it (deferred:not-called-func "ERROR : post errorback"))
             (errorc it (cadr e))
             (nextc it (concat x " ok2")))))

  (should= "Child deferred chain"
          ;; child deferred chain test
          (dtest
           (next
            (next "Child deferred chain"))
           (errorf it "Error on simple chain : %s")))

  (should= "chain watch ok"
          ;; watch chain: normal
          (let ((val "><"))
            (dtest
             (next "chain")
             (deferred:watch it
               (lambda (_) (setq val " watch") nil))
             (nextc it (concat x val " ok")))))

  (should= "error!! watch ok"
          ;; watch chain: error
          (let ((val "><"))
            (dtest
             (next "chain")
             (nextc it (error "error!!"))
             (deferred:watch it (lambda (x) (setq val " watch") nil))
             (errorc it (concat (cadr e) val " ok")))))

  (should= "chain watch ok2"
          ;; watch chain: normal
          (let ((val "><"))
            (dtest
             (next "chain")
             (deferred:watch it
               (lambda (_) (error "ERROR")))
             (nextc it (concat x " watch ok2"))))))

(ert-deftest deferred-async-connect ()
  "> async connect"
  (should= "saved result!"
          ;; asynchronously connect deferred and propagate a value
          (let (d ret)
            (clear)
            (setq d (next "saved "))
            (deferred:callback d)
            (flush)
            (setq d (nextc d (concat x "result")))
            (nextc d (setq ret (concat x "!")))
            ret)))

(ert-deftest deferred-global-onerror ()
  "> global onerror"
  (should= "ONERROR"
          ;; default onerror handler test
           (let (ret)
             (let ((deferred:onerror
                     (lambda (e) (setq ret (concat "ON" (error-message-string e))))))
               (dtest
                (next (error "ERROR")))
               ret))))

(ert-deftest deferred-async-call ()
  "> async call"
  (should= "ASYNC CALL"
          ;; basic async 'call' test
          (dtest
           (deferred:call 'concat "ASYNC" " " "CALL")))

  (should= "ASYNC APPLY"
          ;; basic async 'apply' test
          (dtest
           (deferred:apply 'concat '("ASYNC" " " "APPLY")))))

(ert-deftest deferred-wait ()
  "> wait"
  (should= "wait ok"
          ;; basic wait test
          (dtest
           (wait 1)
           (nextc it (if (< x 300) "wait ok" x))
           (errorf it "Error on simple wait : %s")))

  (should= "waitc ok"
          ;; wait chain test
          (dtest
           (wait 1)
           (nextc it "wait")
           (nextc it (wait 1))
           (nextc it (if (< x 300) "waitc ok" x))
           (errorf it "Error on simple wait chain : %s")))

  (should= nil
          ;; wait cancel test
          (dtest
           (wait 1000)
           (cancelc it)
           (nextc it (deferred:not-called-func "wait cancel"))))

  (should= "wait-idle ok"
          ;; basic wait test
          (dtest
           (deferred:wait-idle 1)
           (nextc it (if (< x 300) "wait-idle ok" x))
           (errorf it "Error on simple wait-idle : %s")))

  (should= "wait-idlec ok"
          ;; wait chain test
          (dtest
           (deferred:wait-idle 1)
           (nextc it "wait")
           (nextc it (deferred:wait-idle 1))
           (nextc it (if (< x 300) "wait-idlec ok" x))
           (errorf it "Error on simple wait-idle chain : %s")))

  (should= nil
          ;; wait cancel test
          (dtest
           (deferred:wait-idle 1000)
           (cancelc it)
           (nextc it (deferred:not-called-func "wait-idle cancel")))))

(ert-deftest deferred-sync-connect ()
  "> synchronized connection and wait a value"
  (should= "sync connect1"
          ;; real time connection1
          (dtest
           (deferred:succeed "sync ")
           (nextc it
                  (concat x "connect1"))))

  (should= "sync connect11"
          ;; real time connection11
          (dtest
           (deferred:succeed "sync ")
           (nextc it
                  (concat x "connect1"))
           (nextc it
                  (concat x "1"))))

  (should= "connect2"
          ;; real time connection1
          (dtest
           (deferred:succeed "sync ")
           (nextc it
                  (next "connect"))
           (nextc it
                  (concat x "2"))))

  (should= "connect!! GO"
          ;; real time connection2
          (dtest
           (deferred:succeed "sync ")
           (nextc it
                  ($
                   (next "connect")
                   (nextc it (concat x "!!"))))
           (nextc it
                  (concat x " GO")))))

(ert-deftest deferred-try ()
  "> try-catch-finally"

  (should= "try"
          ;; try block
          (dtest
           (deferred:try
             (next "try"))))

  (should= "try"
          ;; try catch block
          (dtest
           (deferred:try
             (next "try")
             :catch
             (lambda (e) (concat "CATCH:" e)))))

  (should= "try-finally"
          ;; try catch finally block
          (let (val)
            (dtest
             (deferred:try
               (next "try")
               :finally
               (lambda (x) (setq val "finally")))
             (nextc it (concat x "-" val)))))

  (should= "try-finally2"
          ;; try catch finally block
          (let (val)
            (dtest
             (deferred:try
               (next "try")
               :catch
               (lambda (e) (concat "CATCH:" e))
               :finally
               (lambda (x) (setq val "finally2")))
             (nextc it (concat x "-" val)))))

  (should= "try-catch:err"
          ;; try block
          (dtest
           (deferred:try
             ($ (next "start")
                (nextc it (error "err"))
                (nextc it (deferred:not-called-func x)))
             :catch
             (lambda (e) (concat "catch:" (cadr e))))
           (nextc it (concat "try-" x))))

  (should= "try-catch:err-finally"
          ;; try catch finally block
          (let (val)
            (dtest
             (deferred:try
               ($ (next "start")
                  (nextc it (error "err"))
                  (nextc it (deferred:not-called-func x)))
               :catch
               (lambda (e) (concat "catch:" (cadr e)))
               :finally
               (lambda (x) (setq val "finally")))
             (nextc it (concat "try-" x "-" val))))))



(ert-deftest deferred-loop ()
  "> loop"
  (should= 10
          ;; basic loop test
          (let ((v 0))
            (dtest
             (dloop 5 (lambda (i) (setq v (+ v i))))
             (errorf it "Error on simple loop calling : %s"))
            v))

  (should= "loop ok 4"
          ;; return value for a loop
          (dtest
           (dloop 5 (lambda (i) i))
           (nextc it (format "loop ok %i" x))
           (errorf it "Error on simple loop calling : %s")))

  (should= "nested loop ok (4 nil 3 2 1 0)"
          ;; nested deferred task in a loop
          (let (count)
            (dtest
             (dloop 5 (lambda (i)
                        (push i count)
                        (if (eql i 3) (next (push x count)))))
             (nextc it (format "nested loop ok %s" count))
             (errorf it "Error on simple loop calling : %s"))
            )
          )

  (should= '(6 4 2)
          ;; do-loop test
          (let (count)
            (dtest
             (dloop '(1 2 3)
                    (lambda (x) (push (* 2 x) count)))
             (errorf it "Error on do-loop calling : %s"))))

  (should= nil
          ;; zero times loop test
          (dtest
           (dloop 0 (lambda (i) (deferred:not-called-func "zero loop")))))

  (should= nil
          ;; loop cancel test
          (dtest
           (dloop 3 (lambda (i) (deferred:not-called-func "loop cancel")))
           (cancelc it)))

  (should= "loop error!"
          ;; loop error recover test
          (dtest
           (deferred:loop 5
             (lambda (i) (if (= 2 i) (error "loop error"))))
           (nextc it (deferred:not-called-func))
           (errorc it (format "%s!" (cadr e)))
           (nextc it x)))

  (should= "loop error catch ok"
          ;; try catch finally test
          (let ((body (lambda ()
                        (deferred:loop 5
                          (lambda (i) (if (= 2 i) (error "loop error")))))))
            (dtest
             (next  "try ") ; try
             (nextc it (funcall body)) ; body
             (errorc it (format "%s catch " (cadr e))) ; catch
             (nextc it (concat x "ok"))))) ; finally

  (should= "4 ok"
          ;; try catch finally test
          (let ((body (lambda ()
                        (deferred:loop 5
                          (lambda (i) i)))))
            (dtest
             (next  "try ") ; try
             (nextc it (funcall body)) ; body
             (errorc it (format "%s catch " e)) ; catch
             (nextc it (format "%s ok" x))))) ; finally
  )



(ert-deftest deferred-parallel ()
  "> parallel"
  (should= nil
          ;; nil test
          (dtest
           (parallel '())))

  (should= '(1)
          ;; single job test: argument
          (dtest
           (parallel
            (next 1))))

  (should= '(1)
          ;; single job test: function
          (dtest
           (parallel
            (lambda () 1))))

  (should= '(1)
          ;; single job test: list
          (dtest
           (parallel
            (list (next 1)))))

  (should= '((a . 1))
          ;; single job test: alist
          (dtest
           (parallel
            (list (cons 'a (next 1))))))

  (should= '(0 1)
          ;; simple parallel test: just return value
          (dtest
           (parallel
            (next 0) (next 1))))

  (should= '(13 14)
          ;; simple parallel test: list
          (dtest
           (parallel
            (list (next 13)
                  (next 14)))))

  (should= '((a . 20) (b . 30))
          ;; simple parallel test: alist
          (dtest
           (parallel
            (list (cons 'a (next 20))
                  (cons 'b (next 30))))))

  (should= '(0 1)
          ;; simple parallel test: function list
          (dtest
           (parallel
            (lambda () 0) (lambda () 1))))

  (should= '(0 1)
          ;; nested deferred and order change test
          (dtest
           (parallel
            (lambda () (next 0))
            (next 1))))

  (should= "((error ERROR) OK (error ERROR2))"
          ;; error handling
          (dtest
           (parallel
            (next (error "ERROR")) (next "OK") (next (error "ERROR2")))
           (nextc it (format "%s" x))))

  (should= "((error ERROR) (error ERROR2))"
          ;; failed test
          (dtest
           (parallel
            (next (error "ERROR")) (next (error "ERROR2")))
           (nextc it (format "%s" x))))

  (should= "((b . OK) (a error ERROR) (c error ERROR2))"
          ;; error handling
          (dtest
           (parallel
            (cons 'a (next (error "ERROR")))
            (cons 'b (next "OK"))
            (cons 'c (next (error "ERROR2"))))
           (nextc it (format "%s" x))))

  (should= "((a error ERROR) (b error ERROR2))"
          ;; failed test
          (dtest
           (parallel
            (cons 'a (next (error "ERROR")))
            (cons 'b (next (error "ERROR2"))))
           (nextc it (format "%s" x))))

  (should= nil
          ;; parallel cancel test
          (dtest
           (parallel
            (list (next (deferred:not-called-func "parallel 1"))
                  (next (deferred:not-called-func "parallel 2"))))
           (cancelc it)))

  (should= "nest parallel ok"
          ;; parallel next
          (let* ((flow (lambda (x)
                         (parallel
                          (next "nest ")
                          (next "parallel ")))))
            (dtest
             (next  "start ")
             (nextc it (funcall flow x))
             (nextc it (apply 'concat x))
             (nextc it (concat x "ok")))))

  (should= "arrived (1) ok"
          ;; arrived one deferred
          (dtest
           (parallel (deferred:succeed 1))
           (nextc it (format "arrived %s ok" x))))

  (should= "arrived (1 2) ok"
          ;; arrived deferreds
          (dtest
           (parallel (deferred:succeed 1) (deferred:succeed 2))
           (nextc it (format "arrived %s ok" x)))))



(ert-deftest deferred-earlier ()
  "> earlier"
  (should= nil
          ;; nil test
          (dtest
           (earlier '())))

  (should= 1
          ;; single job test: argument
          (dtest
           (earlier
            (nextc (wait 10) 1))
           (nextc it x)))

  (should= 1
          ;; single job test: function
          (dtest
           (earlier
            (lambda () 1))
           (nextc it x)))

  (should= 1
          ;; single job test: list
          (dtest
           (earlier
            (list (next 1)))
           (nextc it x)))

  (should= '(a . 1)
          ;; single job test: alist
          (dtest
           (earlier
            (list (cons 'a (next 1))))
           (nextc it x)))

  (should= '0
          ;; simple earlier test
          (dtest
           (earlier
            (next 0) (next 1))
           (nextc it x)))

  (should= '11
          ;; simple earlier test: argument
          (dtest
           (earlier
            (next 11) (next 12))
           (nextc it x)))

  (should= '13
          ;; simple earlier test: list
          (dtest
           (earlier
            (list (next 13) (next 14)))
           (nextc it x)))

  (should= '(a . 20)
          ;; simple earlier test: alist
          (dtest
           (earlier
            (list (cons 'a (next 20))
                  (cons 'b (next 30))))
           (nextc it x)))

  (should= '0
          ;; simple earlier test: function list
          (dtest
           (earlier
            (lambda () 0) (lambda () 1))
           (nextc it x)))

  (should= '1
          ;; nested deferred and order change test
          (dtest
           (earlier
            (lambda () (dnew 0))
            (next 1))))

  (should= "OK"
          ;; error handling
          (dtest
           (earlier
            (next (error "ERROR")) (next "OK") (next (error "ERROR2")))
           (nextc it x)))

  (should= nil
          ;; failed test
          (dtest
           (earlier
            (next (error "ERROR")) (next (error "ERROR2")))
           (nextc it x)))

  (should= '(b . "OK")
          ;; error handling
          (dtest
           (earlier
            (cons 'a (next (error "ERROR")))
            (cons 'b (next "OK"))
            (cons 'c (next (error "ERROR2"))))
           (nextc it x)))

  (should= nil
          ;; failed test
          (dtest
           (earlier
            (cons 'a (next (error "ERROR")))
            (cons 'b (next (error "ERROR2"))))
           (nextc it x)))

  (should= nil
          ;; cancel test
          (dtest
           (earlier
            (list (next (deferred:not-called-func "earlier 1"))
                  (next (deferred:not-called-func "earlier 2"))))
           (cancelc it)))

  (should= "arrived 1 ok"
          ;; arrived one deferred
          (dtest
           (earlier (deferred:succeed 1))
           (nextc it (format "arrived %s ok" x))))

  (should= "arrived 1 ok"
          ;; arrived deferreds
          (dtest
           (earlier (deferred:succeed 1) (deferred:succeed 2))
           (nextc it (format "arrived %s ok" x)))))

(ert-deftest deferred-sync! ()
  (should= "foo"
           (deferred:$
             (deferred:next
               (lambda ()
                 "foo"))
             (deferred:sync! it))))

;; process

(ert-deftest deferred-process ()
  "> Process"
  (should=
   (with-temp-buffer
     (call-process "pwd" nil t nil)
     (buffer-string))
   (wtest 0.1 ;; maybe fail in some environments...
          (deferred:process "pwd")))

  (should=
   (with-temp-buffer
     (call-process "pwd" nil t nil)
     (buffer-string))
   (wtest 0.1 ;; maybe fail in some environments...
          (deferred:process "pwd" nil)))

  (should=
   (length (buffer-list))
   (deferred:cancel (deferred:process "pwd" nil))
   (length (buffer-list)))

  (should= 0
          (dtest
           (deferred:process "pwd---")
           (nextc it (deferred:not-called-func))
           (errorc it (string-match "^Searching for program" (cadr e)))))

  (should=
   (with-temp-buffer (call-process "pwd" nil t nil)
                     (buffer-string))
   (wtest 0.1
          (wait 0.1)
          (deferred:processc it "pwd" nil)))

  (should=
   (with-temp-buffer
     (call-process "ls" nil t "-1")
     (buffer-string))
   (wtest 0.1 ;; maybe fail in some environments...
          (deferred:process-buffer "ls" "-1")
          (nextc it
                 (unless (buffer-live-p x)
                   (error "Not live buffer : %s" x))
                 (with-current-buffer x (buffer-string)))))

  (should=
   (with-temp-buffer
     (call-process "ls" nil t "-1")
     (buffer-string))
   (wtest 0.1 ;; maybe fail in some environments...
          (wait 0.1)
          (deferred:process-bufferc it "ls" "-1")
          (nextc it
                 (unless (buffer-live-p x)
                   (error "Not live buffer : %s" x))
                 (with-current-buffer x (buffer-string)))))

  (should=
   (length (buffer-list))
   (deferred:cancel (deferred:process-buffer "ls" nil))
   (length (buffer-list)))

  (should= 0
          (dtest
           (deferred:process-buffer "pwd---")
           (nextc it (deferred:not-called-func))
           (errorc it (string-match "^Searching for program" (cadr e)))))

  ;;shell

  (should=
   (with-temp-buffer
     (call-process-shell-command "pwd" nil t nil)
     (buffer-string))
   (wtest 0.1 ;; maybe fail in some environments...
          (deferred:process-shell "pwd")))

  (should=
   (with-temp-buffer
     (call-process-shell-command "pwd" nil t nil)
     (buffer-string))
   (wtest 0.1 ;; maybe fail in some environments...
          (deferred:process-shell "pwd" nil)))

  (should=
   (length (buffer-list))
   (deferred:cancel (deferred:process-shell "pwd" nil))
   (length (buffer-list)))

  (should= "ERROR"
          (wtest 0.1
                 (deferred:process-shell "lsasfdsadf")
                 (nextc it (deferred:not-called-func))
                 (errorc it "ERROR")))

  (should=
   (with-temp-buffer (call-process-shell-command "pwd" nil t nil)
                     (buffer-string))
   (wtest 0.1
          (wait 0.1)
          (deferred:process-shellc it "pwd" nil)))

  (should=
   (with-temp-buffer
     (call-process-shell-command "ls" nil t "-1")
     (buffer-string))
   (wtest 0.1 ;; maybe fail in some environments...
          (deferred:process-shell-buffer "ls" "-1")
          (nextc it
                 (unless (buffer-live-p x)
                   (error "Not live buffer : %s" x))
                 (with-current-buffer x (buffer-string)))))

  (should=
   (with-temp-buffer
     (call-process-shell-command "ls" nil t "-1")
     (buffer-string))
   (wtest 0.1 ;; maybe fail in some environments...
          (wait 0.1)
          (deferred:process-shell-bufferc it "ls" "-1")
          (nextc it
                 (unless (buffer-live-p x)
                   (error "Not live buffer : %s" x))
                 (with-current-buffer x (buffer-string)))))

  (should=
   (length (buffer-list))
   (deferred:cancel (deferred:process-shell-buffer "ls" nil))
   (length (buffer-list)))

  (should= "ERROR"
          (wtest 0.1
                 (deferred:process-shell-buffer "lssaf")
                 (nextc it (deferred:not-called-func))
                 (errorc it "ERROR"))))
