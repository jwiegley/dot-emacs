;;; test code for concurrent.el  -*- lexical-binding: t; -*-

;; Copyright (C) 2010  SAKURAI Masashi
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

;; How to run this test ?
;; $ emacs -L . -L $HOME/.emacs.d/elisp -batch -l deferred -l concurrent -l test-concurrent -f cc:test-all

(require 'undercover)
(undercover "concurrent.el"
            (:send-report nil)
            (:report-file "/tmp/undercover-report.json"))
(require 'concurrent)
(require 'cl-lib)
(require 'pp)
(require 'ert)

(defmacro cc:debug (d msg &rest args)
  `(deferred:nextc ,d
     (lambda (x) (funcall 'message ,msg ,@args) x)))

;; generator

(defun cc:fib-gen (callback)
  (let ((a1 0) (a2 1)
        (callback callback))
        (cc:generator
         callback
         (yield a1)
         (yield a2)
         (while t
           (let ((next (+ a1 a2)))
             (setq a1 a2
                   a2 next)
             (yield next))))))

(defun cc:test-fib-gen ()
  (let* ((count 0)
         (dfinish (deferred:new))
         gen
         (cc (lambda (x)
               (cond
                ((= count 10)
                 (deferred:callback
                   dfinish
                   (if (= x 55) t
                     (format "Fib 10 = 55 -> %s" x))))
                (t
                 (cl-incf count)
                 (deferred:call gen))))))
    (setq gen (cc:fib-gen cc))
    (deferred:call gen)
    dfinish))

;; (cc:debug (cc:test-fib-gen) "Fib10 : %s" x)

;; thread

(defun cc:test-thread ()
  (let ((dfinish (deferred:new))
        (result nil) (start-time (float-time))
        (count 0) (end 20))
    (push 1 result)
    (cc:thread
     60
     (push 2 result)
     (while (> end (cl-incf count))
       (when (= 0 (% count 10))
         (push count result)))
     (push 99 result)
     (setq result (reverse result))
     (deferred:callback dfinish
       (and (or (equal '(1 2 10 99) result) result)
            (let ((elapsed-time (- (float-time) start-time)))
              (or (and (< 1.0 elapsed-time) (< elapsed-time 6)) elapsed-time)))))
    dfinish))

;; (cc:debug (cc:test-thread) "Thread : %s" x)

;; semaphore

(defun cc:test-semaphore1 ()
  (let* ((result nil)
         (dfinish (deferred:new
                    (lambda (_)
                      (setq result (reverse result))
                      (or (equal '(1 2 5 6 (size . 1) 3 7 8 canceled (size . 0)) result)
                          result))))
         (smp (cc:semaphore-create 1)))

    (push 1 result)

    (deferred:nextc (cc:semaphore-acquire smp)
      (lambda(_) (push 2 result)))
    (deferred:nextc (cc:semaphore-acquire smp)
      (lambda(_) (push 3 result)))
    (deferred:nextc (cc:semaphore-acquire smp)
      (lambda(x) (push x result)))

    (deferred:$
      (deferred:next
        (lambda (_)
          (push 5 result)
          (cc:semaphore-release smp)
          (push 6 result)))
      (deferred:nextc it
        (lambda (_)
          (push (cons 'size (length (cc:semaphore-waiting-deferreds smp))) result)))
      (deferred:nextc it
        (lambda (_)
          (push 7 result)
          (cl-loop for i in (cc:semaphore-release-all smp)
                   do (deferred:callback i 'canceled))
          (push 8 result)))
      (deferred:nextc it
        (lambda (_)
          (push (cons 'size (length (cc:semaphore-waiting-deferreds smp))) result)))
      (deferred:nextc it
        (lambda (_) (deferred:callback dfinish))))

    dfinish))

;; (cc:debug (cc:test-semaphore1) "Semaphore1 : %s" x)

(defun cc:test-semaphore2 ()
  (let* ((result nil)
         (dfinish (deferred:new
                    (lambda (_)
                      (setq result (reverse result))
                      (or (equal '(0 a b c d e f g) result)
                          result))))
         (smp (cc:semaphore-create 1)))

    (push 0 result)

    (cc:semaphore-with
     smp (lambda (_)
           (deferred:nextc (cc:semaphore-acquire smp)
             (lambda (_)
               (push 'c result)
               (cc:semaphore-release smp)))
           (push 'a result)
           (deferred:nextc
             (deferred:wait 100)
             (lambda (_) (push 'b result)))))

    (cc:semaphore-with
     smp (lambda (_)
           (deferred:nextc (cc:semaphore-acquire smp)
             (lambda (_)
               (push 'g result)
               (cc:semaphore-release smp)
               (deferred:callback dfinish)))
             (push 'd result)
             (deferred:nextc
               (deferred:wait 100)
               (lambda (_)
                 (push 'e result)
                 (error "SMP CC ERR"))))
     (lambda (e)
       (cl-destructuring-bind (sym msg) e
         (when (and (eq 'error sym) (equal "SMP CC ERR" msg))
           (push 'f result)))))

    dfinish))

;; (cc:debug (cc:test-semaphore2) "Semaphore2 : %s" x)

;; Dataflow

(defun cc:test-dataflow-simple1 ()
  (let* ((result '(1))
         (dfinish (deferred:new
                    (lambda (_)
                      (setq result (reverse result))
                      (or (equal '(1 (2 . nil) 4 5 (3 . 256) (6 . 256) (7 . nil)) result)
                          result))))
         (dfenv (cc:dataflow-environment)))

    (push (cons 2 (cc:dataflow-get-sync dfenv "aaa")) result)

    (deferred:$
      (deferred:parallel
        (deferred:$
          (cc:dataflow-get dfenv "abc")
          (deferred:nextc it
            (lambda (x) (push (cons 3 x) result))))
        (deferred:$
          (deferred:next
            (lambda (_)
              (push 4 result)
              (cc:dataflow-set dfenv "abc" 256)
              (push 5 result)))))
      (deferred:nextc it
        (lambda (_)
          (push (cons 6 (cc:dataflow-get-sync dfenv "abc")) result)
          (cc:dataflow-clear dfenv "abc")
          (push (cons 7 (cc:dataflow-get-sync dfenv "abc")) result)))
      (deferred:nextc it
        (lambda (_)
          (deferred:callback dfinish))))

    dfinish))

;; (cc:debug (cc:test-dataflow-simple1) "Dataflow1 : %s" x)

(defun cc:test-dataflow-simple2 ()
  (let* ((result nil)
         (dfinish (deferred:new
                    (lambda (_)
                      (or (equal '("a.jpg:300 OK jpeg") result)
                          result))))
         (dfenv (cc:dataflow-environment)))

    (deferred:$
      (cc:dataflow-get dfenv '("http://example.com/a.jpg" 300))
      (deferred:nextc it
        (lambda (x) (push (format "a.jpg:300 OK %s" x) result)))
      (deferred:nextc it
        (lambda (_)
          (deferred:callback dfinish))))

    (cc:dataflow-set dfenv '("http://example.com/a.jpg" 300) 'jpeg)

    dfinish))

;; (cc:debug (cc:test-dataflow-simple2) "Dataflow2 : %s" x)

(defun cc:test-dataflow-simple3 ()
  (let* ((result nil)
         (dfinish (deferred:new
                    (lambda (_)
                      (or (equal '(">> 384") result)
                          result))))
         (dfenv (cc:dataflow-environment)))

    (deferred:$
      (deferred:parallel
        (cc:dataflow-get dfenv "def")
        (cc:dataflow-get dfenv "abc"))
      (deferred:nextc it
        (lambda (values)
          (apply '+ values)))
      (deferred:nextc it
        (lambda (x) (push (format ">> %s" x) result)))
      (deferred:nextc it
        (lambda (_)
          (deferred:callback dfinish))))

    (deferred:nextc (deferred:wait 0.2)
      (lambda (_)
        (cc:dataflow-set dfenv "def" 128)
        (cc:dataflow-set dfenv "abc" 256)
        (cc:dataflow-set dfenv "aaa" 512)
        ))

    dfinish))

;; (cc:debug (cc:test-dataflow-simple3) "Dataflow3 : %s" x)

(defun cc:test-dataflow-simple4 ()
  (let* ((result nil)
         (dfinish (deferred:new
                    (lambda (_)
                      (or (equal '(">> 3") result)
                          result))))
         (dfenv (cc:dataflow-environment)))

    (deferred:$
      (deferred:parallel
        (cc:dataflow-get dfenv "abc")
        (cc:dataflow-get dfenv "abc")
        (cc:dataflow-get dfenv "abc"))
      (deferred:nextc it
        (lambda (values)
          (apply '+ values)))
      (deferred:nextc it
        (lambda (x) (push (format ">> %s" x) result)))
      (deferred:nextc it
        (lambda (_)
          (deferred:callback dfinish))))

    (deferred:nextc (deferred:wait 0.2)
      (lambda (_)
        (cc:dataflow-set dfenv "abc" 1)
        ))

    dfinish))

;; (cc:debug (cc:test-dataflow-simple4) "Dataflow4 : %s" x)

(defun cc:test-dataflow-signal ()
  (let* ((result '(1))
         (dfinish (deferred:new
                    (lambda (_)
                      (setq result (reverse result))
                      (or (equal
                           '(1
                             (2 . nil)
                             (get-first ("abc"))
                             (get-waiting ("abc"))
                             4 5
                             (set ("abc"))
                             (3 . 256)
                             6 7
                             (get ("abc"))
                             (8 . 256)
                             (9 . nil)
                             (clear ("abc"))
                             (clear-all (nil))
                             )
                           result)
                          result))))
         (dfenv (cc:dataflow-environment)))

    (cl-loop for i in '(get get-first get-waiting set clear clear-all)
             do (cc:dataflow-connect dfenv i (lambda (ev) (push ev result))))

    (push (cons 2 (cc:dataflow-get-sync dfenv "aaa")) result)

    (deferred:$
      (deferred:parallel
        (deferred:$
          (cc:dataflow-get dfenv "abc")
          (deferred:nextc it
            (lambda (x) (push (cons 3 x) result))))
        (deferred:$
          (deferred:next
            (lambda (_)
              (push 4 result)
              (cc:dataflow-set dfenv "abc" 256)
              (push 5 result)))))
      (deferred:nextc it
        (lambda (_)
          (push 6 result)
          (cc:dataflow-get dfenv "abc")
          (push 7 result)))
      (deferred:nextc it
        (lambda (_)
          (push (cons 8 (cc:dataflow-get-sync dfenv "abc")) result)
          (cc:dataflow-clear dfenv "abc")
          (push (cons 9 (cc:dataflow-get-sync dfenv "abc")) result)))
      (deferred:nextc it
        (lambda (_)
          (cc:dataflow-clear-all dfenv)))
      (deferred:nextc it
        (lambda (_)
          (deferred:callback dfinish))))

    dfinish))

;; (cc:debug (cc:test-dataflow-signal) "Dataflow Signal : %s" x)


(defun cc:test-dataflow-parent1 ()
  (let* ((result '(1))
         (dfinish (deferred:new
                    (lambda (_)
                      (setq result (reverse result))
                      (or (equal
                           '(1
                             (available-parent . (("abc" . 128)))
                             (available-child . (("abc" . 128)))
                             (waiting-parent . nil)
                             (waiting-child . ("aaa"))
                             (get-sync . 256)
                             (get . 256)
                             )
                           result)
                          result))))
         (dfenv-parent (cc:dataflow-environment))
         (dfenv (cc:dataflow-environment dfenv-parent)))

    (cc:dataflow-set dfenv-parent "abc" 128)

    (deferred:$
      (deferred:parallel
        (deferred:$
          (cc:dataflow-get dfenv "aaa")
          (deferred:nextc it
            (lambda (x) (push (cons 'get x) result))))
        (deferred:$
          (deferred:next
            (lambda (_)
              (push (cons 'available-parent (cc:dataflow-get-avalable-pairs dfenv-parent)) result)
              (push (cons 'available-child  (cc:dataflow-get-avalable-pairs dfenv)) result)
              (push (cons 'waiting-parent (cc:dataflow-get-waiting-keys dfenv-parent)) result)
              (push (cons 'waiting-child  (cc:dataflow-get-waiting-keys dfenv)) result)))
          (deferred:next
            (lambda (_)
              (cc:dataflow-set dfenv-parent "aaa" 256)
              (push (cons 'get-sync (cc:dataflow-get-sync dfenv "aaa")) result)))))
      (deferred:nextc it
        (lambda (_) (deferred:callback dfinish))))

    dfinish))

;; (cc:debug (cc:test-dataflow-parent1) "Dataflow Parent1 : %s" x)

(defun cc:test-dataflow-parent2 ()
  (let* ((result '())
         (dfinish (deferred:new
                    (lambda (_)
                      (setq result (reverse result))
                      (or (equal
                           '("parent get 256" "child get 256") result)
                          result))))
         (dfenv-parent (cc:dataflow-environment))
         (dfenv (cc:dataflow-environment dfenv-parent)))

    (deferred:$
      (deferred:parallel
        (deferred:$
          (cc:dataflow-get dfenv-parent "abc")
          (deferred:nextc it
            (lambda (x) (push (format "parent get %s" x) result))))
        (deferred:$
          (cc:dataflow-get dfenv "abc")
          (deferred:nextc it
            (lambda (x) (push (format "child get %s" x) result))))
        (deferred:nextc (deferred:wait 0.2)
          (lambda (_) (cc:dataflow-set dfenv-parent "abc" 256))))
      (deferred:nextc it
        (lambda (_) (deferred:callback dfinish))))

    dfinish))

;; (cc:debug (cc:test-dataflow-parent2) "Dataflow Parent : %s" x)


;; Signal

(defun cc:test-signal1 ()
  (let* ((result '())
         (dfinish (deferred:new
                    (lambda (_)
                      (setq result (reverse result))
                      (or (equal
                           '(
                             (ls ev1 (1))
                             (sig ev1 (1))
                             (ls ev2 (2))
                             (def ev1 (1))
                             )
                           result)
                          result))))
         (channel (cc:signal-channel "child")))

    (cc:signal-connect channel 'ev1
                       (lambda (event)
                         (push (cons 'sig event) result)))
    (cc:signal-connect channel t
                       (lambda (event)
                         (push (cons 'ls event) result)))
    (deferred:$
      (cc:signal-connect channel 'ev1)
      (deferred:nextc it
        (lambda (x) (push (cons 'def x) result))))

    (deferred:$
      (deferred:next
        (lambda (_)
          (cc:signal-send channel 'ev1 1)
          (cc:signal-send channel 'ev2 2)))
      (deferred:nextc it
        (lambda (_) (deferred:wait 300)))
      (deferred:nextc it
        (lambda (_)
          (deferred:callback dfinish))))

    dfinish))

;; (cc:debug (cc:test-signal1) "Signal1 : %s" x)

;; (cc:debug (cc:test-signal2) "Signal2 : %s" x)

(defun cc:test-signal2 ()
  (let* ((result nil)
         (dfinish (deferred:new
                    (lambda (_)
                      (setq result (reverse result))
                      (or (equal
                           '(
                             (pls pev1 (1))
                             (psig pev1 (1))
                             (pls ev1 (2))
                             (ls ev1 (3))
                             (sig ev1 (3))
                             (pls ev2 (4))
                             (pls ev2 (5))

                             (ls pev1 (1))
                             (ls ev1 (2))

                             (sig ev1 (2))
                             (def ev1 (3))
                             (ls ev2 (4))
                             (ls ev2 (5))

                             (def ev1 (2))
                             )
                           result)
                          result))))
         (parent-channel (cc:signal-channel "parent"))
         (channel (cc:signal-channel "child" parent-channel)))

    (cc:signal-connect parent-channel 'pev1
                       (lambda (event)
                         (push (cons 'psig event) result)))
    (cc:signal-connect parent-channel t
                       (lambda (event)
                         (push (cons 'pls event) result)))
    (cc:signal-connect channel 'ev1
                       (lambda (event)
                         (push (cons 'sig event) result)))
    (cc:signal-connect channel t
                       (lambda (event)
                         (push (cons 'ls event) result)))
    (deferred:$
      (cc:signal-connect channel 'ev1)
      (deferred:nextc it
        (lambda (x)
          (push (cons 'def x) result))))

    (deferred:$
      (deferred:next
        (lambda (_)
          (cc:signal-send parent-channel 'pev1 1)
          (cc:signal-send parent-channel 'ev1  2)
          (cc:signal-send channel        'ev1  3)
          (cc:signal-send parent-channel 'ev2  4)
          (cc:signal-send-global channel 'ev2  5)))
      (deferred:nextc it
        (lambda (_) (deferred:wait 300)))
      (deferred:nextc it
        (lambda (_)
          (deferred:callback-post dfinish))))

    dfinish))

;; (cc:debug (cc:test-signal2) "Signal2 : %s" x)

(defvar cc:test-finished-flag nil)
(defvar cc:test-fails 0)

(defun cc:test-all ()
  (interactive)
  (setq cc:test-finished-flag nil)
  (setq cc:test-fails 0)
  (deferred:$
    (deferred:parallel
      (cl-loop for i in '(cc:test-fib-gen
                          cc:test-thread
                          cc:test-semaphore1
                          cc:test-semaphore2
                          cc:test-dataflow-simple1
                          cc:test-dataflow-simple2
                          cc:test-dataflow-simple3
                          cc:test-dataflow-simple4
                          cc:test-dataflow-signal
                          cc:test-dataflow-parent1
                          cc:test-dataflow-parent2
                          cc:test-signal1
                          cc:test-signal2
                          )
               collect (cons i (deferred:timeout 5000 "timeout" (funcall i)))))
    (deferred:nextc it
      (lambda (results)
        (pop-to-buffer
         (with-current-buffer (get-buffer-create "*cc:test*")
           (erase-buffer)
           (cl-loop for i in results
                    for name = (car i)
                    for result = (cdr i)
                    with fails = 0
                    do (insert (format "%s : %s\n" name
                                       (if (eq t result) "OK"
                                         (format "FAIL > %s" result))))
                    (unless (eq t result) (cl-incf fails))
                    finally
                    (goto-char (point-min))
                    (insert (format "Test Finished : %s\nTests Fails: %s / %s\n"
                                    (format-time-string   "%Y/%m/%d %H:%M:%S" (current-time))
                                    fails (length results)))
                    (setq cc:test-fails fails))
           (message (buffer-string))
           (current-buffer)))
        (setq cc:test-finished-flag t))))

  (while (null cc:test-finished-flag)
    (sleep-for 0 100) (sit-for 0 100))
  (when (and noninteractive
             (> cc:test-fails 0))
    (error "Test failed")))

(ert-deftest concurrent-all-the-thing ()
  (should-not (cc:test-all)))
