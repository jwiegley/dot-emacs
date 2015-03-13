;;; Sample code for concurrent.el

;; Evaluate following code in the scratch buffer.

;;==================================================
;;; generator

(setq fib-list nil)

(setq fib-gen ; Create a generator object.
      (lexical-let ((a1 0) (a2 1))
        (cc:generator
         (lambda (x) (push x fib-list)) ; receiving values
         (yield a1)
         (yield a2)
         (while t
           (let ((next (+ a1 a2)))
             (setq a1 a2
                   a2 next)
             (yield next))))))

(funcall fib-gen) ; Generate 5 times
(funcall fib-gen) (funcall fib-gen)
(funcall fib-gen) (funcall fib-gen)

fib-list ;=> (3 2 1 1 0)


;;==================================================
;;; thread

(lexical-let 
    ((count 0) (anm "-/|\\-")
     (end 50) (pos (point)))
  (cc:thread 
   60 
   (message "Animation started.")
   (while (> end (incf count))
     (save-excursion
       (when (< 1 count)
         (goto-char pos) (delete-char 1))
       (insert (char-to-string 
                (aref anm (% count (length anm)))))))
   (save-excursion
     (goto-char pos) (delete-char 1))
   (message "Animation finished.")))

;; Play the simple character animation here.


;;==================================================
;;; semaphore

;; create a semaphore object with permit=1.
(setq smp (cc:semaphore-create 1))

;; executing three tasks...
(deferred:nextc (cc:semaphore-acquire smp)
  (lambda(x) 
    (message "go1")))
(deferred:nextc (cc:semaphore-acquire smp)
  (lambda(x) 
    (message "go2")))
(deferred:nextc (cc:semaphore-acquire smp)
  (lambda(x) 
    (message "go3")))

;; => Only the fist task is executed and displays "go1".

(cc:semaphore-release smp)

;; => The second task is executed and displays "go2".

(cc:semaphore-waiting-deferreds smp) ; return the deferred object that displays "go3".

(cc:semaphore-release-all smp) ; => reset permit count and return the deferred object that displays "go3".

(cc:semaphore-waiting-deferreds smp) ; => nil


;;==================================================
;; Dataflow

;; create a parent environment and bind "aaa" to 256.
(setq dfenv-parent (cc:dataflow-environment))
(cc:dataflow-set dfenv-parent "aaa" 256)

;; create an environment with the parent one.
(setq dfenv (cc:dataflow-environment dfenv-parent))

;; Return the parent value.
(cc:dataflow-get-sync dfenv "aaa") ; => 256

(deferred:$ 
  (cc:dataflow-get dfenv "abc")
  (deferred:nextc it
    (lambda (x) (message "Got abc : %s" x))))
;; => This task is blocked

(cc:dataflow-set dfenv "abc" 256) ; bind 256 to "abc"

;; => The blocked task is executed and displays "Got abc : 256".

(cc:dataflow-get-sync dfenv "abc") ; => 256

;; unbind the variable "abc"
(cc:dataflow-clear dfenv "abc")

(cc:dataflow-get-sync dfenv "abc") ; => nil


;; complicated key (`equal' can compare nested lists.)

(deferred:$
  (cc:dataflow-get dfenv '("http://example.com/a.jpg" 300))
  (deferred:nextc it
    (lambda (x) (message "a.jpg:300 OK %s" x))))

(cc:dataflow-set dfenv '("http://example.com/a.jpg" 300) 'jpeg)

;; waiting for two variables

(deferred:$
  (deferred:parallel
    (cc:dataflow-get dfenv "abc")
    (cc:dataflow-get dfenv "def"))
  (deferred:nextc it
    (lambda (values) 
      (apply 'message "Got values : %s, %s" values)
      (apply '+ values)))
  (deferred:nextc it
    (lambda (x) (insert (format ">> %s" x)))))

(cc:dataflow-get-waiting-keys dfenv)   ; => ("def" "abc")
(cc:dataflow-get-avalable-pairs dfenv) ; => (("aaa" . 256))

(cc:dataflow-set dfenv "abc" 128)
(cc:dataflow-set dfenv "def" 256)

;; => "Got values : 128, 256"
;; inserted ">> 384"

(cc:dataflow-get-avalable-pairs dfenv)

(cc:dataflow-clear-all dfenv)

(cc:dataflow-get-avalable-pairs dfenv)


;;==================================================
;; Signal

(progn
  (setq parent-channel (cc:signal-channel "parent"))
  (cc:signal-connect 
   parent-channel 'parent-load
   (lambda (event) (message "Parent Signal : %s" event)))
  (cc:signal-connect 
   parent-channel t
   (lambda (event) (message "Parent Listener : %s" event)))

  (setq channel (cc:signal-channel "child" parent-channel))
  (cc:signal-connect 
   channel 'window-load 
   (lambda (event) (message "Signal : %s" event)))
  (cc:signal-connect
   channel t 
   (lambda (event) (message "Listener : %s" event)))
  (deferred:$
    (cc:signal-connect channel 'window-load)
    (deferred:nextc it
      (lambda (x) (message "Deferred Signal : %s" x))))
  )

(cc:signal-send channel 'window-load "hello signal!")
(cc:signal-send channel 'some "some signal!")

(cc:signal-send parent-channel 'parent-load "parent hello!")
(cc:signal-send parent-channel 'window-load "parent hello!")
(cc:signal-send parent-channel 'some "parent some hello!")
(cc:signal-send-global channel 'some "parent some hello!")

(cc:signal-disconnect-all channel)
 
