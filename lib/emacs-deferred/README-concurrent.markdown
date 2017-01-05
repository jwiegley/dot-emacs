# concurrent.el

[![Build Status](https://travis-ci.org/kiwanami/emacs-deferred.svg)](https://travis-ci.org/kiwanami/emacs-deferred)
[![Coverage Status](https://coveralls.io/repos/kiwanami/emacs-deferred/badge.svg)](https://coveralls.io/r/kiwanami/emacs-deferred)
[![MELPA](http://melpa.org/packages/concurrent-badge.svg)](http://melpa.org/#/concurrent)
[![MELPA stable](http://stable.melpa.org/packages/concurrent-badge.svg)](http://stable.melpa.org/#/concurrent)
[![Tag Version](https://img.shields.io/github/tag/kiwanami/emacs-deferred.svg)](https://github.com/kiwanami/emacs-deferred/tags)
[![License](http://img.shields.io/:license-gpl3-blue.svg)](http://www.gnu.org/licenses/gpl-3.0.html)

`concurrent.el` is a higher level library for asynchronous tasks, based on `deferred.el`.

It is inspired by libraries of other environments and concurrent programing models.
It has following facilities: *pseud-thread*, *generator*, *semaphore*, *dataflow variables* and
*event management*.

## Installation ##

You can install `concurrent.el` from [MELPA](http://melpa.org) by `package.el`.

## Sample codes ##

You can find following sample codes in `concurrent-sample.el`.
Executing `eval-last-sexp` (C-x C-e), you can try those codes.

### Pseud-thread

Evaluating the let in the blow code, the animation starts. After few seconds, the animation will stop.

Thread:

```el
(let ((count 0) (anm "-/|\\-")
      (end 50) (pos (point)))
  (cc:thread
   60
   (message "Animation started.")
   (while (> end (cl-incf count))
     (save-excursion
       (when (< 1 count)
         (goto-char pos) (delete-char 1))
       (insert (char-to-string
                (aref anm (% count (length anm)))))))
   (save-excursion
     (goto-char pos) (delete-char 1))
   (message "Animation finished.")))
```

Using `while` clause in the body content, one can make a loop in the thread.

Be careful not to make an infinite loop or heavy loop accidentally. If you find that the Emacs enters infinite loop, you may be able to stop the loop with executing the command `deferred:clear-queue`.

### Generator

The following code creates a generator object and binds it to the variable `fib-gen`.
One can receive values, using `yield` function in the generator body code.
When the generator returns a value, the evaluation process stops.
Calling generator object as a function, the evaluation process resumes.

Generator:

```el
(setq fib-list nil)
(setq fib-gen
      (let ((a1 0) (a2 1))
        (cc:generator
         (lambda (x) (push x fib-list)) ; Receiving values as a callback function
         (yield a1)
         (yield a2)
         (while t
           (let ((next (+ a1 a2)))
             (setq a1 a2
                   a2 next)
             (yield next))))))

(funcall fib-gen) ; calling 5 times
(funcall fib-gen) (funcall fib-gen)
(funcall fib-gen) (funcall fib-gen)

fib-list ; => (3 2 1 1 0)
```

### Semaphore

The semaphore restricts the number of concurrent tasks.
The following code creates a semaphore object with one permit, and binds it to the variable `smp`.
The subsequent codes and comments show how the semaphore object works.

Semaphore:

```el
;; Create a semaphore with permit=1.
(setq smp (cc:semaphore-create 1))

;; Start three tasks with acquiring permit.
(deferred:nextc (cc:semaphore-acquire smp)
  (lambda(x)
    (message "go1")))
(deferred:nextc (cc:semaphore-acquire smp)
  (lambda(x)
    (message "go2")))
(deferred:nextc (cc:semaphore-acquire smp)
  (lambda(x)
    (message "go3")))

;; => Only the first task is executed and displays "go1".
;;    Rest ones are blocked.

(cc:semaphore-release smp) ; Releasing one permit

;; => The second task is executed, then, displays "go2".

(cc:semaphore-waiting-deferreds smp) ; => The third task object

(cc:semaphore-release-all smp) ; => Reset permits and return the third task object

(cc:semaphore-waiting-deferreds smp) ; => nil
```

### Dataflow

The function `cc:dataflow-environment` creates an environment for dataflow variables.
The function `cc:dataflow-get` returns a deferred object that can refer the value.
The function `cc:dataflow-set` binds a value to a dataflow variable.
Any objects can be variable keys in the environment. This sample code uses strings as keys.

Dataflow:

```el
;; Create an environment.
(setq dfenv (cc:dataflow-environment))

;;## Basic usage

;; Referring a variable synchronously. This function doesn't block.
(cc:dataflow-get-sync dfenv "abc") ; => nil

(deferred:$ ; Start the task that gets the value of `abc` and that displays the value.
  (cc:dataflow-get dfenv "abc")
  (deferred:nextc it
    (lambda (x) (message "Got abc : %s" x))))
;; => This task is blocked because no value is bound to the variable `abc`.

(cc:dataflow-set dfenv "abc" 256) ; Binding a value to the variable `abc`.
;; => The blocked task resumes and displays "Got abc : 256".

(cc:dataflow-get-sync dfenv "abc") ; => 256

(cc:dataflow-clear dfenv "abc") ; unbind the variable `abc`

(cc:dataflow-get-sync dfenv "abc") ; => nil

;;## Complex key

(deferred:$
  (cc:dataflow-get dfenv '("http://example.com/a.jpg" 300))
  (deferred:nextc it
    (lambda (x) (message "a.jpg:300 OK %s" x))))

(cc:dataflow-set dfenv '("http://example.com/a.jpg" 300) 'jpeg)

;; => a.jpg:300 OK jpeg

;;## Waiting for two variables

(deferred:$ ; Start the task that refers two variables, `abc` and `def`.
  (deferred:parallel
    (cc:dataflow-get dfenv "abc")
    (cc:dataflow-get dfenv "def"))
  (deferred:nextc it
    (lambda (values)
      (apply 'message "Got values : %s, %s" values)
      (apply '+ values)))
  (deferred:nextc it
    (lambda (x) (insert (format ">> %s" x)))))
;; => This task is blocked.

(cc:dataflow-get-waiting-keys dfenv) ; => ("def" "abc")
(cc:dataflow-get-avalable-pairs dfenv) ; => ((("http://example.com/a.jpg" 300) . jpeg))

(cc:dataflow-set dfenv "abc" 128) ; Binding one value. The task is still blocked.
(cc:dataflow-set dfenv "def" 256) ; Binding the next value. Then, the task resumes.
;; => Got values : 128, 256
```

### Signal

The function `cc:signal-channel` creates a channel for signals.
Then, one can connect receivers and send signals.

Signal:

```el
;; Create a channel.
(setq channel (cc:signal-channel))

(cc:signal-connect ; Connect the receiver for the signal 'foo.
 channel 'foo
 (lambda (event) (message "Signal : %S" event)))

(cc:signal-connect
 channel t  ; The signal symbol 't' means any signals.
 (lambda (event)
   (cl-destructuring-bind (event-name (args)) event
     (message "Listener : %S / %S" event-name args))))

(deferred:$ ; Connect the deferred task.
  (cc:signal-connect channel 'foo)
  (deferred:nextc it
    (lambda (x) (message "Deferred Signal : %S" x))))

(cc:signal-send channel 'foo "hello signal!")
;; =>
;; Listener : foo / "hello signal!"
;; Signal : (foo ("hello signal!"))
;; Deferred Signal : (foo ("hello signal!"))

(cc:signal-send channel 'some "some signal!")
;; =>
;; Listener : some / "some signal!"
```

Dataflow objects have the own channel to notify accessing to the variables.
Receiving the signals for referring unbound variables, one can create values on demand.

The signal and dataflow objects can be cascades, creating objects with the parent ones.
It enables that the dataflow object can have the default values, and that
one can use the different scope signals in the tree structure of the channel objects, such as global signals and local signals.

## API Details

### Thread

* cc:thread (wait-time-msec &rest body)
   * Arguments
      * wait-time-msec: The interval time between tasks (millisecond).
   * Return
      * A thread object.
   * This function creates a thread and start it.
   * The `thread` means that each s-exps in the body part are executed as asynchronous tasks. Then, the interval between tasks is `wait-time-msec`.
   * The `while` form in the body part acts as a loop.
   * Note that the infinite loops or the heavy loop tasks may make the Emacs freeze. The command `deferred:clear-queue` may recover such freeze situation.

### Generator

* cc:generator (callback &rest body)
   * Arguments
      * callback: A function to receive the value passed by `yield` form.
      * body: Generator forms.
   * Return
      * A generating function.
   * Similar to `cc:thread`, each s-exps in the body part are executed as asynchronous tasks and the `while` form in the body part acts as a loop.
   * The `yield` form in the body part passes the value to the `callback` function and pause the asynchronous tasks.
   * Calling the generating function, the asynchronous tasks resume.

### Semaphore

* cc:semaphore-create (permits-num)
   * Arguments
      * permits-num: The number of permits.
   * Return
      * A semaphore object.
   * This function creates a semaphore object.

* cc:semaphore-acquire (semaphore)
   * Argument
      * semaphore: A semaphore object.
   * Return
      * A deferred object.
   * Acquire an execution permission and return deferred object to chain.
   * If this semaphore object has permissions, the subsequent deferred task is executed immediately.
   * If this semaphore object has no permissions, the subsequent deferred task is blocked. After the permission is returned, the task is executed.

* cc:semaphore-release (semaphore)
   * Arguments
      * semaphore: A semaphore object
   * Return
      * The given semaphore object
   * Release an execution permission.
   * The programmer is responsible to return the permissions.

* cc:semaphore-with (semaphore body-func &optional error-func)
   * Arguments
      * semaphore: A semaphore object
      * body-func: A task function
      * error-func: An error handling function (which is connected by `deferred:error`.)
   * Return
      * A deferred object
   * Execute the task function asynchronously with the semaphore block.
   * Using this function is bit safer than using a pair of `cc:semaphore-acquire` and `cc:semaphore-release`.

* cc:semaphore-release-all (semaphore)
   * Arguments
      * semaphore: A semaphore object
   * Return
      * Deferred objects those were waiting for permission.
   * Release all permissions for resetting the semaphore object.
   * If the semaphore object has some blocked tasks, this function return a list of the tasks and clear the list of the blocked tasks in the semaphore object.

* cc:semaphore-interrupt-all (semaphore)
   * Arguments
      * semaphore: A semaphore object
   * Return
      * A deferred object
   * Clear the list of the blocked tasks in the semaphore and return a deferred object to chain.
   * This function is used for the interruption cases.

### Signal

* cc:signal-channel (&optional name parent-channel)
   * Arguments
      * name: A channel name for debug.
      * parent-channel: An upstream channel object.
   * Return
      * A channel object.
   * Create a new channel object.
   * The observers of this channel can receive the upstream signals.
      * In the case of using the function `cc:signal-send`, the observers of the upstream channel can not receive the signals of this channel.
      * The function `cc:signal-send-global` can send a signal to the upstream channels from the downstream channels.

* cc:signal-connect (channel event-sym &optional callback)
   * Arguments
      * channel: A channel object
      * event-sym: A signal symbol
      * callback: A receiver function
   * Return
      * A deferred object
   * Append an observer for the symbol of the channel and return a deferred object.
   * If `event-sym` is `t`, the observer receives all signals of the channel.
   * If the callback function is given, the deferred object executes the callback function asynchronously.
   * One can connect subsequent tasks to the returned deferred object.

* cc:signal-send (channel event-sym &rest args)
   * Arguments
      * channel: A channel object
      * event-sym: A signal symbol
      * args: Signal arguments
   * Return
      * None
   * Send a signal to the channel.
   * If the `args` are given, observers can get the values by following code:
      * `(lambda (event) (cl-destructuring-bind (event-sym (args)) event ... ))`

* cc:signal-send-global (channel event-sym &rest args)
   * Arguments
      * channel: A channel object
      * event-sym: A signal symbol
      * args: Signal arguments
   * Return
      * None
   * Send a signal to the most upstream channel.

* cc:signal-disconnect (channel deferred)
   * Arguments
      * channel: A channel object
      * deferred: The deferred object to delete
   * Return
      * The deleted deferred object
   * Remove the observer object from the channel and return the removed deferred object.

* cc:signal-disconnect-all (channel)
   * Arguments
      * channel: A channel object
   * Return
      * None
   * Remove all observers.

### Dataflow

* cc:dataflow-environment (&optional parent-env test-func channel)
   * Arguments
      * parent-env: A dataflow object as the default value.
      * test-func: A test function that compares the entry keys.
      * channel: A channel object that sends signals of variable events.
   * Return
      * A dataflow object
   * Create a dataflow environment.
   * The parent environment
      * If this environment doesn't have the entry A and the parent one has the entry A, this environment can return the entry A.
      * One can override the entry, setting another entry A to this environment.
   * If no channel is given, this function creates a new channel object internally.
   * Observers can receive following signals:
      * `get-first` : the fist referrer is waiting for binding,
      * `get-waiting` : another referrer is waiting for binding,
      * `set` : a value is bound,
      * `get` : returned a bound value,
      * `clear` : cleared one entry,
      * `clear-all` : cleared all entries.

* cc:dataflow-get (df key)
   * Arguments
      * df: A dataflow object
      * key: A key object
   * Return
      * A deferred object
   * Return a deferred object that can refer the value which is indicated by the key.
   * If the dataflow object has the entry that bound value, the subsequent deferred task is executed immediately.
   * If not, the task is deferred till a value is bound.

* cc:dataflow-get-sync (df key)
   * Arguments
      * df: A dataflow object
      * key: A key object
   * Return
      * Nil or a value
   * Return the value which is indicated by the key synchronously.
   * If the environment doesn't have an entry of the key, this function returns nil.

* cc:dataflow-set (df key value)
   * Arguments
      * df: A dataflow object
      * key: A key object
      * value: A value
   * Return
      * None
   * Bind the value to the key in the environment.
   * If the dataflow already has the bound entry of the key, this function throws an error signal.
   * The value can be nil as a value.

* cc:dataflow-clear (df key)
   * Arguments
      * df: A dataflow object
      * key: A key object
   * Return
      * None
   * Clear the entry which is indicated by the key.
   * This function does nothing for the waiting deferred objects.

* cc:dataflow-get-avalable-pairs (df)
   * Arguments
      * df: A dataflow object
   * Return
      * An available key-value alist in the environment and the parent ones.

* cc:dataflow-get-waiting-keys (df)
   * Arguments
      * df: A dataflow object
   * Return
      * A list of keys which have waiting deferred objects in the environment and the parent ones.

* cc:dataflow-clear-all (df)
   * Arguments
      * df: A dataflow object
   * Return
      * None
   * Clear all entries in the environment.
   * This function does nothing for the waiting deferred objects.

* cc:dataflow-connect (df event-sym &optional callback)
   * Arguments
      * df: A dataflow object
      * event-sym: A signal symbol
      * callback: A receiver function
   * Return
      * A deferred object
   * Append an observer for the symbol of the channel of the environment and return a deferred object.
   * See the document of `cc:dataflow-environment` for details of signals.


* * * * *

(C) 2011-2016  SAKURAI Masashi  All rights reserved.
m.sakurai at kiwanami.net
