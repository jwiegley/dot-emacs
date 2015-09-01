# deferred.el #

'deferred.el' provides facilities to manage asynchronous tasks.
The API and implementations were translated from 
[JSDeferred](https://github.com/cho45/jsdeferred "JSDeferred") (by cho45) and 
[Mochikit.Async](http://mochikit.com/doc/html/MochiKit/Async.html
"Mochikit.Async") (by Bob Ippolito) in JavaScript.

## Installation ##

Put 'deferred.el' into your 'load-path'.

If you have [auto-install.el](http://www.emacswiki.org/emacs/auto-install.el "auto-install.el]"), evaluating a following s-expression, you can install immediately.

Install by auto-install:

    (auto-install-from-url https://github.com/kiwanami/emacs-deferred/raw/master/deferred.el")


## Sample codes ##

You can find following sample codes in 'deferred-sample.el'.
Executing 'eval-last-sexp' (C-x C-e), you can try those codes.

### Basic usage ###

This is a basic deferred chain. This code puts some outputs into
message buffer, and then require a number from minibuffer.

Chain:

    (deferred:$
      (deferred:next 
        (lambda () (message "deferred start")))
      (deferred:nextc it
        (lambda () 
          (message "chain 1")
          1))
      (deferred:nextc it
        (lambda (x)
          (message "chain 2 : %s" x)))
      (deferred:nextc it
        (lambda ()
          (read-minibuffer "Input a number: ")))
      (deferred:nextc it
        (lambda (x)
          (message "Got the number : %i" x)))
      (deferred:error it
        (lambda (err)
          (message "Wrong input : %s" err))))


* This s-exp returns immediately. 
 * Asynchronous tasks start subsequently.
* The macro 'deferred:$' chains deferred objects.
 * The anaphoric variable 'it' holds a deferred object in the previous line.
* The next deferred task receives the value that is returned by the previous deferred one.
* Inputting a wrong value, such as alphabets, this s-exp raises an error. The error is caught by the errorback function defined by 'deferred:error'.

### Timer ###

After evaluating this s-exp and waiting for 1 second, a message is shown in the minibuffer.

Timer:

    (deferred:$
      (deferred:wait 1000) ; 1000msec
      (deferred:nextc it
        (lambda (x)
          (message "Timer sample! : %s msec" x))))

* The next deferred task subsequent to deferred:wait receives the actual elapse time in millisecond.

### Commands and Sub-process ###

This s-exp inserts the result that is performed by the command 'ls -la'. (This s-exp may not run in windows. Try 'dir' command.)

Command process:

    (deferred:$
      (deferred:process "ls" "-la")
      (deferred:nextc it
        (lambda (x) (insert x))))

* This s-exp hardly blocks Emacs because of asynchronous mechanisms.


### HTTP GET : Text ###

This s-exp inserts a text from http://www.gnu.org asynchronously. (You can clear the result with undo command.)

HTTP GET:

    (require 'url)
    
    (deferred:$
      (deferred:url-retrieve "http://www.gnu.org")
      (deferred:nextc it
        (lambda (buf)
          (insert  (with-current-buffer buf (buffer-string)))
          (kill-buffer buf))))
    
### HTTP Get : Image ###

This s-exp inserts an image from google asynchronously.

Get an image:

    (deferred:$
      (deferred:url-retrieve "http://www.google.co.jp/intl/en_com/images/srpr/logo1w.png")
      (deferred:nextc it
        (lambda (buf)
          (insert-image 
           (create-image 
            (let ((data (with-current-buffer buf (buffer-string))))
              (substring data (+ (string-match "\n\n" data) 2)))
            'png t))
          (kill-buffer buf))))
    
### Parallel ###

This s-exp retrieves two images from google concurrently and wait for the both results. Then, the file sizes of the images are inserted the current buffer.

Parallel deferred:

    (deferred:$
      (deferred:parallel
        (lambda ()
          (deferred:url-retrieve "http://www.google.co.jp/intl/en_com/images/srpr/logo1w.png"))
        (lambda ()
          (deferred:url-retrieve "http://www.google.co.jp/images/srpr/nav_logo14.png")))
      (deferred:nextc it
        (lambda (buffers)
          (loop for i in buffers
                do 
                (insert 
                 (format 
                  "size: %s\n"
                  (with-current-buffer i (length (buffer-string)))))
                (kill-buffer i)))))

* The function 'deferred:parallel' runs asynchronous tasks concurrently.
* The function wait for all results, regardless normal or abnormal. Then, the subsequent tasks are executed.
* The next task receives a list of the results.
 * The order of the results is corresponding to one of the argument.
 * Giving an alist of tasks as the argument, the results alist is returned.
    
### Deferred Combination : try-catch-finally ###

This s-exp executes following tasks:
* Getting an image by wget command,
* Resizing the image by convert command in ImageMagick,
* Insert the re-sized image into the current buffer.
You can construct the control structure of deferred tasks, like try-catch-finally in Java.

Get an image by wget and resize by ImageMagick:

    (deferred:$ 
    
      ;; try
      (deferred:$
        (deferred:process "wget" "-O" "a.jpg" "http://www.gnu.org/software/emacs/tour/images/splash.png")
        (deferred:nextc it
          (lambda () (deferred:process "convert" "a.jpg" "-resize" "100x100" "jpg:b.jpg")))
        (deferred:nextc it
          (lambda ()
            (clear-image-cache)
            (insert-image (create-image (expand-file-name "b.jpg") 'jpeg nil)))))
    
      ;; catch
      (deferred:error it ; 
        (lambda (err) 
          (insert "Can not get a image! : " err)))
    
      ;; finally
      (deferred:nextc it
        (lambda ()
          (deferred:parallel
            (lambda () (delete-file "a.jpg"))
            (lambda () (delete-file "b.jpg")))))
      (deferred:nextc it
        (lambda (x) (message ">> %s" x))))

* In this case, the deferred tasks are statically connected.

Here is an another sample code for try-catch-finally blocks. This is simpler than above code because of the 'deferred:try' macro. (Note: They bring the same results practically, but are not perfectly identical. The 'finally' task may not be called because of asynchrony.)

Try-catch-finally:

    (deferred:$
      (deferred:try
        (deferred:$
          (deferred:process "wget" "-O" "a.jpg" "http://www.gnu.org/software/emacs/tour/images/splash.png")
          (deferred:nextc it
            (lambda () (deferred:process "convert" "a.jpg" "-resize" "100x100" "jpg:b.jpg")))
          (deferred:nextc it
            (lambda ()
              (clear-image-cache)
              (insert-image (create-image (expand-file-name "b.jpg") 'jpeg nil)))))
        :catch
        (lambda (err) (insert "Can not get a image! : " err))
        :finally
        (lambda ()
          (delete-file "a.jpg")
          (delete-file "b.jpg")))
      (deferred:nextc it
        (lambda (x) (message ">> %s" x))))

### Timeout ###

Although a long time command is executed (3 second sleeping), the task is canceled by timeout for 1 second.

The function 'deferred:earlier' also runs asynchronous tasks concurrently, however, the next deferred task receives the first result. The other results and tasks will be canceled.

Timeout Process:

    (deferred:$
      (deferred:earlier
        (deferred:process "sh" "-c" "sleep 3 | echo 'hello!'")
        (deferred:$
          (deferred:wait 1000) ; timeout msec
          (deferred:nextc it (lambda () "canceled!"))))
      (deferred:nextc it
        (lambda (x) (insert x))))

* Changing longer timeout for 'deferred:wait', the next task receives a result of the command.
* When a task finishes abnormally, the task is ignored.
   * When all tasks finishes abnormally, the next task receives nil.
* The functions 'deferred:parallel' and 'deferred:earlier' may be corresponding to 'and' and 'or', respectively.

Here is an another sample code for timeout, employing 'deferred:timeout' macro.

Timeout macro:

    (deferred:$
      (deferred:timeout
        1000 "canceled!"
        (deferred:process "sh" "-c" "sleep 3 | echo 'hello!'"))
      (deferred:nextc it
        (lambda (x) (insert x))))

### Loop and Animation ###

This s-exp plays an animation at the cursor position for few seconds. Then, you can move cursor freely, because the animation does not block Emacs.

Returning a deferred object in the deferred tasks, the returned task is executed before the next deferred one that is statically connected on the source code. (In this case, the interrupt task is dynamically connected.)

Employing a recursive structure of deferred tasks, you can construct a deferred loop.
It may seem the multi-thread in Emacs Lisp.

Loop and animation:

    (lexical-let ((count 0) (anm "-/|\\-")
                  (end 50) (pos (point))
                  (wait-time 50))
      (deferred:$
        (deferred:next
          (lambda (x) (message "Animation started.")))
    
        (deferred:nextc it
          (deferred:lambda (x)
            (save-excursion
              (when (< 0 count)
                (goto-char pos) (delete-char 1))
              (insert (char-to-string 
                       (aref anm (% count (length anm))))))
            (if (> end (incf count)) ; return nil to stop this loop
                (deferred:nextc (deferred:wait wait-time) self)))) ; return the deferred
    
        (deferred:nextc it
          (lambda (x)
            (save-excursion
              (goto-char pos) (delete-char 1))
            (message "Animation finished.")))))

* 'deferred:lambda' is an anaphoric macro in which 'self' refers itself. It is convenient to construct a recursive structure.

### Wrapping asynchronous function ###

Let's say you have an asynchronous function which takes a callback.  For example, dbus.el, xml-rpc.el and websocket.el has such kind of asynchronous APIs.  To use such libraries with deferred.el, you can make an unregistered deferred object using `deferred:new` and then start the deferred callback queue using `deferred:callback-post` in the callback given to the asynchronous function.  If the asynchronous function supports "errorback", you can use `deferred:errorback-post` to pass the error information to the following callback queue.

In the following example, `run-at-time` is used as an example for the asynchronous function.  Deferred.el already has `deferred:wait` for this purpose so that you don't need the following code if you want to use `run-at-time`.

    (deferred:$
      (deferred:next
        (lambda ()
          (message "1")
          1))
      (deferred:nextc it
        (lambda (x)
          (lexical-let ((d (deferred:new #'identity)))
            (run-at-time 0 nil (lambda (x)
                                 ;; Start the following callback queue now.
                                 (deferred:callback-post d x))
                         x)
            ;; Return the unregistered (not yet started) callback
            ;; queue, so that the following queue will wait until it
            ;; is started.
            d)))
      ;; You can connect deferred callback queues
      (deferred:nextc it
        (lambda (x)
          (message "%s" (1+ x)))))

## API ##

### Functions ###

#### Basic functions ####

* deferred:next (callback)
   * Arguments
      * callback: a function with zero or one argument
   * Return
      * a deferred object
   * Return a deferred object that wrap the given callback function. Then, put the deferred object into the execution queue to run asynchronously.
      * Namely, run the given function asynchronously.
 

* deferred:nextc (d callback)
   * Arguments
      * d: a deferred object
      * callback: a function with zero or one argument
   * Return
      * a deferred object
   * Return a deferred object that wrap the given callback function. Then, connect the created deferred object with the given deferred object.
      * Namely, add the given function to the previous deferred object.

* deferred:error (d errorback)
   * Arguments 
      * d: a deferred object
      * errorback: a function with zero or one argument
   * Return
      * a deferred object
   * Return a deferred object that wrap the given function as errorback. Then, connect the created deferred object with the given deferred object.
      * Namely, the given function catches the error occurred in the previous task.
   * If this function does not throw an error, the subsequent callback functions are executed.

* deferred:cancel (d)
   * Arguments
      * d: a deferred object
   * Return
      * the given deferred object (invalidated)
   * Invalidate the given deferred object.
   * Because this function modifies the deferred object, it can not be used in future.

* deferred:watch (d callback)
   * Arguments
      * d: deferred object
      * callback: a function with zero or one argument
   * Return
      * a deferred object
   * Create a deferred object with watch task and connect it to the given deferred object.
   * The watch task CALLBACK can not affect deferred chains with return values.
   * This function is used in following purposes, simulation of try-finally block in asynchronous tasks, monitoring of progress of deferred tasks.

* deferred:wait (msec)
   * Arguments
      * msec: a number (millisecond)
   * Return
      * a deferred object
   * Return a deferred object that will be called after the specified millisecond.
   * The subsequent deferred task receives the actual elapse time in millisecond.

* deferred:$
   * Arguments / more than one deferred forms
   * Return / the last deferred object
   * An anaphoric macro chains deferred objects.
      * The anaphoric variable 'it' holds a deferred object in the previous line.

#### Utility functions ####

* deferred:loop (number-or-list callback)
   * Arguments
      * number-or-list: an integer or a list
      * callback: a function with zero or one argument
   * Return
      * a deferred object
   * Return a deferred object that iterates the function for the specified times.
      * The function receives the count number that begins zero.
   * If a list is given, not a number, the function visits each elements in the list like 'mapc'.

* deferred:parallel (list-or-alist)
   * Arguments 
      * list-or-alist:
      * more than one deferred objects or a list of functions
      * an alist consist of cons cells with a symbol and a deferred object or a function
   * Return
      * a deferred object
   * Return a deferred object that executes given functions in parallel and wait for all callback values.
   * The subsequent deferred task receives a list of the results. The order of the results is corresponding to one of the argument.
   * Giving an alist of tasks as the argument, the results alist is returned.
   * If the parallel task throws an error, the error object is passed as a result.

* deferred:earlier (list-or-alist)
   * Arguments
      * list-or-alist:
      * more than one deferred objects or a list of functions
      * an alist consist of cons cells with a symbol and a deferred object or a function
   * Return
      * a deferred object
   * Return a deferred object that executes given functions in parallel and wait for the first callback value.
      * The other tasks are canceled.
   * Giving an alist of tasks as the argument, a cons cell is returned as a result.
   * When a task finishes abnormally, the task is ignored.
      * When all tasks finishes abnormally, the next task receives nil. That is, no errorback function is called.

#### Wrapper functions ####

* deferred:call (function args...)
   * Arguments
      * function: a function
      * args: arguments (variable length)
   * Return
      * a deferred object
   * a wrapper of the function 'funcall'

* deferred:apply (function args)
   * Arguments
      * function: a function
      * args: a list of arguments
   * Return
      * a deferred object
   * a wrapper of the function 'apply'

* deferred:process (command args...) / deferred:process-shell (command args...)
   * Arguments
      * command: command to execute
      * args: command arguments (variable length)
   * Return
      * a deferred object
   * Execute a command asynchronously. These functions are wrappers of 'start-process' and 'start-process-shell-command'.
   * The subsequent deferred task receives the stdout from the command as a string.

* deferred:process-buffer (command args...) / deferred:process-shell-buffer (command args...)
   * Arguments
      * command: command to execute
      * args: command arguments (variable length)
   * Return
      * a deferred object
   * Execute a command asynchronously. These functions are wrappers of 'start-process' and 'start-process-shell-command'.
   * The subsequent deferred task receives the stdout from the command as a buffer.
      * The following tasks are responsible to kill the buffer.

* deferred:wait-idle (msec)
   * Arguments
      * msec: a number (millisecond)
   * Return
      * a deferred object
   * Return a deferred object that will be called when Emacs has been idle for the specified millisecond.
   * The subsequent deferred task receives the elapse time in millisecond.

* deferred:url-retrieve (url [cbargs])
   * Arguments
      * url: URL to get
      * cbargs: callback argument (optional)
   * Return
      * a deferred object
   * A wrapper function of 'url-retrieve' in the 'url' package.
   * The subsequent deferred task receives the content as a buffer.
      * The following tasks are responsible to kill the buffer.

* [experimental] deferred:url-get (url [params])
   * Arguments
      * url: URL to get
      * params: alist of parameters
   * Return 
      * a deferred object

* [experimental] deferred:url-post (url [params])
   * Arguments
      * url: URL to get
      * params: alist of parameters
   * Return 
      * a deferred object

#### Primitive functions ####

* deferred:new ([callback])
   * Arguments
      * callback: a function with zero or one argument (optional)
   * Return
      * a deferred object
   * Create a deferred object
   * The created deferred object is never called until someone call the function 'deferred:callback' or 'deferred:errorback'.
   * Using this object, a deferred chain can pause to wait for other events. (See the source for 'deferred:wait'.)

* deferred:succeed ([value])
   * Arguments 
      * value: a value (optional)
   * Return
      * a deferred object
   * Create a deferred object that has been called the callback function.
   * When a deferred task is connected, the subsequent task will be executed immediately (synchronously).

* deferred:fail ([error])
   * Arguments 
      * error: an error value (optional)
   * Return 
      * a deferred object
   * Create a deferred object that has been called the errorback function.
   * When a deferred task is connected, the subsequent task will be executed immediately (synchronously).

* deferred:callback (d [value])
   * Arguments 
      * d: a deferred object
      * value: a value (optional)
   * Return 
      * a deferred object or a result value
   * Start executing the deferred tasks. The first task is executed synchronously.

* deferred:callback-post (d [value])
   * Arguments 
      * d: a deferred object
      * value: a value (optional)
   * Return 
      * a deferred object or a result value
   * Start executing the deferred tasks. The first task is executed asynchronously.

* deferred:errorback (d [error])
   * Arguments
      * d: a deferred object 
      * error: an error value (optional)
   * Return 
      * a deferred object or a result value
   * Start executing the deferred tasks from errorback. The first task is executed synchronously.

* deferred:errorback-post (d [error])
   * Arguments
      * d: a deferred object 
      * error: an error value (optional)
   * Return 
      * a deferred object or a result value
   * Start executing the deferred tasks from errorback. The first task is executed asynchronously.

### Utility Macros ###

* deferred:try (d &key catch finally)
   * Arguments
      * d: deferred object
      * catch: [keyword argument] A function that is called when an error is occurred during tasks 'd'. (This function is expanded as an argument of 'deferred:error'.)
      * finally: [keyword argument] A function that is called when tasks 'd' finishes whether in success or failure. (This function is expanded as an argument of deferred:watch.)
   * Return
      * a deferred object
   * Try-catch-finally macro. This macro simulates the try-catch-finally block asynchronously.
   * Because of asynchrony, this macro does not ensure that the 'finally' task should be called.
   * This macro is implemented by 'deferred:error' and 'deferred:watch'.

* deferred:timeout (msec timeout-form d)
   * Arguments
      * msec: a number
      * timeout-form: sexp-form
      * d: a deferred object
   * Return
      * a deferred object
   * Time out macro on a deferred task 'd'.
   * If the deferred task 'd' does not complete within 'timeout-msec', this macro cancels the deferred task and return the 'timeout-form'.
   * This macro is implemented by 'deferred:earlier' and 'deferred:wait'.

* deferred:process...
   * deferred:processc (d command args...)
   * deferred:process-bufferc (d command args...)
   * deferred:process-shellc (d command args...)
   * deferred:process-shell-bufferc (d command args...)
   * Arguments
      * d: a deferred object
      * command: command to execute
      * args: command arguments (variable length)
   * Return
      * a deferred object
   * This macro wraps the deferred:process function in deferred:nextc and connect the given deferred task.

### Execution and Connection ###

#### Firing ####

Some deferred functions can fire a deferred chain implicitly. Following functions register a deferred object with the execution queue to run asynchronously.

* next
* wait
* loop
* parallel
* earlier
* call, apply
* process
* url-retrieve, url-get, url-post


The deferred tasks those are created by 'deferred:new' are never called. Using this object, a deferred chain can pause to wait for other events. (See the source for 'deferred:wait'.)


One can fire the chain before connecting. That is, deferred objects wait for connecting the subsequent task holding the result value. The functions 'deferred:succeed' and 'deferred:fail' create those waiting objects.

#### Static connection ####

The 'static connection (statically connected)' is a connection between deferred tasks on the source code.
This is a basic usage for the deferred chain.

The static connection is almost equivalent to ordinary callback notation as an argument in the function declarations. The deferred notation is easy to read and write better than the callback one, because the sequence of asynchronous tasks can be written by the deferred notation straightforward.

#### Dynamic Connection ####

Returning a deferred object in the deferred tasks, the returned task is executed before the next deferred one that is statically connected on the source code. This is the 'dynamic connection (dynamically connected)'.

Employing a recursive structure of deferred tasks, you can construct higher level control structures, such as loop.

## Discussion ##

Some discussions of writing deferred codes.

### Using lexical scope ###

Using the lexical scope macro, such as 'lexical-let', the deferred tasks defined by lambdas can access local variables.

lexical-let Ex.:

    (lexical-let ((a (point)))
      (deferred:$
        (deferred:wait 1000)
        (deferred:nextc it
          (lambda (x) 
            (goto-char a)
            (insert "here!")))))

If you write a code of deferred tasks without lexical scope macros, you should be careful with the scopes of each variables.

### Excursion (Current status) ###

The 'excursion' functions those hold the current status with the s-exp form, such as 'save-execursion' or 'with-current-buffer', are not valid in the deferred tasks, because of execution asynchronously.

Wrong Ex.:

    (with-current-buffer (get-buffer "*Message*")
      (deferred:$
        (deferred:wait 1000)
        (deferred:nextc it
          (lambda (x)
            (insert "Time: %s " x) ; 'insert' may not be in the *Message* buffer!
          )))) 

In this case, using lexical scope macros to access the buffer variable, you can change the buffer in the deferred task.

Corrected:

    (lexical-let ((buf (get-buffer "*Message*")))
      (deferred:$
        (deferred:wait 1000)
        (deferred:nextc it
          (lambda (x)
            (with-current-buffer buf ; Set buffer in the asynchronous task.
              (insert "Time: %s " x))))))


### Be aware of return values ###

However the dynamic connection is a powerful feature, sometimes it causes bugs of the wrong execution order, because of returning not intended deferred objects.

Then, you should watch the return values of the deferred tasks not to cause an unexpected dynamic connection. 

### Debugging ###

The debugging of asynchronous tasks is difficult. Of course, you can use debugger for deferred tasks, but asynchronous tasks cause some troubles, such as interruptions of your debugging and timing gap of simultaneous deferred tasks. Therefore, logging is a safe debugging to observe the tasks correctly, for example, using the 'message' function and making custom application log buffer.

If deferred tasks fall into an infinite loop unexpectedly (but Emacs may not freeze), calling the command 'deferred:clear-queue', you can stop the deferred tasks immediately.

If the errors occurred in deferred tasks are caught by no errorback functions, finally the deferred framework catches it and reports to the message buffer. Because the implementation of the framework uses a 'condition-case' form, the debugger can not catch the signals normally. If you want to debug the errors in the deferred tasks with the debug-on-error mechanism, set the variable 'deferred:debug-on-signal' non-nil.

Wrapping a deferred task in the function 'deferred:sync!', you can wait for the result of the task synchronously. However, the wrapper function should be used for test or debug purpose, because the synchronous waiting is not exact.

### Using macros ###

Writing deferred tasks with 'deferred.el', you may write a lot of 'deferred:nextc' and 'lambda' to define tasks. Defining a macro, you may write codes shortly. The test code 'test-deferred.el' uses many macros to shorten test codes.

On the other hand, using macros to hide 'lambda', it is difficult to realize when the deferred codes are evaluated. That is why 'deferred.el' does not provide lot of convenient macros. If you use macros, be careful evaluation timing of deferred forms.

### Introduction for deferred ###

Following documents are good introduction to deferred.

* [Introduction to JSDeferred](http://cho45.stfuawsc.com/jsdeferred/doc/intro.en.html "Introduction to JSDeferred")
* [JSDeferred site](http://cho45.stfuawsc.com/jsdeferred/ "JSDeferred site")

* * * * *

(C) 2010, 2011  SAKURAI Masashi  All rights reserved.
m.sakurai at kiwanami.net
