(cl-defstruct (eshell-function-target
               (:constructor nil)
               (:constructor eshell-function-target-create
                             (output-function &optional close-function)))
  "An Eshell target that calls an OUTPUT-FUNCTION."
  output-function close-function)

(defun eshell-exec-lisp (printer errprint func-or-form args form-p)
  "Execute a Lisp FUNC-OR-FORM, maybe passing ARGS.
PRINTER and ERRPRINT are functions to use for printing regular
messages and errors, respectively.  FORM-P should be non-nil if
FUNC-OR-FORM represent a Lisp form; ARGS will be ignored in that
case."
  (eshell-condition-case err
      (let ((result
             (save-current-buffer
               (if form-p
                   (eval func-or-form)
                 (apply func-or-form args)))))
        ;; As a special case, a Lisp function or form may evaluate to an
        ;; `eshell-function-target', which represents a virtual output
        ;; device. In that case, any output piped to the lisp command
        ;; will be fed to that function. This makes it possible to use
        ;; Lisp commands on the right-hand side of a pipeline.
        (if (and result (not (eshell-function-target-p result)))
            (funcall printer result))
        result)
    (eshell-pipe-broken
     ;; If FUNC-OR-FORM tried and failed to write some output to a
     ;; process, it will raise an `eshell-pipe-broken' signal (this is
     ;; analogous to SIGPIPE on POSIX systems).  In this case, set the
     ;; command status to some non-zero value to indicate an error; to
     ;; match GNU/Linux, we use 141, which the numeric value of
     ;; SIGPIPE on GNU/Linux (13) with the high bit (2^7) set.
     (setq eshell-last-command-status 141)
     nil)
    (error
     (setq eshell-last-command-status 1)
     (let ((msg (error-message-string err)))
       (if (and (not form-p)
                (string-match "^Wrong number of arguments" msg)
                (fboundp 'eldoc-get-fnsym-args-string))
           (let ((func-doc (eldoc-get-fnsym-args-string func-or-form)))
             (setq msg (format "usage: %s" func-doc))))
       (funcall errprint msg))
     nil)))

(defun eshell-lisp-command (object &optional args)
  "Insert Lisp OBJECT, using ARGS if a function."
  (catch 'eshell-external               ; deferred to an external command
    (setq eshell-last-command-status 0
          eshell-last-arguments args)
    (let* ((eshell-ensure-newline-p (eshell-interactive-output-p))
           (command-form-p (functionp object))
           (result
            (if command-form-p
                (let ((numeric (not (get object
                                         'eshell-no-numeric-conversions)))
                      (fname-args (get object 'eshell-filename-arguments)))
                  (when (or numeric fname-args)
                    (while args
                      (let ((arg (car args)))
                        (cond
                         ((and numeric (stringp arg) (> (length arg) 0)
                               (text-property-any 0 (length arg)
                                                  'number t arg))
                          ;; If any of the arguments are flagged as
                          ;; numbers waiting for conversion, convert
                          ;; them now.
                          (setcar args (string-to-number arg)))
                         ((and fname-args (stringp arg)
                               (string-equal arg "~"))
                          ;; If any of the arguments match "~",
                          ;; prepend "./" to treat it as a regular
                          ;; file name.
                          (setcar args (concat "./" arg)))))
                      (setq args (cdr args))))
                  (setq eshell-last-command-name
                        (concat "#<function " (symbol-name object) ">"))
                  (eshell-apply object eshell-last-arguments))
              (setq eshell-last-command-name "#<Lisp object>")
              (eshell-eval object))))
      (if (and eshell-ensure-newline-p
	       (save-excursion
		 (goto-char eshell-last-output-end)
		 (not (bolp))))
	  (eshell-print "\n"))
      (eshell-close-handles
       ;; If `eshell-lisp-form-nil-is-failure' is non-nil, Lisp forms
       ;; that succeeded but have a nil result should have an exit
       ;; status of 2.
       (when (and eshell-lisp-form-nil-is-failure
                  (not command-form-p)
                  (= eshell-last-command-status 0)
                  (not result))
         2)
       (list 'quote result))
      (and (eshell-function-target-p result)
           result))))

(defun eshell-close-target (target status)
  "Close an output TARGET, passing STATUS as the result.
STATUS should be non-nil on successful termination of the output."
  (cond
   ((symbolp target) nil)

   ;; If we were redirecting to a file, save the file and close the
   ;; buffer.
   ((markerp target)
    (let ((buf (marker-buffer target)))
      (when buf                         ; somebody's already killed it!
	(save-current-buffer
	  (set-buffer buf)
	  (when eshell-output-file-buffer
	    (save-buffer)
	    (when (eq eshell-output-file-buffer t)
	      (or status (set-buffer-modified-p nil))
	      (kill-buffer buf)))))))

   ;; If we're redirecting to a process (via a pipe, or process
   ;; redirection), send it EOF so that it knows we're finished.
   ((eshell-processp target)
    ;; According to POSIX.1-2017, section 11.1.9, when communicating
    ;; via terminal, sending EOF causes all bytes waiting to be read
    ;; to be sent to the process immediately.  Thus, if there are any
    ;; bytes waiting, we need to send EOF twice: once to flush the
    ;; buffer, and a second time to cause the next read() to return a
    ;; size of 0, indicating end-of-file to the reading process.
    ;; However, some platforms (e.g. Solaris) actually require sending
    ;; a *third* EOF.  Since sending extra EOFs while the process is
    ;; running are a no-op, we'll just send the maximum we'd ever
    ;; need.  See bug#56025 for further details.
    (let ((i 0)
          ;; Only call `process-send-eof' once if communicating via a
          ;; pipe (in truth, this just closes the pipe).
          (max-attempts (if (process-tty-name target 'stdin) 3 1)))
      (while (and (<= (cl-incf i) max-attempts)
                  (eq (process-status target) 'run))
        (process-send-eof target))))

   ;; A plain function redirection needs no additional arguments
   ;; passed.
   ((functionp target)
    (funcall target status))

   ((eshell-function-target-p target)
    (funcall (eshell-function-target-close-function target) status))

   ;; But a more complicated function redirection (which can only
   ;; happen with aliases at the moment) has arguments that need to be
   ;; passed along with it.
   ((consp target)
    (apply (car target) status (cdr target)))))

(defun eshell-get-target (target &optional mode)
  "Convert TARGET, which is a raw argument, into a valid output target.
MODE is either `overwrite', `append' or `insert'; if it is omitted or nil,
it defaults to `insert'."
  (setq mode (or mode 'insert))
  (cond
   ((stringp target)
    (let ((redir (assoc target eshell-virtual-targets)))
      (if redir
	  (if (nth 2 redir)
	      (funcall (nth 1 redir) mode)
	    (nth 1 redir))
	(let* ((exists (get-file-buffer target))
	       (buf (find-file-noselect target t)))
	  (with-current-buffer buf
	    (if buffer-file-read-only
		(error "Cannot write to read-only file `%s'" target))
	    (setq buffer-read-only nil)
            (setq-local eshell-output-file-buffer
                        (if (eq exists buf) 0 t))
	    (cond ((eq mode 'overwrite)
		   (erase-buffer))
		  ((eq mode 'append)
		   (goto-char (point-max))))
	    (point-marker))))))


   ((bufferp target)
    (with-current-buffer target
      (cond ((eq mode 'overwrite)
             (erase-buffer))
            ((eq mode 'append)
             (goto-char (point-max))))
      (point-marker)))

   ((functionp target) nil)

   ((eshell-function-target-p target) target)

   ((symbolp target)
    (if (eq mode 'overwrite)
	(set target nil))
    target)

   ((or (eshell-processp target)
	(markerp target))
    target)

   (t
    (error "Invalid redirection target: %s"
	   (eshell-stringify target)))))

(defun eshell-output-object-to-target (object target)
  "Insert OBJECT into TARGET.
Returns what was actually sent, or nil if nothing was sent."
  (cond
   ((functionp target)
    (funcall target object))

   ((eshell-function-target-p target)
    (funcall (eshell-function-target-output-function target) object))

   ((symbolp target)
    (if (eq target t)                   ; means "print to display"
	(eshell-output-filter nil (eshell-stringify object))
      (if (not (symbol-value target))
	  (set target object)
	(setq object (eshell-stringify object))
	(if (not (stringp (symbol-value target)))
	    (set target (eshell-stringify
			 (symbol-value target))))
	(set target (concat (symbol-value target) object)))))

   ((markerp target)
    (if (buffer-live-p (marker-buffer target))
	(with-current-buffer (marker-buffer target)
	  (let ((moving (= (point) target)))
	    (save-excursion
	      (goto-char target)
	      (unless (stringp object)
		(setq object (eshell-stringify object)))
	      (insert-and-inherit object)
	      (set-marker target (point-marker)))
	    (if moving
		(goto-char target))))))

   ((eshell-processp target)
    (unless (stringp object)
      (setq object (eshell-stringify object)))
    (condition-case err
        (process-send-string target object)
      (error
       ;; If `process-send-string' raises an error and the process has
       ;; finished, treat it as a broken pipe.  Otherwise, just
       ;; re-throw the signal.
       (if (memq (process-status target)
		 '(run stop open closed))
           (signal (car err) (cdr err))
         (signal 'eshell-pipe-broken (list target))))))

   ((consp target)
    (apply (car target) object (cdr target))))
  object)
