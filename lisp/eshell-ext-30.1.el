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
  (unless eshell-allow-commands
    (signal 'eshell-commands-forbidden '(lisp)))
  (catch 'eshell-external               ; deferred to an external command
    (setq eshell-last-command-status 0
          eshell-last-arguments args)
    (let* ((eshell-ensure-newline-p t)
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
                  (eshell-apply* #'eshell-print-maybe-n
                                 #'eshell-error-maybe-n
                                 object eshell-last-arguments))
              (setq eshell-last-command-name "#<Lisp object>")
              (eshell-eval* #'eshell-print-maybe-n
                            #'eshell-error-maybe-n
                            object))))
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

(cl-defstruct (eshell-function-target
               (:include eshell-generic-target)
               (:constructor nil)
               (:constructor eshell-function-target-create
                             (output-function &optional close-function)))
  "An Eshell target that calls an OUTPUT-FUNCTION."
  output-function close-function)

(cl-defmethod eshell-get-target ((raw-target eshell-function-target) &optional _mode)
  "Convert a function RAW-TARGET into a valid output target.
This just returns RAW-TARGET."
  raw-target)