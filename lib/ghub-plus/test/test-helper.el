(unless (require 'ghub+ nil 'noerror)
  (message "attempting to load ghub+ manually...")
  (load-file "./ghub+.el")
  (message "attempting to load ghub+ manually...done")
  (require 'ghub+))

(require 'subr-x)
(require 'dash)
(require 's)

(cl-defun test-request-override (method resource &optional params &key query payload
                                        headers unpaginate noerror reader username auth host)
  (pcase (list method resource params query payload headers
               unpaginate noerror reader username auth host)
    (`("GET" "/repos/vermiculus/ghub-plus" nil nil nil nil nil nil nil nil nil nil)
     '((id . 82884749)))))
(setq ghubp-request-override-function #'test-request-override)

(defun lint-is-api-form-p (form)
  "Is FORM a defapi* macro call?"
  (and (s-prefix-p "defapi" (symbol-name (car form)))
       form))

(defun lint-get-forms (filename)
  "Read FILENAME and return a list of its Lisp forms."
  (let ((pos 0) forms)
    (with-temp-buffer
      (insert-file-contents filename)
      (condition-case _
          (while t
            (when-let ((cell (read-from-string (buffer-string) pos)))
              (push (car cell) forms)
              (goto-char (setq pos (cdr cell)))))
        (error forms)))
    forms))

(defun lint-api-forms (filename)
  "From FILENAME, return a list of API forms."
  (-filter #'lint-is-api-form-p (lint-get-forms filename)))

(defun lint-arg-appears-in-target-p (arg target-string)
  "Does symbol ARG appear in TARGET-STRING?
Such that `apiwrap-resolve-api-params' would see it?"
  (and (stringp target-string)
       (or (s-contains-p (format ":%S." arg) target-string)
           (s-contains-p (format ":%S/" arg) target-string)
           (s-suffix-p   (format ":%S"  arg) target-string))))

(defun lint-target-to-args (target-string)
  (let (args)
    (with-temp-buffer
      (save-excursion
        (insert target-string))
      (while (search-forward ":" nil t)
        (let ((arg (buffer-substring-no-properties
                    (point)
                    (1- (search-forward-regexp (rx (or "." "/" eol)))))))
          (unless (member arg args)
            (push arg args)))))
    args))

(defun lint-form-used-args (form)
  (when-let ((target (nth 5 form)))
    (when (stringp target)
      (lint-target-to-args target))))

(defun lint-form-declared-args (form)
  (when-let ((arg-list (nth 4 form)))
    (when (and (listp arg-list) (-all-p #'symbolp arg-list))
      (mapcar #'symbol-name arg-list))))

(defun lint--sets-equal (l1 l2)
  (and (--all-p (member it l1) l2)
       (--all-p (member it l2) l1)))

(defun lint-macro-to-method (msym)
  "Get the HTTP method corresponding to MSYM."
  (let ((s (symbol-name msym)))
    (upcase (substring s 6 (s-index-of "-" s)))))

(defun lint-unused-args (form)
  "Check for any unused arguments in FORM.
If there are unused arguments, print them out with `message' and
return them.  Return nil if there are no offenders."
  (let ((used (lint-form-used-args form))
        (declared (lint-form-declared-args form))
        (defapi (lint-format-defapi-form form))
        unused undeclared)
    (unless (lint--sets-equal used declared)
      (setq unused     (cl-set-difference declared used :test #'string=)
            undeclared (cl-set-difference used declared :test #'string=))
      (dolist (arg unused)
        (message "Unused argument in '%s': %s" defapi arg))
      (dolist (arg undeclared)
        (message "Undeclared argument in '%s': %s" defapi arg))
      t)))

(defun lint-format-defapi-form (form)
  "=> GET /some/thing/here"
  (concat (lint-macro-to-method (car form)) " " (cadr form)))

(defun lint-standard-args-undeclared--get-backend (filename)
  "Get the backend declaration form from FILENAME."
  (with-temp-buffer
    (insert-file filename)
    (let ((needle "(apiwrap-new-backend"))
      (search-forward needle)
      (backward-char (length needle))
      (read (current-buffer)))))

(defun lint-standard-args-undeclared--get-std-vars (backend)
  "Get the list of standard vars from BACKEND."
  (mapcar #'car (cadr (nth 3 backend))))

(defun lint-standard-args-undeclared--internal (form std-args)
  "Non-nil if FORM uses args not in STD-ARGS"
  (let (fail)
    (when (listp (nth 4 form))
      (dolist (std-arg (nth 4 form))
        (unless (memq std-arg std-args)
          (setq fail t)
          (message "Undefined standard argument in '%s': %S"
                   (lint-format-defapi-form form)
                   std-arg))))
    fail))

(defun lint-undeclared-standard-args (filename)
  "Wrapper for `lint-standard-args-undeclared--internal'."
  (let ((forms (lint-api-forms filename))
        (stdargs (lint-standard-args-undeclared--get-std-vars
                  (lint-standard-args-undeclared--get-backend filename)))
        fail)
    (dolist (form forms)
      (setq fail (or (lint-standard-args-undeclared--internal form stdargs) fail)))
    fail))

(defun lint-ext-reference-in-name (form)
  (s-contains-p "." (cadr form)))

(defun lint (filename lint-function &optional per-form)
  "Run all linting checks on forms in FILENAME."
  (let (fail)
    (if per-form
        (dolist (form (lint-api-forms filename))
          (setq fail (or (funcall lint-function form) fail)))
      (setq fail (funcall lint-function filename)))
    (not fail)))
