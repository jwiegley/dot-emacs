;;; peval.el --- Partial evaluation of elisp forms   -*- lexical-binding: t; -*-

;; Copyright (C) 2017  Wilfred Hughes

;; Author: Wilfred Hughes <me@wilfred.me.uk>
;; Keywords: lisp
;; Version: 0.1

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

;; Partially evaluate (and simplify) elisp forms.

;;; Code:

(require 'cl-lib)
(require 'dash)

;; Backport of
;; http://git.savannah.gnu.org/cgit/emacs.git/commit/?id=dc79aa10f117dea1204634626a5f96a21722807f
(when (< emacs-major-version 26)
  (put 'keywordp 'side-effect-free 'error-free))

(defun peval--source (sym)
  "Return the source code of SYM as an s-expression."
  (-if-let ((buf . start-pos) (peval--definition sym))
      (with-current-buffer buf
        (save-excursion
          (goto-char start-pos)
          (read (current-buffer))))
    ;; Could not find source -- probably defined interactively, or via
    ;; a macro, or file has changed, or a primitive.
    (indirect-function sym)))

(defun peval--definition (sym)
  "Return a pair (BUF . POS) where SYM is defined."
  (let (buf-and-pos)
    (ignore-errors
      (setq buf-and-pos
            (find-function-noselect sym)))
    (if buf-and-pos
        buf-and-pos
      ;; If it's defined interactively, it may have an edebug property
      ;; that tells us where it's defined.
      (-when-let (marker (get sym 'edebug))
        (cons (marker-buffer marker)
              (marker-position marker))))))

(define-derived-mode peval-mode emacs-lisp-mode "Partial Eval"
  "Major mode for partially evaluating elisp functions.")

(defun peval ()
  (interactive)
  (let* ((buf (get-buffer-create "*peval*")))
    (with-current-buffer buf
      (let ((inhibit-read-only t))
        (erase-buffer)
        (insert ";; Specify function arguments\n"
                "(-slice '(2 3 4 5) _ 3)\n"
                "\n"
                ";; Simplified function (press C-c C-c to update):")
        (peval-update)
        (peval-mode)))
    (switch-to-buffer buf)))

(define-key peval-mode-map (kbd "C-c C-c") #'peval-update)

(defconst peval-placeholder
  (make-symbol "peval-placeholder")
  "A unique symbol representing _ in forms given.")

(defun peval--zip-bindings (bindings-given raw-func-args)
  "Given BINDINGS-GIVEN of the form (1 2 3) and RAW-FUNC-ARGS
of the form (x y &optional z), return a list of zipped pairs."
  (let ((bindings-i 0)
        (args-i 0)
        (required-args t)
        result)
    ;; All the bindings we have been given for arguments.
    (while (< bindings-i (length bindings-given))
      (let ((binding (nth bindings-i bindings-given))
            (arg (nth args-i raw-func-args)))
        (cond
         ((eq arg '&optional)
          (setq required-args nil)
          (cl-incf args-i))
         ((eq arg '&rest)
          (error "todo"))
         ;; Skip placeholders.
         ((eq binding peval-placeholder)
          (cl-incf bindings-i)
          (cl-incf args-i))
         ;; Match up an argument with the binding given.
         (t
          (push (cons arg binding) result)
          (cl-incf bindings-i)
          (cl-incf args-i)))))
    ;; All the remaining optional arguments.
    (while (< args-i (length raw-func-args))
      (let ((arg (nth args-i raw-func-args)))
        (cond
         ((not required-args)
          (push (cons arg nil) result))
         ((eq arg '&optional)
          (setq required-args nil)))
        (cl-incf args-i)))
    (nreverse result)))

(defun peval-update ()
  (interactive)
  (let (form-given sym-given raw-bindings-given bindings-given)
    (save-excursion
      ;; Get the form entered by the user.
      (goto-char (point-min))
      (setq form-given (read (current-buffer)))
      (setq sym-given (car form-given))
      (setq raw-bindings-given (cdr form-given))

      ;; Go to the next comment and erase the previous simplified
      ;; form.
      (search-forward ";;")
      (forward-line)
      (delete-region (point) (point-max))

      ;; TODO: ensure SYM-GIVEN is a defined function.

      ;; Evaluate the bindings specified by the user. This enables us
      ;; to convert (foo tab-width) => (foo 4)
      (dolist (form raw-bindings-given)
        (push 
         (if (eq form '_)
             peval-placeholder
           (eval form))
         bindings-given))
      (setq bindings-given (nreverse bindings-given))

      ;; Get the source and partially evaluate it with respect to the
      ;; arguments given.
      (let* ((src (peval--source sym-given))
             (fn-name (cl-second src))
             (fn-args (cl-third src))
             (fn-body `(progn ,@(-slice src 3)))
             (simple-body
              (peval-result-value
               (peval--simplify
                fn-body
                (peval--zip-bindings bindings-given fn-args))))
             (simple-fn `(defun ,fn-name ,fn-args
                           ,simple-body)))
        (cl-prettyprint simple-fn)))))

(defun peval--simplify-progn-body (forms bindings)
  "Simplify all the forms in FORMS using partial application.
If any form evaluates to a simple value, discard it unless
it is the final form."
  (let (simplified-exprs current)
    ;; Evaluate every expression in the progn body.
    (dolist (form forms)
      (setq current (peval--simplify-1 form bindings))
      ;; If we evaluated the expression to a value, just throw it
      ;; away.
      (unless (peval-result-evaluated-p current)
        (push current simplified-exprs)))
    ;; If the last expression was a value, we still need to return
    ;; it.
    (when (and current (peval-result-evaluated-p current))
      (push current simplified-exprs))
    
    (setq simplified-exprs (nreverse simplified-exprs))
    (if (= (length simplified-exprs) 1)
        (car simplified-exprs)
      (make-peval-result
       :evaluated-p nil
       :value `(progn
                 ,@(mapcar #'peval-result-value simplified-exprs))))))

(defun peval--progn-body-safe (form)
  "Strip the leading 'progn in FORM, if present.
Always returns a list.

'(progn x y) => '(x y)
'(a b) => '((a b))
1 => '(1)"
  (cond
   ((eq (car-safe form) 'progn)
    (cdr form))
   (t
    (list form))))

;; TODO: we need to ensure we are splicing symbols/lists in correctly.

(defun peval--simplify-let (let-sym exprs let-bindings bindings)
  (let ((bindings-inside (peval--push-scope bindings))
        unknown-bindings
        simple-body)
    (dolist (let-binding let-bindings)
      (pcase let-binding
        (`(,sym ,form)
         (peval--add-local-var sym nil bindings-inside)
         ;; Evaluate form, and set it in the new scope in bindings.
         (let* ((val (peval--simplify-1 form
                                        (if (eq let-sym 'let*)
                                            bindings-inside
                                          bindings))))
           (if (peval-result-evaluated-p val)
               (peval--set-var sym (peval-result-value val) bindings-inside)
             ;; Could not evaluate, so mark this variable as unknown in the environment.
             (peval--set-var-unknown sym bindings-inside)
             ;; We will keep this variable visible in the let binding.
             ;; TODO: We should preserve variables if later values are unknown, e.g.
             ;; (let ((x 1)) (setq x (foo x)))
             (push
              (list sym (peval-result-value val))
              unknown-bindings))))
        (`,sym
         ;; (let (x) ...) is equivalent to (let ((x nil)) ...).
         (peval--add-local-var sym nil bindings))))
    (setq unknown-bindings (nreverse unknown-bindings))

    (setq simple-body (peval--simplify-progn-body exprs bindings-inside))

    (if (peval-result-evaluated-p simple-body)
        (make-peval-result
         :evaluated-p t
         :value (peval-result-value simple-body))

      ;; (let () x) => x
      (if (null unknown-bindings)
          (make-peval-result
           :evaluated-p nil
           :value (peval-result-value simple-body))
        ;; a progn can be added by `peval--simplify-progn-body', so
        ;; (let _ (progn x y)) => (let _ x y)
        (make-peval-result
         :evaluated-p nil
         :value
         `(let ,unknown-bindings
            ,@(peval--progn-body-safe (peval-result-value simple-body))))))))

(cl-defstruct peval-result
  "Structure that represents the result of partially evaluating
an s-expression.

Slots:

`evaluated-p'
    Whether we were able to fully evaluate the form given.

`value'
    The result of evaluating the form. This may be the original form,
    a simplified version of that form, or a simple value."
  evaluated-p value)

(cl-defstruct peval-bound-val
  "Structure that represents the value of a bound variable in a scope.

Slots:

`known-p'
    Whether we know the current value.

`value'
    The current value this represents. This is meaningless if
    `known-p' is nil."
  known-p value)

;; TODO: this is just the variable namespace. What about the function
;; namespace?
;; TODO: use "env" instead of "bindings" everywhere.
(defun peval--fresh-env ()
  "Return a new empty environment without any bindings."
  (list nil))

(defun peval--push-scope (env)
  "Add a new inner scope to ENV."
  (cons nil env))

(defun peval--bound-p (sym env)
  "Return non-nil if SYM is bound in ENV."
  (-any-p
   (lambda (scope)
     (assoc sym scope))
   env))

(defun peval--add-local-var (sym value env)
  "Define SYM with VALUE in the innermost scope in ENV.
Mutates ENV."
  (let ((scope (car env)))
    (setcar env
            (cons
             (cons
              sym
              (make-peval-bound-val :known-p t :value value))
             scope))
    nil))

(defun peval--add-global-var (sym value env)
  "Define SYM with VALUE in the outermost scope in ENV.
Mutates ENV."
  (let ((scope-cons (last env)))
    (setcar scope-cons
            (cons
             (cons
              sym
              (make-peval-bound-val :known-p t :value value))
             (car scope-cons)))
    nil))

(defun peval--set-var (sym value env)
  "Set SYM to VALUE in ENV."
  (if (peval--bound-p sym env)
      (catch 'break
        (dolist (scope env)
          (let ((binding (assoc sym scope)))
            (when binding
              (setcdr binding
                      (make-peval-bound-val :known-p t :value value))
              (throw 'break nil)))))
    ;; Assigning to a non-existent variable creates a global.
    (peval--add-global-var sym value env))
  nil)

(defun peval--set-var-unknown (sym env)
  "Mark SYM as unknown in ENV."
  (catch 'break
    (dolist (scope env)
      (let ((binding (assoc sym scope)))
        (when binding
          (setcdr binding
                  (make-peval-bound-val :known-p nil))
          (throw 'break nil))))))

(defun peval--get-var (sym env)
  (catch 'break
    (dolist (scope env)
      (let ((binding (assoc sym scope)))
        (when binding
          (throw 'break (cdr binding)))))))

;; TODO: copy bindings to handle conditional assignments.
;; e.g. (if unknown (setq x 1)) ; x is not known after this if!
(defun peval--simplify-list (form bindings)
  "Simplify FORM in the context of BINDINGS using partial application.
FORM must be a cons cell."
  (pcase form
    (`(if ,cond ,then)
     (peval--simplify-1 `(if ,cond ,then nil) bindings))
    (`(if ,cond ,then . ,else)
     (setq cond (peval--simplify-1 cond bindings))
     (setq then (peval--simplify-1 then bindings))
     (setq else (peval--simplify-progn-body else bindings))
     (cond
      ;; If we can evaluate the if condition, then simplify to just the
      ;; THEN or the ELSE.
      ((peval-result-evaluated-p cond)
       (if (peval-result-value cond) then else))
      ;; `peval--simplify-progn-body' may have added a progn, so
      ;; simplify: (if _ _ (progn x y)) => (if _ _ x y)
      ((not (peval-result-evaluated-p else))
       (make-peval-result
        :evaluated-p nil
        :value `(if ,(peval-result-value cond)
                    ,(peval-result-value then)
                  ,@(peval--progn-body-safe (peval-result-value else)))))
      ;; Otherwise, return an if where we have simplified as much as
      ;; we can.
      (t
       (make-peval-result
        :evaluated-p nil
        :value `(if ,(peval-result-value cond)
                    ,(peval-result-value then)
                  ,(peval-result-value else))))))

    ;; Discard (declare ...) forms.
    (`(declare . ,_)
     (make-peval-result
      :evaluated-p t :value nil))

    ;; Remove pointless values in progn, e.g.
    ;; (progn nil (foo) (bar)) -> (progn (foo) (bar))
    (`(progn . ,exprs)
     (peval--simplify-progn-body exprs bindings))

    (`(let ,let-bindings . ,exprs)
     (peval--simplify-let 'let exprs let-bindings bindings))

    (`(let* ,let-bindings . ,exprs)
     (peval--simplify-let 'let* exprs let-bindings bindings))
    
    (`(when ,cond . ,body)
     (setq cond (peval--simplify-1 cond bindings))
     (setq body (peval--simplify-progn-body body bindings))
     (cond
      ;; (when t _) => _
      ((and
        (peval-result-evaluated-p cond)
        (peval-result-value cond))
       body)
      ;; (when nil _) => nil
      ((peval-result-evaluated-p cond)
       (make-peval-result
        :evaluated-p t :value nil))
      ;; If we've fully evaluated the body, but not the condition.
      ((peval-result-evaluated-p body)
       (make-peval-result
        :evaluated-p nil
        :value `(when ,(peval-result-value cond)
                  ,(peval-result-value body))))
      ;; Partially evaluated form.
      (t
       (make-peval-result
        :evaluated-p nil
        :value `(when ,(peval-result-value cond)
                  ;; body looks like (progn BODY...), so strip the progn.
                  ,@(peval--progn-body-safe (peval-result-value body)))))))
    
    (`(unless ,cond . ,body)
     (setq cond (peval--simplify-1 cond bindings))
     (setq body (peval--simplify-progn-body body bindings))
     (cond
      ;; (unless nil _) => _
      ((and
        (peval-result-evaluated-p cond)
        (not (peval-result-value cond)))
       body)
      ;; (unless t _) => nil
      ((peval-result-evaluated-p cond)
       (make-peval-result
        :evaluated-p t :value nil))
      ;; Partially evaluated form.
      (t
       (make-peval-result
        :evaluated-p nil
        :value `(unless ,(peval-result-value cond)
                  ;; body looks like (progn BODY...), so strip the progn.
                  ,@(peval--progn-body-safe (peval-result-value body)))))))
    
    ;; TODO: backquote.
    (`(quote ,sym)
     (make-peval-result
      :evaluated-p t :value sym))

    ;; (`(set ,sym ,val)
    ;;  (setq sym (peval--simplify-1 sym bindings))
    ;;  (setq val (peval--simplify-1 val bindings))
    ;;  (if (and (peval-result-evaluated-p)))
    ;;  )
    
    ;; TODO: consider aliasing of mutable values (e.g. two variables
    ;; pointing to the same list).
    (`(setq . ,syms-and-vals)
     (setq syms-and-vals (-partition 2 syms-and-vals))
     (let ((results
            (-map (-lambda ((sym val))
                    (setq val (peval--simplify-1 val bindings))
                    (if (peval-result-evaluated-p val)
                        (peval--set-var sym (peval-result-value val) bindings)
                      (peval--set-var-unknown sym bindings))
                    val)
                  syms-and-vals)))
       (if (-all-p #'peval-result-evaluated-p results)
           (-last-item results)
         (let ((syms (-map #'-first-item syms-and-vals)))
           ;; TODO: (setq x 1 y (unknown)) => (setq y unknown)
           ;; if x is unused elsewhere.
           (make-peval-result
            :evaluated-p nil :value
            ;; TODO: Use splice here.
            `(setq ,@(-interleave syms (-map #'peval-result-value results))))))))

    (`(or . ,exprs)
     (let (simple-exprs
           current)
       (cl-block nil           ; dolist is not advised in `ert-runner'
         (dolist (expr exprs)
           (setq current (peval--simplify-1 expr bindings))
           (cond
            ;; If a value is truthy, we can simplify.
            ;; (or x t y) => (or x t)
            ((and
              (peval-result-evaluated-p current)
              (peval-result-value current))
             (push current simple-exprs)
             (cl-return))              ; break from dolist
            ;; If the current value is evaluated and falsy, discard
            ;; it.
            ((peval-result-evaluated-p current))
            ;; Otherwise, we will need to build up a list of
            ;; unevaluated arguments to `or'.
            (t
             (push current simple-exprs)))))

       (setq simple-exprs (nreverse simple-exprs))
       (cond
        ;; (or) => nil
        ((null simple-exprs)
         (make-peval-result
          :evaluated-p t :value nil))
        ;; (or _) => _
        ((= (length simple-exprs) 1)
         (car simple-exprs))
        ;; Partially evaluated or.
        (t
         (make-peval-result
          :evaluated-p nil
          :value `(or ,@(mapcar #'peval-result-value simple-exprs)))))))

    (`(cond . ,clauses)
     (let (simple-clauses)
       (cl-block nil           ; dolist is not advised in ert-runner
         (dolist (clause clauses)
           (pcase clause
             (`(,condition)
              (setq condition (peval--simplify-1 condition bindings))

              (cond
               ;; If this clause is falsy, discard it.
               ;; (cond (nil) (y z)) => (cond (y z))
               ((and
                 (peval-result-evaluated-p condition)
                 (not (peval-result-value condition))))
               ;; If this clause is truthy, we can simplify.
               ;; (cond (x y) (123) (a b)) => (cond (x y) (123))
               ((peval-result-evaluated-p condition)
                (push (list condition) simple-clauses)
                ;; Break from dolist, because we will never execute
                ;; later clauses.
                (cl-return))
               ;; Otherwise, build up the list of simplified clauses.
               (t
                (push (list condition) simple-clauses))))
             
             (`(,condition . ,body)
              (setq condition (peval--simplify-1 condition bindings))

              (cond
               ;; If this clause is falsy, discard it.
               ;; (cond (nil x) (y z)) => (cond (y z))
               ((and
                 (peval-result-evaluated-p condition)
                 (not (peval-result-value condition))))
               ;; If this clause is truthy, we can simplify
               ;; (cond (x y) (t z) (a b)) => (cond (x y) (t z))
               ((peval-result-evaluated-p condition)
                (push (list condition
                            (peval--simplify-progn-body body bindings))
                      simple-clauses)
                ;; Break from dolist, because we will never execute
                ;; later clauses.
                (cl-return))
               ;; Otherwise, build up the list of simplified clauses.
               (t
                (push (list condition
                            (peval--simplify-progn-body body bindings))
                      simple-clauses)))))))

       (pcase (nreverse simple-clauses)
         ;; We simplified away all the clauses, so this is just nil.
         ;; (cond) => nil
         (`()
          (make-peval-result
           :evaluated-p t :value nil))
         ;; We simplifed to a single clause without a body.
         ;; (cond (a)) => a
         (`((,condition))
          condition)
         ;; We simplified to a single clause with a body.
         (`((,condition ,body))
          (cond
           ;; (cond (t x)) => x
           ((and
             (peval-result-evaluated-p condition)
             (peval-result-value condition))
            body)
           ;; (cond (nil x)) => nil
           ((peval-result-evaluated-p condition)
            ;; TODO: returning nil here looks wrong.
            (make-peval-result
             :evaluated-p nil
             :value nil))
           ;; (cond (a b c)) => (when a b c)
           (t
            (make-peval-result
             :evaluated-p nil
             :value `(when ,(peval-result-value condition)
                       ,@(peval--progn-body-safe (peval-result-value body)))))))
         ;; Return a cond of the clauses that we couldn't simplify.
         (`,clauses
          (make-peval-result
           :evaluated-p nil
           :value (let ((clause-forms
                         (--map
                          (pcase it
                            (`(,condition)
                             (list (peval-result-value condition)))
                            (`(,condition ,body)
                             (cons (peval-result-value condition)
                                   (peval--progn-body-safe (peval-result-value body)))))
                          clauses)))
                    `(cond ,@clause-forms)))))))

    ;; Function call.
    ((and `(,fn . ,args) (guard (functionp fn)))
     (setq args (--map (peval--simplify-1 it bindings) args))
     ;; If it's a pure function, and we could evaluate all the
     ;; arguments, call it.
     (if (and
          (--all-p (peval-result-evaluated-p it) args)
          (get fn 'side-effect-free))
         (make-peval-result
          :evaluated-p t
          :value (apply fn (mapcar #'peval-result-value args)))
       (make-peval-result
        :evaluated-p nil
        :value `(,fn ,@(mapcar #'peval-result-value args)))))
    (`(,fn . ,args)
     ;; Either a function we don't know about, or a macro. We can't
     ;; simplify because we don't know which arguments are evaluated.
     (make-peval-result
      :evaluated-p nil
      :value form))

    (_ (error "Don't know how to simplify list: %s" form))))

(defun peval--simplify-atom (form bindings)
  "Simplify FORM in the context of BINDINGS using partial application."
  (cond
   ;; Symbols that we don't look up in BINDINGS.
   ((eq form nil)
    (make-peval-result
     :evaluated-p t :value nil))
   ((eq form t)
    (make-peval-result
     :evaluated-p t :value t))

   ;; Keywords (which are symbols) evaluate to themselves.
   ((keywordp form)
    (make-peval-result
     :evaluated-p t :value form))
   
   ;; We can evaluate a symbol if it is present in BINDINGS with a
   ;; known value.
   ;; TODO: rename peval-bound-val to peval-var.
   ((symbolp form)
    (if (peval--bound-p form bindings)
        (let ((var (peval--get-var form bindings)))
          (if (peval-bound-val-known-p var)
              (make-peval-result
               :evaluated-p t :value (peval-bound-val-value var))
            (make-peval-result
             :evaluated-p nil :value form)))
      ;; Variable was not even bound. Probably a global defvar that we
      ;; haven't seen.
      (make-peval-result
       :evaluated-p nil :value form)))
   ;; Other atoms (strings, keywords, integers, characters) just
   ;; evaluate to themselves.
   (t
    (make-peval-result
     :evaluated-p t :value form))))

(defun peval--simplify-1 (form bindings)
  (cond
   ((atom form)
    (peval--simplify-atom form bindings))
   (t
    (peval--simplify-list form bindings))))

(defun peval--simplify (form &optional bindings)
  "Simplify FORM in the context of BINDINGS using partial application.
Loops are not executed and side-effecting functions are not run.

Bindings should be an alist of symbols to values.

Returns a `peval-value' struct."
  (let ((env (peval--fresh-env)))
    (-each bindings
      (-lambda ((sym . value))
        (peval--set-var sym value env)))
    (peval--simplify-1 form env)))

(provide 'peval)
;;; peval.el ends here

