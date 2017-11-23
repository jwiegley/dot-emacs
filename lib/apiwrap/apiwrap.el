;;; apiwrap.el --- api-wrapping macros     -*- lexical-binding: t; -*-

;; Copyright (C) 2017  Sean Allred

;; Author: Sean Allred <code@seanallred.com>
;; Keywords: tools, maint, convenience
;; Homepage: https://github.com/vermiculus/apiwrap.el
;; Package-Requires: ((emacs "25"))
;; Package-Version: 0.3

;; This file is not part of GNU Emacs.

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

;; API-Wrap.el is a tool to interface with the APIs of your favorite
;; services.  These macros make it easy to define efficient and
;; consistently-documented Elisp functions that use a natural syntax
;; for application development.

;;; Code:

(require 'cl-lib)

(defun apiwrap-genform-resolve-api-params (object url)
  "Resolve parameters in URL to values in OBJECT.

Example:

    \(apiwrap-genform-resolve-api-params
        '\(\(name . \"Hello-World\"\)
          \(owner \(login . \"octocat\"\)\)\)
      \"/repos/:owner.login/:name/issues\"\)

    ;; \"/repos/octocat/Hello-World/issues\"

"
  (declare (indent 1))
  ;; Yes I know it's hacky, but it works and it's compile-time
  ;; (which is to say: pull-requests welcome!)
  (save-match-data
    (with-temp-buffer
      (insert url)
      (goto-char 0)
      (let ((param-regexp (rx ":" (group (+? (any alpha "-" "."))) (or (group "/") eos)))
            replacements)
        (while (search-forward-regexp param-regexp nil 'noerror)
          (push (match-string-no-properties 1) replacements)
          (if (null (match-string-no-properties 2))
              (replace-match "%s")
            (replace-match "%s/")))
        (setq replacements
              (mapcar (lambda (s) (list #'apiwrap--encode-url (make-symbol (concat "." s))))
                      (nreverse replacements)))
        (macroexpand-all
         `(let-alist ,(if (or (symbolp object)
                              (and (listp object)
                                   (not (consp (car object)))))
                          object
                        `',object)
            (format ,(buffer-string) ,@replacements)))))))

(defun apiwrap--encode-url (thing)
  (if (numberp thing)
      (number-to-string thing)
    (url-encode-url thing)))

(defun apiwrap-plist->alist (plist)
  "Convert PLIST to an alist.
If a PLIST key is a `:keyword', then it is converted into a
symbol `keyword'."
  (when (= 1 (mod (length plist) 2))
    (error "bad plist"))
  (let (alist)
    (while plist
      (push (cons (apiwrap--kw->sym (car plist))
                  (cadr plist))
            alist)
      (setq plist (cddr plist)))
    alist))

(defun apiwrap--kw->sym (kw)
  "Convert a keyword to a symbol."
  (if (keywordp kw)
      (intern (substring (symbol-name kw) 1))
    kw))

(defun apiwrap--docfn (service-name doc object-param-doc method external-resource link)
  "Documentation string for resource-wrapping functions created
by `apiwrap--defresource'.

SERVICE-NAME is the name of the API being wrapped (e.g., \"ghub\")

DOC is the documentation string for this endpoint.

OBJECT-PARAM-DOC is a string describing the standard parameters
this endpoint requires (usually provided by
`apiwrap-new-backend').  If it's not a string, nothing will be
inserted into the documentation string.

METHOD is one of `get', `post', etc.

EXTERNAL-RESOURCE is the API endpoint as documented in the API.
It does not usually include any syntax for reference-resolution.

LINK is a link to the official documentation for this API
endpoint from the service provider."
  (format "%s

%sDATA is a data structure to be sent with this request.  If it's
not required, it can simply be omitted.

PARAMS is a plist of parameters appended to the method call.

%s

This generated function wraps the %s API endpoint

    %s %s

which is documented at

    URL `%s'"
          doc
          (or (and (stringp object-param-doc)
                   (concat object-param-doc "\n\n"))
              "")
          (make-string 20 ?-)
          service-name
          (upcase (symbol-name method))
          external-resource link))

(defun apiwrap--docmacro (service-name method)
  "Documentation string for macros created by
`apiwrap-new-backend'

SERVICE-NAME is the name of the API being wrapped (e.g., \"ghub\")

METHOD is one of `get', `post', etc."
  (apply #'format "Define a new %s resource wrapper function.

RESOURCE is the API endpoint as written in the %s API
documentation.  Along with the backend prefix (from
`apiwrap-new-backend') and the method (%s), this string will be
used to create the symbol for the new function.

DOC is a specific documentation string for the new function.
Usually, this can be copied from the %s API documentation.

LINK is a link to the %s API documentation.

If non-nil, OBJECTS is a list of symbols that will be used to
resolve parameters in the resource and will be required arguments
of the new function.  Documentation for these parameters (from
the standard parameters of the call to `apiwrap-new-backend')
will be inserted into the docstring of the generated function.

If non-nil, INTERNAL-RESOURCE is the resource-string used to
resolve OBJECT to the ultimate call instead of RESOURCE.  This is
useful in the likely event that the advertised resource syntax
does not align with the structure of the object it works with.
For example, GitHub's endpoint

    GET /repos/:owner/:repo/issues

would be written as

    \(defapiget-<prefix> \"/repos/:owner/:repo/issues\"
      \"List issues for a repository.\"
      \"issues/#list-issues-for-a-repository\"
      (repo) \"/repos/:repo.owner.login/:repo.name/issues\"\)

defining a function called `<prefix>-get-repos-owner-repo-issues'
and taking an object (a parameter called `repo') with the
structure

    \(\(owner \(login . \"octocat\"\)\)
     \(name . \"hello-world\"\)

See the documentation of `apiwrap-resolve-api-params' for more
details on that behavior.

FUNCTIONS is a list of override configuration parameters.  Values
set here (notably those explicitly set to nil) will take
precedence over the defaults provided to `apiwrap-new-backend'."
         (upcase (symbol-name method))
         service-name
         (upcase (symbol-name method))
         (make-list 2 service-name)))

(defun apiwrap-gensym (prefix api-method &optional resource)
  "Generate a symbol for a macro/function."
  (let ((api-method (symbol-name (apiwrap--kw->sym api-method))))
    (intern
     (if resource
         (format "%s-%s%s" prefix api-method
                 (replace-regexp-in-string
                  ":" ""
                  (replace-regexp-in-string "/" "-" resource)))
       (format "defapi%s-%s" api-method prefix)))))

(defun apiwrap-stdgenlink (alist)
  "Standard link generation function."
  (alist-get 'link alist))

(defconst apiwrap-primitives
  '(get put head post patch delete)
  "List of primitive methods.
The `:request' value given to `apiwrap-new-backend' must
appropriately handle all of these symbols as a METHOD.")

(defun apiwrap-genmacros (name prefix standard-parameters functions)
  "Validate arguments and generate all macro forms"
  ;; Default to raw link entered in the macro
  (unless (alist-get 'link functions)
    (setcdr (last functions) (list '(link . apiwrap-stdgenlink))))

  ;; Verify all extension functions are actually functions
  (dolist (f functions)
    (let ((key (car f)) (fn (cdr f)))
      (unless (or (functionp fn)
                  (macrop fn)
                  (and (consp fn)
                       (eq 'function (car fn))
                       (or (functionp (cadr fn))
                           (macrop (cadr fn)))))
        (if (memq key apiwrap-primitives)
            (error "Primitive function literal required: %s" key)
          (byte-compile-warn "Unknown function for `%S': %S" key fn)))))

  ;; Build the macros
  (let (super-form)
    (dolist (method (reverse apiwrap-primitives))
      (let ((macrosym (apiwrap-gensym prefix method)))
        (push `(defmacro ,macrosym (resource doc link
                                             &optional objects internal-resource
                                             &rest functions)
                 ,(apiwrap--docmacro name method)
                 (declare (indent defun) (doc-string 2))
                 (apiwrap-gendefun ,name ,prefix ',standard-parameters ',method
                                   resource doc link objects internal-resource
                                   ',functions functions))
              super-form)))
    super-form))

(defun apiwrap--maybe-apply (func value)
  "Conditionally apply FUNC to VALUE.
If FUNC is non-nil, return a form to apply FUNC to VALUE.
Otherwise, just return VALUE quoted."
  (if func `(funcall ,func ,value) value))

(defun apiwrap-gendefun (name prefix standard-parameters method resource doc link objects internal-resource std-functions override-functions)
  "Generate a single defun form"
  (let ((args '(&optional data &rest params))
        (funsym (apiwrap-gensym prefix method resource))
        resolved-resource-form form functions
        data-massage-func params-massage-func
        primitive-func link-func)

    ;; Be smart about when configuration starts.  Neither `objects' nor
    ;; `internal-resource' can be keywords, so we know that if they
    ;; are, then we need to shift things around.
    (when (keywordp objects)
      (push internal-resource override-functions)
      (push objects override-functions)
      (setq objects nil internal-resource nil))
    (when (keywordp internal-resource)
      (push internal-resource override-functions)
      (setq internal-resource nil))
    (setq functions (append (apiwrap-plist->alist override-functions)
                            std-functions))

    ;; Now that our arguments have settled, let's use them
    (when objects (setq args (append objects args)))

    (setq internal-resource (or internal-resource resource)
          around (alist-get 'around functions)
          primitive-func (alist-get 'request functions)
          data-massage-func (alist-get 'pre-process-data functions)
          params-massage-func (alist-get 'pre-process-params functions)
          link-func (alist-get 'link functions))

    ;; If our functions are already functions (and not quoted), we'll
    ;; have to quote them for the actual defun
    (when (functionp primitive-func)
      (setq primitive-func `(function ,primitive-func)))
    (when (functionp data-massage-func)
      (setq data-massage-func `(function ,data-massage-func)))
    (when (functionp params-massage-func)
      (setq params-massage-func `(function ,params-massage-func)))

    ;; Alright, we're ready to build our function
    (setq resolved-resource-form
          (apiwrap-genform-resolve-api-params
              `(list ,@(mapcar (lambda (o) `(cons ',o ,o)) objects))
            internal-resource)
          form
          `(apply ,primitive-func ',method ,resolved-resource-form
                  (if (keywordp data)
                      (list ,(apiwrap--maybe-apply params-massage-func '(cons data params)) nil)
                    (list ,(apiwrap--maybe-apply params-massage-func 'params)
                          ,(apiwrap--maybe-apply data-massage-func 'data)))))

    (when around
      (unless (macrop around)
        (error ":around must be a macro: %S" around))
      (setq form (macroexpand `(,around ,form))))

    (let ((props `((prefix   . ,prefix)
                   (method   . ,method)
                   (endpoint . ,resource)
                   (link     . ,link)))
          fn-form)
      (push `(put ',funsym 'apiwrap ',props) fn-form)
      (push `(defun ,funsym ,args
               ,(apiwrap--docfn name doc (alist-get objects standard-parameters) method resource
                                (funcall link-func props))
               ,form)
            fn-form)
      (cons 'prog1 fn-form))))

(defmacro apiwrap-new-backend (name prefix standard-parameters &rest functions)
  "Define a new API backend.

SERVICE-NAME is the name of the service this backend will wrap.
It will be used in docstrings of the primitive method macros.

PREFIX is the prefix to use for the macros and for the
resource-wrapping functions.

STANDARD-PARAMETERS is an alist of standard parameters that can
be used to resolve resource URLs like `/users/:user/info'.  Each
key of the alist is the parameter name (as a symbol) and its
value is the documentation to insert in the docstring of
resource-wrapping functions.

FUNCTIONS is a list of arguments to configure the generated
macros.

  Required:

    :request

        API request primitive.  This function is expected to take
        the following required arguments:

          (METHOD RESOURCE PARAMS DATA)

        METHOD is provided as a symbol, one of `apiwrap-primitives',
        that specifies which HTTP method to use for the request.

        RESOURCE is the resource being accessed as a string.
        This will be passed through from each method macro after
        being resolved in the context of its parameters.  See the
        generated macro documentation (or `apiwrap--docmacro')
        for more details.

        PARAMS is provided as a property list of parameters.
        This will be passed in from each method function call.

        DATA is provided as an alist of data (e.g., for posting
        data to RESOURCE).  This will be passed in from each
        method function call.

  Optional:

    :link

        Function to process an alist and return a link.  This
        function should take an alist as its sole parameter and
        return a fully-qualified URL to be considered the
        official documentation of the API endpoint.

        This function is passed an alist with the following
        properties:

          endpoint  string  the documented endpoint being wrapped
          link      string  the link passed as documentation
          method    symbol  one of `get', `put', etc.
          prefix    string  the prefix used to generate wrappers

        The default is `apiwrap-stdgenlink'.

    :pre-process-params

        Function to process request parameters before the request
        is passed to the `:request' function.

    :pre-process-data

        Function to process request data before the request is
        passed to the `:request' function.

    :around

        Macro to wrap around the request form (which is passed as
        the only argument)."
  (declare (indent 2))
  (let ((sname (cl-gensym)) (sprefix (cl-gensym))
        (sstdp (cl-gensym)) (sfuncs (cl-gensym)))
    `(let ((,sname ,name)
           (,sprefix ,prefix)
           (,sstdp ,standard-parameters)
           (,sfuncs ',(mapcar (lambda (f) (cons (car f) (eval (cdr f))))
                              (apiwrap-plist->alist functions))))
       (mapc #'eval (apiwrap-genmacros ,sname ,sprefix ,sstdp ,sfuncs)))))

(provide 'apiwrap)
;;; apiwrap.el ends here
