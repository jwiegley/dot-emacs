;;; esxml-form.el --- HTML Forms with EmacsLisp  -*- lexical-binding: t -*-

;; Copyright (C) 2012  Nic Ferrier

;; Author: Nic Ferrier <nferrier@ferrier.me.uk>
;; Maintainer: Nic Ferrier <nferrier@ferrier.me.uk>
;; Keywords: data, lisp
;; Created: 23rd September 2012
;; Package-Requires: ((kv "0.0.7")(esxml "0.0.7")(db "0.0.1"))
;; Version: 0.0.1

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

;; This is an HTML Form processing library for ESXML. It ties together
;; the things in Lisp you need to make Forms work; like validation,
;; database validation and rendering.


;;; Code:

(require 'kv)
(require 'esxml)

(defconst esxml-form-field-defn
  '(name
    &key
    (type :regex) ; or :password, :email
    (regex ".+")
    ;; :html is one of :text :textarea :password
    ;; :checkbox :radio :select
    ;;
    ;; Further options should deal with the extra
    ;; data required by some of those types, for
    ;; example, :checkbox_selected could be used
    ;; for the checkbox
    (html :text)
    (check-failure "the content of the field was wrong")
    (type-check-failure "the content of the field was wrong")
    db-key
    db-check)
  "The Lisp definition used for a field.")

(defmacro* esxml-form ((&key db db-key) &rest field-args)
  "Make a field set.

A field set binds some field parameters together with some other
data, for example, a database."
  (declare (indent 0))
  (let ((fields (make-symbol "fieldsv")))
    `(let ((,fields
            (map-bind ;; FIXME optional fields?
             ,esxml-form-field-defn
             (list name
                   :type type
                   :regex regex
                   :check-failure check-failure
                   :type-check-failure type-check-failure
                   :html html
                   :db-check db-check
                   :db-key db-key)
             (quote ,field-args))))
       (list :db (quote ,db)
             :db-key (quote ,db-key)
             :fields ,fields))))

(defun esxml-form-fields (fs)
  (plist-get fs :fields))

(defun esxml-form-db (fs)
  (symbol-value (plist-get fs :db)))

(defun esxml-form-db-key (fs)
  (plist-get fs :db-key))

(defmacro esxml-form-bind (body form)
  "Bind BODY successively to FORMS fields."
  `(map-bind
    ,esxml-form-field-defn
    ,body
    (esxml-form-fields ,form)))


;; Verification stuff

(defconst esxml-form-field-set-email-verify-re
  (concat
   "[a-zA-Z0-9-]+@[a-zA-Z0-9.-]+"
   "\\.\\(com\\|net\\|org\\|gov\\|[A-Za-z]+\\.[A-Za-z]+\\)$"))

(defun esxml--field-check (field value &optional db query)
  "Do a validity check on the FIELD.

Return the type of validation failure or `nil' for no failure.

The tyoe of validation failure can be used as a key into the
field's `:check-failure' alist (if it is a list).  This means the
form can respond differently about database validation or other
types of validation."
  (let* ((field-type (plist-get field :type))
         (valid
          (case field-type
            (:regex
             (equal
              0
              (string-match
               (plist-get field :regex)
               (or value ""))))
            (:email
             (string-match esxml-form-field-set-email-verify-re value))
            (:password
             ;; really? is this a verification?
             t))))
    (if (and valid db query)
        (when (db-query db query) :db-check)
        (unless valid field-type))))

(defun* esxml-field-set-check (fs params
                                  &key
                                  onerror
                                  onsuccess)
  "Check field set FS against the PARAMS values.

Checks that ALL the required fields are there and that any field
that is there is correclty specified.

Returns the empty list when it passes and an alist of field-name,
field-value and validation error message if it fails."
  (flet ((subs-all (new old lst)
           (let ((l (lambda (e) (if (listp e) (subs-all new old e) e))))
             (substitute new old (mapcar l lst)))))
    (let* (last-check
           (db (esxml-form-db fs))
           (fields-set (esxml-form-fields fs))
           (errors
            (loop with field-value
               for (field-name . field-plist) in fields-set
               do
                 (setq field-value (cdr (kvassoqc field-name params)))
               when
                 (setq
                  last-check
                  (esxml--field-check
                   field-plist field-value
                   db (when db
                        (subs-all field-value '$
                                  (plist-get field-plist :db-check)))))
               collect (list ; return the error structure
                        field-name
                        field-value
                        (let ((check-msg
                               (plist-get field-plist :check-failure)))
                          (if (listp check-msg)
                              (car (aget check-msg last-check))
                              check-msg))))))
      (cond
        ((and errors (functionp onerror))
         (funcall onerror params errors))
        ((and (not errors) (functionp onsuccess))
         (funcall onsuccess params))
        (t errors)))))

(defun* esxml-field-set/label-style (&key
                                     html
                                     name
                                     value
                                     err)
  (esxml-label
   name
   nil
   (cons
    'div
    (cons
     '()
     (cons
      (case html
        (:text (esxml-input name "text" value))
        (:password (esxml-input name "password" value))
        (:checkbox (esxml-input name "checkbox" value))
        (:radio (esxml-input name "radio" value))
        ;;(:select (esxml-select (symbol-name name)))
        (:textarea (esxml-textarea name value)))
      (when err
        (list
         `(div
           ((class . "error"))
           ,(elt err 1)))))))))

(defun* esxml-field-set/bootstrap-style (&key
                                          html
                                          name
                                          value
                                          err)
  "Produce a field in twitter bootstrap style."
  `(div
    ((class . ,(concat
                "control-group"
                (when err " error"))))
    ,(esxml-label name '((class . "control-label")))
    (div
     ((class . "controls"))
     ,@(let ((ctrl
             (case html
               (:text (esxml-input name "text" value))
               (:password (esxml-input name "password" value))
               (:checkbox (esxml-input name "checkbox" value))
               (:radio (esxml-input name "radio" value))
               ;;(:select (esxml-select (symbol-name name)))
               (:textarea (esxml-textarea name (or value ""))))))
           (if err
               (list ctrl
                     `(span ((class . "help-inline"))
                            ,(elt err 1)))
               (list ctrl))))))

(defvar esxml-field-style :label
  "Style used for making form fields.")

(defun esxml-field-set->esxml (form &optional params errors style)
  "Fieldset of FORM to ESXML description of fields.

PARAMS, if supplied, is an ALIST of field-names -> value bindings
which are used to validate the fields and assigned to the
respective fields in the output.

The output is an ESXML representation of a form in label
style (an HTML LABEL element contains the controls).

If validation errors occur they are output as a DIV with class
\"error\", again, inside the LABEL.

STYLE, if specified is a either `:label' or `:bootstrap' to
indicate the style of form output used."
  (let ((form-style (or style esxml-field-style :label)))
    `(fieldset
      ()
      ,@(esxml-form-bind
         (let* ((symname (symbol-name name))
                (value (aget params symname))
                (err (aget errors name)))
           (funcall
            (case form-style
              (:label 'esxml-field-set/label-style)
              (:bootstrap 'esxml-field-set/bootstrap-style))
            :html html
            :name symname
            :value value
            :err err))
         form))))

(defun* esxml-form-save (form params
                              &key db-data)
  "Save the specified PARAMS in the FORM in the attached DB.

If DB-DATA is a function it is called to filter the data going
into the DB."
  (let ((db (esxml-form-db form))
        (db-key (esxml-form-db-key form)))
    (when (and db db-key)
      (let ((key-value (aget params db-key))
            (form-data
             (esxml-form-bind (assoc (symbol-name name) params) form)))
        (db-put key-value
                (if (functionp db-data)
                    (funcall db-data form-data)
                    form-data)
                db)))))


;;; This isn't right yet. needs to be more generic.
(defun esxml-form-handle (form httpcon page handler &optional extra-data)
  "Handle the FORM on the HTTPCON.

PAGE is the file you will send.

HANDLER is a function that takes the DATA from the POST that has
been validated by the FORM for saving it.

EXTRA-DATA is passed to the PAGE as extra `replacements'."
  (flet ((send (&optional data errors)
           (let ((esxml (esxml-field-set->esxml form data errors)))
             (elnode-send-file
              httpcon page
              :replacements `(("form" . ,(esxml-to-xml esxml))
                              ,@extra-data)))))
    (elnode-method httpcon
      (GET (send))
      (POST
       (esxml-field-set-check
        form (elnode-http-params httpcon)
        :onerror 'send
        :onsuccess handler)))))


(provide 'esxml-form)

;;; esxml-form.el ends here
