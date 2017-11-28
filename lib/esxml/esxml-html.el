;;; esxml-html.el --- HTML convenience functions for esxml
;; Copyright (C) 2012

;; Author: Evan Izaksonas-Smith <izak0002 at umn dot edu>
;; Maintainer: Evan Izaksonas-Smith
;; Created: 15th August 2012
;; Version: 0.3.0
;; Package-Requires: ((kv "0.0.5"))
;; Keywords: tools, lisp, comm
;; Description: esxml convenience functions for certain HTML elements
;;
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

;; This is a set of convenience functions for generating esxml for
;; certain HTML elements.
;;
;; NOTICE: Code base will be trasnitioning to using pcase instead of
;; destructuring bind wherever possible.  If this leads to hard to
;; debug code, please let me know, and I will do whatever I can to
;; resolve these issues.
;;
;;; Code:
(eval-when-compile
  (require 'cl))
(require 'esxml)
(require 'xml)
(require 'kv)
(require 'pcase)

(defun esxml-link (url &rest body)
  "Creates a standard hypereference link for HTML.

URL is the URL of the document, BODY is the body of the link."
  `(a ((href . ,url)) ,@body))

(defun esxml-label (label-text attribs &rest body)
  "Make a HTML <label> with LABEL-TEXT and ATTRIBS.

Optionally include the BODY."
  (let ((label-element
         `(label
           ,attribs
           (span () ,(concat label-text ": ")))))
    (if body
        (append label-element body)
        label-element)))

(defun esxml-input (name type &optional value)
  "Make an HTML <input> control.

VALUE is optional, if it's supplied whatever is supplied is used.
`nil' is the blank string."
  `(input ((name . ,name)
           (type . ,type)
           (placeholder . ,name)
           ,@(when value `((value . ,value))))))

(defun esxml-textarea (name &optional content)
  "Make an HTML <textarea> control."
  `(textarea ((name . ,name)
              (placeholder . ,name))
             ;; textareas require a body all the time
             ,@(if content (list content) "")))

(defun esxml-listify (bodys &optional ordered-p item-attrs)
  "Transforms a list of esxml body forms into an unordered HTML list.

BODYS is a list of esxml bodies.  If ORDERED-P is non-nil,
instead creates an ordered list.  If ITEM-ATTRS is non-nil it
specifies attributes to apply to each item.  ITEM-ATTRS must be
an alist satisfying `attrsp'."
  `(,(if ordered-p 'ol 'ul) ()
    ,@(kvmap-bind item
          `(li () ,@item)
        bodys)))

(defun esxml-head-base (url &optional target)
  "The HTML <base> element.

URL is the base url of the page, if non-nil.  TARGET is the base
target, if non-nil"
  `(base ,(remove nil
                  (list (when url `(href . ,url))
                        (when target `(target . ,target))))))

(defun esxml-head-link (relationship mime-type url &optional misc-attrs)
  "The HTML <link> element.
RELATIONSHIP is the relationship of the link, as a symbol
MIME_TYPE is the mime-type of the link as a string, URL is the
url of the link MISC-ATTRS is any additional attributes, as an
alist"
  `(link ((rel . ,(symbol-name relationship))
          (type . ,mime-type)
          (href . ,url)
          ,@misc-attrs)))

(defun esxml-head-css-link (url)
  "The HTML <link> element for CSS.

As this is a common usage this conveniance function for
`esxml-head-link' for linking to stylesheets.  URL is the
location of the CSS."
  (esxml-head-link 'stylesheet "text/css" url))

(defun esxml-head-meta (directive content &optional http-equiv)
  "The META element.  Only supports content and either http-equiv
or name.

DIRECTIVE is a symbol that supplied to name unless HTTP-EQUIV is non-nil, in
which case it the value of http-equiv.
Content is the content

Example:
> (esxml-head-meta 'keyword \"cool, awesome, unignorable\")
  (meta ((name . \"keyword\")
         (content . \"cool, awesome, unignorable\")))

> (esxml-head-meta 'content-type \"text/html\" t)
  (meta ((http-equiv . \"content-type\")
         (content . \"text/html\")))"
  `(meta ((,(if http-equiv 'http-equiv 'name) . ,(symbol-name directive))
          (content . ,content))))

(defun esxml-head-script (url &optional script)
  "A presumptious version of the HTML head script element.

You always use js, right?  Good.  Now that that's settled...

URL is the URL of the script, if for some reason you want to
include a script in the file, set this to nil.

SCRIPT is the script as a string.  Will not be used if URL is non-nil"
  `(script (,@(when url `((src . ,url)))
            (type . "text/javascript"))
           ,@(unless url (list script))))

(defun esxml-head-style (css)
  "The HTML <style> <head> element.

The argument CSS is a string containing valid CSS."
  `(style ((type . "text/css"))
          ,css))

(defun esxml--head (title &rest body)
  `(head ()
         (title () ,title)
         ,@body))

(defmacro esxml-head (title &rest body)
  "DSL for writing the HEAD element of HTML.
Required argument TITLE is the title of the page as a string.
Within the BODY the following functions are aliased:

 base     `esxml-head-base'
 link     `esxml-head-link'
 css-link `esxml-head-css-link'
 meta     `esxml-head-meta'
 script   `esxml-head-script'
 style    `esxml-head-style'

Additionally, one may also include arbitrary esxml (and
esxml-generation), within BODY.

e.g.
 (esxml-head \"Title Text\"
   (base \"http://this.url/resources/\")
   (css-link \"some.css\")
   (meta 'keyword \"cool, awesome, unignorable\")
   (meta 'content-type \"text/html\" t)
   (script \"example-script.js\"))"
  (declare (indent 1))
  `(letf ,(kvmap-bind (symbol value)
              `((symbol-function ',symbol) ,value)
            '((base 'esxml-head-base)
              (link 'esxml-head-link)
              (css-link 'esxml-head-css-link)
              (meta 'esxml-head-meta)
              (script 'esxml-head-script)
              (style 'esxml-head-style)))
     (esxml--head ,title ,@body)))

;;; Some generators for common problems
;; Tabular and listed data are common patterns, so rather than do
;; something like:
;; (esxml-to-xml
;;  `(html ()
;;         (body ()
;;               ,@(mapcar (lambda (url-entry)
;;                           (destructuring-bind (url name)
;;                               `(li ()
;;                                    (a ((href . ,url))
;;                                       ,name))))))))
;; we should instead define this cleanly.

(defun esxml-create-bookmark-list (bookmark-list seperator &optional ordered-p)
"Example:
  (setq bookmark-list
        '((\"http://www.emacswiki.org\" \"Emacs Wiki\" \"Accept no substitutes\")
          (\"http://www.github.com/\" \"Github\")
          (\"http://www.google.com\" \"Google\" \"Everyones favorite search engine\")))

  (esxml-to-xml (esxml-create-bookmark-list bookmark-list \": \"))"
  (esxml-listify (kvmap-bind (url name &optional description)
                           `(,(esxml-link url name)
                             ,@(when description
                                 `(,seperator ,description)))
                           bookmark-list)
                 ordered-p))
Example
(setq bookmark-list
      '(("http://www.emacswiki.org" "Emacs Wiki" "Accept no substitutes")
        ("http://www.github.com/" "Github")
        ("http://www.google.com" "Google" "Everyones favorite search engine")))

(esxml-to-xml (esxml-create-bookmark-list bookmark-list ": "))

;; hint, at this point it may be wise to consider breaking this out as
;; a seperate web library.



(provide 'esxml-html)
;;; esxml-html.el ends here
