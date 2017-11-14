;;; zencoding-mode.el --- Unfold CSS-selector-like expressions to markup

;; Copyright (C) 2009, Chris Done

;; Version: 0.5.1
;; Author: Chris Done <chrisdone@gmail.com>
;; URL: https://github.com/rooney/zencoding
;; Last-Updated: 2011-12-31 Sat
;; Keywords: convenience

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.
;;
;; This file is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Commentary:
;;
;; Unfold CSS-selector-like expressions to markup. Intended to be used
;; with sgml-like languages; xml, html, xhtml, xsl, etc.
;;
;; See `zencoding-mode' for more information.
;;
;; Copy zencoding-mode.el to your load-path and add to your .emacs:
;;
;;    (require 'zencoding-mode)
;;
;; Example setup:
;;
;;    (add-to-list 'load-path "~/Emacs/zencoding/")
;;    (require 'zencoding-mode)
;;    (add-hook 'sgml-mode-hook 'zencoding-mode) ;; Auto-start on any markup modes
;;
;; Enable the minor mode with M-x zencoding-mode.
;;
;; See ``Test cases'' section for a complete set of expression types.
;;
;; If you are hacking on this project, eval (zencoding-test-cases) to
;; ensure that your changes have not broken anything. Feel free to add
;; new test cases if you add new features.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; History:
;;
;; Modified by Lennart Borgman.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Code:

(defconst zencoding-mode:version "0.5.1")

;; Include the trie data structure for caching
;(require 'zencoding-trie)

(require 'cl)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Generic parsing macros and utilities

(defmacro zencoding-aif (test-form then-form &rest else-forms)
  "Anaphoric if. Temporary variable `it' is the result of test-form."
  `(let ((it ,test-form))
     (if it ,then-form ,@(or else-forms '(it)))))

(defmacro zencoding-pif (test-form then-form &rest else-forms)
  "Parser anaphoric if. Temporary variable `it' is the result of test-form."
  `(let ((it ,test-form))
     (if (not (eq 'error (car it))) ,then-form ,@(or else-forms '(it)))))

(defmacro zencoding-parse (regex nums label &rest body)
  "Parse according to a regex and update the `input' variable."
  `(zencoding-aif (zencoding-regex ,regex input ',(number-sequence 0 nums))
                  (let ((input (elt it ,nums)))
                    ,@body)
                  `,`(error ,(concat "expected " ,label))))

(defmacro zencoding-run (parser then-form &rest else-forms)
  "Run a parser and update the input properly, extract the parsed
   expression."
  `(zencoding-pif (,parser input)
                  (let ((input (cdr it))
                        (expr (car it)))
                    ,then-form)
                  ,@(or else-forms '(it))))

(defmacro zencoding-por (parser1 parser2 then-form &rest else-forms)
  "OR two parsers. Try one parser, if it fails try the next."
  `(zencoding-pif (,parser1 input)
                  (let ((input (cdr it))
                        (expr (car it)))
                    ,then-form)
                  (zencoding-pif (,parser2 input)
                                 (let ((input (cdr it))
                                       (expr (car it)))
                                   ,then-form)
                                 ,@else-forms)))

(defun zencoding-regex (regexp string refs)
  "Return a list of (`ref') matches for a `regex' on a `string' or nil."
  (if (string-match (concat "^" regexp "\\([^\n]*\\)$") string)
      (mapcar (lambda (ref) (match-string ref string))
              (if (sequencep refs) refs (list refs)))
    nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Zen coding parsers

(defun zencoding-expr (input)
  "Parse a zen coding expression with optional filters."
  (zencoding-pif (zencoding-parse "\\(.*?\\)|" 2 "expr|filter" it)
                 (let ((input (elt it 1))
                       (filters (elt it 2)))
                   (zencoding-pif (zencoding-extract-filters filters)
                                  (zencoding-filter input it)
                                  it))
                 (zencoding-filter input (zencoding-default-filter))))

(defun zencoding-subexpr (input)
  "Parse a zen coding expression with no filter. This pretty much defines precedence."
  (zencoding-run zencoding-siblings
                 it
                 (zencoding-run zencoding-parent-child
                                it
                                (zencoding-run zencoding-multiplier
                                               it
                                               (zencoding-run zencoding-pexpr
                                                              it
                                                              (zencoding-run zencoding-tag
                                                                             it
                                                                             '(error "no match, expecting ( or a-zA-Z0-9")))))))

(defun zencoding-extract-filters (input)
  "Extract filters from expression."
  (zencoding-pif (zencoding-parse "\\([^\\|]+?\\)|" 2 "" it)
                 (let ((filter-name (elt it 1))
                       (more-filters (elt it 2)))
                   (zencoding-pif (zencoding-extract-filters more-filters)
                                  (cons filter-name it)
                                  it))
                 (zencoding-parse "\\([^\\|]+\\)" 1 "filter name" `(,(elt it 1)))))

(defun zencoding-filter (input filters)
  "Construct AST with specified filters."
  (zencoding-pif (zencoding-subexpr input)
                 (let ((result (car it))
                       (rest (cdr it)))
                   `((filter ,filters ,result) . ,rest))
                 it))

(defun zencoding-default-filter ()
  "Default filter(s) to be used if none is specified."
  (let* ((file-ext (car (zencoding-regex ".*\\(\\..*\\)" (or (buffer-file-name) "") 1)))
         (defaults '(".html" ("html")
                     ".htm"  ("html")
                     ".haml" ("haml")
                     ".clj"  ("hic")))
         (default-else      '("html"))
         (selected-default (member file-ext defaults)))
    (if selected-default
        (cadr selected-default)
      default-else)))

(defun zencoding-multiplier (input)
  (zencoding-por zencoding-pexpr zencoding-tag
                 (let ((multiplier expr))
                   (zencoding-parse "\\*\\([0-9]+\\)" 2 "*n where n is a number"
                                    (let ((multiplicand (read (elt it 1))))
                                      `((list ,(make-list multiplicand multiplier)) . ,input))))
                 '(error "expected *n multiplier")))

(defun zencoding-tag (input)
  "Parse a tag."
  (zencoding-run zencoding-tagname
                 (let ((tagname (cadr expr))
                       (has-body? (cddr expr)))
                   (zencoding-pif (zencoding-run zencoding-identifier
                                                 (zencoding-tag-classes
                                                  `(tag (,tagname ,has-body? ,(cddr expr))) input)
                                                 (zencoding-tag-classes
                                                  `(tag (,tagname ,has-body? nil)) input))
                                  (let ((expr (car it))
                                        (input (cdr it)))
                                    (zencoding-tag-props expr input))))
                 (zencoding-default-tag input)))

(defun zencoding-default-tag (input)
  "Parse a #id or .class"
  (zencoding-parse "\\([#|\\.]\\)" 1 "tagname"
                   (zencoding-tag (concat "div" (elt it 0)))))

(defun zencoding-tag-props (tag input)
  (let ((tag-data (cadr tag)))
    (zencoding-run zencoding-props
                   (let ((props (cdr expr)))
                     `((tag ,(append tag-data (list props))) . ,input))
                   `((tag ,(append tag-data '(nil))) . ,input))))

(defun zencoding-props (input)
  "Parse many props."
    (zencoding-run zencoding-prop
                   (zencoding-pif (zencoding-props input)
                                  `((props . ,(cons expr (cdar it))) . ,(cdr it))
                                  `((props . ,(list expr)) . ,input))))

(defun zencoding-prop (input)
  (zencoding-parse
   " " 1 "space"
   (zencoding-run
    zencoding-name
    (let ((name (cdr expr)))
      (zencoding-pif (zencoding-prop-value name input)
                     it
                     `((,(read name) "") . ,input))))))

(defun zencoding-prop-value (name input)
  (zencoding-pif (zencoding-parse "=\"\\(.*?\\)\"" 2
                                  "=\"property value\""
                                  (let ((value (elt it 1))
                                        (input (elt it 2)))
                                    `((,(read name) ,value) . ,input)))
                 it
                 (zencoding-parse "=\\([^\\,\\+\\>\\ )]*\\)" 2
                                  "=property value"
                                  (let ((value (elt it 1))
                                        (input (elt it 2)))
                                    `((,(read name) ,value) . ,input)))))

(defun zencoding-tag-classes (tag input)
  (let ((tag-data (cadr tag)))
    (zencoding-run zencoding-classes
                   (let ((classes (mapcar (lambda (cls) (cdadr cls))
                                          (cdr expr))))
                     `((tag ,(append tag-data (list classes))) . ,input))
                   `((tag ,(append tag-data '(nil))) . ,input))))

(defun zencoding-tagname (input)
  "Parse a tagname a-zA-Z0-9 tagname (e.g. html/head/xsl:if/br)."
  (zencoding-parse "\\([a-zA-Z][a-zA-Z0-9:-]*\/?\\)" 2 "tagname, a-zA-Z0-9"
                   (let* ((tag-spec (elt it 1))
                          (empty-tag (zencoding-regex "\\([^\/]*\\)\/" tag-spec 1))
                          (tag (if empty-tag
                                   (car empty-tag)
                                 tag-spec)))
                     `((tagname . (,tag . ,(not empty-tag))) . ,input))))

(defun zencoding-pexpr (input)
  "A zen coding expression with parentheses around it."
  (zencoding-parse "(" 1 "("
                   (zencoding-run zencoding-subexpr
                                  (zencoding-aif (zencoding-regex ")" input '(0 1))
                                                 `(,expr . ,(elt it 1))
                                                 '(error "expecting `)'")))))

(defun zencoding-parent-child (input)
  "Parse an tag>e expression, where `n' is an tag and `e' is any
   expression."
  (zencoding-run zencoding-multiplier
                 (let* ((items (cadr expr))
                        (rest (zencoding-child-sans expr input)))
                   (if (not (eq (car rest) 'error))
                       (let ((child (car rest))
                             (input (cdr rest)))
                         (cons (cons 'list
                                     (cons (mapcar (lambda (parent)
                                                     `(parent-child ,parent ,child))
                                                   items)
                                           nil))
                               input))
                     '(error "expected child")))
                 (zencoding-run zencoding-tag
                                (zencoding-child expr input)
                                '(error "expected parent"))))

(defun zencoding-child-sans (parent input)
  (zencoding-parse ">" 1 ">"
                   (zencoding-run zencoding-subexpr
                                  it
                                  '(error "expected child"))))

(defun zencoding-child (parent input)
  (zencoding-parse ">" 1 ">"
                   (zencoding-run zencoding-subexpr
                                  (let ((child expr))
                                    `((parent-child ,parent ,child) . ,input))
                                  '(error "expected child"))))

(defun zencoding-sibling (input)
  (zencoding-por zencoding-pexpr zencoding-multiplier
                 it
                 (zencoding-run zencoding-tag
                                it
                                '(error "expected sibling"))))

(defun zencoding-siblings (input)
  "Parse an e+e expression, where e is an tag or a pexpr."
  (zencoding-run zencoding-sibling
                 (let ((parent expr))
                   (zencoding-parse "\\+" 1 "+"
                                    (zencoding-run zencoding-subexpr
                                                   (let ((child expr))
                                                     `((sibling ,parent ,child) . ,input))
                                                   (zencoding-expand parent input))))
                 '(error "expected first sibling")))

(defvar zencoding-expandable-tags
  '("dl"    ">(dt+dd)"
    "ol"    ">li"
    "ul"    ">li"
    "table" ">tr>td"))

(defun zencoding-expand (parent input)
  "Parse an e+ expression, where e is an expandable tag"
  (let* ((parent-tag (car (elt parent 1)))
         (expandable (member parent-tag zencoding-expandable-tags)))
    (if expandable
        (let ((expansion (zencoding-child parent (concat (cadr expandable)))))
          (zencoding-pif (zencoding-parse "+\\(.*\\)" 1 "+expr"
                                          (zencoding-subexpr (elt it 1)))
                         `((sibling ,(car expansion) ,(car it)))
                         expansion))
      '(error "expected second sibling"))))

(defun zencoding-name (input)
  "Parse a class or identifier name, e.g. news, footer, mainimage"
  (zencoding-parse "\\([a-zA-Z][a-zA-Z0-9-_:]*\\)" 2 "class or identifer name"
                   `((name . ,(elt it 1)) . ,input)))

(defun zencoding-class (input)
  "Parse a classname expression, e.g. .foo"
  (zencoding-parse "\\." 1 "."
                   (zencoding-run zencoding-name
                                  `((class ,expr) . ,input)
                                  '(error "expected class name"))))
(defun zencoding-identifier (input)
  "Parse an identifier expression, e.g. #foo"
  (zencoding-parse "#" 1 "#"
                   (zencoding-run zencoding-name
                                  `((identifier . ,expr) . ,input))))

(defun zencoding-classes (input)
  "Parse many classes."
  (zencoding-run zencoding-class
                 (zencoding-pif (zencoding-classes input)
                                `((classes . ,(cons expr (cdar it))) . ,(cdr it))
                                `((classes . ,(list expr)) . ,input))
                 '(error "expected class")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Zen coding transformer from AST to string

(defvar zencoding-inline-tags
  '("a"
    "abbr"
    "acronym"
    "cite"
    "code"
    "dd"
    "dfn"
    "dt"
    "em"
    "h1" "h2" "h3" "h4" "h5" "h6"
    "kbd"
    "li"
    "q"
    "span"
    "strong"
    "var"))

(defvar zencoding-block-tags
  '("p"))

(defvar zencoding-self-closing-tags
  '("br"
    "img"
    "input"))

(defvar zencoding-leaf-function nil
  "Function to execute when expanding a leaf node in the
  Zencoding AST.")

(defvar zencoding-filters
  '("html" (zencoding-primary-filter zencoding-make-html-tag)
    "c"    (zencoding-primary-filter zencoding-make-commented-html-tag)
    "haml" (zencoding-primary-filter zencoding-make-haml-tag)
    "hic"  (zencoding-primary-filter zencoding-make-hiccup-tag)
    "e"    (zencoding-escape-xml)))

(defun zencoding-primary-filter (input proc)
  "Process filter that needs to be executed first, ie. not given output from other filter."
  (if (listp input)
      (let ((tag-maker (cadr proc)))
        (zencoding-transform-ast input tag-maker))
    nil))

(defun zencoding-process-filter (filters input)
  "Process filters, chain one filter output as the input of the next filter."
  (let ((filter-data (member (car filters) zencoding-filters))
        (more-filters (cdr filters)))
    (if filter-data
        (let* ((proc   (cadr filter-data))
               (fun    (car proc))
               (filter-output (funcall fun input proc)))
          (if more-filters
              (zencoding-process-filter more-filters filter-output)
            filter-output))
      nil)))

(defun zencoding-make-tag (tag-maker tag-info &optional content)
  "Extract tag info and pass them to tag-maker."
  (let* ((name      (pop tag-info))
         (has-body? (pop tag-info))
         (id        (pop tag-info))
         (classes   (pop tag-info))
         (props     (pop tag-info))
         (self-closing? (not (or content
                                 (and has-body?
                                      (not (member name zencoding-self-closing-tags)))))))
    (funcall tag-maker name id classes props self-closing?
             (if content content
               (if zencoding-leaf-function (funcall zencoding-leaf-function))))))

(defun zencoding-make-html-tag (tag-name tag-id tag-classes tag-props self-closing? content)
  "Create HTML markup string"
  (let* ((id      (zencoding-concat-or-empty " id=\"" tag-id "\""))
         (classes (zencoding-mapconcat-or-empty " class=\"" tag-classes " " "\""))
         (props   (zencoding-mapconcat-or-empty " " tag-props " " nil
                                                (lambda (prop)
                                                  (concat (symbol-name (car prop)) "=\"" (cadr prop) "\""))))
         (content-multiline? (and content (string-match "\n" content)))
         (block-tag? (or (member tag-name zencoding-block-tags)
                         (and (> (length tag-name) 1)
                              (not (member tag-name zencoding-inline-tags)))))
         (lf (if (or content-multiline? block-tag?)
                 "\n")))
    (concat "<" tag-name id classes props (if self-closing?
                                              "/>"
                                            (concat ">" (if content
                                                            (if (or content-multiline? block-tag?)
                                                                (zencoding-indent content)
                                                              content))
                                                    lf
                                                    "</" tag-name ">")))))

(defun zencoding-make-commented-html-tag (tag-name tag-id tag-classes tag-props self-closing? content)
  "Create HTML markup string with extra comments for elements with #id or .classes"
  (let ((body (zencoding-make-html-tag tag-name tag-id tag-classes tag-props self-closing? content)))
    (if (or tag-id tag-classes)
        (let ((id      (zencoding-concat-or-empty "#" tag-id))
              (classes (zencoding-mapconcat-or-empty "." tag-classes ".")))
          (concat "<!-- " id classes " -->\n"
                  body
                  "\n<!-- /" id classes " -->"))
      body)))

(defun zencoding-make-haml-tag (tag-name tag-id tag-classes tag-props self-closing? content)
  "Create HAML string"
  (let ((name    (if (and (equal tag-name "div")
                          (or tag-id tag-classes))
                     ""
                   (concat "%" tag-name)))
        (id      (zencoding-concat-or-empty "#" tag-id))
        (classes (zencoding-mapconcat-or-empty "." tag-classes "."))
        (props   (zencoding-mapconcat-or-empty "{" tag-props ", " "}"
                                               (lambda (prop)
                                                 (concat ":" (symbol-name (car prop)) " => \"" (cadr prop) "\"")))))
    (concat name id classes props (if content
                                      (zencoding-indent content)))))

(defun zencoding-make-hiccup-tag (tag-name tag-id tag-classes tag-props self-closing? content)
  "Create Hiccup string"
  (let* ((id      (zencoding-concat-or-empty "#" tag-id))
         (classes (zencoding-mapconcat-or-empty "." tag-classes "."))
         (props   (zencoding-mapconcat-or-empty " {" tag-props ", " "}"
                                                (lambda (prop)
                                                  (concat ":" (symbol-name (car prop)) " \"" (cadr prop) "\""))))
         (content-multiline? (and content (string-match "\n" content)))
         (block-tag? (or (member tag-name zencoding-block-tags)
                         (and (> (length tag-name) 1)
                              (not (member tag-name zencoding-inline-tags))))))
    (concat "[:" tag-name id classes props
            (if content
                (if (or content-multiline? block-tag?)
                    (zencoding-indent content)
                  (concat " " content)))
            "]")))

(defun zencoding-concat-or-empty (prefix body &optional suffix)
  "Return prefixed suffixed text or empty string."
  (if body
      (concat prefix body suffix)
    ""))

(defun zencoding-mapconcat-or-empty (prefix list-body delimiter &optional suffix map-fun)
  "Return prefixed suffixed mapconcated text or empty string."
  (if list-body
      (let* ((mapper (if map-fun map-fun 'identity))
             (body (mapconcat mapper list-body delimiter)))
        (concat prefix body suffix))
    ""))

(defun zencoding-escape-xml (input proc)
  "Escapes XML-unsafe characters: <, > and &."
  (replace-regexp-in-string
   "<" "&lt;"
   (replace-regexp-in-string
    ">" "&gt;"
    (replace-regexp-in-string
     "&" "&amp;"
     (if (stringp input)
         input
       (zencoding-process-filter (zencoding-default-filter) input))))))

(defun zencoding-transform (ast-with-filters)
  "Transform AST (containing filter data) into string."
  (let ((filters (cadr ast-with-filters))
        (ast (caddr ast-with-filters)))
    (zencoding-process-filter filters ast)))

(defun zencoding-transform-ast (ast tag-maker)
  "Transform AST (without filter data) into string."
  (let ((type (car ast)))
    (cond
     ((eq type 'list)
      (mapconcat (lexical-let ((make-tag-fun tag-maker))
                   #'(lambda (sub-ast)
                       (zencoding-transform-ast sub-ast make-tag-fun)))
                 (cadr ast)
                 "\n"))
     ((eq type 'tag)
      (zencoding-make-tag tag-maker (cadr ast)))
     ((eq type 'parent-child)
      (let ((parent (cadadr ast))
            (children (zencoding-transform-ast (caddr ast) tag-maker)))
        (zencoding-make-tag tag-maker parent children)))
     ((eq type 'sibling)
      (let ((sib1 (zencoding-transform-ast (cadr ast) tag-maker))
            (sib2 (zencoding-transform-ast (caddr ast) tag-maker)))
        (concat sib1 "\n" sib2))))))

(defun zencoding-indent-size ()
  "Calculate indent size using current mode as a guidance"
  (let ((mode (with-current-buffer (current-buffer) major-mode)))
    (cond
     ((string= mode "nxml-mode") nxml-child-indent)
     ((string= mode "html-mode") sgml-basic-offset)
     ((string= mode "sgml-mode") sgml-basic-offset)
     (t 4)
     ))
  )

(defun zencoding-indent (text)
  "Indent the text"
  (if text
      (replace-regexp-in-string
       "\n"
       (concat
        "\n"
        (make-string (zencoding-indent-size) ?\ ))
       (concat "\n" text))
    nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Test-cases

(defun zencoding-test-cases ()
  (let ((tests '(;; Tags
                 ("a"                      "<a></a>")
                 ("a.x"                    "<a class=\"x\"></a>")
                 ("a#q.x"                  "<a id=\"q\" class=\"x\"></a>")
                 ("a#q.x.y.z"              "<a id=\"q\" class=\"x y z\"></a>")
                 ("#q"                     "<div id=\"q\">"
                                           "</div>")
                 (".x"                     "<div class=\"x\">"
                                           "</div>")
                 ("#q.x"                   "<div id=\"q\" class=\"x\">"
                                           "</div>")
                 ("#q.x.y.z"               "<div id=\"q\" class=\"x y z\">"
                                           "</div>")
                 ;; Empty tags
                 ("a/"                     "<a/>")
                 ("a/.x"                   "<a class=\"x\"/>")
                 ("a/#q.x"                 "<a id=\"q\" class=\"x\"/>")
                 ("a/#q.x.y.z"             "<a id=\"q\" class=\"x y z\"/>")
                 ;; Self-closing tags
                 ("input type=text"        "<input type=\"text\"/>")
                 ("img"                    "<img/>")
                 ("img>metadata/*2"        "<img>"
                                           "    <metadata/>"
                                           "    <metadata/>"
                                           "</img>")
                 ;; Siblings
                 ("a+b"                    "<a></a>"
                                           "<b></b>")
                 ("a+b+c"                  "<a></a>"
                                           "<b></b>"
                                           "<c></c>")
                 ("a.x+b"                  "<a class=\"x\"></a>"
                                           "<b></b>")
                 ("a#q.x+b"                "<a id=\"q\" class=\"x\"></a>"
                                           "<b></b>")
                 ("a#q.x.y.z+b"            "<a id=\"q\" class=\"x y z\"></a>"
                                           "<b></b>")
                 ("a#q.x.y.z+b#p.l.m.n"    "<a id=\"q\" class=\"x y z\"></a>"
                                           "<b id=\"p\" class=\"l m n\"></b>")
                 ;; Tag expansion
                 ("table+"                 "<table>"
                                           "    <tr>"
                                           "        <td>"
                                           "        </td>"
                                           "    </tr>"
                                           "</table>")
                 ("dl+"                    "<dl>"
                                           "    <dt></dt>"
                                           "    <dd></dd>"
                                           "</dl>")
                 ("ul+"                    "<ul>"
                                           "    <li></li>"
                                           "</ul>")
                 ("ul++ol+"                "<ul>"
                                           "    <li></li>"
                                           "</ul>"
                                           "<ol>"
                                           "    <li></li>"
                                           "</ol>")
                 ("ul#q.x.y m=l+"          "<ul id=\"q\" class=\"x y\" m=\"l\">"
                                           "    <li></li>"
                                           "</ul>")
                 ;; Parent > child
                 ("a>b"                    "<a><b></b></a>")
                 ("a>b>c"                  "<a><b><c></c></b></a>")
                 ("a.x>b"                  "<a class=\"x\"><b></b></a>")
                 ("a#q.x>b"                "<a id=\"q\" class=\"x\"><b></b></a>")
                 ("a#q.x.y.z>b"            "<a id=\"q\" class=\"x y z\"><b></b></a>")
                 ("a#q.x.y.z>b#p.l.m.n"    "<a id=\"q\" class=\"x y z\"><b id=\"p\" class=\"l m n\"></b></a>")
                 ("#q>.x"                  "<div id=\"q\">"
                                           "    <div class=\"x\">"
                                           "    </div>"
                                           "</div>")
                 ("a>b+c"                  "<a>"
                                           "    <b></b>"
                                           "    <c></c>"
                                           "</a>")
                 ("a>b+c>d"                "<a>"
                                           "    <b></b>"
                                           "    <c><d></d></c>"
                                           "</a>")
                 ;; Multiplication
                 ("a*1"                    "<a></a>")
                 ("a*2"                    "<a></a>"
                                           "<a></a>")
                 ("a/*2"                   "<a/>"
                                           "<a/>")
                 ("a*2+b*2"                "<a></a>"
                                           "<a></a>"
                                           "<b></b>"
                                           "<b></b>")
                 ("a*2>b*2"                "<a>"
                                           "    <b></b>"
                                           "    <b></b>"
                                           "</a>"
                                           "<a>"
                                           "    <b></b>"
                                           "    <b></b>"
                                           "</a>")
                 ("a>b*2"                  "<a>"
                                           "    <b></b>"
                                           "    <b></b>"
                                           "</a>")
                 ("a#q.x>b#q.x*2"          "<a id=\"q\" class=\"x\">"
                                           "    <b id=\"q\" class=\"x\"></b>"
                                           "    <b id=\"q\" class=\"x\"></b>"
                                           "</a>")
                 ("a#q.x>b/#q.x*2"         "<a id=\"q\" class=\"x\">"
                                           "    <b id=\"q\" class=\"x\"/>"
                                           "    <b id=\"q\" class=\"x\"/>"
                                           "</a>")
                 ;; Properties
                 ("a x"                    "<a x=\"\"></a>")
                 ("a x="                   "<a x=\"\"></a>")
                 ("a x=\"\""               "<a x=\"\"></a>")
                 ("a x=y"                  "<a x=\"y\"></a>")
                 ("a x=\"y\""              "<a x=\"y\"></a>")
                 ("a x=\"()\""             "<a x=\"()\"></a>")
                 ("a x m"                  "<a x=\"\" m=\"\"></a>")
                 ("a x= m=\"\""            "<a x=\"\" m=\"\"></a>")
                 ("a x=y m=l"              "<a x=\"y\" m=\"l\"></a>")
                 ("a/ x=y m=l"             "<a x=\"y\" m=\"l\"/>")
                 ("a#foo x=y m=l"          "<a id=\"foo\" x=\"y\" m=\"l\"></a>")
                 ("a.foo x=y m=l"          "<a class=\"foo\" x=\"y\" m=\"l\"></a>")
                 ("a#foo.bar.mu x=y m=l"   "<a id=\"foo\" class=\"bar mu\" x=\"y\" m=\"l\"></a>")
                 ("a/#foo.bar.mu x=y m=l"  "<a id=\"foo\" class=\"bar mu\" x=\"y\" m=\"l\"/>")
                 ("a x=y+b"                "<a x=\"y\"></a>"
                                           "<b></b>")
                 ("a x=y+b x=y"            "<a x=\"y\"></a>"
                                           "<b x=\"y\"></b>")
                 ("a x=y>b"                "<a x=\"y\"><b></b></a>")
                 ("a x=y>b x=y"            "<a x=\"y\"><b x=\"y\"></b></a>")
                 ("a x=y>b x=y+c x=y"      "<a x=\"y\">"
                                           "    <b x=\"y\"></b>"
                                           "    <c x=\"y\"></c>"
                                           "</a>")
                 ;; Parentheses
                 ("(a)"                    "<a></a>")
                 ("(a)+(b)"                "<a></a>"
                                           "<b></b>")
                 ("a>(b)"                  "<a><b></b></a>")
                 ("(a>b)>c"                "<a><b></b></a>")
                 ("(a>b)+c"                "<a><b></b></a>"
                                           "<c></c>")
                 ("z+(a>b)+c+k"            "<z></z>"
                                           "<a><b></b></a>"
                                           "<c></c>"
                                           "<k></k>")
                 ("(a)*2"                  "<a></a>"
                                           "<a></a>")
                 ("((a)*2)"                "<a></a>"
                                           "<a></a>")
                 ("((a))*2"                "<a></a>"
                                           "<a></a>")
                 ("(a>b)*2"                "<a><b></b></a>"
                                           "<a><b></b></a>")
                 ("(a+b)*2"                "<a></a>"
                                           "<b></b>"
                                           "<a></a>"
                                           "<b></b>")
                 ;; Filter: comment
                 ("a.b|c"                  "<!-- .b -->"
                                           "<a class=\"b\"></a>"
                                           "<!-- /.b -->")
                 ("#a>.b|c"                "<!-- #a -->"
                                           "<div id=\"a\">"
                                           "    <!-- .b -->"
                                           "    <div class=\"b\">"
                                           "    </div>"
                                           "    <!-- /.b -->"
                                           "</div>"
                                           "<!-- /#a -->")
                 ;; Filter: HAML
                 ("a|haml"                 "%a")
                 ("a#q.x.y.z|haml"         "%a#q.x.y.z")
                 ("a#q.x x=y m=l|haml"     "%a#q.x{:x => \"y\", :m => \"l\"}")
                 ("div|haml"               "%div")
                 ("div.footer|haml"        ".footer")
                 (".footer|haml"           ".footer")
                 ("p>a href=#+br|haml"     "%p"
                                           "    %a{:href => \"#\"}"
                                           "    %br")
                 ;; Filter: Hiccup
                 ("a|hic"                  "[:a]")
                 ("a#q.x.y.z|hic"          "[:a#q.x.y.z]")
                 ("a#q.x x=y m=l|hic"      "[:a#q.x {:x \"y\", :m \"l\"}]")
                 (".footer|hic"            "[:div.footer]")
                 ("p>a href=#+br|hic"      "[:p"
                                           "    [:a {:href \"#\"}]"
                                           "    [:br]]")
                 ("#q>(a*2>b)+p>b|hic"     "[:div#q"
                                           "    [:a [:b]]"
                                           "    [:a [:b]]"
                                           "    [:p"
                                           "        [:b]]]")
                 ;; Filter: escape
                 ("script src=&quot;|e"    "&lt;script src=\"&amp;quot;\"&gt;"
                                           "&lt;/script&gt;")
                 )))
    (mapc (lambda (input)
            (let ((expected (mapconcat 'identity (cdr input) "\n"))
                  (actual (zencoding-transform (car (zencoding-expr (car input))))))
              (if (not (equal expected actual))
                  (error (concat "Assertion " (car input) " failed:"
                                 expected
                                 " == "
                                 actual)))))
            tests)
    (concat (number-to-string (length tests)) " tests performed. All OK.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Zencoding minor mode

(defgroup zencoding nil
  "Customization group for zencoding-mode."
  :group 'convenience)

(defun zencoding-expr-on-line ()
  "Extract a zencoding expression and the corresponding bounds
   for the current line."
  (let* ((start (line-beginning-position))
         (end (line-end-position))
         (line (buffer-substring-no-properties start end))
         (expr (zencoding-regex "\\([ \t]*\\)\\([^\n]+\\)" line 2)))
    (if (first expr)
        (list (first expr) start end))))

(defcustom zencoding-indentation 4
  "Number of spaces used for indentation."
  :type '(number :tag "Spaces")
  :group 'zencoding)

(defun zencoding-prettify (markup indent)
  (let ((first-col (format (format "%%%ds" indent) ""))
        (tab       (format (format "%%%ds" zencoding-indentation) "")))
    (concat first-col
            (replace-regexp-in-string "\n" (concat "\n" first-col)
                                      (replace-regexp-in-string "    " tab markup)))))

;;;###autoload
(defun zencoding-expand-line (arg)
  "Replace the current line's zencode expression with the corresponding expansion.
If prefix ARG is given or region is visible call `zencoding-preview' to start an
interactive preview.

Otherwise expand line directly.

For more information see `zencoding-mode'."
  (interactive "P")
  (let* ((here (point))
         (preview (if zencoding-preview-default (not arg) arg))
         (beg (if preview
                  (progn
                    (beginning-of-line)
                    (skip-chars-forward " \t")
                    (point))
                (when mark-active (region-beginning))))
         (end (if preview
                  (progn
                    (end-of-line)
                    (skip-chars-backward " \t")
                    (point))
                (when mark-active (region-end)))))
    (if beg
        (progn
          (goto-char here)
          (zencoding-preview beg end))
      (let ((expr (zencoding-expr-on-line)))
        (if expr
            (let* ((markup (zencoding-transform (car (zencoding-expr (first expr)))))
                   (pretty (zencoding-prettify markup (current-indentation))))
              (save-excursion
                (delete-region (second expr) (third expr))
                (zencoding-insert-and-flash pretty))))))))

(defvar zencoding-mode-keymap nil
  "Keymap for zencode minor mode.")

(if zencoding-mode-keymap
    nil
  (progn
    (setq zencoding-mode-keymap (make-sparse-keymap))
    (define-key zencoding-mode-keymap (kbd "C-j") 'zencoding-expand-line)
    (define-key zencoding-mode-keymap (kbd "<C-return>") 'zencoding-expand-line)))

;;;###autoload
(define-minor-mode zencoding-mode
  "Minor mode for writing HTML and CSS markup.
With zen coding for HTML and CSS you can write a line like

  ul#name>li.item*2

and have it expanded to

  <ul id=\"name\">
    <li class=\"item\"></li>
    <li class=\"item\"></li>
  </ul>

This minor mode defines keys for quick access:

\\{zencoding-mode-keymap}

Home page URL `http://www.emacswiki.org/emacs/ZenCoding'.

See also `zencoding-expand-line'."
  :lighter " Zen"
  :keymap zencoding-mode-keymap)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Zencoding yasnippet integration

(defun zencoding-transform-yas (ast)
  (let* ((leaf-count 0)
         (zencoding-leaf-function
          (lambda ()
            (format "$%d" (incf leaf-count)))))
    (zencoding-transform ast)))

;;;###autoload
(defun zencoding-expand-yas ()
  (interactive)
  (let ((expr (zencoding-expr-on-line)))
    (if expr
        (let* ((markup (zencoding-transform-yas (car (zencoding-expr (first expr)))))
               (filled (replace-regexp-in-string "><" ">\n<" markup)))
          (delete-region (second expr) (third expr))
          (insert filled)
          (indent-region (second expr) (point))
          (yas/expand-snippet
           (buffer-substring (second expr) (point))
           (second expr) (point))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Real-time preview
;;

;;;;;;;;;;
;; Lennart's version

(defvar zencoding-preview-input nil)
(make-local-variable 'zencoding-preview-input)
(defvar zencoding-preview-output nil)
(make-local-variable 'zencoding-preview-output)
(defvar zencoding-old-show-paren nil)
(make-local-variable 'zencoding-old-show-paren)

(defface zencoding-preview-input
  '((default :box t :inherit secondary-selection))
  "Face for preview input field."
  :group 'zencoding)

(defface zencoding-preview-output
  '((default :inherit highlight))
  "Face for preview output field."
  :group 'zencoding)

(defvar zencoding-preview-keymap
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "RET") 'zencoding-preview-accept)
    (define-key map (kbd "<return>") 'zencoding-preview-accept)
    (define-key map [(control ?g)] 'zencoding-preview-abort)
    map))

(defun zencoding-preview-accept ()
  (interactive)
  (let ((ovli zencoding-preview-input))
    (if (not (and (overlayp ovli)
                  (bufferp (overlay-buffer ovli))))
        (message "Preview is not active")
      (let* ((indent (current-indentation))
             (markup (zencoding-preview-transformed indent)))
        (when markup
          (delete-region (line-beginning-position) (overlay-end ovli))
          (zencoding-insert-and-flash markup)))))
  (zencoding-preview-abort))

(defvar zencoding-flash-ovl nil)
(make-variable-buffer-local 'zencoding-flash-ovl)

(defun zencoding-remove-flash-ovl (buf)
  (with-current-buffer buf
    (when (overlayp zencoding-flash-ovl)
      (delete-overlay zencoding-flash-ovl))
    (setq zencoding-flash-ovl nil)))

(defcustom zencoding-preview-default t
  "If non-nil then preview is the default action.
This determines how `zencoding-expand-line' works by default."
  :type 'boolean
  :group 'zencoding)

(defcustom zencoding-insert-flash-time 0.5
  "Time to flash insertion.
Set this to a negative number if you do not want flashing the
expansion after insertion."
  :type '(number :tag "Seconds")
  :group 'zencoding)

(defun zencoding-insert-and-flash (markup)
  (zencoding-remove-flash-ovl (current-buffer))
  (let ((here (point)))
    (insert markup)
    (setq zencoding-flash-ovl (make-overlay here (point)))
    (overlay-put zencoding-flash-ovl 'face 'zencoding-preview-output)
    (when (< 0 zencoding-insert-flash-time)
      (run-with-idle-timer zencoding-insert-flash-time
                           nil 'zencoding-remove-flash-ovl (current-buffer)))))

;;;###autoload
(defun zencoding-preview (beg end)
  "Expand zencode between BEG and END interactively.
This will show a preview of the expanded zen code and you can
accept it or skip it."
  (interactive (if mark-active
                   (list (region-beginning) (region-end))
                 (list nil nil)))
  (zencoding-preview-abort)
  (if (not beg)
      (message "Region not active")
    (setq zencoding-old-show-paren show-paren-mode)
    (show-paren-mode -1)
    (let ((here (point)))
      (goto-char beg)
      (forward-line 1)
      (unless (= 0 (current-column))
        (insert "\n"))
      (let* ((opos (point))
             (ovli (make-overlay beg end nil nil t))
             (ovlo (make-overlay opos opos))
             (info (propertize " Zen preview. Choose with RET. Cancel by stepping out. \n"
                               'face 'tooltip)))
        (overlay-put ovli 'face 'zencoding-preview-input)
        (overlay-put ovli 'keymap zencoding-preview-keymap)
        (overlay-put ovlo 'face 'zencoding-preview-output)
        (overlay-put ovlo 'before-string info)
        (setq zencoding-preview-input  ovli)
        (setq zencoding-preview-output ovlo)
        (add-hook 'before-change-functions 'zencoding-preview-before-change t t)
        (goto-char here)
        (add-hook 'post-command-hook 'zencoding-preview-post-command t t)))))

(defvar zencoding-preview-pending-abort nil)
(make-variable-buffer-local 'zencoding-preview-pending-abort)

(defun zencoding-preview-before-change (beg end)
  (when
      (or (> beg (overlay-end zencoding-preview-input))
          (< beg (overlay-start zencoding-preview-input))
          (> end (overlay-end zencoding-preview-input))
          (< end (overlay-start zencoding-preview-input)))
    (setq zencoding-preview-pending-abort t)))

(defun zencoding-preview-abort ()
  "Abort zen code preview."
  (interactive)
  (setq zencoding-preview-pending-abort nil)
  (remove-hook 'before-change-functions 'zencoding-preview-before-change t)
  (when (overlayp zencoding-preview-input)
    (delete-overlay zencoding-preview-input))
  (setq zencoding-preview-input nil)
  (when (overlayp zencoding-preview-output)
    (delete-overlay zencoding-preview-output))
  (setq zencoding-preview-output nil)
  (remove-hook 'post-command-hook 'zencoding-preview-post-command t)
  (when zencoding-old-show-paren (show-paren-mode 1)))

(defun zencoding-preview-post-command ()
  (condition-case err
      (zencoding-preview-post-command-1)
    (error (message "zencoding-preview-post: %s" err))))

(defun zencoding-preview-post-command-1 ()
  (if (and (not zencoding-preview-pending-abort)
           (<= (point) (overlay-end zencoding-preview-input))
           (>= (point) (overlay-start zencoding-preview-input)))
      (zencoding-update-preview (current-indentation))
    (zencoding-preview-abort)))

(defun zencoding-preview-transformed (indent)
  (let* ((string (buffer-substring-no-properties
		  (overlay-start zencoding-preview-input)
		  (overlay-end zencoding-preview-input)))
	 (ast    (car (zencoding-expr string))))
    (when (not (eq ast 'error))
      (let ((output (zencoding-transform ast)))
        (when output
          (zencoding-prettify output indent))))))

(defun zencoding-update-preview (indent)
  (let* ((pretty (zencoding-preview-transformed indent))
         (show (when pretty
                 (propertize pretty 'face 'highlight))))
    (when show
      (overlay-put zencoding-preview-output 'after-string
                   (concat show "\n")))))

(provide 'zencoding-mode)

;;; zencoding-mode.el ends here
