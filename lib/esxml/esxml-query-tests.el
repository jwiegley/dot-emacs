(require 'esxml)
(require 'esxml-query)
(require 'ert)

(ert-deftest esxml-parse-css-selector-test ()
  (should-error (esxml-parse-css-selector ""))
  (should-error (esxml-parse-css-selector "'foo'"))
  (should (equal (esxml-parse-css-selector "*")
                 '((((wildcard))))))
  (should (equal (esxml-parse-css-selector "foo")
                 '((((tag . foo))))))
  (should-error (esxml-parse-css-selector "foo 123"))
  (should (equal (esxml-parse-css-selector "foo bar")
                 '((((tag . foo))
                    ((combinator . descendant))
                    ((tag . bar))))))
  (should (equal (esxml-parse-css-selector "foo,bar")
                 '((((tag . foo)))
                   (((tag . bar))))))
  (should (equal (esxml-parse-css-selector "foo, bar")
                 '((((tag . foo)))
                   (((tag . bar))))))
  (should (equal (esxml-parse-css-selector "foo ,bar")
                 '((((tag . foo)))
                   (((tag . bar))))))
  (should (equal (esxml-parse-css-selector "foo , bar")
                 '((((tag . foo)))
                   (((tag . bar))))))
  (should-error (esxml-parse-css-selector "foo, "))
  (should-error (esxml-parse-css-selector "foo,"))
  (should-error (esxml-parse-css-selector "foo ,"))
  (should-error (esxml-parse-css-selector "foo , "))
  (should (equal (esxml-parse-css-selector "foo > bar")
                 '((((tag . foo))
                    ((combinator . child))
                    ((tag . bar))))))
  (should (equal (esxml-parse-css-selector "foo>bar")
                 '((((tag . foo))
                    ((combinator . child))
                    ((tag . bar))))))
  (should (equal (esxml-parse-css-selector "foo ~ bar")
                 '((((tag . foo))
                    ((combinator . indirect-sibling))
                    ((tag . bar))))))
  (should (equal (esxml-parse-css-selector "foo + bar")
                 '((((tag . foo))
                    ((combinator . direct-sibling))
                    ((tag . bar))))))
  (should-error (esxml-parse-css-selector "foo >"))
  (should (equal (esxml-parse-css-selector "foo#bar.baz.qux")
                 '((((tag . foo)
                     (id . "bar")
                     (class . "baz")
                     (class . "qux"))))))
  (should (equal (esxml-parse-css-selector "#foo.bar.baz[qux=quux]:foo(bar baz)")
                 '((((id . "foo")
                     (class . "bar")
                     (class . "baz")
                     (attribute
                      (name . "qux")
                      (exact-match . "quux"))
                     (pseudo-class
                      (name . "foo")
                      (args
                       (ident . "bar")
                       (ident . "baz"))))))))
  (should-error (esxml-parse-css-selector "foo#bar#baz"))
  (should (equal (esxml-parse-css-selector "foo[bar=baz][qux=quux]")
                 '((((tag . foo)
                     (attribute
                      (name . "bar")
                      (exact-match . "baz"))
                     (attribute
                      (name . "qux")
                      (exact-match . "quux")))))))
  (should (equal (esxml-parse-css-selector "foo::bar:baz(qux quux)")
                 '((((tag . foo)
                     (pseudo-element
                      (name . "bar"))
                     (pseudo-class
                      (name . "baz")
                      (args
                       (ident . "qux")
                       (ident . "quux"))))))))
  (should (equal (esxml-parse-css-selector "#foo")
                 '((((id . "foo"))))))
  (should-error (esxml-parse-css-selector "# #bar"))
  (should (equal (esxml-parse-css-selector ".foo")
                 '((((class . "foo"))))))
  (should-error (esxml-parse-css-selector ". .bar"))
  (should (equal (esxml-parse-css-selector "[foo]")
                 '((((attribute
                      (name . "foo")))))))
  (should-error (esxml-parse-css-selector "[foo=]"))
  (should (equal (esxml-parse-css-selector "[foo=bar]")
                 '((((attribute
                      (name . "foo")
                      (exact-match . "bar")))))))
  (should (equal (esxml-parse-css-selector "[foo^=bar]")
                 '((((attribute
                      (name . "foo")
                      (prefix-match . "bar")))))))
  (should (equal (esxml-parse-css-selector "[foo$=bar]")
                 '((((attribute
                      (name . "foo")
                      (suffix-match . "bar")))))))
  (should (equal (esxml-parse-css-selector "[foo*=bar]")
                 '((((attribute
                      (name . "foo")
                      (substring-match . "bar")))))))
  (should (equal (esxml-parse-css-selector "[foo~=bar]")
                 '((((attribute
                      (name . "foo")
                      (include-match . "bar")))))))
  (should (equal (esxml-parse-css-selector "[foo|=bar]")
                 '((((attribute
                      (name . "foo")
                      (dash-match . "bar")))))))
  (should-error (esxml-parse-css-selector "[foo=bar"))
  (should (equal (esxml-parse-css-selector "[foo='bar']")
                 '((((attribute
                      (name . "foo")
                      (exact-match . "bar")))))))
  (should (equal (esxml-parse-css-selector "[foo=\"bar\"]")
                 '((((attribute
                      (name . "foo")
                      (exact-match . "bar")))))))
  (should-error (esxml-parse-css-selector "[foo='bar]"))
  (should (equal (esxml-parse-css-selector "[ foo = bar ]")
                 '((((attribute
                      (name . "foo")
                      (exact-match . "bar")))))))
  (should (equal (esxml-parse-css-selector ":foo")
                 '((((pseudo-class
                      (name . "foo")))))))
  (should (equal (esxml-parse-css-selector "::foo")
                 '((((pseudo-element
                      (name . "foo")))))))
  (should-error (esxml-parse-css-selector ": foo"))
  (should-error (esxml-parse-css-selector ":: foo"))
  (should-error (esxml-parse-css-selector ":foo()"))
  (should (equal (esxml-parse-css-selector ":foo(bar)")
                 '((((pseudo-class
                      (name . "foo")
                      (args
                       (ident . "bar"))))))))
  (should-error (esxml-parse-css-selector "::foo(bar)"))
  (should (equal (esxml-parse-css-selector ":foo(bar baz)")
                 '((((pseudo-class
                      (name . "foo")
                      (args
                       (ident . "bar")
                       (ident . "baz"))))))))
  (should (equal (esxml-parse-css-selector ":foo(1)")
                 '((((pseudo-class
                      (name . "foo")
                      (args
                       (number . 1))))))))
  (should (equal (esxml-parse-css-selector ":foo(42rem)")
                 '((((pseudo-class
                      (name . "foo")
                      (args
                       (dimension . "42rem"))))))))
  (should (equal (esxml-parse-css-selector ":foo(2n+1)")
                 '((((pseudo-class
                      (name . "foo")
                      (args
                       (number . 2)
                       (ident . "n")
                       (operator . +)
                       (number . 1))))))))
  (should (equal (esxml-parse-css-selector ":foo(1-1)")
                 '((((pseudo-class
                      (name . "foo")
                      (args
                       (number . 1)
                       (operator . -)
                       (number . 1))))))))
  (should-error (esxml-parse-css-selector ":foo(bar")))

(defvar esxml-query-document
  (xml-to-esxml
   "<!DOCTYPE html>
<html lang=\"en-US\">
  <head>
    <meta charset=\"utf-8\" />
    <link rel=\"self\" />
    <title>Foobar</title>
  </head>
  <body>
    <table>
      <thead>
        <tr class=\"row\" id=\"heading\">
          <th class=\"col\">Key</th>
          <th class=\"col\">Value</th>
        </tr>
      </thead>
      <tbody>
        <tr class=\"row even\">
          <td class=\"col key\">Foo</td>
          <td class=\"col value\">1</td>
        </tr>
        <tr class=\"row odd\">
          <td class=\"col key\">Bar</td>
          <td class=\"col value\">2</td>
        </tr>
      </tbody>
    </table>
  </body>
</html>"))

(ert-deftest esxml-query-test ()
  (let ((root esxml-query-document))
    (should (eq (esxml-node-tag (esxml-query "*" root)) 'html))
    (should (eq (esxml-node-tag (esxml-query "table" root)) 'table))
    (should-not (esxml-query "foo" root))
    (should (eq (esxml-node-tag (esxml-query "table, foo" root)) 'table))
    (should (eq (esxml-node-tag (esxml-query "foo, table" root)) 'table))
    (should-not (esxml-query "foo, bar" root))
    (should (eq (esxml-node-tag (esxml-query "thead, tbody" root)) 'thead))
    (should (eq (esxml-node-tag (esxml-query "tbody, thead" root)) 'thead))

    (should-not (esxml-query "table table" root))
    (should (equal (esxml-node-children (esxml-query "table thead th" root))
                   '("Key")))
    (should (equal (esxml-node-children (esxml-query "table td" root))
                   '("Foo")))
    (should (equal (esxml-node-children (esxml-query "table * td" root))
                   '("Foo")))
    (should-not (esxml-query "td foo" root))
    (should-not (esxml-query "tr foo td" root))
    (should (equal (esxml-node-children (esxml-query "tbody>tr>td" root))
                   '("Foo")))
    (should-not (esxml-query "tr>foo" root))
    (should-not (esxml-query "foo>td" root))

    (should (equal (esxml-node-children (esxml-query "#heading>th" root))
                   '("Key")))
    (should (equal (esxml-node-tag (esxml-query "tr#heading" root)) 'tr))
    (should (equal (esxml-node-tag (esxml-query "#heading" root)) 'tr))
    (should-not (esxml-query "th#heading" root))
    (should-not (esxml-query "tr #heading" root))

    (should (equal (esxml-node-children (esxml-query ".row>td" root))
                   '("Foo")))
    (should-not (esxml-query ".foo" root))
    (should (esxml-query ".row.even" root))
    (should-not (esxml-query ".row.foo" root))
    (should (equal (esxml-node-children (esxml-query ".row .value" root))
                   '("1")))
    (should (equal (esxml-node-children (esxml-query ".row.odd .value" root))
                   '("2")))
    (should (equal (esxml-node-children (esxml-query ".even .value, .odd .value" root))
                   '("1")))

    (should (eq (esxml-node-tag (esxml-query "[rel=self]" root)) 'link))
    (should-not (esxml-query "[rel=elf]" root))
    (should-not (esxml-query "[rel=sel]" root))
    (should-not (esxml-query "[rel=selfie]" root))
    (should (equal (esxml-node-children (esxml-query "[class='row even'] td" root))
                   '("Foo")))
    (should (esxml-query "[class^=row]" root))
    (should (esxml-query "[class$=row]" root))
    (should-not (esxml-query "[class^=key]" root))
    (should (esxml-query "[class$=key]" root))
    (should-not (esxml-query "[class^=foo]" root))
    (should-not (esxml-query "[class$=bar]" root))
    (should (esxml-query "[charset^=utf][charset$='8']" root))
    (should (esxml-query "[charset*=utf]" root))
    (should (esxml-query "[class*=val]" root))
    (should-not (esxml-query "[class*=foo]" root))
    (should (esxml-query "[rel*=self]" root))
    (should (esxml-query "[class*='l k']" root))
    (should-not (esxml-query "[charset~=utf]" root))
    (should (esxml-query "[rel~=self]" root))
    (should (esxml-query "[class~=row]" root))
    (should (esxml-query "[class~=key]" root))
    (should-not (esxml-query "[class~=foo]" root))
    (should (equal (esxml-node-children (esxml-query "[class~=row][class~=odd] [class~=value]" root))
                   '("2")))
    (should (equal (cdr (assq 'lang (esxml-node-attributes (esxml-query "[lang|=en]" root))))
                   "en-US"))
    (should-not (esxml-query "[lang|=US]" root))))

(ert-deftest esxml-query-all-test ()
  (let ((root esxml-query-document))
    (should (equal (cl-remove-if 'not (mapcar 'esxml-node-tag
                                              (esxml-query-all "*" root)))
                   '(html head meta link title
                          body table thead tr th th tbody tr td td tr td td)))
    (should (equal (mapcar 'esxml-node-tag (esxml-query-all "table" root))
                   '(table)))
    (should-not (esxml-query-all "foo" root))
    (should (equal (mapcar 'esxml-node-tag (esxml-query-all "table, foo" root))
                   '(table)))
    (should (equal (mapcar 'esxml-node-tag (esxml-query-all "foo, table" root))
                   '(table)))
    (should-not (esxml-query-all "foo, bar" root))
    (should (equal (mapcar 'esxml-node-tag (esxml-query-all "thead, tbody" root))
                   '(thead tbody)))
    (should (equal (mapcar 'esxml-node-tag (esxml-query-all "tbody, thead" root))
                   '(thead tbody)))

    (should-not (esxml-query-all "table table" root))
    (should (equal (mapcar 'car (mapcar 'esxml-node-children (esxml-query-all "table thead th" root)))
                   '("Key" "Value")))
    (should (equal (mapcar 'car (mapcar 'esxml-node-children (esxml-query-all "table td" root)))
                   '("Foo" "1" "Bar" "2")))
    (should (equal (mapcar 'car (mapcar 'esxml-node-children (esxml-query-all "table * td" root)))
                   '("Foo" "1" "Bar" "2")))
    (should-not (esxml-query-all "td foo" root))
    (should-not (esxml-query-all "tr foo td" root))
    (should (equal (mapcar 'car (mapcar 'esxml-node-children (esxml-query-all "tbody>tr>td" root)))
                   '("Foo" "1" "Bar" "2")))
    (should-not (esxml-query-all "tr>foo" root))
    (should-not (esxml-query-all "foo>td" root))

    (should (equal (mapcar 'car (mapcar 'esxml-node-children (esxml-query-all "#heading>th" root)))
                   '("Key" "Value")))
    (should (equal (mapcar 'esxml-node-tag (esxml-query-all "tr#heading" root))
                   '(tr)))
    (should (equal (mapcar 'esxml-node-tag (esxml-query-all "#heading" root))
                   '(tr)))
    (should-not (esxml-query-all "th#heading" root))
    (should-not (esxml-query-all "tr #heading" root))

    (should (equal (mapcar 'car (mapcar 'esxml-node-children (esxml-query-all ".row>td" root)))
                   '("Foo" "1" "Bar" "2")))
    (should-not (esxml-query-all ".foo" root))
    (should (= (length (esxml-query-all ".row.even" root)) 1))
    (should-not (esxml-query-all ".row.foo" root))
    (should (equal (mapcar 'car (mapcar 'esxml-node-children (esxml-query-all ".row .value" root)))
                   '("1" "2")))
    (should (equal (mapcar 'car (mapcar 'esxml-node-children (esxml-query-all ".row.odd .value" root)))
                   '("2")))
    (should (= (length (esxml-query-all ".even, .odd" root)) 2))
    (should (equal (mapcar 'car (mapcar 'esxml-node-children (esxml-query-all ".even .value, .odd .value" root)))
                   '("1" "2")))

    (should (eq (esxml-node-tag (car (esxml-query-all "[rel=self]" root)))
                'link))
    (should-not (esxml-query-all "[rel=elf]" root))
    (should-not (esxml-query-all "[rel=sel]" root))
    (should-not (esxml-query-all "[rel=selfie]" root))
    (should (equal (mapcar 'car (mapcar 'esxml-node-children (esxml-query-all "[class='row even'] td" root)))
                   '("Foo" "1")))
    (should (= (length (esxml-query-all "[class^=row]" root)) 3))
    (should (= (length (esxml-query-all "[class$=row]" root)) 1))
    (should-not (esxml-query-all "[class^=key]" root))
    (should (= (length (esxml-query-all "[class$=key]" root)) 2))
    (should-not (esxml-query-all "[class^=foo]" root))
    (should-not (esxml-query-all "[class$=bar]" root))
    (should (= (length (esxml-query-all "[charset^=utf][charset$='8']" root)) 1))
    (should (= (length (esxml-query-all "[charset*=utf]" root)) 1))
    (should (= (length (esxml-query-all "[class*=val]" root)) 2))
    (should-not (esxml-query-all "[class*=foo]" root))
    (should (= (length (esxml-query-all "[rel*=self]" root)) 1))
    (should (= (length (esxml-query-all "[class*='l k']" root)) 2))
    (should-not (esxml-query-all "[charset~=utf]" root))
    (should (= (length (esxml-query-all "[rel~=self]" root)) 1))
    (should (= (length (esxml-query-all "[class~=row]" root)) 3))
    (should (= (length (esxml-query-all "[class~=key]" root)) 2))
    (should-not (esxml-query-all "[class~=foo]" root))
    (should (equal (car (esxml-node-children (car (esxml-query-all "[class~=row][class~=odd] [class~=value]" root))))
                   "2"))
    (should (equal (cdr (assq 'lang (esxml-node-attributes (car (esxml-query-all "[lang|=en]" root)))))
                   "en-US"))
    (should-not (esxml-query-all "[lang|=US]" root))))
