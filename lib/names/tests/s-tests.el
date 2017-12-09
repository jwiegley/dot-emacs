
(byte-compile-file "s.el")
(require 's)

(ert-deftest s-trim ()
  (should (equal (s-trim "trim ") "trim"))
  (should (equal (s-trim " this") "this"))
  (should (equal (s-trim " only  trims beg and end  ") "only  trims beg and end")))

(ert-deftest s-trim-left ()
  (should (equal (s-trim-left "trim ") "trim "))
  (should (equal (s-trim-left " this") "this")))

(ert-deftest s-trim-right ()
  (should (equal (s-trim-right "trim ") "trim"))
  (should (equal (s-trim-right " this") " this")))

(ert-deftest s-chomp ()
  (should (equal (s-chomp "no newlines\n") "no newlines"))
  (should (equal (s-chomp "no newlines\r\n") "no newlines"))
  (should (equal (s-chomp "some newlines\n\n") "some newlines\n")))

(ert-deftest s-collapse-whitespace ()
  (should (equal (s-collapse-whitespace "only   one space   please") "only one space please"))
  (should (equal (s-collapse-whitespace "collapse \n all \t sorts of \r whitespace") "collapse all sorts of whitespace")))

(ert-deftest s-word-wrap ()
  (should (equal (s-word-wrap 10 "This is too long") "This is\ntoo long"))
  (should (equal (s-word-wrap 10 "This is way way too long") "This is\nway way\ntoo long"))
  (should (equal (s-word-wrap 10 "It-wraps-words-but-does-not-break-them") "It-wraps-words-but-does-not-break-them")))

(ert-deftest s-center ()
  (should (equal (s-center 5 "a") "  a  "))
  (should (equal (s-center 5 "ab") "  ab "))
  (should (equal (s-center 1 "abc") "abc"))
  (should (equal (s-center 6 "ab") "  ab  ")))

(ert-deftest s-pad-left ()
  (should (equal (s-pad-left 3 "0" "3") "003"))
  (should (equal (s-pad-left 3 "0" "23") "023"))
  (should (equal (s-pad-left 3 "0" "1234") "1234")))

(ert-deftest s-pad-right ()
  (should (equal (s-pad-right 3 "." "3") "3.."))
  (should (equal (s-pad-right 3 "." "23") "23."))
  (should (equal (s-pad-right 3 "." "1234") "1234")))

(ert-deftest s-truncate ()
  (should (equal (s-truncate 6 "This is too long") "Thi..."))
  (should (equal (s-truncate 16 "This is also too long") "This is also ..."))
  (should (equal (s-truncate 16 "But this is not!") "But this is not!")))

(ert-deftest s-left ()
  (should (equal (s-left 3 "lib/file.js") "lib"))
  (should (equal (s-left 3 "li") "li")))

(ert-deftest s-right ()
  (should (equal (s-right 3 "lib/file.js") ".js"))
  (should (equal (s-right 3 "li") "li")))

(ert-deftest s-chop-suffix ()
  (should (equal (s-chop-suffix "-test.js" "penguin-test.js") "penguin"))
  (should (equal (s-chop-suffix "\n" "no newlines\n") "no newlines"))
  (should (equal (s-chop-suffix "\n" "some newlines\n\n") "some newlines\n")))

(ert-deftest s-chop-suffixes ()
  (should (equal (s-chop-suffixes '("_test.js" "-test.js" "Test.js") "penguin-test.js") "penguin"))
  (should (equal (s-chop-suffixes '("\r" "\n") "penguin\r\n") "penguin\r"))
  (should (equal (s-chop-suffixes '("\n" "\r") "penguin\r\n") "penguin")))

(ert-deftest s-chop-prefix ()
  (should (equal (s-chop-prefix "/tmp" "/tmp/file.js") "/file.js"))
  (should (equal (s-chop-prefix "/tmp" "/tmp/tmp/file.js") "/tmp/file.js")))

(ert-deftest s-chop-prefixes ()
  (should (equal (s-chop-prefixes '("/tmp" "/my") "/tmp/my/file.js") "/file.js"))
  (should (equal (s-chop-prefixes '("/my" "/tmp") "/tmp/my/file.js") "/my/file.js")))

(ert-deftest s-shared-start ()
  (should (equal (s-shared-start "bar" "baz") "ba"))
  (should (equal (s-shared-start "foobar" "foo") "foo"))
  (should (equal (s-shared-start "bar" "foo") ""))
  (should (equal (s-shared-start "" "foo") ""))
  (should (equal (s-shared-start "foo" "foo") "foo"))
  (should (equal (s-shared-start "" "") "")))

(ert-deftest s-shared-end ()
  (should (equal (s-shared-end "bar" "var") "ar"))
  (should (equal (s-shared-end "foo" "foo") "foo"))
  (should (equal (s-shared-end "bar" "foo") ""))
  (should (equal (s-shared-end "" "foo") ""))
  (should (equal (s-shared-end "" "") "")))

(ert-deftest s-repeat ()
  (should (equal (s-repeat 10 " ") "          "))
  (should (equal (s-concat (s-repeat 8 "Na") " Batman!") "NaNaNaNaNaNaNaNa Batman!")))

(ert-deftest s-concat ()
  (should (equal (s-concat "abc" "def" "ghi") "abcdefghi")))

(ert-deftest s-prepend ()
  (should (equal (s-prepend "abc" "def") "abcdef")))

(ert-deftest s-append ()
  (should (equal (s-append "abc" "def") "defabc")))

(ert-deftest s-lines ()
  (should (equal (s-lines "abc\ndef\nghi") '("abc" "def" "ghi")))
  (should (equal (s-lines "abc\rdef\rghi") '("abc" "def" "ghi")))
  (should (equal (s-lines "abc\r\ndef\r\nghi") '("abc" "def" "ghi"))))

(ert-deftest s-match ()
  (should (equal (s-match "^def" "abcdefg") nil))
  (should (equal (s-match "^abc" "abcdefg") '("abc")))
  (should (equal (s-match "^/.*/\\([a-z]+\\)\\.\\([a-z]+\\)" "/some/weird/file.html") '("/some/weird/file.html" "file" "html")))
  (should (equal (s-match "^/.*/\\([a-z]+\\)\\.\\([a-z]+\\)" "/some/weird/file.org") '("/some/weird/file.org" "file" "org")))
  (should (equal (s-match "^\\(abc\\)\\(def\\)?" "abcdef") '("abcdef" "abc" "def")))
  (should (equal (s-match "^\\(abc\\)\\(def\\)?" "abc") '("abc" "abc")))
  (should (equal (s-match "^\\(abc\\)\\(def\\)?\\(ghi\\)" "abcghi") '("abcghi" "abc" nil "ghi")))
  (should (equal (s-match "abc" "abcdef" 1) nil))
  (should (equal (s-match "abc" "abcdefabc" 2) '("abc"))))

(ert-deftest s-match-strings-all ()
  (should (equal (s-match-strings-all
                  "{\\([^}]+\\)}" "x is {x} and y is {y}") '(("{x}" "x") ("{y}" "y"))))
  (should (equal (s-match-strings-all "ab." "abXabY") '(("abX") ("abY"))))
  (should (equal (s-match-strings-all "\\<" "foo bar baz") '(("") ("") ("")))))

(ert-deftest s-slice-at ()
  (should (equal (s-slice-at "-" "abc") '("abc")))
  (should (equal (s-slice-at "-" "abc-def") '("abc" "-def")))
  (should (equal (s-slice-at "[\.#]" "abc.def.ghi#id") '("abc" ".def" ".ghi" "#id")))
  (should (equal (s-slice-at "-" "abc-def-") '("abc" "-def" "-"))))

(ert-deftest s-split ()
  (should (equal (s-split "|" "a|bc|12|3") '("a" "bc" "12" "3")))
  (should (equal (s-split ":" "a,c,d") '("a,c,d")))
  (should (equal (s-split "\n" "z\nefg\n") '("z" "efg" "")))
  (should (equal (s-split "\n" "z\nefg\n" t) '("z" "efg")))
  (should (equal (s-split "ö" "xyöözeföklmö") '("xy" "" "zef" "klm" "")))
  (should (equal (s-split "ö" "xyöözeföklmö" t) '("xy" "zef" "klm"))))

(ert-deftest s-join ()
  (should (equal (s-join "+" '("abc" "def" "ghi")) "abc+def+ghi"))
  (should (equal (s-join "\n" '("abc" "def" "ghi")) "abc\ndef\nghi")))

(ert-deftest s-equals? ()
  (should (equal (s-equals? "abc" "ABC") nil))
  (should (equal (s-equals? "abc" "abc") t)))

(ert-deftest s-less? ()
  (should (equal (s-less? "abc" "abd") t))
  (should (equal (s-less? "abd" "abc") nil))
  (should (equal (s-less? "abc" "abc") nil)))

(ert-deftest s-matches? ()
  (should (equal (s-matches? "^[0-9]+$" "123") t))
  (should (equal (s-matches? "^[0-9]+$" "a123") nil))
  (should (equal (s-matches? "1" "1a" 1) nil))
  (should (equal (s-matches? "1" "1a1" 1) t)))

(ert-deftest s-blank? ()
  (should (equal (s-blank? "") t))
  (should (equal (s-blank? nil) t))
  (should (equal (s-blank? " ") nil)))

(ert-deftest s-present? ()
  (should (equal (s-present? "") nil))
  (should (equal (s-present? nil) nil))
  (should (equal (s-present? " ") t)))

(ert-deftest s-ends-with? ()
  (should (equal (s-ends-with? ".md" "readme.md") t))
  (should (equal (s-ends-with? ".MD" "readme.md") nil))
  (should (equal (s-ends-with? ".MD" "readme.md" t) t))
  (should (equal (s-ends-with? ".md" "md") nil))
  (should (equal (s-suffix? ".md" "readme.md") t)))

(ert-deftest s-starts-with? ()
  (should (equal (s-starts-with? "lib/" "lib/file.js") t))
  (should (equal (s-starts-with? "LIB/" "lib/file.js") nil))
  (should (equal (s-starts-with? "LIB/" "lib/file.js" t) t))
  (should (equal (s-starts-with? "lib/" "lib") nil))
  (should (equal (s-prefix? "lib/" "lib/file.js") t)))

(ert-deftest s-contains? ()
  (should (equal (s-contains? "file" "lib/file.js") t))
  (should (equal (s-contains? "nope" "lib/file.js") nil))
  (should (equal (s-contains? "^a" "it's not ^a regexp") t))
  (should (equal (s-contains? "FILE" "lib/file.js") nil))
  (should (equal (s-contains? "FILE" "lib/file.js" t) t)))

(ert-deftest s-lowercase? ()
  (should (equal (s-lowercase? "file") t))
  (should (equal (s-lowercase? "File") nil))
  (should (equal (s-lowercase? "filä") t))
  (should (equal (s-lowercase? "filÄ") nil))
  (should (equal (s-lowercase? "123?") t)))

(ert-deftest s-uppercase? ()
  (should (equal (s-uppercase? "HULK SMASH") t))
  (should (equal (s-uppercase? "Bruce no smash") nil))
  (should (equal (s-uppercase? "FöB") nil))
  (should (equal (s-uppercase? "FÖB") t))
  (should (equal (s-uppercase? "123?") t)))

(ert-deftest s-mixedcase? ()
  (should (equal (s-mixedcase? "HULK SMASH") nil))
  (should (equal (s-mixedcase? "Bruce no smash") t))
  (should (equal (s-mixedcase? "BRÜCE") nil))
  (should (equal (s-mixedcase? "BRüCE") t))
  (should (equal (s-mixedcase? "123?") nil)))

(ert-deftest s-capitalized? ()
  (should (equal (s-capitalized? "Capitalized") t))
  (should (equal (s-capitalized? "I am capitalized") t))
  (should (equal (s-capitalized? "I Am Titleized") nil))
  (should (equal (s-capitalized? "lower") nil))
  (should (equal (s-capitalized? "UPPER") nil))
  (should (equal (s-capitalized? "Привет") t)))

(ert-deftest s-numeric? ()
  (should (equal (s-numeric? "123") t))
  (should (equal (s-numeric? "onetwothree") nil))
  (should (equal (s-numeric? "7a") nil))
  (should (equal (s-numeric? "a89") nil)))

(ert-deftest s-replace ()
  (should (equal (s-replace "file" "nope" "lib/file.js") "lib/nope.js"))
  (should (equal (s-replace "^a" "\\1" "it's not ^a regexp") "it's not \\1 regexp")))

(ert-deftest s-replace-all ()
  (should (equal (s-replace-all '(("lib" . "test") ("file" . "file_test")) "lib/file.js") "test/file_test.js"))
  (should (equal (s-replace-all '(("lib" . "test") ("test" . "lib")) "lib/test.js") "test/lib.js")))

(ert-deftest s-downcase ()
  (should (equal (s-downcase "ABC") "abc")))

(ert-deftest s-upcase ()
  (should (equal (s-upcase "abc") "ABC")))

(ert-deftest s-capitalize ()
  (should (equal (s-capitalize "abc DEF") "Abc def"))
  (should (equal (s-capitalize "abc.DEF") "Abc.def")))

(ert-deftest s-titleize ()
  (should (equal (s-titleize "abc DEF") "Abc Def"))
  (should (equal (s-titleize "abc.DEF") "Abc.Def")))

(ert-deftest s-with ()
  (should (equal (s-with "   hulk smash   " s-trim s-upcase) "HULK SMASH"))
  (should (equal (s-with "My car is a Toyota" (s-replace "car" "name") (s-replace "a Toyota" "Bond") (s-append ", James Bond")) "My name is Bond, James Bond"))
  (should (equal (s-with "abc \ndef  \nghi" s-lines (mapcar 's-trim) (s-join "-") s-reverse) "ihg-fed-cba")))

(ert-deftest s-index-of ()
  (should (equal (s-index-of "abc" "abcdef") 0))
  (should (equal (s-index-of "CDE" "abcdef" t) 2))
  (should (equal (s-index-of "n.t" "not a regexp") nil)))

(ert-deftest s-reverse ()
  (should (equal (s-reverse "abc") "cba"))
  (should (equal (s-reverse "ab xyz") "zyx ba"))
  (should (equal (s-reverse "") "")))

(ert-deftest s-presence ()
  (should (equal (s-presence nil) nil))
  (should (equal (s-presence "") nil))
  (should (equal (s-presence "foo") "foo")))

(ert-deftest s-format ()
  ;; One with an alist works
  (should (equal (s-format
                  "help ${name}! I'm ${malady}"
                  'aget
                  '(("name" . "nic") ("malady" . "on fire"))) "help nic! I'm on fire"))

  ;; One with a function works
  (should (equal (s-format "hello ${name}, nice day" (lambda (var-name) "nic")) "hello nic, nice day"))

  ;; One with a list works
  (should (equal (s-format "hello $0, nice $1" 'elt '("nic" "day")) "hello nic, nice day"))

  ;; Two with a hash-table works
  (should (equal (s-format
                  "help ${name}! I'm ${malady}"
                  'gethash
                  #s(hash-table test equal data ("name" "nic" "malady" "on fire"))) "help nic! I'm on fire"))

  ;; Replacing case has no effect on s-format
  (should (equal (let ((case-replace t))
                   (s-format "help ${NAME}!" 'aget '(("NAME" . "Nick")))) "help Nick!"))

  (should (equal (let ((case-replace nil))
                   (s-format "help ${NAME}!" 'aget '(("NAME" . "Nick")))) "help Nick!"))

  (should (equal (let ((case-replace nil))
                   (s-format "help ${name}!" 'aget '(("name" . "Nick")))) "help Nick!"))

  ;; What happens when we have literal slashes?
  (should (equal (s-format "$0" 'elt '("Hello\\nWorld")) "Hello\\nWorld"))

  ;; What happens when we don't have the elements? with hash...
  (should (equal (condition-case err
                     (s-format
                      "help ${name}! I'm ${malady}"
                      'gethash
                      #s(hash-table test equal data ("name" "nic" )))
                   (s-format-resolve (car err))) 's-format-resolve)))

(ert-deftest s-lex-format ()
  ;; lexical stuff
  (should (equal (let ((x 1))
                   (s-lex-format "x is ${x}")) "x is 1"))

  (should (equal (let ((str1 "this")
                       (str2 "that"))
                   (s-lex-format "${str1} and ${str2}")) "this and that"))

  ;; Have a litteral \ in the replacement
  (should (equal (let ((foo "Hello\\nWorld"))
                   (s-lex-format "${foo}")) "Hello\\nWorld"))
  )

(ert-deftest s-count-matches ()
  (should (equal (s-count-matches "a" "aba") 2))
  (should (equal (s-count-matches "a" "aba" 0 2) 1))
  (should (equal (s-count-matches "\\w\\{2\\}[0-9]+" "ab1bab2frobinator") 2)))

(ert-deftest s-split-words ()
  (should (equal (s-split-words "under_score") '("under" "score")))
  (should (equal (s-split-words "some-dashed-words") '("some" "dashed" "words")))
  (should (equal (s-split-words "evenCamelCase") '("even" "Camel" "Case")))
  (should (equal (s-split-words "!map (fn list)") '("map" "fn" "list")))
  (should (equal (s-split-words "Привет, мир") '("Привет" "мир")))
  (should (equal (s-split-words "e é è e") '("e" "é" "è" "e")))
  (should (equal (s-split-words "MANYUpperCases") '("MANY" "Upper" "Cases")))
  (should (equal (s-split-words "Приве́т") '("Приве́т")))
  (should (equal (s-split-words "漢語") '("漢語"))))

(ert-deftest s-lower-camel-case ()
  (should (equal (s-lower-camel-case "some words") "someWords"))
  (should (equal (s-lower-camel-case "dashed-words") "dashedWords"))
  (should (equal (s-lower-camel-case "under_scored_words") "underScoredWords")))

(ert-deftest s-upper-camel-case ()
  (should (equal (s-upper-camel-case "some words") "SomeWords"))
  (should (equal (s-upper-camel-case "dashed-words") "DashedWords"))
  (should (equal (s-upper-camel-case "under_scored_words") "UnderScoredWords")))

(ert-deftest s-snake-case ()
  (should (equal (s-snake-case "some words") "some_words"))
  (should (equal (s-snake-case "dashed-words") "dashed_words"))
  (should (equal (s-snake-case "camelCasedWords") "camel_cased_words")))

(ert-deftest s-dashed-words ()
  (should (equal (s-dashed-words "some words") "some-words"))
  (should (equal (s-dashed-words "under_scored_words") "under-scored-words"))
  (should (equal (s-dashed-words "camelCasedWords") "camel-cased-words")))

(ert-deftest s-capitalized-words ()
  (should (equal (s-capitalized-words "some words") "Some words"))
  (should (equal (s-capitalized-words "under_scored_words") "Under scored words"))
  (should (equal (s-capitalized-words "camelCasedWords") "Camel cased words")))

(ert-deftest s-titleized-words ()
  (should (equal (s-titleized-words "some words") "Some Words"))
  (should (equal (s-titleized-words "under_scored_words") "Under Scored Words"))
  (should (equal (s-titleized-words "camelCasedWords") "Camel Cased Words")))

(ert-deftest s-word-initials ()
  (should (equal (s-word-initials "some words") "sw"))
  (should (equal (s-word-initials "under_scored_words") "usw"))
  (should (equal (s-word-initials "camelCasedWords") "cCW"))
  (should (equal (s-word-initials "dashed-words") "dw")))

