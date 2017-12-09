#+TITLE: parsec.el

A parser combinator library for Emacs Lisp similar to Haskell's Parsec library.

* Overview

This work is based on [[https://github.com/jwiegley/][John Wiegley]]'s [[https://github.com/jwiegley/emacs-pl][emacs-pl]]. The original [[https://github.com/jwiegley/emacs-pl][emacs-pl]] is awesome,
but I found following problems when I tried to use it:

- It only contains a very limited set of combinators
- Some of its functions (combinators) have different behaviors than their
  Haskell counterparts
- It can't show error messages when parsing fails

So I decided to make a new library on top of it. This library, however, contains
most of the parser combinators in =Text.Parsec.Combinator=, which should be
enough in most use cases. Of course more combinators can be added if necessary!
Most of the parser combinators have the same behavior as their Haskell
counterparts. =parsec.el= also comes with a simple error handling mechanism so
that it can display an error message showing how the parser fails.

So we can

- use these parser combinators to write parsers easily from scratch in Emacs
  Lisp like what we can do in Haskell
- port existing Haskell program using Parsec to its equivalent Emacs Lisp
  program easily

* Parsing Functions & Parser Combinators

  We compare the functions and macros defined in this library with their Haskell
  counterparts, assuming you're already familiar with Haskell's Parsec. If you
  don't have any experience with parser combinators, look at the docstrings of
  these functions and macros and try them to see the results! They are really
  easy to learn and use!

  The *Usage* column for each function/combinator in the following tables is
  much simplified. Check the docstring of the function/combinator to see the
  full description.

** Basic Parsing Functions
   These parsing functions are used as the basic building block for a parser. By
   default, their return value is a *string*.

  | parsec.el              | Haskell's Parsec | Usage                                                 |
  |------------------------+------------------+-------------------------------------------------------|
  | parsec-ch              | char             | parse a character                                     |
  | parsec-any-ch          | anyChar          | parse an arbitrary character                          |
  | parsec-satisfy         | satisfy          | parse a character satisfying a predicate              |
  | parsec-newline         | newline          | parse '\n'                                            |
  | parsec-crlf            | crlf             | parse '\r\n'                                          |
  | parsec-eol             | eol              | parse newline or CRLF                                 |
  | parsec-eof, parsec-eob | eof              | parse end of file                                     |
  | parsec-eol-or-eof      | *N/A*            | parse EOL or EOL                                      |
  | parsec-re              | *N/A*            | parse using a regular expression                      |
  | parsec-one-of          | oneOf            | parse one of the characters                           |
  | parsec-none-of         | noneOf           | parse any character other than the supplied ones      |
  | parsec-str             | *N/A*            | parse a string but consume input only when successful |
  | parsec-string          | string           | parse a string and consume input for partial matches  |
  | parsec-num             | *N/A*            | parse a number                                        |
  | parsec-letter          | letter           | parse a letter                                        |
  | parsec-digit           | digit            | parse a digit                                         |

  Note:
  - =parsec-str= and =parsec-string= are different. =parsec-string= behaves the
    same as =string= in Haskell, and =parsec-str= is more like combining
    =string= and =try= in Haskell. Personally I found =parsec-str= easier to use
    because =parsec-str= is "atomic", which is similar to =parsec-ch=.
  - Use the power of regular expressions provided by =parsec-re= and simplify the parser!

** Parser Combinators
   These combinators can be used to combine different parsers.

  | parsec.el                 | Haskell's Parsec | Usage                                                        |
  |---------------------------+------------------+--------------------------------------------------------------|
  | parsec-or                 | choice           | try the parsers until one succeeds                           |
  | parsec-try                | try              | try parser and consume no input when an error occurs         |
  | parsec-lookahead          | lookahead        | try parser and consume no input when successful              |
  | parsec-peek               | try && lookahead | try parser without comsuming any input                       |
  | parsec-peek-p             | try && lookahead | same as parsec-peek except the return value for failure      |
  | parsec-with-error-message | <?> (similar)    | use the new error message when an error occurs               |
  | parsec-many               | many             | apply the parser zero or more times                          |
  | parsec-many1              | many1            | apply the parser one or more times                           |
  | parsec-many-till          | manyTill         | apply parser zero or more times until end succeeds           |
  | parsec-until              | *N/A*            | parse until end succeeds                                     |
  | parsec-not-followed-by    | notFollowedBy    | succeed when the parser fails                                |
  | parsec-endby              | endby            | apply parser zero or more times, separated and ended by end  |
  | parsec-sepby              | sepby            | apply parser zero or more times, separated by sep            |
  | parsec-between            | between          | apply parser between open and close                          |
  | parsec-count              | count            | apply parser n times                                         |
  | parsec-option             | option           | apply parser, if it fails, return opt                        |
  | parsec-optional           | *N/A*            | apply parser zero or one time and return the result          |
  | parsec-optional*          | optional         | apply parser zero or one time and discard the result         |
  | parsec-optional-maybe     | optionMaybe      | apply parser zero or one time and return the result in Maybe |

  Note:
  - =parsec-or= can also be used to replace =<|>=.
  - =parsec-with-error-message= is slightly different from =<?>=. It will
    replace the error message even when the input is consumed.
  - By default, =parsec-many-till= behaves as Haskell's =manyTill=. However,
    =parsec-many-till= and =parsec-until= can accept an optional argument to
    specify which part(s) to be returned. You can use =:both= or =:end= as the
    optional argument to change the default behavior. See the docstrings for
    more information.

** Parser Utilities
   These utilities can be used together with parser combinators to build a
   parser and ease the translation process if you're trying to port an existing
   Haskell program.

  | parsec.el                        | Haskell's Parsec | Usage                                                   |
  |----------------------------------+------------------+---------------------------------------------------------|
  | parsec-and                       | do block         | try all parsers and return the last result              |
  | parsec-return                    | do block         | try all parsers and return the first result             |
  | parsec-ensure                    | *N/A*            | quit the parsing when an error occurs                   |
  | parsec-ensure-with-error-message | *N/A*            | quit the parsing when an error occurs with new message  |
  | parsec-collect                   | sequence         | try all parsers and collect the results into a list     |
  | parsec-collect*                  | *N/A*            | try all parsers and collect non-nil results into a list |
  | parsec-start                     | parse            | entry point                                             |
  | parsec-parse                     | parse            | entry point (same as parsec-start)                      |
  | parsec-with-input                | parse            | perform parsers on input                                |
  | parsec-from-maybe                | fromMaybe        | retrieve value from Maybe                               |
  | parsec-maybe-p                   | *N/A*            | is a Maybe value or not                                 |
  | parsec-query                     | *N/A*            | change the parser's return value                        |

** Variants that Return a String

   By default, the macros/functions that return multiple values will put the
   values into a list. These macros/functions are:
   - =parsec-many=
   - =parsec-many1=
   - =parsec-many-till=
   - =parsec-until=
   - =parsec-count=
   - =parsec-collect= and =parsec-collect*=

   They all have a variant that returns a string by concatenating the results in
   the list:
   - =parsec-many-as-string= or =parsec-many-s=
   - =parsec-many1-as-string= or =parsec-many1-s=
   - =parsec-many-till-as-string= or =parsec-many-till-s=
   - =parsec-until-as-string= or =parsec-until-s=
   - =parsec-collect-as-string= or =parsec-collect-s=
   - =parsec-count-as-string= or =parsec-count-s=

   The =*-s= and =*-as-string= variants are the same, except the =*-s= variants
   have a shorter name. Using these =*-s= functions are recommended if you're
   dealing with strings very frequently in your code. These variants accept the
   same arguments and have the same behavior as their original counterpart that
   returns a list. The only difference is the return value.
* Code Examples
  Some very simple examples are given here. You can see many code examples in
  the test files in this GitHub repo.

  The following code extract the "hello" from the comment:
  #+BEGIN_SRC elisp
  (parsec-with-input "/* hello */"
    (parsec-string "/*")
    (parsec-many-till-as-string (parsec-any-ch)
                                (parsec-try
                                 (parsec-string "*/"))))
  #+END_SRC

  The following Haskell program does a similar thing:
  #+BEGIN_SRC haskell
  import           Text.Parsec

  main :: IO ()
  main = print $ parse p "" "/* hello */"
    where
      p = do string "/*"
             manyTill anyChar (try (string "*/"))
  #+END_SRC

  The following code returns the "aeiou" before "end":
  #+BEGIN_SRC elisp
  (parsec-with-input "if aeiou end"
    (parsec-str "if ")
    (parsec-return
        (parsec-many-as-string (parsec-one-of ?a ?e ?i ?o ?u))
      (parsec-str " end")))
  #+END_SRC

* Write a Parser: a Simple CSV Parser
  You can find the code in =examples/simple-csv-parser.el=. The code is based
  on the Haskell code in [[http://book.realworldhaskell.org/read/using-parsec.html][Using Parsec]].

  An end-of-line should be a string =\n=. We use =(parsec-str "\n")= to parse it
  (Note that since =\n= is also one character, =(parsec-ch ?\n)= also works).
  Some files may not contain a newline at the end, but we can view end-of-file
  as the end-of-line for the last line, and use =parsec-eof= (or =parsec-eob=)
  to parse the end-of-file. We use =parsec-or= to combine these two combinators:
  #+BEGIN_SRC elisp
  (defun s-csv-eol ()
    (parsec-or (parsec-str "\n")
               (parsec-eof)))
  #+END_SRC

  A CSV file contains many lines and ends with an end-of-file. Use
  =parsec-return= to return the result of the first parser as the result.
  #+BEGIN_SRC elisp
  (defun s-csv-file ()
    (parsec-return (parsec-many (s-csv-line))
      (parsec-eof)))
  #+END_SRC

  A CSV line contains many CSV cells and ends with an end-of-line, and we
  should return the cells as the results:
  #+BEGIN_SRC elisp
  (defun s-csv-line ()
    (parsec-return (s-csv-cells)
      (s-csv-eol)))
  #+END_SRC

  CSV cells is a list, containing the first cell and the remaining cells:
  #+BEGIN_SRC elisp
  (defun s-csv-cells ()
    (cons (s-csv-cell-content) (s-csv-remaining-cells)))
  #+END_SRC

  A CSV cell consists any character that is not =,= or =\n=, and we use the
  =parsec-many-as-string= variant to return the whole content as a string
  instead of a list of single-character strings:
  #+BEGIN_SRC elisp
  (defun s-csv-cell-content ()
    (parsec-many-as-string (parsec-none-of ?, ?\n)))
  #+END_SRC

  For the remaining cells: if followed by a comma =,=, we try to parse more csv
  cells. Otherwise, we should return the =nil=:
  #+BEGIN_SRC elisp
  (defun s-csv-remaining-cells ()
    (parsec-or (parsec-and (parsec-ch ?,) (s-csv-cells)) nil))
  #+END_SRC

  OK. Our parser is almost done. To begin parsing the content in buffer =foo=,
  you need to wrap the parser inside =parsec-start= (or =parsec-parse=):
  #+BEGIN_SRC elisp
  (with-current-buffer "foo"
    (goto-char (point-min))
    (parsec-parse
     (s-csv-file)))
  #+END_SRC

  If you want to parse a string instead, we provide a simple wrapper macro
  =parsec-with-input=, and you feed a string as the input and put arbitraty
  parsers inside the macro body. =parsec-start= or =parsec-parse= is not needed.
  #+BEGIN_SRC elisp
  (parsec-with-input "a1,b1,c1\na2,b2,c2"
    (s-csv-file))
  #+END_SRC

  The above code returns:
  #+BEGIN_SRC elisp
  (("a1" "b1" "c1") ("a2" "b2" "c2"))
  #+END_SRC

  Note that if we replace =parsec-many-as-string= with =parsec-many= in
  =s-csv-cell-content=:
  #+BEGIN_SRC elisp
  (defun s-csv-cell-content ()
    (parsec-many (parsec-none-of ?, ?\n)))
  #+END_SRC

  The result would be:
  #+BEGIN_SRC elisp
  ((("a" "1") ("b" "1") ("c" "1")) (("a" "2") ("b" "2") ("c" "2")))
  #+END_SRC

* More Parser Examples
  I translate some Haskell Parsec examples into Emacs Lisp using =parsec.el=.
  You can see from these examples that it is very easy to write parsers using
  =parsec.el=, and if you know haskell, you can see that basically I just
  translate the Haskell into Emacs Lisp one by one because most of them are just
  the same!

  You can find five examples under the =examples/= directory.

  Three of the examples are taken from the chapter [[http://book.realworldhaskell.org/read/using-parsec.html][Using Parsec]] in the book of
  [[http://book.realworldhaskell.org/read/][Real World Haskell]]:
  - =simple-csv-parser.el=: a simple csv parser with no support for quoted
    cells, as explained in previous section.
  - =full-csv-parser.el=: a full csv parser
  - =url-str-parser.el=: parser parameters in URL

  =pjson.el= is a translation of Haskell's [[https://hackage.haskell.org/package/json-0.9.1/docs/src/Text-JSON-Parsec.html][json library using Parsec]].

  =scheme.el= is a much simplified Scheme parser based on [[https://en.wikibooks.org/wiki/Write_Yourself_a_Scheme_in_48_Hours/][Write Yourself a
  Scheme in 48 Hours]].

  They're really simple but you can see how this library works!

* Change the Return Values using =parsec-query=
  Parsing has side-effects such as forwarding the current point. In the original
  [[https://github.com/jwiegley/emacs-pl][emacs-pl]], you can specify some optional arguments to some parsing functions
  (=pl-ch=, =pl-re= etc.) to change the return values. In =parsec.el=, these
  functions don't have such a behavior. Instead, we provide a unified interface
  =parsec-query=, which accepts any parser, and changes the return value of the
  parser.

  You can speicify following arguments:
  #+BEGIN_EXAMPLE
  :beg      --> return the point before applying the PARSER
  :end      --> return the point after applying the PARSER
  :nil      --> return nil
  :groups N --> return Nth group for `parsec-re'."
  #+END_EXAMPLE

  So instead of returning "b" as the result, the following code returns 2:
  #+BEGIN_SRC elisp
  (parsec-with-input "ab"
    (parsec-ch ?a)
    (parsec-query (parsec-ch ?b) :beg))
  #+END_SRC

  Returning a point means that you can also incorporate =parsec.el= with Emacs
  Lisp functions that can operate on points/regions, such as =goto-char= and
  =kill-region=.

  =:group= can be specified when using =parsec-re=:
  #+BEGIN_SRC elisp
  (parsec-with-input "ab"
    (parsec-query (parsec-re "\\(a\\)\\(b\\)") :group 2))
  #+END_SRC

  The above code will return "b" instead of "ab".
* Error Messages

  =parsec.el= implements a simple error handling mechanism. When an error
  happens, it will show how the parser fails.

  For example, the following code fails:
  #+BEGIN_SRC elisp
  (parsec-with-input "aac"
    (parsec-count 2 (parsec-ch ?a))
    (parsec-ch ?b))
  #+END_SRC

  The return value is:
  #+BEGIN_SRC elisp
  (parsec-error . "Found \"c\" -> Expected \"b\"")
  #+END_SRC

  This also works when parser combinators fail:
  #+BEGIN_SRC elisp
  (parsec-with-input "a"
    (parsec-or (parsec-ch ?b)
               (parsec-ch ?c)))
  #+END_SRC

  The return value is:
  #+BEGIN_SRC elisp
  (parsec-error . "None of the parsers succeeds:
	Found \"a\" -> Expected \"c\"
	Found \"a\" -> Expected \"b\"")
  #+END_SRC

  If an error occurs, the return value is a cons cell that contains the error
  message in its =cdr=. Compared to Haskell's Parsec, it's really simple, but at
  least the error message could tell us some information. Yeah, not perfect but
  usable.

  To test whether a parser returns an error, use =parsec-error-p=. If it returns
  an error, you can use =parsec-error-str= to retrieve the error message as a
  string.

  You can decide what to do based on the return value of a parser:
  #+BEGIN_SRC elisp
  (let ((res (parsec-with-input "hello"
               (parsec-str "world"))))
    (if (parsec-error-p res)
        (message "Parser failed:\n%s" (parsec-error-str res))
      (message "Parser succeeded by returning %s" res)))
  #+END_SRC

* Acknowledgement
  - Daan Leijen for Haskell's Parsec
  - [[https://github.com/jwiegley/][John Wiegley]] for [[https://github.com/jwiegley/emacs-pl][emacs-pl]]
