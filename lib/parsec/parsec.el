;;; parsec.el --- Parser combinator library  -*- lexical-binding: t; -*-

;; Copyright (C) 2016  Free Software Foundation, Inc.

;; Author: Junpeng Qiu <qjpchmail@gmail.com>
;; Maintainer: Junpeng Qiu <qjpchmail@gmail.com>
;; URL: https://github.com/cute-jumper/parsec.el
;; Version: 0.1.3
;; Package-Requires: ((emacs "24") (cl-lib "0.5"))
;; Keywords: extensions

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

;;                              _____________

;;                                PARSEC.EL

;;                               Junpeng Qiu
;;                              _____________


;; Table of Contents
;; _________________

;; 1 Overview
;; 2 Parsing Functions & Parser Combinators
;; .. 2.1 Basic Parsing Functions
;; .. 2.2 Parser Combinators
;; .. 2.3 Parser Utilities
;; .. 2.4 Variants that Return a String
;; 3 Code Examples
;; 4 Write a Parser: a Simple CSV Parser
;; 5 More Parser Examples
;; 6 Change the Return Values using `parsec-query'
;; 7 Error Messages
;; 8 Acknowledgement


;; A parser combinator library for Emacs Lisp similar to Haskell's Parsec
;; library.


;; 1 Overview
;; ==========

;;   This work is based on [John Wiegley]'s [emacs-pl]. The original
;;   [emacs-pl] is awesome, but I found following problems when I tried to
;;   use it:

;;   - It only contains a very limited set of combinators
;;   - Some of its functions (combinators) have different behaviors than
;;     their Haskell counterparts
;;   - It can't show error messages when parsing fails

;;   So I decided to make a new library on top of it. This library,
;;   however, contains most of the parser combinators in
;;   `Text.Parsec.Combinator', which should be enough in most use cases. Of
;;   course more combinators can be added if necessary! Most of the parser
;;   combinators have the same behavior as their Haskell counterparts.
;;   `parsec.el' also comes with a simple error handling mechanism so that
;;   it can display an error message showing how the parser fails.

;;   So we can

;;   - use these parser combinators to write parsers easily from scratch in
;;     Emacs Lisp like what we can do in Haskell
;;   - port existing Haskell program using Parsec to its equivalent Emacs
;;     Lisp program easily


;; [John Wiegley] https://github.com/jwiegley/

;; [emacs-pl] https://github.com/jwiegley/emacs-pl


;; 2 Parsing Functions & Parser Combinators
;; ========================================

;;   We compare the functions and macros defined in this library with their
;;   Haskell counterparts, assuming you're already familiar with Haskell's
;;   Parsec. If you don't have any experience with parser combinators, look
;;   at the docstrings of these functions and macros and try them to see
;;   the results! They are really easy to learn and use!

;;   The *Usage* column for each function/combinator in the following
;;   tables is much simplified. Check the docstring of the
;;   function/combinator to see the full description.


;; 2.1 Basic Parsing Functions
;; ~~~~~~~~~~~~~~~~~~~~~~~~~~~

;;   These parsing functions are used as the basic building block for a
;;   parser. By default, their return value is a *string*.

;;    parsec.el               Haskell's Parsec  Usage
;;   -------------------------------------------------------------------------------------------------
;;    parsec-ch               char              parse a character
;;    parsec-any-ch           anyChar           parse an arbitrary character
;;    parsec-satisfy          satisfy           parse a character satisfying a predicate
;;    parsec-newline          newline           parse '\n'
;;    parsec-crlf             crlf              parse '\r\n'
;;    parsec-eol              eol               parse newline or CRLF
;;    parsec-eof, parsec-eob  eof               parse end of file
;;    parsec-eol-or-eof       *N/A*             parse EOL or EOL
;;    parsec-re               *N/A*             parse using a regular expression
;;    parsec-one-of           oneOf             parse one of the characters
;;    parsec-none-of          noneOf            parse any character other than the supplied ones
;;    parsec-str              *N/A*             parse a string but consume input only when successful
;;    parsec-string           string            parse a string and consume input for partial matches
;;    parsec-num              *N/A*             parse a number
;;    parsec-letter           letter            parse a letter
;;    parsec-digit            digit             parse a digit

;;   Note:
;;   - `parsec-str' and `parsec-string' are different. `parsec-string'
;;     behaves the same as `string' in Haskell, and `parsec-str' is more
;;     like combining `string' and `try' in Haskell. Personally I found
;;     `parsec-str' easier to use because `parsec-str' is "atomic", which
;;     is similar to `parsec-ch'.
;;   - Use the power of regular expressions provided by `parsec-re' and
;;     simplify the parser!


;; 2.2 Parser Combinators
;; ~~~~~~~~~~~~~~~~~~~~~~

;;   These combinators can be used to combine different parsers.

;;    parsec.el                  Haskell's Parsec  Usage
;;   -----------------------------------------------------------------------------------------------------------
;;    parsec-or                  choice            try the parsers until one succeeds
;;    parsec-try                 try               try parser and consume no input when an error occurs
;;    parsec-lookahead           lookahead         try parser and consume no input when successful
;;    parsec-peek                try && lookahead  try parser without comsuming any input
;;    parsec-peek-p              try && lookahead  same as parsec-peek except the return value for failure
;;    parsec-with-error-message  <?> (similar)     use the new error message when an error occurs
;;    parsec-many                many              apply the parser zero or more times
;;    parsec-many1               many1             apply the parser one or more times
;;    parsec-many-till           manyTill          apply parser zero or more times until end succeeds
;;    parsec-until               *N/A*             parse until end succeeds
;;    parsec-not-followed-by     notFollowedBy     succeed when the parser fails
;;    parsec-endby               endby             apply parser zero or more times, separated and ended by end
;;    parsec-sepby               sepby             apply parser zero or more times, separated by sep
;;    parsec-between             between           apply parser between open and close
;;    parsec-count               count             apply parser n times
;;    parsec-option              option            apply parser, if it fails, return opt
;;    parsec-optional            *N/A*             apply parser zero or one time and return the result
;;    parsec-optional*           optional          apply parser zero or one time and discard the result
;;    parsec-optional-maybe      optionMaybe       apply parser zero or one time and return the result in Maybe

;;   Note:
;;   - `parsec-or' can also be used to replace `<|>'.
;;   - `parsec-with-error-message' is slightly different from `<?>'. It
;;     will replace the error message even when the input is consumed.
;;   - By default, `parsec-many-till' behaves as Haskell's `manyTill'.
;;     However, `parsec-many-till' and `parsec-until' can accept an
;;     optional argument to specify which part(s) to be returned. You can
;;     use `:both' or `:end' as the optional argument to change the default
;;     behavior. See the docstrings for more information.


;; 2.3 Parser Utilities
;; ~~~~~~~~~~~~~~~~~~~~

;;   These utilities can be used together with parser combinators to build
;;   a parser and ease the translation process if you're trying to port an
;;   existing Haskell program.

;;    parsec.el                         Haskell's Parsec  Usage
;;   -------------------------------------------------------------------------------------------------------------
;;    parsec-and                        do block          try all parsers and return the last result
;;    parsec-return                     do block          try all parsers and return the first result
;;    parsec-ensure                     *N/A*             quit the parsing when an error occurs
;;    parsec-ensure-with-error-message  *N/A*             quit the parsing when an error occurs with new message
;;    parsec-collect                    sequence          try all parsers and collect the results into a list
;;    parsec-collect*                   *N/A*             try all parsers and collect non-nil results into a list
;;    parsec-start                      parse             entry point
;;    parsec-parse                      parse             entry point (same as parsec-start)
;;    parsec-with-input                 parse             perform parsers on input
;;    parsec-from-maybe                 fromMaybe         retrieve value from Maybe
;;    parsec-maybe-p                    *N/A*             is a Maybe value or not
;;    parsec-query                      *N/A*             change the parser's return value


;; 2.4 Variants that Return a String
;; ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

;;   By default, the macros/functions that return multiple values will put
;;   the values into a list. These macros/functions are:
;;   - `parsec-many'
;;   - `parsec-many1'
;;   - `parsec-many-till'
;;   - `parsec-until'
;;   - `parsec-count'
;;   - `parsec-collect' and `parsec-collect*'

;;   They all have a variant that returns a string by concatenating the
;;   results in the list:
;;   - `parsec-many-as-string' or `parsec-many-s'
;;   - `parsec-many1-as-string' or `parsec-many1-s'
;;   - `parsec-many-till-as-string' or `parsec-many-till-s'
;;   - `parsec-until-as-string' or `parsec-until-s'
;;   - `parsec-collect-as-string' or `parsec-collect-s'
;;   - `parsec-count-as-string' or `parsec-count-s'

;;   The `*-s' and `*-as-string' variants are the same, except the `*-s'
;;   variants have a shorter name. Using these `*-s' functions are
;;   recommended if you're dealing with strings very frequently in your
;;   code. These variants accept the same arguments and have the same
;;   behavior as their original counterpart that returns a list. The only
;;   difference is the return value.


;; 3 Code Examples
;; ===============

;;   Some very simple examples are given here. You can see many code
;;   examples in the test files in this GitHub repo.

;;   The following code extract the "hello" from the comment:
;;   ,----
;;   | (parsec-with-input "/* hello */"
;;   |   (parsec-string "/*")
;;   |   (parsec-many-till-as-string (parsec-any-ch)
;;   |                               (parsec-try
;;   |                                (parsec-string "*/"))))
;;   `----

;;   The following Haskell program does a similar thing:
;;   ,----
;;   | import           Text.Parsec
;;   |
;;   | main :: IO ()
;;   | main = print $ parse p "" "/* hello */"
;;   |   where
;;   |     p = do string "/*"
;;   |            manyTill anyChar (try (string "*/"))
;;   `----

;;   The following code returns the "aeiou" before "end":
;;   ,----
;;   | (parsec-with-input "if aeiou end"
;;   |   (parsec-str "if ")
;;   |   (parsec-return
;;   |       (parsec-many-as-string (parsec-one-of ?a ?e ?i ?o ?u))
;;   |     (parsec-str " end")))
;;   `----


;; 4 Write a Parser: a Simple CSV Parser
;; =====================================

;;   You can find the code in `examples/simple-csv-parser.el'. The code is
;;   based on the Haskell code in [Using Parsec].

;;   An end-of-line should be a string `\n'. We use `(parsec-str "\n")' to
;;   parse it (Note that since `\n' is also one character, `(parsec-ch
;;   ?\n)' also works). Some files may not contain a newline at the end,
;;   but we can view end-of-file as the end-of-line for the last line, and
;;   use `parsec-eof' (or `parsec-eob') to parse the end-of-file. We use
;;   `parsec-or' to combine these two combinators:
;;   ,----
;;   | (defun s-csv-eol ()
;;   |   (parsec-or (parsec-str "\n")
;;   |              (parsec-eof)))
;;   `----

;;   A CSV file contains many lines and ends with an end-of-file. Use
;;   `parsec-return' to return the result of the first parser as the
;;   result.
;;   ,----
;;   | (defun s-csv-file ()
;;   |   (parsec-return (parsec-many (s-csv-line))
;;   |     (parsec-eof)))
;;   `----

;;   A CSV line contains many CSV cells and ends with an end-of-line, and
;;   we should return the cells as the results:
;;   ,----
;;   | (defun s-csv-line ()
;;   |   (parsec-return (s-csv-cells)
;;   |     (s-csv-eol)))
;;   `----

;;   CSV cells is a list, containing the first cell and the remaining
;;   cells:
;;   ,----
;;   | (defun s-csv-cells ()
;;   |   (cons (s-csv-cell-content) (s-csv-remaining-cells)))
;;   `----

;;   A CSV cell consists any character that is not =,= or `\n', and we use
;;   the `parsec-many-as-string' variant to return the whole content as a
;;   string instead of a list of single-character strings:
;;   ,----
;;   | (defun s-csv-cell-content ()
;;   |   (parsec-many-as-string (parsec-none-of ?, ?\n)))
;;   `----

;;   For the remaining cells: if followed by a comma =,=, we try to parse
;;   more csv cells. Otherwise, we should return the `nil':
;;   ,----
;;   | (defun s-csv-remaining-cells ()
;;   |   (parsec-or (parsec-and (parsec-ch ?,) (s-csv-cells)) nil))
;;   `----

;;   OK. Our parser is almost done. To begin parsing the content in buffer
;;   `foo', you need to wrap the parser inside `parsec-start' (or
;;   `parsec-parse'):
;;   ,----
;;   | (with-current-buffer "foo"
;;   |   (goto-char (point-min))
;;   |   (parsec-parse
;;   |    (s-csv-file)))
;;   `----

;;   If you want to parse a string instead, we provide a simple wrapper
;;   macro `parsec-with-input', and you feed a string as the input and put
;;   arbitraty parsers inside the macro body. `parsec-start' or
;;   `parsec-parse' is not needed.
;;   ,----
;;   | (parsec-with-input "a1,b1,c1\na2,b2,c2"
;;   |   (s-csv-file))
;;   `----

;;   The above code returns:
;;   ,----
;;   | (("a1" "b1" "c1") ("a2" "b2" "c2"))
;;   `----

;;   Note that if we replace `parsec-many-as-string' with `parsec-many' in
;;   `s-csv-cell-content':
;;   ,----
;;   | (defun s-csv-cell-content ()
;;   |   (parsec-many (parsec-none-of ?, ?\n)))
;;   `----

;;   The result would be:
;;   ,----
;;   | ((("a" "1") ("b" "1") ("c" "1")) (("a" "2") ("b" "2") ("c" "2")))
;;   `----


;; [Using Parsec] http://book.realworldhaskell.org/read/using-parsec.html


;; 5 More Parser Examples
;; ======================

;;   I translate some Haskell Parsec examples into Emacs Lisp using
;;   `parsec.el'. You can see from these examples that it is very easy to
;;   write parsers using `parsec.el', and if you know haskell, you can see
;;   that basically I just translate the Haskell into Emacs Lisp one by one
;;   because most of them are just the same!

;;   You can find five examples under the `examples/' directory.

;;   Three of the examples are taken from the chapter [Using Parsec] in the
;;   book of [Real World Haskell]:
;;   - `simple-csv-parser.el': a simple csv parser with no support for
;;     quoted cells, as explained in previous section.
;;   - `full-csv-parser.el': a full csv parser
;;   - `url-str-parser.el': parser parameters in URL

;;   `pjson.el' is a translation of Haskell's [json library using Parsec].

;;   `scheme.el' is a much simplified Scheme parser based on [Write
;;   Yourself a Scheme in 48 Hours].

;;   They're really simple but you can see how this library works!


;; [Using Parsec] http://book.realworldhaskell.org/read/using-parsec.html

;; [Real World Haskell] http://book.realworldhaskell.org/read/

;; [json library using Parsec]
;; https://hackage.haskell.org/package/json-0.9.1/docs/src/Text-JSON-Parsec.html

;; [Write Yourself a Scheme in 48 Hours]
;; https://en.wikibooks.org/wiki/Write_Yourself_a_Scheme_in_48_Hours/


;; 6 Change the Return Values using `parsec-query'
;; ===============================================

;;   Parsing has side-effects such as forwarding the current point. In the
;;   original [emacs-pl], you can specify some optional arguments to some
;;   parsing functions (`pl-ch', `pl-re' etc.) to change the return values.
;;   In `parsec.el', these functions don't have such a behavior. Instead,
;;   we provide a unified interface `parsec-query', which accepts any
;;   parser, and changes the return value of the parser.

;;   You can speicify following arguments:
;;   ,----
;;   | :beg      --> return the point before applying the PARSER
;;   | :end      --> return the point after applying the PARSER
;;   | :nil      --> return nil
;;   | :groups N --> return Nth group for `parsec-re'."
;;   `----

;;   So instead of returning "b" as the result, the following code returns
;;   2:
;;   ,----
;;   | (parsec-with-input "ab"
;;   |   (parsec-ch ?a)
;;   |   (parsec-query (parsec-ch ?b) :beg))
;;   `----

;;   Returning a point means that you can also incorporate `parsec.el' with
;;   Emacs Lisp functions that can operate on points/regions, such as
;;   `goto-char' and `kill-region'.

;;   `:group' can be specified when using `parsec-re':
;;   ,----
;;   | (parsec-with-input "ab"
;;   |   (parsec-query (parsec-re "\\(a\\)\\(b\\)") :group 2))
;;   `----

;;   The above code will return "b" instead of "ab".


;; [emacs-pl] https://github.com/jwiegley/emacs-pl


;; 7 Error Messages
;; ================

;;   `parsec.el' implements a simple error handling mechanism. When an
;;   error happens, it will show how the parser fails.

;;   For example, the following code fails:
;;   ,----
;;   | (parsec-with-input "aac"
;;   |   (parsec-count 2 (parsec-ch ?a))
;;   |   (parsec-ch ?b))
;;   `----

;;   The return value is:
;;   ,----
;;   | (parsec-error . "Found \"c\" -> Expected \"b\"")
;;   `----

;;   This also works when parser combinators fail:
;;   ,----
;;   | (parsec-with-input "a"
;;   |   (parsec-or (parsec-ch ?b)
;;   |              (parsec-ch ?c)))
;;   `----

;;   The return value is:
;;   ,----
;;   | (parsec-error . "None of the parsers succeeds:
;;   |       Found \"a\" -> Expected \"c\"
;;   |       Found \"a\" -> Expected \"b\"")
;;   `----

;;   If an error occurs, the return value is a cons cell that contains the
;;   error message in its `cdr'. Compared to Haskell's Parsec, it's really
;;   simple, but at least the error message could tell us some information.
;;   Yeah, not perfect but usable.

;;   To test whether a parser returns an error, use `parsec-error-p'. If it
;;   returns an error, you can use `parsec-error-str' to retrieve the error
;;   message as a string.

;;   You can decide what to do based on the return value of a parser:
;;   ,----
;;   | (let ((res (parsec-with-input "hello"
;;   |              (parsec-str "world"))))
;;   |   (if (parsec-error-p res)
;;   |       (message "Parser failed:\n%s" (parsec-error-str res))
;;   |     (message "Parser succeeded by returning %s" res)))
;;   `----


;; 8 Acknowledgement
;; =================

;;   - Daan Leijen for Haskell's Parsec
;;   - [John Wiegley] for [emacs-pl]


;; [John Wiegley] https://github.com/jwiegley/

;; [emacs-pl] https://github.com/jwiegley/emacs-pl

;;; Code:

(require 'cl-lib)

(defgroup parsec nil
  "Parser combinators for Emacs Lisp"
  :group 'development)

(defvar parsec-last-error-message nil)

(defun parsec-eof-or-char-as-string ()
  (let ((c (char-after)))
    (if c
        (char-to-string c)
      "`EOF'")))

(defun parsec-error-new (msg)
  (cons 'parsec-error msg))

(defun parsec-error-new-2 (expected found)
  (parsec-error-new (format "Found \"%s\" -> Expected \"%s\""
                            found expected)))

(defun parsec-error-p (obj)
  (and (consp obj)
       (eq (car obj) 'parsec-error)))

(defalias 'parsec-error-str 'cdr)

(defsubst parsec-throw (msg)
  (throw 'parsec-failed msg))

(defun parsec-stop (&rest args)
  (parsec-throw
   (setq parsec-last-error-message
         (let ((msg (plist-get args :message))
               (expected (plist-get args :expected))
               (found (plist-get args :found)))
           (when (or (stringp msg)
                     (and (stringp expected)
                          (stringp found)))
             (if (stringp msg)
                 (parsec-error-new msg)
               (parsec-error-new-2 expected found)))))))

(defun parsec-ch (ch)
  "Parse a character CH."
  (let ((next-char (char-after)))
    (if (and (not (eobp))
             (char-equal next-char ch))
        (progn (forward-char 1)
               (char-to-string ch))
      (parsec-stop :expected (char-to-string ch)
                   :found (parsec-eof-or-char-as-string)))))

(defun parsec-any-ch ()
  "Parse any character."
  (if (not (eobp))
      (prog1 (char-to-string (char-after))
        (forward-char))
    (parsec-stop :expected "any char"
                 :found (parsec-eof-or-char-as-string))))

(defun parsec-satisfy (pred)
  "Parse any character that satisfies the predicate PRED."
  (let ((next-char (char-after)))
    (if (and (not (eobp))
             (funcall pred next-char))
        (progn (forward-char 1)
               (char-to-string next-char))
      (parsec-stop :expected (format "%s" pred)
                   :found (parsec-eof-or-char-as-string)))))

(defun parsec-re (regexp)
  "Parse the input matching the regular expression REGEXP."
  (if (looking-at regexp)
      (progn (goto-char (match-end 0))
             (match-string 0))
    (parsec-stop :expected regexp
                 :found (parsec-eof-or-char-as-string))))

(defun parsec-make-alternatives (chars)
  (let ((regex-head "")
        (regex-str "")
        (regex-end "")
        contains-caret-p)
    (dolist (c chars)
      (cond
       ((char-equal c ?\]) (setq regex-head "]"))
       ((char-equal c ?-) (setq regex-end "-"))
       ((char-equal c ?^) (setq contains-caret-p t))
       (t (setq regex-str (concat regex-str (char-to-string c))))))
    (when contains-caret-p
      (if (and
           (string-equal regex-end "-")
           (string-equal regex-head "")
           (string-equal regex-str ""))
          (setq regex-end "-^")
        (setq regex-str (concat regex-str "^"))))
    (concat regex-head regex-str regex-end)))

(defmacro parsec-one-of (&rest chars)
  "Succeed if the current character is in the supplied list of CHARS.
Return the parsed character.

>  (parsec-one-of ?a ?e ?i ?o ?u)"
  (let ((sexp '(parsec-or))
	(parsers (mapcar (lambda (c) (list #'parsec-ch c)) chars)))
    (append sexp parsers)))

(defun parsec-none-of (&rest chars)
  "Succeed if the current character not in the supplied list of CHARS.
Return the parsed character.

>  (parsec-none-of ?a ?e ?i ?o ?u)

Note this function is just a wrapper of `parsec-re'.  For complicated use cases,
consider using `parsec-re' instead."
  (parsec-re (format "[^%s]" (parsec-make-alternatives chars))))

(defsubst parsec-str (str)
  "Parse STR and only consume the input for an exact match.
Return the parsed string.

Note this function's behavior is different from the `string'
function of Haskll's Parsec.  Use `parsec-string' if you want the
same behavior as in Haskell."
  (parsec-re (regexp-quote str)))

(defsubst parsec-string (str)
  "Parse STR and consume the input even for a partial match.
Return the parsed string.

It is equivalent to calling `parsec-ch' multiples times so the
input will be consumed if the parser fails in the middle of the
STR.  This function has the same behavior as the `string' function
of Haskell's Parsec.  See also `parsec-str'."
  (mapc (lambda (c) (parsec-ch c)) str))

(defsubst parsec-num (num)
  "Parse the number NUM and return the parsed number as a string."
  (parsec-re (regexp-quote (number-to-string num))))

(defsubst parsec-letter ()
  "Parse any English letter."
  (parsec-re "[a-zA-Z]"))

(defsubst parsec-digit ()
  "Parse any digit."
  (parsec-re "[0-9]"))

(defmacro parsec-or (&rest parsers)
  "Try the PARSERS one by one.
If the current parser succeeds, return its results.  If the
current parser fails without consuming any input, try the next
parser if available.  This combinator fails if the current parser
fails after consuming some input or there is no more parsers."
  (let ((parser-sym (make-symbol "parser"))
        (error-sym (make-symbol "err"))
        (error-str-list-sym (make-symbol "err-list")))
    `(let (,error-str-list-sym ,parser-sym ,error-sym)
       (catch 'parsec-failed-or
         ,@(mapcar
            (lambda (parser)
              `(parsec-protect-atom parsec-or
                 (parsec-start
                  (throw 'parsec-failed-or
                         (parsec-eavesdrop-error ,error-sym
                             (parsec-make-atom parsec-or ,parser)
                           (push (parsec-error-str ,error-sym) ,error-str-list-sym))))))
            parsers)
         (parsec-stop
          :message
          (replace-regexp-in-string
           "\n" "\n\t"
           (concat "None of the parsers succeeds:\n"
                   (mapconcat #'identity ,error-str-list-sym "\n"))))))))

(defmacro parsec-and (&rest body)
  "Eval BODY sequentially and return the result of the last parser.
This combinator fails if one of the parsers fails."
  `(progn ,@body))

(defmacro parsec-return (first &rest body)
  "Eval FIRST and BODY sequentially and return the results of the first parser.
This combinator fails if one of the parsers fails."
  (declare (indent 1))
  `(prog1 ,first ,@body))

(defalias 'parsec-collect 'list
  "Collect the results of all the parsers OBJECTS into a list.")

(defun parsec-collect* (&rest args)
  "Collect the non-nil results of all the parsers ARGS into a list."
  (delq nil (apply #'parsec-collect args)))

(defmacro parsec-collect-as-string (&rest forms)
  "Collect the results of all the parsers FORMS as a string."
  `(parsec-list-to-string (parsec-collect ,@forms)))

(defalias 'parsec-collect-s 'parsec-collect-as-string)

(defmacro parsec-start (&rest forms)
  "Eval the parsers FORMS and return the results or a `parsec-error'.
This combinator should be used at the top level as the entry
point of your parsing program."
  `(catch 'parsec-failed ,@forms))

(defalias 'parsec-parse 'parsec-start)

(defmacro parsec-try (parser)
  "Try PARSER, and pretend that no input is consumed when an error occurs."
  (let ((orig-pt-sym (make-symbol "orig-pt"))
        (error-sym (make-symbol "err")))
    `(let ((,orig-pt-sym (point)))
       (parsec-eavesdrop-error ,error-sym
           (parsec-and ,parser)
         (goto-char ,orig-pt-sym)))))

(defmacro parsec-lookahead (parser)
  "Try PARSER, and pretend that no input is consumed when it succeeds."
  (let ((orig-pt-sym (make-symbol "orig-pt")))
    `(let ((,orig-pt-sym (point)))
       (parsec-return ,parser
         (goto-char ,orig-pt-sym)))))

(defsubst parsec--atom-tag (name)
  (intern (format "parsec-failed-at-half-%s" name)))

(defmacro parsec-protect-atom (name parser)
  "This must be used together with `parsec-make-atom'."
  (declare (indent 1))
  (let ((tag (parsec--atom-tag name)))
    `(catch 'parsec-failed-protect-atom
       (parsec-throw (catch ',tag
                       (throw 'parsec-failed-protect-atom ,parser))))))

(defmacro parsec-make-atom (name parser)
  (let ((orig-pt-sym (make-symbol "orig-pt"))
        (error-sym (make-symbol "err"))
        (tag (parsec--atom-tag name)))
    `(let ((,orig-pt-sym (point)))
       (parsec-eavesdrop-error ,error-sym
           ,parser
         (unless (= (point) ,orig-pt-sym)
           (throw ',tag ,error-sym))))))

(defmacro parsec-eavesdrop-error (error-sym parser &rest handler)
  (declare (indent 2))
  `(catch 'parsec-failed-eavesdrop-error
     (let ((,error-sym (parsec-start
                        (throw 'parsec-failed-eavesdrop-error ,parser))))
       ,@handler
       (parsec-throw ,error-sym))))

(defmacro parsec-with-error-message (msg &rest forms)
  "Use MSG as the error message if an error occurs when Evaling the FORMS."
  (declare (indent 1))
  `(parsec-eavesdrop-error _
       (parsec-and ,@forms)
     (parsec-throw (parsec-error-new ,msg))))

(defmacro parsec-ensure (&rest forms)
  "Exit the program immediately if FORMS fail."
  (let ((error-sym (make-symbol "err")))
    `(parsec-eavesdrop-error ,error-sym
         (parsec-and ,@forms)
       (error "%s" (parsec-error-str ,error-sym)))))

(defmacro parsec-ensure-with-error-message (msg &rest forms)
  "Exit the program immediately with MSG if FORMS fail."
  (declare (indent 1))
  `(parsec-ensure
    (parsec-with-error-message ,msg
      (parsec-and ,@forms))))

(defmacro parsec-many (parser)
  "Apply the PARSER zero or more times and return a list of the results."
  (let ((res-sym (make-symbol "results")))
    `(let (,res-sym)
       (parsec-protect-atom parsec-many
         (parsec-start
          (while (not (eobp))
            (push (parsec-make-atom parsec-many ,parser) ,res-sym))))
       (nreverse ,res-sym))))

(defmacro parsec-many1 (parser)
  "Apply the PARSER one or more times and return a list of the results."
  `(cons ,parser (parsec-many ,parser)))

(defsubst parsec-list-to-string (l)
  (if (stringp l)
      l
    (mapconcat #'identity l "")))

(defmacro parsec-many-as-string (parser)
  "Apply the PARSER zero or more times and return the results as a string."
  `(mapconcat #'identity (parsec-many ,parser) ""))

(defalias 'parsec-many-s 'parsec-many-as-string)

(defmacro parsec-many1-as-string (parser)
  "Apply the PARSER one or more times and return the results as a string."
  `(mapconcat #'identity (parsec-many1 ,parser) ""))

(defalias 'parsec-many1-s 'parsec-many1-as-string)

(defmacro parsec-many-till (parser end &optional type)
  "Apply PARSER zero or more times until END succeeds.
The return value is determined by TYPE.  If TYPE is `:both', return
the cons `(many . end)'.  If TYPE is `:end', return the result of END.
In other cases, return the result of PARSER.

Used to scan comments:

> (parsec-and
>   (parsec-str \"<--\")
>   (parsec-many-till (parsec-any-ch) (parsec-str \"-->\")))"

  (let ((res-sym (make-symbol "results"))
        (end-res-sym (make-symbol "end-result")))
    `(let ((,res-sym nil) ,end-res-sym)
       (setq ,end-res-sym
             (catch 'parsec-failed-many-till
               (while t
                 (parsec-or (throw 'parsec-failed-many-till ,end)
                            (push ,parser ,res-sym)))))
       (setq ,res-sym (nreverse ,res-sym))
       ,(cond
         ((eq type :both) `(cons ,res-sym ,end-res-sym))
         ((eq type :end) end-res-sym)
         (t res-sym)))))

(defmacro parsec-many-till-as-string (parser end &optional type)
  "Apply PARSER zero or more times until END succeeds.
Return the result of PARSER or END as a string.  TYPE has the same
meaning as `parsec-many-till'."
  (let ((res-sym (make-symbol "results")))
    (cond
     ((eq type :both)
      `(let ((,res-sym (parsec-many-till ,parser ,end ,type)))
         (cons (parsec-list-to-string (car ,res-sym))
               (parsec-list-to-string (cdr ,res-sym)))))
     (t
      `(parsec-list-to-string (parsec-many-till ,parser ,end ,type))))))

(defalias 'parsec-many-till-s 'parsec-many-till-as-string)

(defmacro parsec-until (parser &optional type)
  "Parse any characters until PARSER succeeds.
TYPE has the same meaning as `parsec-many-till'."
  `(parsec-many-till (parsec-any-ch) ,parser ,type))

(defmacro parsec-until-as-string (parser &optional type)
  "Parse any characters until PARSER succeeds.
Return the result of either part as a string.  TYPE has the same
meaning as `parsec-many-till'."
  `(parsec-many-till-as-string (parsec-any-ch) ,parser ,type))

(defalias 'parsec-until-s 'parsec-until-as-string)

(defmacro parsec-not-followed-by (parser)
  "Succeed only when PARSER fails.  Consume no input."
  (let ((res-sym (make-symbol "results")))
    `(catch 'parsec-failed-not-followed-by-out
       (parsec-try
        (let ((,res-sym
               (catch 'parsec-failed-not-followed-by-in
                 (throw 'parsec-failed-not-followed-by-out
                        (parsec-or (throw 'parsec-failed-not-followed-by-in (parsec-try ,parser))
                                   nil)))))
          (parsec-stop :message (format "Unexpected followed by: %s" ,res-sym)))))))

(defmacro parsec-endby (parser end)
  "Parse zero or more occurrences of PARSER, separated and ended by END.
Return a list of values returned by PARSER."
  `(parsec-many (parsec-return ,parser
                  ,end)))

(defmacro parsec-sepby (parser separator)
  "Parse zero or more occurrences of PARSER, separated by SEPARATOR.
Return a list of values returned by PARSER."
  `(parsec-or
    (cons ,parser (parsec-many (parsec-and ,separator ,parser)))
    nil))

(defmacro parsec-between (open close parser)
  "Parse OPEN, followed by PARSER and CLOSE.
Return the value returned by PARSER."
  `(parsec-and
     ,open
     (parsec-return ,parser
       ,close)))

(defmacro parsec-count (n parser)
  "Parse N occurrences of PARSER.
Return a list of N values returned by PARSER."
  (let ((res-sym (make-symbol "results")))
    `(let (,res-sym)
       (dotimes (_ ,n ,res-sym)
         (push ,parser ,res-sym))
       (nreverse ,res-sym))))

(defmacro parsec-count-as-string (n parser)
  "Parse N occurrences of PARSER.
Return the N values returned by PARSER as a string."
  `(parsec-list-to-string (parsec-count ,n ,parser)))

(defalias 'parsec-count-s 'parsec-count-as-string)

(defmacro parsec-option (opt parser)
  "Try to apply PARSER and return OPT if PARSER fails without comsuming input."
  `(parsec-or ,parser ,opt))

(defmacro parsec-optional (parser)
  "Apply PARSER zero or one time.  Fail if PARSER fails after consuming input.
Return the result of PARSER or nil.

Note this combinator doesn't discard the result of PARSER so it is
different from the `optional' function of Haskell's Parsec.  If
you want the Haskell's behavior, use `parsec-optional*'."
  `(parsec-or ,parser nil))

(defmacro parsec-optional* (parser)
  "Apply PARSER zero or one time and discard the result.
Fail if PARSER fails after consuming input.

This combinator has the same behavior as the `optional' function of
Haskell's Parsec."
  `(parsec-and ,parser nil))

(defmacro parsec-peek (parser)
  "Apply PARSER without consuming any input.
When PARSER succeeds, the result of the PARSER is returned.
Otherwise, the return value is an error.  Use `parsec-error-p' on
the return value to see whether the PARSER fails or not.  Use
`parsec-peek-p' if you want nil to be returned when PARSER fails.

This is a shortcut of combining `parsec-start', `parsec-try' and
`parsec-lookahead'.  Since arbitrary parser is allowed, this
function can be viewed as a more powerful version of `looking-at'
in Emacs Lisp."
  `(parsec-start
    (parsec-try
     (parsec-lookahead ,parser))))

(defmacro parsec-peek-p (parser)
  "Same as `parsec-peek' except a nil is returned when the PARSER fails."
  (let ((res-sym (make-symbol "res")))
    `(let ((,res-sym (parsec-peek ,parser)))
       (unless (parsec-error-p ,res-sym)
         ,res-sym))))

(defmacro parsec-query (parser &rest args)
  "Get an alternative return value of the PARSER specified by the ARGS.

The args can be in the following forms:

    :beg      --> return the point before applying the PARSER
    :end      --> return the point after applying the PARSER
    :nil      --> return nil
    :groups N --> return Nth group for `parsec-re'."
  (let ((orig-pt-sym (make-symbol "orig-pt"))
        (res-sym (make-symbol "results")))
    `(let ((,orig-pt-sym (point))
           (,res-sym ,parser))
       ,(cond
         ((memq :beg args) orig-pt-sym)
         ((memq :end args) '(point))
         ((memq :nil args) nil)
         ((and (memq :group args)
               (consp parser)
               (eq (car parser) 'parsec-re))
          (let ((group
                 (cl-loop named outer for arg on args
                          when (eq (car arg) :group) do
                          (cl-return-from outer (cadr arg)))))
            (if (and group (integerp group))
                `(match-string ,group)
              (error "Invalid query :group %s" group))))
         (t res-sym)))))

(defsubst parsec-just (x) (cons 'Just x))

(defconst parsec-nothing 'Nothing)

(defun parsec-maybe-p (x)
  (or (eq x parsec-nothing)
      (and
       (consp x)
       (eq (car x) 'Just))))

(defun parsec-from-maybe (x)
  "Retrieve the value from Maybe monad X.
If X is `(Just . p)', return p. Otherwise return nil."
  (and (consp x)
       (eq (car x) 'Just)
       (cdr x)))

(defmacro parsec-optional-maybe (parser)
  "Apply PARSER zero or one time and return the value in a Maybe monad.
If PARSER fails without consuming any input, return `parsec-nothing'.
Otherwise, return `(Just . p)' where p is the result of PARSER."
  (let ((res-sym (make-symbol "result")))
    `(let ((,res-sym (parsec-optional ,parser)))
       (if ,res-sym
           (parsec-just ,res-sym)
         parsec-nothing))))

(defun parsec-newline ()
  "Parse a newline character \"\\n\"."
  (parsec-ch ?\n))

(defun parsec-crlf ()
  "Parse a carriage return (\'\\r\') followed by a newline \"\\n\"."
  (parsec-and (parsec-ch ?\r) (parsec-ch ?\n)))

(defun parsec-eol ()
  "Parse a newline or a CRLF and return \"\\n\"."
  (parsec-or (parsec-newline) (parsec-crlf)))

(defun parsec-eob ()
  "Indicate the end of file (buffer)."
  (unless (eobp)
    (parsec-stop :expected "`EOF'"
                 :found (parsec-eof-or-char-as-string))))

(defalias 'parsec-eof 'parsec-eob)

(defun parsec-eol-or-eof ()
  "Indicate either eol or eof."
  (parsec-or (parsec-eol) (parsec-eof)))

(defmacro parsec-with-input (input &rest parsers)
  "With INPUT, start parsing by applying PARSERS sequentially."
  (declare (indent 1))
  `(with-temp-buffer
     (insert ,input)
     (goto-char (point-min))
     (parsec-start
      ,@parsers)))

(provide 'parsec)
;;; parsec.el ends here
