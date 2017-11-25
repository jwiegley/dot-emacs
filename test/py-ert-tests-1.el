;; py-ert-tests.el --- Tests, some adapted from python.el -*- lexical-binding: t; -*- 

;; Copyright (C) 2013 Free Software Foundation, Inc.
;; Copyright (C) 2014-2015 Andreas Röhler, <andreas.roehler@online.de>

;; GNU Emacs is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; GNU Emacs is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;;; Code:

;; (require 'ert)

;; tests are expected to run from directory test

(defvar py-def-and-class-test-string "class kugel(object):
    zeit = time.strftime('%Y%m%d--%H-%M-%S')
    # zeit = time.strftime('%Y-%m-%d--%H-%M-%S')
    spiel = []
    gruen = [0]
    rot = [1, 3, 5, 7, 9, 12, 14, 16, 18, 19, 21, 23, 25, 27, 30, 32, 34, 36]

    def pylauf(self):
        \"\"\"Eine Doku fuer pylauf\"\"\"
        ausgabe = [\" \",\" \",\" \",\" \",\" \",\" \",\" \",\" \", \" \"]

        ausgabe[0] = treffer
        fertig = ''
#        print \"treffer, schwarz, gruen, rot, pair, impair, passe, manque, spiel\"
        if treffer in gruen:
            # print \"0, Gruen\"
            ausgabe[1] = treffer
            ausgabe[2] = treffer

        elif treffer in schwarz:
            # print \"%i, Schwarz\" % (treffer)
            ausgabe[1] = treffer

if __name__ == \"__main__\":
    main()
")

(setq ert-test-default-buffer "*Python*")

(add-to-list 'load-path default-directory)

(ert-deftest py-ert-electric-kill-backward-bracket-test ()
  (let ((py-electric-kill-backward-p t))
    (py-test-with-temp-buffer
      "mystring[0:1]"
      (py-electric-backspace 1)
      (should (eq ?\] (char-after))))))

(ert-deftest py-ert-electric-kill-backward-region-test ()
  (let ((py-electric-kill-backward-p t)
	(delete-active-region t)
	(transient-mark-mode t))
    (py-test-with-temp-buffer
	"mystring[0:1]     "
      (skip-chars-backward " \t\r\n\f")
      (set-mark (point))
      (goto-char (point-max))
      (py-electric-backspace 1)
      (should (eq ?\] (char-before))))))

(ert-deftest py-ert-electric-delete-eob-test ()
  (let ((py-electric-kill-backward-p t)
	(delete-active-region t)
	(transient-mark-mode t))
    (py-test-with-temp-buffer
	"mystring[0:1]     "
      (skip-chars-backward " \t")
      (set-mark (point))
      (skip-chars-forward " \t")
      (py-electric-delete)
      (should (eobp)))))

(ert-deftest py-ert-electric-delete-test ()
  (let ((py-electric-kill-backward-p t)
	(delete-active-region t)
	(transient-mark-mode t))
    (py-test-with-temp-buffer
	"mystring[0:1]     "
      (set-mark (point))
      (skip-chars-backward " \t\r\n\f")
      (py-electric-delete)
      (should (eobp)))))

(ert-deftest py-ert-electric-kill-backward-paren-test ()
  (let ((py-electric-kill-backward-p t))
    (py-test-with-temp-buffer
      "mystring(\"asdf\")"
      (py-electric-backspace 1)
      (should (eq ?\) (char-after)))
      )))

(ert-deftest py-ert-electric-kill-backward-brace-test ()
  (let ((py-electric-kill-backward-p t))
    (py-test-with-temp-buffer
      "mystring{0 . 1}"
      (py-electric-backspace 1)
      (should (eq ?\} (char-after))))))

(ert-deftest py-ert-indent-dedenters-1 ()
  "Check all dedenters."

  (py-test-with-temp-buffer-point-min
    "def foo(a, b, c):
    if a:
        print (a)
    elif b:
        print (b)
    else:
        try:
            print (c.pop())
        except (IndexError, AttributeError):
            print (c)
        finally:
            print ('nor a, nor b are true')
"
   (search-forward "if a:")
   (should (= (py-compute-indentation) 4))
   (search-forward "print (a)")
   (should (= (py-compute-indentation) 8))
   (search-forward "elif b:")
   (should (= (py-compute-indentation) 4))
   (search-forward "print (b)")
   (should (= (py-compute-indentation) 8))
   (search-forward "else:")
   (should (= (py-compute-indentation) 4))
   (search-forward "try:")
   (should (= (py-compute-indentation) 8))
   (search-forward "print (c.pop())")
   (should (= (py-compute-indentation) 12))
   (search-forward "except (IndexError, AttributeError):")
   (should (= (py-compute-indentation) 8))
   (search-forward "print (c)")
   (should (= (py-compute-indentation) 12))
   (search-forward "finally:")
   (should (= (py-compute-indentation) 8))
   (search-forward "print ('nor a, nor b are true')")
   (should (= (py-compute-indentation) 12))))

(ert-deftest py-ert-indent-after-backslash-lp-852052-1 ()
  "The most common case."
  (py-test-with-temp-buffer-point-min
      "
from foo.bar.baz import something, something_1 \\
     something_2 something_3, \\
     something_4, something_5
"
    (search-forward "from foo.bar.baz import something, something_1")
    (should (= (py-compute-indentation) 0))
    (search-forward "something_2 something_3,")
    (should (= (py-compute-indentation) 5))
    (search-forward "something_4, something_5")
    (should (= (py-compute-indentation) 5))))

(ert-deftest py-ert-indent-closing ()
  ""
  (py-test-with-temp-buffer-point-min
   "
my_list = [
    1, 2, 3,
    4, 5, 6,
    ]
result = some_function_that_takes_arguments(
    'a', 'b', 'c',
    'd', 'e', 'f',
    )
"
   (goto-char 40)
   (should (eq 4 (py-compute-indentation)))
   (goto-char 129)
   (should (eq 4 (py-compute-indentation)))))

(setq py-ert-moves-text "class OrderedDict1(dict):
    \"\"\"
    This implementation of a dictionary keeps track of the order
    in which keys were inserted.
    \"\"\"

    def __init__(self, d={}):
        self._keys = d.keys()
        dict.__init__(self, d)

    def f():
        \"\"\"
        class for in 'for in while with blah'
        \"\"\"
        if a:

            ar_atpt_python_list_roh = ([
                'python-expression',

            # def ar_thingatpt_write_lists (&optional datei):
            'python-partial-expression',
            'python-statement',
            ])
        elif b:
            pass
        else b:
            pass

''' asdf' asdf asdf asdf asdf asdfasdf asdfasdf a asdf asdf asdf asdfasdfa asdf asdf asdf asdf asdf' asdf asdf asdf asdf asdfasdf asdfasdf a asdf asdf asdf asdfasdfa asdf asdf asdf asdf
'''
")

(ert-deftest py-ert-moves-up-class-bol-1 ()
  (py-test-with-temp-buffer-point-min
      py-ert-moves-text
    (goto-char 410)
    (should (eq 1 (py-up-class-bol)))))

(ert-deftest py-ert-moves-up-def-or-class-bol-1 ()
  (py-test-with-temp-buffer-point-min
      py-ert-moves-text
    (goto-char 410)
    (py-up-def-or-class)
    (should (looking-at "class"))))

(ert-deftest py-ert-moves-up-minor-block-bol-1 ()
  (py-test-with-temp-buffer-point-min
      py-ert-moves-text
    (goto-char 410)
    (py-up-minor-block-bol)
    (should (bobp))))

(ert-deftest py-ert-moves-up-block-bol-1 ()
  (py-test-with-temp-buffer-point-min
      py-ert-moves-text
    (goto-char 410)
    (py-up-block-bol)
    (should (looking-at " +def f():"))))

(ert-deftest py-ert-moves-up-block-2 ()
  (py-test-with-temp-buffer
      py-ert-moves-text
    (search-backward "pass")
    (py-up-block)
    (should (looking-at "def f():"))))

(ert-deftest py-ert-moves-up-minor-block-bol-2 ()
  (py-test-with-temp-buffer
      "class OrderedDict1(dict):
    \"\"\"
    This implementation of a dictionary keeps track of the order
    in which keys were inserted.
    \"\"\"

    def __init__(self, d={}):
        self._keys = d.keys()
        dict.__init__(self, d)

    def f():
        \"\"\"
        class for in 'for in while with blah'
        \"\"\"
        if a:
        # if c
            if b:
                pass
"
    (py-up-minor-block)
    (should (looking-at "if a:"))))

(ert-deftest py-ert-moves-up-block-bol-2 ()
  (py-test-with-temp-buffer
      py-ert-moves-text
    (search-backward "pass")
    (py-up-block-bol)
    (should (looking-at " +def f"))))

(ert-deftest py-ert-moves-up-def-bol-2 ()
  (py-test-with-temp-buffer-point-min
      py-ert-moves-text
    (goto-char 410)
    (py-up-def-bol)
    (should (bobp))))

(ert-deftest py-ert-moves-up-class-bol-2 ()
  (py-test-with-temp-buffer-point-min
      py-ert-moves-text
    (goto-char 410)
    (should (eq 1 (py-up-class)))))

(ert-deftest py-ert-moves-up-def-or-class-bol-2 ()
  (py-test-with-temp-buffer
      py-ert-moves-text
    (search-backward "pass")
    (py-up-def-or-class)
    (should (looking-at "class"))))

(ert-deftest py-ert-moves-down-block-bol-1 ()
  (py-test-with-temp-buffer-point-min
      py-ert-moves-text
    (goto-char 264)
    (py-down-block-bol)
    (should (bolp))))

(ert-deftest py-ert-moves-down-def-bol-1 ()
  (py-test-with-temp-buffer
      py-ert-moves-text
    (search-backward "__init__")
    (py-down-def-bol)
    (should (bolp)) 
    (should (looking-at " +def"))))

(ert-deftest py-ert-down-class-bol-1 ()
  (py-test-with-temp-buffer-point-min
      py-ert-moves-text
    (goto-char 410)
    (should (not (py-down-class-bol)))))

(ert-deftest py-ert-moves-down-def-or-class-bol-1 ()
  (py-test-with-temp-buffer
      py-ert-moves-text
    (search-backward "__init__")
    (py-down-def-or-class-bol)
    (should (bolp))
    (should (looking-at " +def"))))

(ert-deftest py-ert-moves-down-block-1 ()
  (py-test-with-temp-buffer
      py-ert-moves-text
    (search-backward "__init__") 
    (py-down-block)
    (should (looking-at "def"))))

(ert-deftest py-ert-moves-down-block-bol-2 ()
  (py-test-with-temp-buffer
      py-ert-moves-text
    (search-backward "__init__") 
    (py-down-block-bol)
    (should (bolp))
    (should (looking-at " +def"))))

(ert-deftest py-ert-moves-down-minor-block-1 ()
  (py-test-with-temp-buffer
      "class OrderedDict1(dict):
    \"\"\"
    This implementation of a dictionary keeps track of the order
    in which keys were inserted.
    \"\"\"

    def __init__(self, d={}):
        self._keys = d.keys()
        dict.__init__(self, d)

    def f():
        \"\"\"
        class for in 'for in while with blah'
        \"\"\"
        if a:

            ar_atpt_python_list_roh = ([
                'python-expression',

            # def ar_thingatpt_write_lists (&optional datei):
            'python-partial-expression',
            'python-statement',
            ])
        if b:
            pass"
    (switch-to-buffer (current-buffer)) 
    (search-backward "a:") 
    (py-down-minor-block)
    (should (eq (char-after) ?i))))

(ert-deftest py-ert-moves-down-minor-block-bol-1 ()
  (py-test-with-temp-buffer
      "class OrderedDict1(dict):
    \"\"\"
    This implementation of a dictionary keeps track of the order
    in which keys were inserted.
    \"\"\"

    def __init__(self, d={}):
        self._keys = d.keys()
        dict.__init__(self, d)

    def f():
        \"\"\"
        class for in 'for in while with blah'
        \"\"\"
        if a:

            ar_atpt_python_list_roh = ([
                'python-expression',

            # def ar_thingatpt_write_lists (&optional datei):
            'python-partial-expression',
            'python-statement',
            ])
        if b:
            pass"
    (search-backward "__init__") 
    (py-down-minor-block-bol)
    (should (bolp))
    (should (looking-at " +if"))))

(ert-deftest py-ert-moves-down-def-1 ()
  (py-test-with-temp-buffer-point-min
      py-ert-moves-text
    (should (py-down-def))))

(ert-deftest py-ert-moves-down-def-2 ()
  (py-test-with-temp-buffer
      py-ert-moves-text
    (search-backward "__init__")
    (py-down-def)
    (should (eq (char-after) ?d))))

(ert-deftest py-ert-moves-down-class-1 ()
  (py-test-with-temp-buffer-point-min
      py-ert-moves-text
    (goto-char 410)
    (should (not (py-down-class)))))

(ert-deftest py-ert-moves-down-def-or-class-1 ()
  (py-test-with-temp-buffer
      py-ert-moves-text
    (search-backward "__init__")
    (py-down-def-or-class)
    (should (eq (char-after) ?d))))

(ert-deftest py-ert-moves-backward-statement-bol-1 ()
  (py-test-with-temp-buffer-point-min
      py-ert-moves-text
    (goto-char 410)
    (should (eq 332 (py-backward-statement-bol)))))

(ert-deftest py-ert-moves-backward-block-bol-1 ()
  (py-test-with-temp-buffer-point-min
      py-ert-moves-text
    (goto-char 410)
    (indent-to 8)
    (should (eq 317 (py-backward-block-bol)))))

(ert-deftest py-ert-moves-backward-clause-bol-1 ()
  (py-test-with-temp-buffer-point-min
      py-ert-moves-text
    (goto-char 410)
    (indent-to 8)
    (should (eq 317 (py-backward-clause-bol)))))

(ert-deftest py-ert-moves-backward-block-or-clause-bol-1 ()
  (py-test-with-temp-buffer-point-min
      py-ert-moves-text
    (goto-char 410)
    (indent-to 8)
    (should (eq 317 (py-backward-block-or-clause-bol)))))

(ert-deftest py-ert-moves-backward-class-bol ()
  (py-test-with-temp-buffer
      py-ert-moves-text
    (should (eq 1 (py-backward-class-bol)))))

(ert-deftest py-ert-moves-backward-def-or-class-bol ()
  (py-test-with-temp-buffer-point-min
      py-ert-moves-text
    (goto-char 410)
    (indent-to 4)
    (py-backward-def-or-class-bol)
    (should (looking-at "^ +def"))))

(ert-deftest py-ert-moves-forward-clause-bol ()
  (py-test-with-temp-buffer-point-min
      py-ert-moves-text
    (goto-char 576)
    (should (eq 594 (py-forward-clause-bol)))))

(ert-deftest py-ert-moves-forward-block-or-clause-bol ()
  (py-test-with-temp-buffer-point-min
      py-ert-moves-text
    (goto-char 576)
    (should (eq 594 (py-forward-block-or-clause-bol)))))

(ert-deftest py-ert-moves-up-position-tests-4 ()
  (interactive)
  (py-test-with-temp-buffer
      py-kugel-text
    (search-backward "else:")
    (should (eq 190 (py--beginning-of-minor-block-position)))))

(ert-deftest py-ert-moves-up-position-tests-5 ()
  (interactive)
  (py-test-with-temp-buffer
      py-kugel-text
    (search-backward "else:")
    (end-of-line) 
    (should (eq 362 (py--beginning-of-clause-position)))))

(ert-deftest py-ert-moves-up-position-tests-6 ()
  (interactive)
  (py-test-with-temp-buffer
      py-kugel-text
    (search-backward "else:")
    (should (eq 362 (py--beginning-of-clause-position)))))

(ert-deftest py-ert-moves-up-position-tests-7 ()
  (interactive)
  (py-test-with-temp-buffer
      py-kugel-text
    (search-backward "else:")
    (should (eq 445 (py--end-of-clause-position)))))

(ert-deftest py-ert-moves-up-position-tests-8 ()
  (interactive)
  (py-test-with-temp-buffer
      py-kugel-text
    (search-backward "else:")
    (end-of-line) 
    (should (eq 362 (py--beginning-of-block-or-clause-position)))))

(ert-deftest py-ert-moves-up-position-tests-9 ()
  (interactive)
  (py-test-with-temp-buffer
      py-kugel-text
    (search-backward "else:")
    (should (eq 445 (py--end-of-block-or-clause-position)))))

(ert-deftest py-ert-moves-up-position-tests-10 ()
  (interactive)
  (py-test-with-temp-buffer
      py-kugel-text
    (search-backward "se:")
    (should (eq 445 (py--end-of-block-or-clause-position)))))

(ert-deftest py-ert-moves-up-position-tests-11 ()
  (interactive)
  (py-test-with-temp-buffer
      py-kugel-text
    (search-backward "se:")
    (should (eq 71 (py--beginning-of-def-position)))))

(ert-deftest py-ert-moves-up-position-tests-12 ()
  (interactive)
  (py-test-with-temp-buffer
      py-kugel-text
    (search-backward "self")
    (end-of-line)
    (py-forward-statement)
    (should (eq (char-before) ?\]))))

(ert-deftest py-ert-moves-up-position-tests-13 ()
  (interactive)
  (py-test-with-temp-buffer
      py-kugel-text
    (search-backward "se:")
    (should (eq 445 (py--end-of-def-position)))))

(ert-deftest py-ert-moves-up-position-tests-14 ()
  (interactive)
  (py-test-with-temp-buffer
      py-kugel-text
    (search-backward "se:")
    (should (eq 1 (py--beginning-of-class-position)))))

(ert-deftest py-ert-moves-up-position-tests-15 ()
  (interactive)
  (py-test-with-temp-buffer
      py-kugel-text
    (search-backward "se:")
    (should (eq 445 (py--end-of-class-position)))))

(ert-deftest py-ert-moves-up-position-tests-16 ()
  (interactive)
  (py-test-with-temp-buffer
      py-kugel-text
    (search-backward "se:")
    (should (eq 71 (py--beginning-of-def-or-class-position)))))

(ert-deftest py-ert-moves-up-position-tests-17 ()
  (interactive)
  (py-test-with-temp-buffer
      py-kugel-text
    (search-backward "se:")
    (should (eq 445 (py--end-of-def-or-class-position)))))

(ert-deftest py-ert-moves-up-position-tests-18 ()
  (interactive)
  (py-test-with-temp-buffer-point-min
      py-kugel-text
    (search-forward "#")
    (should (eq 223 (py--beginning-of-comment-position)))))

(ert-deftest py-ert-moves-up-position-tests-19 ()
  (interactive)
  (py-test-with-temp-buffer-point-min
      py-kugel-text
    (search-forward "#")
    (should (eq 241 (py--end-of-comment-position)))))

(ert-deftest py-ert-moves-up-copy-statement-test ()
  (interactive)
  (py-test-with-temp-buffer-point-min
   "from foo.bar.baz import something
"
   (py-copy-statement)
   (should (string-match "from foo.bar.baz import something" (car kill-ring)))))

(ert-deftest py-ert-moves-up-honor-dedent-lp-1280982 ()
  (py-test-with-temp-buffer
      "def foo():
    def bar():
        asdf
    "
    (py-newline-and-indent)
    (py-electric-backspace)
    (py-newline-and-indent)
    (should (eq 42 (point)))))

(ert-deftest py-ert-moves-up-fill-paragraph-lp-1286318 ()
  (py-test-with-temp-buffer-point-min
      "# r1416

def baz():
    \"\"\"Hello there.

    This is a multiline function definition. Don= 't worry, be happy. Be very very happy. Very. happy.
    \"\"\"
    return 7

# The last line of the docstring is longer than fill-column (set to
# 78 = for me). Put point on the 'T' in 'This' and hit M-q= . Nothing
# happens.
#
# Another example:
#
def baz():
    \"\"\"Hello there.

    This is a multiline
    function definition.
    Don't worry, be happy.
    Be very very happy.
    Very. happy.
    \"\"\"
    return 7

# All of those lines are shorter than fill-column. Put point anywhere
# = in that paragraph and hit M-q. Nothing happens.
#
# In both cases I would expect to end up with:
#
def baz():
    \"\"\"Hello there.

    This is a multiline function definition. Don= 't worry, be happy. Be very
    very happy. Very. happy.
    \"\"\"
    return 7
"
    (goto-char 49)
    ;; (sit-for 0.1 t)
    (fill-paragraph)
    (end-of-line)
    (should (<= (current-column) 72))
    (goto-char 409)
    (fill-paragraph)
    (end-of-line)
    (should (<= (current-column) 72))
    (goto-char 731)
    (fill-paragraph)
    (end-of-line)
    (should (<= (current-column) 72))
    (search-forward "\"\"\"")
    (forward-line -1)
    ;; (sit-for 0.1 t)
    (should (not (empty-line-p)))

    ))

(ert-deftest py-ert-moves-up-fill-paragraph-pep-257-nn-1 ()
  (let ((py-docstring-style 'pep-257-nn))
    (py-test-with-temp-buffer-point-min
	"# r1416

def baz():
    \"\"\"Hello there. This is a multiline function definition. Don= 't wor ry, be happy. Be very very happy. Very. happy. This is a multiline function definition. Don= 't worry, be happy. Be very very happy. Very. happy. This is a multiline function definition. Don= 't worry, be happy. Be very very happy. Very. happy.

    This is a multiline function definition. Don= 't worry, be happy. Be very very happy. Very. happy.
    \"\"\"
    return 7
"
      (goto-char 49)
      (py-fill-string)
      (end-of-line)
      ;; (sit-for 0.1 t)
      (should (<= (current-column) 72))
      (forward-line 2)
      (end-of-line)
      (should (<= (current-column) 72))
      (forward-line 1)
      (end-of-line)
      (should (<= (current-column) 72))
      (forward-line 1)
      (end-of-line)
      (should (<= (current-column) 72))
      (search-forward "\"\"\"")
      (forward-line -1)
      (fill-paragraph)
      (end-of-line)
      ;; (sit-for 0.1 t)
      (should (<= (current-column) 72))
      )))

(ert-deftest py-ert-moves-up-fill-paragraph-pep-257 ()
  (let ((py-docstring-style 'pep-257))
    (py-test-with-temp-buffer-point-min
	"# r1416

def baz():
    \"\"\"Hello there. This is a multiline function definition. Don= 't wor ry, be happy. Be very very happy. Very. happy. This is a multiline function definition. Don= 't worry, be happy. Be very very happy. Very. happy. This is a multiline function definition. Don= 't worry, be happy. Be very very happy. Very. happy.

    This is a multiline function definition. Don= 't worry, be happy. Be very very happy. Very. happy.
    \"\"\"
    return 7
"
      (font-lock-fontify-buffer)
      (goto-char 49)
      (fill-paragraph)
      (end-of-line)
      (should (<= (current-column) 72))
      (forward-line 2)
      (end-of-line)
      (should (<= (current-column) 72))
      (forward-line 1)
      (end-of-line)
      (should (<= (current-column) 72))
      (forward-line 1)
      (end-of-line)
      (should (<= (current-column) 72))
      (search-forward "\"\"\"")
      (forward-line -1)
      (should (empty-line-p))
      )))

(ert-deftest py-ert-moves-up-fill-paragraph-onetwo ()
  (let ((py-docstring-style 'onetwo))
    (py-test-with-temp-buffer-point-min
	"# r1416

def baz():
    \"\"\"Hello there. This is a multiline function definition. Don= 't wor ry, be happy. Be very very happy. Very. happy. This is a multiline function definition. Don= 't worry, be happy. Be very very happy. Very. happy. This is a multiline function definition. Don= 't worry, be happy. Be very very happy. Very. happy.

    This is a multiline function definition. Don= 't worry, be happy. Be very very happy. Very. happy.
    \"\"\"
    return 7
"
      (font-lock-fontify-buffer)
      (goto-char 49)
      (fill-paragraph)
      (search-backward "\"\"\"")
      (goto-char (match-end 0))
      (eolp)
      (forward-line 1)
      (end-of-line)
      (should (<= (current-column) 72))
      (search-forward "\"\"\"")
      (forward-line -1)
      (should (empty-line-p)))))

(ert-deftest py-ert-moves-up-fill-paragraph-django-2 ()
  (let ((py-docstring-style 'django))
    (py-test-with-temp-buffer-point-min
	"# r1416

def baz():
    \"\"\"Hello there. This is a multiline function definition. Don't wor ry, be happy. Be very very happy. Very. happy. This is a multiline function definition. Don't worry, be happy. Be very very happy. Very. happy. This is a multiline function definition. Don't worry, be happy. Be very very happy. Very. happy.

    This is a multiline function definition. Don't worry, be happy. Be very very happy. Very. happy.
    \"\"\"
    return 7
"
      (goto-char 49)
      (fill-paragraph)
      (search-forward "\"\"\"")
      (forward-line -2)
      (should (empty-line-p)))))

(ert-deftest py-ert-moves-up-fill-paragraph-symmetric ()
  (let ((py-docstring-style 'symmetric))
    (py-test-with-temp-buffer-point-min
	"# r1416

def baz():
    \"\"\"Hello there. This is a multiline function definition. Don= 't wor ry, be happy. Be very very happy. Very. happy. This is a multiline function definition. Don= 't worry, be happy. Be very very happy. Very. happy. This is a multiline function definition. Don= 't worry, be happy. Be very very happy. Very. happy.

    This is a multiline function definition. Don= 't worry, be happy. Be very very happy. Very. happy.
    \"\"\"
    return 7
"
      (font-lock-fontify-buffer)
      (goto-char 49)
      (fill-paragraph)
      (search-backward "\"\"\"")
      (goto-char (match-end 0))
      (eolp)
      (forward-line 1)
      (end-of-line)
      (should (<= (current-column) 72))
      (search-forward "\"\"\"")
      (forward-line -1)
      (should (not (empty-line-p))))))

(ert-deftest py-partial-expression-test-1 ()
  (py-test-with-temp-buffer-point-min
      "foo=1"
    (and (should (string= "foo" (py-partial-expression)))
	 (py-kill-buffer-unconditional (current-buffer)))))

(ert-deftest py-partial-expression-test-2 ()
  (py-test-with-temp-buffer-point-min
      "print(root.getchildren()[0])"
    (search-forward "getchildren")
    (and (should (string= "getchildren()[0]" (py-partial-expression)))
	 (py-kill-buffer-unconditional (current-buffer)))))

(ert-deftest py-ert-moves-up-execute-statement-test ()
  (py-test-with-temp-buffer-point-min
      "print(\"I'm the py-execute-statement-test\")"
    (let ((py-shell-name "python2"))
      (py-execute-statement)
      (set-buffer "*Python2*")
      (goto-char (point-max))
      ;; (sit-for 0.3 t)
      (and (should (search-backward "py-execute-statement-test" nil t 1))
	   ;; (sit-for 0.1 t)
	   (py-kill-buffer-unconditional (current-buffer))))))

(ert-deftest indent-region-lp-997958-lp-1426903-no-arg-1-test ()
  "Indent line-by-line as first line is okay "
  (py-test-with-temp-buffer-point-min
   "#! /usr/bin/env python
# -*- coding: utf-8 -*-
def foo ():
if True:
    print(123)

with file(\"foo\" + zeit + \".ending\", 'w') as datei:
    for i in range(anzahl):
        bar.dosomething()
        datei.write(str(baz[i]) + \"\\n\")
"
   (search-forward "True")
   (save-excursion
     (py-indent-region (line-beginning-position) (point-max)))
   (should (eq 4 (current-indentation)))
   (search-forward "with file")
   (should (eq 8 (current-indentation)))
   (search-forward "for i ")
   (should (eq 12 (current-indentation)))
   (search-forward "bar.")
   (should (eq 16 (current-indentation)))
   (search-forward "datei.write")
   (should (eq 16 (current-indentation)))))

(ert-deftest indent-region-lp-997958-lp-1426903-no-arg-2-test ()
  "Keep indent of remaining block as first line was fixed. "
  (py-test-with-temp-buffer-point-min
   "#! /usr/bin/env python
# -*- coding: utf-8 -*-
def foo ():
    if True:
	print(123)

with file(\"foo\" + zeit + \".ending\", 'w') as datei:
    for i in range(anzahl):
	bar.dosomething()
	datei.write(str(baz[i]) + \"\\n\")
"
   (search-forward "for i ")
   (save-excursion
     (py-indent-region (line-beginning-position) (point-max)))
   (should (eq 4 (current-indentation)))
   (search-forward "bar.")
   (should (eq 8 (current-indentation)))
   (search-forward "datei.write")
   (should (eq 8 (current-indentation)))))

(ert-deftest indent-region-lp-997958-lp-1426903-arg-1-test ()
  (py-test-with-temp-buffer
   "#! /usr/bin/env python
# -*- coding: utf-8 -*-
def foo ():
print(123)

with file(\"foo\" + zeit + \".ending\", 'w') as datei:
for i in range(anzahl):
bar.dosomething()
datei.write(str(baz[i]) + \"\\n\")
"
   (py-indent-region 48 (point-max))
   (goto-char (point-min))
   (search-forward "print(123)")
   (should (eq 4 (current-indentation)))
   (search-forward "with file")
   (should (eq 4 (current-indentation)))
   (search-forward "for i ")
   (should (eq 8 (current-indentation)))
   (search-forward "bar.")
   (should (eq 12 (current-indentation)))
   (search-forward "datei.write")
   (should (eq 12 (current-indentation)))))

(ert-deftest indent-region-lp-997958-lp-1426903-arg-2-test ()
  "Indent line-by-line as first line is okay "
  (py-test-with-temp-buffer-point-min
      "#! /usr/bin/env python
# -*- coding: utf-8 -*-
with file(\"foo\" + zeit + \".ending\", 'w') as datei:
    for i in range(anzahl):
        bar.dosomething()
        # called from correct first line
        # wrong indent should to be fixed
            datei.write(str(baz[i]) + \"\\n\")
"
    (search-forward "with file")
    (save-excursion
      (py-indent-region (line-beginning-position) (point-max)))
    (should (eq 0 (current-indentation)))
    (search-forward "for i ")
    (should (eq 4 (current-indentation)))
    (search-forward "bar.")
    (should (eq 8 (current-indentation)))
    (search-forward "datei.write")
    (should (eq 8 (current-indentation)))))

(ert-deftest py--pdb-versioned-test ()
  (py-test-with-temp-buffer
      ""
    (let ((py-shell-name "python3"))
      (should (string= "pdb3" (py--pdb-versioned))))
    (let ((py-shell-name "python"))
      (should (string= "pdb" (py--pdb-versioned))))))

(ert-deftest py-ert-moves-up-forward-expression-test ()
    (py-test-with-temp-buffer-point-min
	py-def-and-class-test-string
      (py-forward-expression)
      (should (eq (char-before) ?s))
      (py-forward-expression)
      (should (eq (char-before) ?:))
      (py-forward-expression)
      (should (eq (char-before) ?t))
      (py-forward-expression)
      (should (eq (char-before) ?\)))
      (py-forward-expression)
      (should (eq (char-before) ?l))
      (py-forward-expression)
      (should (eq (char-before) ?\]))
      (py-forward-expression)
      (should (eq (char-before) ?n))
      (py-forward-expression)
      (should (eq (char-before) ?\]))
      (py-forward-expression)
      (should (eq (char-before) ?t))
      (py-forward-expression)
      (should (eq (char-before) ?\]))
      (py-forward-expression)
      (should (eq (char-before) ?f))
      (py-forward-expression)
      (should (eq (char-before) ?:))
      (py-forward-expression)
      (should (eq (char-before) ?\"))
      (search-forward "fertig")
      (py-forward-expression)
      (should (eq (char-before) ?'))
      (py-forward-expression)
      (should (eq (char-before) ?f))
      (search-forward "__name__")
      (py-forward-expression)
      (should (eq (char-before) ?:))
      (py-forward-expression)
      (should (eq (char-before) ?\)))
      ))

(ert-deftest py-ert-moves-up-backward-expression-test ()
    (py-test-with-temp-buffer
	py-def-and-class-test-string
      (py-backward-expression)
      (should (eq (char-after) ?m))
      (py-backward-expression)
      (should (eq (char-after) ?\"))
      (py-backward-expression)
      (should (eq (char-after) ?_))
      (py-backward-expression)
      (should (eq (char-after) ?i))
      (py-backward-expression)
      (should (eq (char-after) ?t))
      (py-backward-expression)
      (should (eq (char-after) ?a))
      (py-backward-expression)
      (should (eq (char-after) ?s))
      (py-backward-expression)
      (should (eq (char-after) ?i))
      (beginning-of-line)
      (search-backward "if")
      (py-backward-expression)
      (should (eq (char-after) ?'))
      (search-backward "ausgabe")
      (py-backward-expression)
      (should (eq (char-after) ?\[))))

(ert-deftest py-ert-which-def-or-class-test-1 ()
  (py-test-with-temp-buffer-point-min
      py-def-and-class-test-string
    (search-forward "kugel")
    (should (string-match "kugel" (py-which-def-or-class)))
    (search-forward "pylauf")
    (should (string-match "kugel.pylauf" (py-which-def-or-class)))))

(ert-deftest py-ert-which-def-or-class-test-2 ()
  (py-test-with-temp-buffer
      "except AttributeError:

    # To fix reloading, force it to create a new foo
    if hasattr(threading.currentThread(), '__decimal_foo__'):
        del threading.currentThread().__decimal_foo__

    def setfoo(foo):
        \"\"\"Set this thread's foo to foo.\"\"\"
        if foo in (DefaultContext, BasicContext, ExtendedContext):
            foo = foo.copy()
            foo.clear_flags()
        threading.currentThread().__decimal_foo__ = foo

    def getfoo():
        \"\"\"Returns this thread's foo.

        If this thread does not yet have a foo, returns
        \"\"\"
        try:
            return threading.currentThread().__decimal_foo__
        except AttributeError:
            foo = Context()
            threading.currentThread().__decimal_foo__ = foo
            return foo

else:
"
    (should (string= "???" (py-which-def-or-class)))
    (forward-line -3)
    (should (string= "getfoo" (py-which-def-or-class)))))

(ert-deftest py-ert-which-def-or-class-test-3 ()
  (py-test-with-temp-buffer

      "class kugel(object):
    zeit = time.strftime('%Y%m%d--%H-%M-%S')
    # zeit = time.strftime('%Y-%m-%d--%H-%M-%S')
    spiel = []
    gruen = [0]
    rot = [1, 3, 5, 7, 9, 12, 14, 16, 18, 19, 21, 23, 25, 27, 30, 32, 34, 36]
    schwarz = [2, 4, 6, 8, 10, 11, 13, 15, 17, 20, 22, 24, 26, 28, 29, 31, 33, 35]
    ausgabe = []
    treffer = None
    fertig = ''
    treffer = random.randint(0, 36)

    def foo():
        bar

    def pylauf(self):
"
    (forward-line -2)
    (should (string= "kugel.foo" (py-which-def-or-class)))))

(ert-deftest py-ert-match-paren-test-1 ()
  (py-test-with-temp-buffer
      "if __name__ == \"__main__\":
    main()"
    (forward-char -1)
    (py-match-paren)
    (should (eq (char-after) ?\())))

(ert-deftest py-ert-match-paren-test-2 ()
    (py-test-with-temp-buffer
	"if __name__ == \"__main__\":
    main()"
      (forward-char -2)
      (py-match-paren)
      (should (eq (char-after) ?\)))))

(ert-deftest py-ert-match-paren-test-4 ()
    (py-test-with-temp-buffer
	"if __name__ == \"__main__\":
    main()
    "
      (py-match-paren)
      (should (eq (char-after) ?m))))

(ert-deftest py-ert-match-paren-test-5 ()
    (py-test-with-temp-buffer-point-min
	"if __name__ == \"__main__\":
    main()
    "
      (py-match-paren)
      (should (bolp))))

(ert-deftest py-ert-match-paren-test-7 ()
  (py-test-with-temp-buffer
      py-def-and-class-test-string
    (skip-chars-backward "^\]")
    (forward-char -1)
    (py-match-paren)
    (should (eq (char-after) ?\[))
    (py-match-paren)
    (should (eq (char-after) ?\]))))

(ert-deftest py-ert-match-paren-test-8 ()
  (py-test-with-temp-buffer
      py-def-and-class-test-string
      (skip-chars-backward "^:")
      (py-match-paren)
      (should (eq (char-after) ?i))))

(ert-deftest py-ert-match-paren-test-9 ()
  (py-test-with-temp-buffer
      py-def-and-class-test-string
      (search-backward "pylauf")
      (py-match-paren)
      (should (eq (char-after) ?\"))
      (py-match-paren)
      (should (eq (char-after) ?\"))
      ))

(ert-deftest py-ert-match-paren-nonempty-test-1 ()
  (py-test-with-temp-buffer
      "def main():
    if len(sys.argv) == 1:
        usage()
        sys.exit()
    #"
    (search-backward "if")
    (py-match-paren)
    (should (eq 4 (current-column)))
    (py-match-paren)
    (should (eq (char-after) ?i))))

(ert-deftest py-ert-match-paren-nonempty-test-2 ()
  (py-test-with-temp-buffer
      "def main():
    if len(sys.argv) == 1:
        usage()
        sys.exit()
     #"
    (search-backward "if")
    (py-match-paren)
    (should (and
	     (eq (char-after) 32)
	     (eq (current-column) 4)))))

(ert-deftest py-ert-match-paren-nonempty-test-3 ()
  (py-test-with-temp-buffer-point-min
      "def main():
    if len(sys.argv) == 1:
        usage()
        sys.exit()
    #"
    (py-match-paren)
    (should (and
	     (eq (char-after) 32)
	     (eq (current-column) 0)))))

(ert-deftest py-ert-match-paren-nonempty-test-4 ()
  (py-test-with-temp-buffer
      "def main():
    if len(sys.argv) == 1:
        usage()
        sys.exit()

    class asdf(object):
        zeit = time.strftime('%Y%m%d--%H-%M-%S')
"
    (search-backward "if")
    (py-match-paren)
    (should (eq (current-column) 4))
    (should (eq (char-before) 32))))

(ert-deftest py-ert-match-paren-nonempty-test-5 ()
  (py-test-with-temp-buffer-point-min
      "import re
import sys
import os
"

    (py-match-paren)
    (should (looking-at "import sys"))
    (setq last-command 'py-match-paren)
    (py-match-paren)
    (should (looking-at "import re"))))

(ert-deftest py-ert-match-paren-nonempty-test-6 ()
  (py-test-with-temp-buffer
      "def main():
    if len(sys.argv) == 1:
        usage()
        sys.exit()

    class asdf(object):
        zeit = time.strftime('%Y%m%d--%H-%M-%S')

        def Utf8_Exists(filename):
            return os.path.exists(filename.encode('utf-8'))
"
    (search-backward "class")
    (py-match-paren)
    (should (empty-line-p))
    (should (eq 4 (current-column)))
    ))

(ert-deftest py-ert-match-paren-nonempty-test-7 ()
  (py-test-with-temp-buffer
      "try:
    anzahl = int(args[1])
except:
    print \"Setze anzahl auf 1\"
"
    (search-backward "arg")
    (py-match-paren)
    (should (eq (char-after) ?\())))

(ert-deftest py-ert-match-paren-nonempty-test-8 ()
  (py-test-with-temp-buffer
      "try:
    anzahl = int(args[1])
except:
    print \"Setze anzahl auf 1\"
"
    (search-backward " int")
    (py-match-paren)
    (should (eq (char-after) ?a))
    (py-match-paren)
    (should (eq (char-before) 32))
    (should (empty-line-p))
    (should (eq 4 (current-column)))))

(ert-deftest py-ert-match-paren-test-9 ()
  (py-test-with-temp-buffer
      "if __name__ == \"__main__\":
    main()
"
    (py-match-paren)
    (should (eq (char-after) ?i))))

(ert-deftest py-ert-moves-up-match-paren-test-2 ()
  (py-test-with-temp-buffer
      py-def-and-class-test-string
    (forward-line -3)
    (indent-to 12)
    (py-match-paren)
    (should (eq (char-after) ?a))))

(ert-deftest py-ert-moves-up-match-paren-test-10 ()
  (py-test-with-temp-buffer
      py-def-and-class-test-string
    (forward-line -3)
    (indent-to 8)
    (py-match-paren)
    (should (eq (char-after) ?e))
    (forward-line 3)
    (should (eolp))))

(ert-deftest py-ert-backward-def-or-class-1 ()
  (py-test-with-temp-buffer
      "class _Simple(object):
    # emulate something
    def foo(self, element, tag, namespaces=None):
        pass
    def bar(self, element, tag, namespaces=None):
        return list(self.iterfind(element, tag, namespaces))"
    (forward-line -1)
    (end-of-line)
    (py-backward-def-or-class)
    (should (char-equal ?d (char-after)))))

(ert-deftest py-ert-backward-def-or-class-2 ()
  (py-test-with-temp-buffer
      "class _Simple(object):
    # emulate something
    def foo(self, element, tag, namespaces=None):
        pass
    def bar(self, element, tag, namespaces=None):
        return list(self.iterfind(element, tag, namespaces))"
    (search-backward "pass")
    (py-backward-def-or-class)
    (should (char-equal ?d (char-after)))))

(ert-deftest py-ert-backward-def-or-class-3 ()
  (py-test-with-temp-buffer
      "class _Simple(object):
    # emulate something
    def foo(self, element, tag, namespaces=None):
        pass
    def bar(self, element, tag, namespaces=None):
        return list(self.iterfind(element, tag, namespaces))"
    (search-backward "def" nil t 2)
    (py-backward-def-or-class)
    (should (char-equal ?c (char-after)))))

(provide 'py-ert-tests-1)
;;; py-ert-tests-1.el ends here
