;;; -*- Mode: Emacs-Lisp -*-

;;; Rudimentary, kludgey test suite for paredit -- work in progress!

;; Copyright (C) 2005--2017 Taylor R. Campbell

;; This file is part of paredit.
;;
;; Paredit is free software: you can redistribute it and/or modify it
;; under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.
;;
;; Paredit is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with paredit.  If not, see <http://www.gnu.org/licenses/>.

(defun paredit-test-failure-default (command before after expected)
  (error "%S failed test: after %S, got %S but expected %S."
         command before after expected))

(defvar paredit-test-failure-function 'paredit-test-failure-default
  "Function to call when `paredit-test' fails.
Four arguments: the paredit command, the text of the buffer
  before, the text of the buffer after, and the expected text of
  the buffer after.")

(defun paredit-test-failed (command before after expected)
  (funcall paredit-test-failure-function command before after expected))

(defun paredit-test (command examples)
  (message "Testing %S..." command)
  (dolist (example examples)
    (let ((before (car example)))
      (dolist (expected (cdr example))
        (with-temp-buffer
          (paredit-test-buffer-setup)
          (insert before)
          (goto-char (point-min))
          (if (search-forward "_" nil t)
              (progn (delete-char -1) (set-mark (point))))
          (goto-char (point-min))
          (search-forward "|")
          (delete-char -1)
          (if (cond ((eq expected 'error)
                     ;++ Check that there are no more expected states.
                     (condition-case condition
                         (progn (call-interactively command) t)
                       (error nil)))
                    ((stringp expected)
                     (call-interactively command)
                     (insert ?\|)
                     (not (string= expected (buffer-string))))
                    (t (error "Bad test expectation: %S" expected)))
              (paredit-test-failed command before (buffer-string) expected)))
        (setq before expected)))))

(defun paredit-test-buffer-setup ()
  (scheme-mode)
  (set (make-local-variable 'indent-tabs-mode) nil)
  (set (make-local-variable 'comment-column) 40)
  (set (make-local-variable 'show-trailing-whitespace) nil))

(paredit-do-commands (spec keys command examples)
    nil                                 ;string case
  ;; `paredit-backslash' has a funny example.
  (if (not (eq command 'paredit-backslash))
      (paredit-test command examples)))

(defun paredit-test-bracketed (entries examples)
  (dolist (entry entries)
    (let ((command (car entry))
          (left (car (cdr entry)))
          (right (car (cdr (cdr entry)))))
      (paredit-test command
        (mapcar
         (lambda (example)
           (mapcar (lambda (step)
                     (if (stringp step)
                         (replace-regexp-in-string "(" (string left)
                           (replace-regexp-in-string ")" (string right) step))
                         step))
                   example))
         examples)))))

;++ Test `paredit-open-...' with the region active.

(paredit-test-bracketed '((paredit-open-round ?\( ?\))
                          (paredit-open-square ?\[ ?\])
                          (paredit-open-curly ?\{ ?\})
                          ;; (paredit-open-angled ?\< ?\>)
                          )
  '(("(foo|bar)" "(foo (|) bar)")
    ("(foo| bar)" "(foo (|) bar)")
    ("(foo |bar)" "(foo (|) bar)")
    ("(foo|\n bar)" "(foo (|)\n bar)")
    ("(foo |(bar) baz)" "(foo (|) (bar) baz)")
    ("(foo (bar)| baz)" "(foo (bar) (|) baz)")
    ("(foo |\"bar\" baz)" "(foo (|) \"bar\" baz)")
    ("(foo \"bar\"| baz)" "(foo \"bar\" (|) baz)")
    ("foo|" "foo (|)")
    ("|foo" "(|) foo")
    ("\\|(" "\\|(")))

(let ((current-prefix-arg 1))
  (paredit-test-bracketed '((paredit-open-round ?\( ?\))
                            (paredit-open-square ?\[ ?\])
                            (paredit-open-curly ?\{ ?\})
                            ;; (paredit-open-angled ?\< ?\>)
                            )
    '(("(foo |bar baz)" "(foo (|bar) baz)")
      ("(x |;y\n z\n w)"
       "(x (|                                    ;y\n    z)\n w)"))))

(let ((current-prefix-arg '(4)))
  ;++ Oops -- `C-u (' is like `M-4 (', not like `C-u M-('.
  (paredit-test-bracketed '((paredit-open-round ?\( ?\))
                            (paredit-open-square ?\[ ?\])
                            (paredit-open-curly ?\{ ?\})
                            ;; (paredit-open-angled ?\< ?\>)
                            )
    '(("(foo |bar baz)" "(foo (|bar baz))")
      ("(x |;y\n z\n w)"
       "(x (|                                    ;y\n    z\n    w))")
      ("foo |bar baz" "foo (|bar baz)")
      ;++ These tests are kinda bunk.  It's not immediately clear to me
      ;++ which is right: including or excluding the trailing comment.
      ("foo\n|bar\nbaz\n;quux\n" "foo\n(|bar\n baz)\n;quux\n")
      ("foo\n|bar\nbaz\n;; quux" "foo\n(|bar\n baz\n ;; quux\n )"))))

(paredit-test-bracketed '((paredit-close-round ?\( ?\))
                          (paredit-close-square ?\[ ?\])
                          (paredit-close-curly ?\{ ?\})
                          ;; (paredit-close-angled ?\< ?\>)
                          )
  '(("(#\\|x)" "(#\\x)|")
    ("(#\\|])" "(#\\])|")
    ("(#\\| )" "(#\\ )|")
    ("(#\\|\")" "(#\\\")|")
    ("(\"|\")" "(\")|\")")
    ("(\"|\")" "(\")|\")")))

(paredit-test-bracketed '((paredit-close-round ?\( ?\))
                          (paredit-close-square ?\[ ?\])
                          (paredit-close-curly ?\{ ?\})
                          ;; (paredit-close-angled ?\< ?\>)
                          )
  '(("(|" "()|")
    ("foo|" error)
    ("(foo|  ;\n   )" "(foo  ;\n )|")
    ("(foo|  ;\n   bar)" "(foo  ;\n   bar)|")
    ("(foo|  ;\n   bar )" "(foo  ;\n   bar)|")))

(paredit-test-bracketed '((paredit-close-round-and-newline ?\( ?\))
                          (paredit-close-square-and-newline ?\[ ?\])
                          (paredit-close-curly-and-newline ?\{ ?\})
                          ;; (paredit-close-angled-and-newline ?\< ?\>)
                          )
  '(("(foo #\\|(  )" "(foo #\\()\n|")
    ("(foo|\n )   ;bar" "(foo)   ;bar\n|")
    ("((foo|\n)    (bar))" "((foo)\n |(bar))")))

(paredit-test-bracketed '((paredit-wrap-round ?\( ?\))
                          (paredit-wrap-square ?\[ ?\])
                          (paredit-wrap-curly ?\{ ?\})
                          ;; (paredit-wrap-angled ?\< ?\>)
                          )
  '(("|foo" "(|foo)")
    ("f|oo" "f (|oo)")
    ("fo|o" "fo (|o)")
    ("|foo bar" "(|foo) bar")
    ("f|oo bar" "f (|oo) bar")
    ("fo|o bar" "fo (|o) bar")
    ("foo| bar" "foo (| bar)")
    ("foo |bar" "foo (|bar)")
    ("foo b|ar" "foo b (|ar)")
    ("foo ba|r" "foo ba (|r)")
    ("|foo bar baz" "(|foo) bar baz")))

(let ((transient-mark-mode t))
  (paredit-test-bracketed '((paredit-wrap-round ?\( ?\))
                            (paredit-wrap-square ?\[ ?\])
                            (paredit-wrap-curly ?\{ ?\})
                            ;; (paredit-wrap-angled ?\< ?\>)
                            )
    '(("|foo bar_" "(|foo bar)")
      ("|foo bar_ baz" "(|foo bar) baz"))))

(let ((transient-mark-mode nil))
  (paredit-test-bracketed '((paredit-wrap-round ?\( ?\))
                            (paredit-wrap-square ?\[ ?\])
                            (paredit-wrap-curly ?\{ ?\})
                            ;; (paredit-wrap-angled ?\< ?\>)
                            )
    '(("|foo bar_" "(|foo) bar")
      ("|foo bar_ baz" "(|foo) bar baz"))))

(let ((current-prefix-arg '(4)))
  (paredit-test 'paredit-wrap-sexp
    '(("(foo |bar baz)" "(foo (|bar baz))"))))

(paredit-test 'paredit-newline
  '(("\"foo|bar\"" "\"foo\n|bar\"")
    ("(frob grovel ;full |(lexical)\n      mumble)"
     "(frob grovel ;full\n      |(lexical)\n      mumble)")
    ("(frob grovel ;full (|lexical)\n      mumble)"
     "(frob grovel ;full (\n             ;|lexical)\n      mumble)")
    ("#\\|(" "#\\(\n|")))

(paredit-test 'paredit-reindent-defun
  ;++ Test filling paragraphs in comments and strings.
  '(("|(define (square x)\n     (* x x))"
     "|(define (square x)\n  (* x x))")
    ("(define (square x)\n     (* x x))|"
     "(define (square x)\n  (* x x))|")
    ("(define (square x)\n     (* x x))|\n(frob\n    wotz)"
     "(define (square x)\n  (* x x))|\n(frob\n    wotz)")
    ("(define (square x)\n     (* x x))\n|(frob\n    wotz)"
     "(define (square x)\n     (* x x))\n|(frob\n wotz)")
    ("(define (square x)\n |  (* x x))"
     "(define (square x)\n | (* x x))")
    ("(define (square x)\n    | (* x x))"
     "(define (square x)\n  |(* x x))")
    ("(define (square x)\n     (* |x x))"
     "(define (square x)\n  (* |x x))")))

(paredit-test 'paredit-semicolon
  '(("|" ";|")
    ("|foo" ";|foo")
    ("f|oo" "f;|oo")
    ("fo|o" "fo;|o")
    ("foo|" "foo;|")
    ("|(foo bar)" ";|(foo bar)")
    ("(|foo bar)" "(;|foo bar\n )")
    ("(f|oo bar)" "(f;|oo bar\n )")
    ("(fo|o bar)" "(fo;|o bar\n )")
    ("(foo| bar)" "(foo;| bar\n )")
    ("(foo |bar)" "(foo ;|bar\n )")
    ("(foo b|ar)" "(foo b;|ar\n     )")
    ("(foo ba|r)" "(foo ba;|r\n     )")
    ("(foo bar|)" "(foo bar;|\n     )")
    ("(foo bar)|" "(foo bar);|")
    ("|(foo\n bar)" ";|\n(foo\n bar)")
    ("(|foo\n bar)" "(;|foo\n bar)")
    ("(f|oo\n bar)" "(f;|oo\n bar)")
    ("(fo|o\n bar)" "(fo;|o\n bar)")
    ("(foo|\n bar)" "(foo;|\n bar)")
    ("(foo\n| bar)" "(foo\n;| bar\n )")
    ("(foo\n |bar)" "(foo\n ;|bar\n )")
    ("(foo\n b|ar)" "(foo\n b;|ar\n )")
    ("(foo\n ba|r)" "(foo\n ba;|r\n )")
    ("(foo\n bar|)" "(foo\n bar;|\n )")
    ("(foo\n bar)|" "(foo\n bar);|")
    ("#\\|(" ";|#\\(")))

(paredit-test 'paredit-comment-dwim
  '(("\"foo|bar;baz\"    ;quux"
     "\"foobar;baz\"                            ;|quux")
    ;; Uh oh!  Bug in `comment-indent'...
    ;; ("\"foo\nbar|baz;quux\"         ;zot"
    ;;  "\"foo\nbarbaz;quux\"                            ;|zot")
    ;; I think the loop in `paredit-comment-on-line' is bogus.  Can you
    ;; elicit more than one iteration of it?  That is, can you cause
    ;; `comment-search-forward' to wind up inside a character or a
    ;; string?
    ))

(paredit-test 'paredit-doublequote
  '(("\"foo \\|x bar\"" "\"foo \\x\\\"| bar\"")))

(paredit-test 'paredit-forward-delete
  '(("f|oo" "f|o")
    (";f|(oo" ";f|oo")
    (";|;(foo)" ";|(foo)")
    ("|;;(foo)" "|;(foo)" "|(foo)")
    (";foo|\n(bar)\n(baz\n quux)" ";foo|(bar)\n(baz\n quux)")
    (";foo|\n(bar\n baz)" error)
    ("|;;foo(" "|;foo(" error)
    (";foo|\n(bar);baz\n" ";foo|(bar);baz\n")
    (";foo|\n(bar);baz" ";foo|(bar);baz")
    (";foo|\n(bar ;baz\n quux)\n" error)
    (";foo|\n(bar ;baz\n quux)" error)
    ("|\\\\\\\\" "|\\\\" "|" error)
    ("\\\\|\\\\" "\\\\|" error)
    ("(|\\\\\\\\)" "(|\\\\)" "(|)" "|" error)
    ("(\\\\|\\\\)" "(\\\\|)" "(\\\\|)")
    ("|(" "|" error)
    ("|)" "|" error)))

(paredit-test 'paredit-backward-delete
  '(("fo|o" "f|o")
    (";fo(|o" ";fo|o")
    (";|;(foo)" "|;(foo)")
    (";;|(foo)" ";|(foo)" "|(foo)")
    (";foo\n|(bar)\n(baz\n quux)" ";foo|(bar)\n(baz\n quux)")
    (";foo\n|(bar\n baz)" error)
    (";;|foo(" ";|foo(" error)
    (";foo\n|(bar);baz\n" ";foo|(bar);baz\n")
    (";foo\n|(bar);baz" ";foo|(bar);baz")
    (";foo\n|(bar ;baz\n quux)\n" error)
    (";foo\n|(bar ;baz\n quux)" error)
    ("\\\\\\\\|" "\\\\|" "|" error)
    ("\\\\|\\\\" "|\\\\" error)
    ("(\\\\\\\\|)" "(\\\\|)" "(|)" "|" error)
    ("(\\\\|\\\\)" "(|\\\\)" "(|\\\\)")
    ("(|" "|" error)
    (")|" "|" error)))

(dolist (command '(paredit-delete-region paredit-kill-region))
  ;++ Need to check whether `paredit-kill-region' updates the kill ring
  ;++ correctly.
  (paredit-test command
    '(("|foo" error)
      ("|foo_" "|")
      ("|(foo)_" "|")
      (";;; f|oo (bar ;_baz\n(zot)\n" ";;; f|baz\n(zot)\n")
      ("(foo |bar_ baz)\n" "(foo | baz)\n")
      ("(foo |(bar \"baz\" ; quux\n          zot)\n     _mumble)"
       "(foo |mumble)")
      ("(foo (bar |baz) (quux _zot) mumble)" "(foo (bar |zot) mumble)")
      ("(foo bar    ;baz| quux\n     zot_)" error)
      ("(foo bar    ;baz| quux\n     _zot\n     mumble)"
       "(foo bar    ;baz|zot\n     mumble)")
      ("(foo bar| baz    ;quux (_)\n     zot)" error)
      ("(foo bar| baz    ;quux ()_\n     zot)"
       "(foo bar|\n     zot)"))))

;;; The hairiest paredit command: paredit-kill.

;++ Need to check whether `paredit-kill' updates the kill ring.

(paredit-test (defun paredit-test-kill ()
                (interactive)
                ;; Horrible kludge.  Do it once, and then yank to make
                ;; sure we get back what we expect.  Then do it again,
                ;; to get the effects on the buffer the automatic test
                ;; framework will check.
                (save-excursion
                  (let ((kill-ring nil))
                    (let ((text (buffer-string)))
                      (call-interactively 'paredit-kill)
                      (call-interactively 'yank)
                      (if (not (equal text (buffer-string)))
                          (error "Before kill %S, after yank %S."
                                 text
                                 (buffer-string))))))
                (let ((kill-ring nil))
                  (call-interactively 'paredit-kill)))
  '(("|" error)
    ("| " "|" error)
    (" |" error)
    ("| \n "
     ;; This ought to be an intermediate step, but evidently it is only
     ;; in recent versions of GNU Emacs with `show-trailing-whitespace'
     ;; set to thanks to some brain damage in `kill-line'.
     ;;
     ;; "|\n "
     "| " "|" error)
    (" |\n " " | " " |" error)
    (" \n| " " \n|" error)

    ("|( )" "|" error)
    ("(| )" "(|)" "(|)")
    ("( |)" "( |)")
    ("( )|" error)

    ("|(     )" "|" error)
    ("(|     )" "(|)" "(|)")
    ("( |    )" "( |)" "( |)")
    ("(  |   )" "(  |)" "(  |)")
    ("(   |  )" "(   |)" "(   |)")
    ("(    | )" "(    |)" "(    |)")
    ("(     |)" "(     |)" "(     |)")

    ("|(\n)" "|" error)
    ("(|\n)" "(|)" "(|)")
    ("(\n|)" "(\n|)")
    ("(\n)|" error)

    ("|(\n)\n" "|\n" "|" error)
    ("(|\n)\n" "(|)\n" "(|)\n")
    ("(\n|)\n" "(\n|)\n" "(\n|)\n")
    ("(\n)|\n" "(\n)|" error)
    ("(\n)\n|" error)

    ("|\"\n\"" "|" error)
    ("\"|\n\"" "\"|\"" "\"|\"")
    ("\"\n|\"" "\"\n|\"")
    ("\"\n\"|" error)

    ("|\"\n\"\n" "|\n" "|" error)
    ("\"|\n\"\n" "\"|\"\n" "\"|\"\n")
    ("\"\n|\"\n" "\"\n|\"\n" "\"\n|\"\n")
    ("\"\n\"|\n" "\"\n\"|" error)
    ("\"\n\"\n|" error)

    ("|(a (b) (c)\n   (d) (e))" "|" error)
    ("(a| (b) (c)\n   (d) (e))"
     "(a|\n   (d) (e))"
     "(a|   (d) (e))"
     "(a|)"
     "(a|)")
    ("(a |(b) (c)\n   (d) (e))"
     "(a |\n   (d) (e))"
     "(a |   (d) (e))"
     "(a |)"
     "(a |)")
    ("(a (|b) (c)\n   (d) (e))"
     "(a (|) (c)\n   (d) (e))"
     "(a (|) (c)\n   (d) (e))")
    ("(a (b|) (c)\n   (d) (e))" "(a (b|) (c)\n   (d) (e))")
    ("(a (b)| (c)\n   (d) (e))"
     "(a (b)|\n   (d) (e))"
     "(a (b)|   (d) (e))"
     "(a (b)|)"
     "(a (b)|)")
    ("(a (b) |(c)\n   (d) (e))"
     "(a (b) |\n   (d) (e))"
     "(a (b) |   (d) (e))"
     "(a (b) |)"
     "(a (b) |)")
    ("(a (b) (|c)\n   (d) (e))"
     "(a (b) (|)\n   (d) (e))"
     "(a (b) (|)\n   (d) (e))")
    ("(a (b) (c|)\n   (d) (e))" "(a (b) (c|)\n   (d) (e))")
    ("(a (b) (c)|\n   (d) (e))"
     "(a (b) (c)|   (d) (e))"
     "(a (b) (c)|)"
     "(a (b) (c)|)")
    ("(a (b) (c)\n|   (d) (e))"
     "(a (b) (c)\n|)"
     "(a (b) (c)\n|)")
    ("(a (b) (c)\n |  (d) (e))"
     "(a (b) (c)\n |)"
     "(a (b) (c)\n |)")
    ("(a (b) (c)\n  | (d) (e))"
     "(a (b) (c)\n  |)"
     "(a (b) (c)\n  |)")
    ("(a (b) (c)\n   |(d) (e))"
     "(a (b) (c)\n   |)"
     "(a (b) (c)\n   |)")
    ("(a (b) (c)\n   (|d) (e))"
     "(a (b) (c)\n   (|) (e))"
     "(a (b) (c)\n   (|) (e))")
    ("(a (b) (c)\n   (d|) (e))" "(a (b) (c)\n   (d|) (e))")
    ("(a (b) (c)\n   (d)| (e))"
     "(a (b) (c)\n   (d)|)"
     "(a (b) (c)\n   (d)|)")
    ("(a (b) (c)\n   (d) |(e))"
     "(a (b) (c)\n   (d) |)"
     "(a (b) (c)\n   (d) |)")
    ("(a (b) (c)\n   (d) (|e))"
     "(a (b) (c)\n   (d) (|))"
     "(a (b) (c)\n   (d) (|))")
    ("(a (b) (c)\n   (d) (e|))" "(a (b) (c)\n   (d) (e|))")
    ("(a (b) (c)\n   (d) (e)|)" "(a (b) (c)\n   (d) (e)|)")
    ("(a (b) (c)\n   (d) (e))|" error)

    ("|(a ((b) (c)\n    (d) (e)) (f))" "|" error)
    ("(|a ((b) (c)\n    (d) (e)) (f))" "(| (f))" "(|)" "(|)")
    ("(a| ((b) (c)\n    (d) (e)) (f))" "(a| (f))" "(a|)" "(a|)")
    ("(a |((b) (c)\n    (d) (e)) (f))" "(a | (f))" "(a |)" "(a |)")
    ("(a (|(b) (c)\n    (d) (e)) (f))"
     "(a (|\n    (d) (e)) (f))"
     "(a (|    (d) (e)) (f))"
     "(a (|) (f))"
     "(a (|) (f))")
    ("(a ((|b) (c)\n    (d) (e)) (f))"
     "(a ((|) (c)\n    (d) (e)) (f))"
     "(a ((|) (c)\n    (d) (e)) (f))")
    ("(a ((b|) (c)\n    (d) (e)) (f))"
     "(a ((b|) (c)\n    (d) (e)) (f))")
    ("(a ((b)| (c)\n    (d) (e)) (f))"
     "(a ((b)|\n    (d) (e)) (f))"
     "(a ((b)|    (d) (e)) (f))"
     "(a ((b)|) (f))"
     "(a ((b)|) (f))")
    ("(a ((b) |(c)\n    (d) (e)) (f))"
     "(a ((b) |\n    (d) (e)) (f))"
     "(a ((b) |    (d) (e)) (f))"
     "(a ((b) |) (f))"
     "(a ((b) |) (f))")
    ("(a ((b) (|c)\n    (d) (e)) (f))"
     "(a ((b) (|)\n    (d) (e)) (f))"
     "(a ((b) (|)\n    (d) (e)) (f))")
    ("(a ((b) (c|)\n    (d) (e)) (f))" "(a ((b) (c|)\n    (d) (e)) (f))")
    ("(a ((b) (c)|\n    (d) (e)) (f))"
     "(a ((b) (c)|    (d) (e)) (f))"
     "(a ((b) (c)|) (f))"
     "(a ((b) (c)|) (f))")
    ("(a ((b) (c)\n|    (d) (e)) (f))"
     "(a ((b) (c)\n|) (f))"
     "(a ((b) (c)\n|) (f))")
    ("(a ((b) (c)\n |   (d) (e)) (f))"
     "(a ((b) (c)\n |) (f))"
     "(a ((b) (c)\n |) (f))")
    ("(a ((b) (c)\n  |  (d) (e)) (f))"
     "(a ((b) (c)\n  |) (f))"
     "(a ((b) (c)\n  |) (f))")
    ("(a ((b) (c)\n   | (d) (e)) (f))"
     "(a ((b) (c)\n   |) (f))"
     "(a ((b) (c)\n   |) (f))")
    ("(a ((b) (c)\n    |(d) (e)) (f))"
     "(a ((b) (c)\n    |) (f))"
     "(a ((b) (c)\n    |) (f))")
    ("(a ((b) (c)\n    (|d) (e)) (f))"
     "(a ((b) (c)\n    (|) (e)) (f))"
     "(a ((b) (c)\n    (|) (e)) (f))")
    ("(a ((b) (c)\n    (d|) (e)) (f))" "(a ((b) (c)\n    (d|) (e)) (f))")
    ("(a ((b) (c)\n    (d)| (e)) (f))"
     "(a ((b) (c)\n    (d)|) (f))"
     "(a ((b) (c)\n    (d)|) (f))")
    ("(a ((b) (c)\n    (d) |(e)) (f))"
     "(a ((b) (c)\n    (d) |) (f))"
     "(a ((b) (c)\n    (d) |) (f))")
    ("(a ((b) (c)\n    (d) (|e)) (f))"
     "(a ((b) (c)\n    (d) (|)) (f))"
     "(a ((b) (c)\n    (d) (|)) (f))")
    ("(a ((b) (c)\n    (d) (e|)) (f))" "(a ((b) (c)\n    (d) (e|)) (f))")
    ("(a ((b) (c)\n    (d) (e)|) (f))" "(a ((b) (c)\n    (d) (e)|) (f))")
    ("(a ((b) (c)\n    (d) (e))| (f))"
     "(a ((b) (c)\n    (d) (e))|)"
     "(a ((b) (c)\n    (d) (e))|)")
    ("(a ((b) (c)\n    (d) (e)) |(f))"
     "(a ((b) (c)\n    (d) (e)) |)"
     "(a ((b) (c)\n    (d) (e)) |)")
    ("(a ((b) (c)\n    (d) (e)) (|f))"
     "(a ((b) (c)\n    (d) (e)) (|))"
     "(a ((b) (c)\n    (d) (e)) (|))")
    ("(a ((b) (c)\n    (d) (e)) (f|))" "(a ((b) (c)\n    (d) (e)) (f|))")
    ("(a ((b) (c)\n    (d) (e)) (f)|)" "(a ((b) (c)\n    (d) (e)) (f)|)")
    ("(a ((b) (c)\n    (d) (e)) (f))|" error)

    ("|(a \"(b) (c)\n )  { ;;;; \n\n\n(d)( (e);\" (f))" "|" error)
    ("(|a \"(b) (c)\n )  { ;;;; \n\n\n(d)( (e);\" (f))" "(| (f))" "(|)" "(|)")
    ("(a| \"(b) (c)\n )  { ;;;; \n\n\n(d)( (e);\" (f))"
     "(a| (f))"
     "(a|)"
     "(a|)")
    ("(a |\"(b) (c)\n )  { ;;;; \n\n\n(d)( (e);\" (f))"
     "(a | (f))"
     "(a |)"
     "(a |)")
    ("(a \"|(b) (c)\n )  { ;;;; \n\n\n(d)( (e);\" (f))"
     "(a \"|\n )  { ;;;; \n\n\n(d)( (e);\" (f))"
     "(a \"| )  { ;;;; \n\n\n(d)( (e);\" (f))"
     "(a \"|\n\n\n(d)( (e);\" (f))"
     "(a \"|\n\n(d)( (e);\" (f))"
     "(a \"|\n(d)( (e);\" (f))"
     "(a \"|(d)( (e);\" (f))"
     "(a \"|\" (f))"
     "(a \"|\" (f))")
    ("(a \"(b) (c)|\n )  { ;;;; \n\n\n(d)( (e);\" (f))"
     "(a \"(b) (c)| )  { ;;;; \n\n\n(d)( (e);\" (f))"
     "(a \"(b) (c)|\n\n\n(d)( (e);\" (f))"
     "(a \"(b) (c)|\n\n(d)( (e);\" (f))"
     "(a \"(b) (c)|\n(d)( (e);\" (f))"
     "(a \"(b) (c)|(d)( (e);\" (f))"
     "(a \"(b) (c)|\" (f))"
     "(a \"(b) (c)|\" (f))")
    ("(a \"(b) (c)\n )  { ;;;; |\n\n\n(d)( (e);\" (f))"
     "(a \"(b) (c)\n )  { ;;;; |\n\n(d)( (e);\" (f))"
     "(a \"(b) (c)\n )  { ;;;; |\n(d)( (e);\" (f))"
     "(a \"(b) (c)\n )  { ;;;; |(d)( (e);\" (f))"
     "(a \"(b) (c)\n )  { ;;;; |\" (f))"
     "(a \"(b) (c)\n )  { ;;;; |\" (f))")
    ("(a \"(b) (c)\n )  { ;;;; \n\n\n|(d)( (e);\" (f))"
     "(a \"(b) (c)\n )  { ;;;; \n\n\n|\" (f))"
     "(a \"(b) (c)\n )  { ;;;; \n\n\n|\" (f))")

    ("|x(\n)(z)" "|(z)" "|" error)
    ("x|(\n)(z)" "x|(z)" "x|" error)
    ("x(|\n)(z)" "x(|)(z)" "x(|)(z)")
    ("x(\n|)(z)" "x(\n|)(z)")
    ("x(\n)|(z)" "x(\n)|" error)
    ("x(\n)(|z)" "x(\n)(|)" "x(\n)(|)")
    ("x(\n)(z|)" "x(\n)(z|)")
    ("x(\n)(z)|" error)

    ("|x\"\n\"(z)" "|(z)" "|" error)
    ("x|\"\n\"(z)" "x|(z)" "x|" error)
    ("x\"|\n\"(z)" "x\"|\"(z)" "x\"|\"(z)")
    ("x\"\n|\"(z)" "x\"\n|\"(z)")
    ("x\"\n\"|(z)" "x\"\n\"|" error)
    ("x\"\n\"(|z)" "x\"\n\"(|)" "x\"\n\"(|)")
    ("x\"\n\"(z|)" "x\"\n\"(z|)")
    ("x\"\n\"(z)|" error)

    ("|(f ;; b\n z)" "|" error)
    ("(|f ;; b\n z)" "(|\n z)" "(| z)" "(|)" "(|)")
    ("(f| ;; b\n z)" "(f|\n z)" "(f| z)" "(f|)" "(f|)")
    ("(f |;; b\n z)" "(f |\n z)" "(f | z)" "(f |)" "(f |)")
    ("(f ;|; b\n z)" "(f ;|\n z)" error)
    ("(f ;;| b\n z)" "(f ;;|\n z)" error)
    ("(f ;; |b\n z)" "(f ;; |\n z)" error)
    ("(f ;; b|\n z)" error)
    ("(f ;; b\n| z)" "(f ;; b\n|)" "(f ;; b\n|)")
    ("(f ;; b\n |z)" "(f ;; b\n |)" "(f ;; b\n |)")
    ("(f ;; b\n z|)" "(f ;; b\n z|)" "(f ;; b\n z|)")
    ("(f ;; b\n z)|" error)

    ("|(f b) ;z" "|" error)
    ("(|f b) ;z" "(|) ;z" "(|) ;z")
    ("(f| b) ;z" "(f|) ;z" "(f|) ;z")
    ("(f |b) ;z" "(f |) ;z" "(f |) ;z")
    ("(f b|) ;z" "(f b|) ;z" "(f b|) ;z")
    ("(f b)| ;z" "(f b)|" error)
    ("(f b) |;z" "(f b) |" error)
    ("(f b) ;|z" "(f b) ;|" error)
    ("(f b) ;z|" error)

    ("|(f b) ;z\n" "|\n" "|" error)
    ("(|f b) ;z\n" "(|) ;z\n" "(|) ;z\n")
    ("(f| b) ;z\n" "(f|) ;z\n" "(f|) ;z\n")
    ("(f |b) ;z\n" "(f |) ;z\n" "(f |) ;z\n")
    ("(f b|) ;z\n" "(f b|) ;z\n")
    ("(f b)| ;z\n" "(f b)|\n" "(f b)|" error)
    ("(f b) |;z\n" "(f b) |\n" "(f b) |" error)
    ("(f b) ;|z\n" "(f b) ;|\n" "(f b) ;|" error)
    ("(f b) ;z|\n" "(f b) ;z|" error)
    ("(f b) ;z\n|" error)

    ("|(f\n b) ;z" "| ;z" "|" error)
    ("(|f\n b) ;z" "(|\n b) ;z" "(| b) ;z" "(|) ;z" "(|) ;z")
    ("(f|\n b) ;z" "(f| b) ;z" "(f|) ;z" "(f|) ;z")
    ("(f\n| b) ;z" "(f\n|) ;z" "(f\n|) ;z")
    ("(f\n |b) ;z" "(f\n |) ;z" "(f\n |) ;z")
    ("(f\n b|) ;z" "(f\n b|) ;z")
    ("(f\n b)| ;z" "(f\n b)|" error)
    ("(f\n b) |;z" "(f\n b) |" error)
    ("(f\n b) ;|z" "(f\n b) ;|" error)
    ("(f\n b) ;z|" error)

    ("|(f\n b) ;z\n" "| ;z\n" "|\n" "|" error)
    ("(|f\n b) ;z\n" "(|\n b) ;z\n" "(| b) ;z\n" "(|) ;z\n" "(|) ;z\n")
    ("(f|\n b) ;z\n" "(f| b) ;z\n" "(f|) ;z\n" "(f|) ;z\n")
    ("(f\n| b) ;z\n" "(f\n|) ;z\n" "(f\n|) ;z\n")
    ("(f\n |b) ;z\n" "(f\n |) ;z\n" "(f\n |) ;z\n")
    ("(f\n b|) ;z\n" "(f\n b|) ;z\n")
    ("(f\n b)| ;z\n" "(f\n b)|\n" "(f\n b)|" error)
    ("(f\n b) |;z\n" "(f\n b) |\n" "(f\n b) |" error)
    ("(f\n b) ;|z\n" "(f\n b) ;|\n" "(f\n b) ;|" error)
    ("(f\n b) ;z|\n" "(f\n b) ;z|" error)
    ("(f\n b) ;z\n|" error)

    ("|;f\n(b)\n" "|\n(b)\n" "|(b)\n" "|\n" "|" error)
    (";|f\n(b)\n" ";|\n(b)\n" ";|(b)\n" ";|\n" ";|" error)
    (";f|\n(b)\n" ";f|(b)\n" ";f|\n" ";f|" error)
    (";f\n|(b)\n" ";f\n|\n" ";f\n|" error)
    (";f\n(|b)\n" ";f\n(|)\n" ";f\n(|)\n")
    (";f\n(b|)\n" ";f\n(b|)\n")
    (";f\n(b)|\n" ";f\n(b)|" error)
    (";f\n(b)\n|" error)

    ("|;f\n(b\n z)\n" "|\n(b\n z)\n" "|(b\n z)\n" "|\n" "|" error)
    (";|f\n(b\n z)\n" ";|\n(b\n z)\n" error)
    (";f|\n(b\n z)\n" error)
    (";f\n|(b\n z)\n" ";f\n|\n" ";f\n|" error)
    (";f\n(|b\n z)\n" ";f\n(|\n z)\n" ";f\n(| z)\n" ";f\n(|)\n" ";f\n(|)\n")
    (";f\n(b|\n z)\n" ";f\n(b| z)\n" ";f\n(b|)\n" ";f\n(b|)\n")
    (";f\n(b\n| z)\n" ";f\n(b\n|)\n" ";f\n(b\n|)\n")
    (";f\n(b\n |z)\n" ";f\n(b\n |)\n" ";f\n(b\n |)\n")
    (";f\n(b\n z|)\n" ";f\n(b\n z|)\n")))

(paredit-test 'paredit-backward-barf-sexp
  '(("|(fo)" error)
    ;++ I think these are wrong.  There should be a space.
    ("(|fo)" "|fo()" error)
    ("(f|o)" "f|o()" error)
    ("(fo|)" "fo(|)" "fo(|)")
    ("(fo)|" error)

    ("|(fo (ba bz qx) zt)" error)
    ("(|fo (ba bz qx) zt)" "|fo ((ba bz qx) zt)" error)
    ("(f|o (ba bz qx) zt)" "f|o ((ba bz qx) zt)" error)
    ("(fo| (ba bz qx) zt)" "fo| ((ba bz qx) zt)" error)
    ("(fo |(ba bz qx) zt)"
     "fo (|(ba bz qx) zt)"
     "fo |(ba bz qx) (zt)"
     error)
    ("(fo (|ba bz qx) zt)"
     "(fo |ba (bz qx) zt)"
     "fo (|ba (bz qx) zt)"
     "fo |ba ((bz qx) zt)"
     error)
    ("(fo (b|a bz qx) zt)"
     "(fo b|a (bz qx) zt)"
     "fo (b|a (bz qx) zt)"
     "fo b|a ((bz qx) zt)"
     error)
    ("(fo (ba| bz qx) zt)"
     "(fo ba| (bz qx) zt)"
     "fo (ba| (bz qx) zt)"
     "fo ba| ((bz qx) zt)"
     error)
    ("(fo (ba |bz qx) zt)"
     "(fo ba (|bz qx) zt)"
     "(fo ba |bz (qx) zt)"
     "fo (ba |bz (qx) zt)"
     "fo ba (|bz (qx) zt)"
     "fo ba |bz ((qx) zt)"
     error)
    ("(fo (ba b|z qx) zt)"
     "(fo ba (b|z qx) zt)"
     "(fo ba b|z (qx) zt)"
     "fo (ba b|z (qx) zt)"
     "fo ba (b|z (qx) zt)"
     "fo ba b|z ((qx) zt)"
     error)
    ("(fo (ba bz| qx) zt)"
     "(fo ba (bz| qx) zt)"
     "(fo ba bz| (qx) zt)"
     "fo (ba bz| (qx) zt)"
     "fo ba (bz| (qx) zt)"
     "fo ba bz| ((qx) zt)"
     error)

    ("(fo (ba bz |qx) zt)"
     "(fo ba (bz |qx) zt)"
     "(fo ba bz (|qx) zt)"
     "(fo ba bz |qx() zt)"        ;++ Should have a space.
     "fo (ba bz |qx() zt)"
     "fo ba (bz |qx() zt)"
     "fo ba bz (|qx() zt)"
     "fo ba bz |qx(() zt)"
     error)
    ("(fo (ba bz |qx) zt)"
     "(fo ba (bz |qx) zt)"
     "(fo ba bz (|qx) zt)"
     "(fo ba bz |qx() zt)"
     "fo (ba bz |qx() zt)"
     "fo ba (bz |qx() zt)"
     "fo ba bz (|qx() zt)"
     "fo ba bz |qx(() zt)"
     error)
    ("(fo (ba bz q|x) zt)"
     "(fo ba (bz q|x) zt)"
     "(fo ba bz (q|x) zt)"
     "(fo ba bz q|x() zt)"
     "fo (ba bz q|x() zt)"
     "fo ba (bz q|x() zt)"
     "fo ba bz (q|x() zt)"
     "fo ba bz q|x(() zt)"
     error)
    ("(fo (ba bz qx|) zt)"
     "(fo ba (bz qx|) zt)"
     "(fo ba bz (qx|) zt)"
     "(fo ba bz qx(|) zt)"
     "(fo ba bz qx(|) zt)")
    ("(fo (ba bz qx)| zt)"
     "fo ((ba bz qx)| zt)"
     "fo (ba bz qx)| (zt)"
     error)
    ("(fo (ba bz qx) |zt)"
     "fo ((ba bz qx) |zt)"
     "fo (ba bz qx) (|zt)"
     "fo (ba bz qx) |zt()"
     error)
    ("(fo (ba bz qx) z|t)"
     "fo ((ba bz qx) z|t)"
     "fo (ba bz qx) (z|t)"
     "fo (ba bz qx) z|t()"
     error)
    ("(fo (ba bz qx) zt|)"
     "fo ((ba bz qx) zt|)"
     "fo (ba bz qx) (zt|)"
     "fo (ba bz qx) zt(|)"
     "fo (ba bz qx) zt(|)")
    ("(fo (ba bz qx) zt)|" error)

    ;++ Test interaction with comments...

    ("\"|\"" error)
    ("\"|xy\"" error)                   ;++ Could be done.  Why not?
    ("\"x|y\"" error)
    ("\"xy|\"" error)))

(paredit-test 'paredit-forward
  '(("|" "|")

    ("|()" "()|" "()|")
    ("(|)" "()|" "()|")
    ("()|" "()|")

    ("|( )" "( )|" "( )|")
    ("(| )" "( )|" "( )|")
    ("( |)" "( )|" "( )|")
    ("( )|" "( )|")

    ("|\"\"" "\"\"|" "\"\"|")
    ("\"|\"" "\"\"|" "\"\"|")
    ("\"\"|" "\"\"|")

    ("|\")\"" "\")\"|" "\")\"|")
    ("\"|)\"" "\")|\"" "\")\"|" "\")\"|")
    ("\")|\"" "\")\"|" "\")\"|")
    ("\")\"|" "\")\"|")

    ("|\"()\"" "\"()\"|" "\"()\"|")
    ("\"|()\"" "\"()|\"" "\"()\"|" "\"()\"|")
    ("\"(|)\"" "\"()|\"" "\"()\"|" "\"()\"|")
    ("\"()\"|" "\"()\"|")

    ("|(\"x\" \"y\")" "(\"x\" \"y\")|" "(\"x\" \"y\")|")
    ("(|\"x\" \"y\")" "(\"x\"| \"y\")" "(\"x\" \"y\"|)"
     "(\"x\" \"y\")|" "(\"x\" \"y\")|")
    ("(\"|x\" \"y\")" "(\"x|\" \"y\")" "(\"x\"| \"y\")" "(\"x\" \"y\"|)"
     "(\"x\" \"y\")|" "(\"x\" \"y\")|")
    ("(\"x|\" \"y\")" "(\"x\"| \"y\")" "(\"x\" \"y\"|)"
     "(\"x\" \"y\")|" "(\"x\" \"y\")|")
    ("(\"x\"| \"y\")" "(\"x\" \"y\"|)" "(\"x\" \"y\")|" "(\"x\" \"y\")|")
    ("(\"x\" |\"y\")" "(\"x\" \"y\"|)" "(\"x\" \"y\")|" "(\"x\" \"y\")|")
    ("(\"x\" \"|y\")" "(\"x\" \"y|\")" "(\"x\" \"y\"|)"
     "(\"x\" \"y\")|" "(\"x\" \"y\")|")
    ("(\"x\" \"y|\")" "(\"x\" \"y\"|)" "(\"x\" \"y\")|" "(\"x\" \"y\")|")
    ("(\"x\" \"y\"|)" "(\"x\" \"y\")|" "(\"x\" \"y\")|")
    ("(\"x\" \"y\")|" "(\"x\" \"y\")|")

    ("|#\\(" "#\\(|" "#\\(|")
    ("#|\\(" "#\\(|" "#\\(|")
    ("#\\|(" "#\\(|" "#\\(|")
    ("#\\(|" "#\\(|")

    ("|#\\)" "#\\)|" "#\\)|")
    ("#|\\)" "#\\)|" "#\\)|")
    ("#\\|)" "#\\)|" "#\\)|")
    ("#\\)|" "#\\)|")

    ("|#\\\\" "#\\\\|" "#\\\\|")
    ("#|\\\\" "#\\\\|" "#\\\\|")
    ("#\\|\\" "#\\\\|" "#\\\\|")
    ("#\\\\|" "#\\\\|")

    ("|#\\;" "#\\;|" "#\\;|")
    ("#|\\;" "#\\;|" "#\\;|")
    ("#\\|;" "#\\;|" "#\\;|")
    ("#\\;|" "#\\;|")))

(paredit-test 'paredit-backward
  '(("|" "|")

    ("|()" "|()")
    ("(|)" "|()" "|()")
    ("()|" "|()" "|()")

    ("|( )" "|( )")
    ("(| )" "|( )" "|( )")
    ("( |)" "|( )" "|( )")
    ("( )|" "|( )" "|( )")

    ("|\"\"" "|\"\"")
    ("\"|\"" "|\"\"" "|\"\"")
    ("\"\"|" "|\"\"" "|\"\"")

    ("|\")\"" "|\")\"")
    ("\"|)\"" "|\")\"" "|\")\"")
    ("\")|\"" "|\")\"" "|\")\"")
    ("\")\"|" "|\")\"" "|\")\"")

    ("|\"()\"" "|\"()\"")
    ("\"|()\"" "|\"()\"" "|\"()\"")
    ("\"(|)\"" "\"|()\"" "|\"()\"" "|\"()\"")
    ("\"()\"|" "|\"()\"" "|\"()\"")

    ("|(\"x\" \"y\")" "|(\"x\" \"y\")")
    ("(|\"x\" \"y\")" "|(\"x\" \"y\")" "|(\"x\" \"y\")")
    ("(\"|x\" \"y\")" "(|\"x\" \"y\")" "|(\"x\" \"y\")" "|(\"x\" \"y\")")
    ("(\"x|\" \"y\")" "(\"|x\" \"y\")" "(|\"x\" \"y\")"
     "|(\"x\" \"y\")" "|(\"x\" \"y\")")
    ("(\"x\"| \"y\")" "(|\"x\" \"y\")" "|(\"x\" \"y\")" "|(\"x\" \"y\")")
    ("(\"x\" |\"y\")" "(|\"x\" \"y\")" "|(\"x\" \"y\")" "|(\"x\" \"y\")")
    ("(\"x\" \"|y\")" "(\"x\" |\"y\")" "(|\"x\" \"y\")"
     "|(\"x\" \"y\")" "|(\"x\" \"y\")")
    ("(\"x\" \"y|\")" "(\"x\" \"|y\")" "(\"x\" |\"y\")" "(|\"x\" \"y\")"
     "|(\"x\" \"y\")" "|(\"x\" \"y\")")
    ("(\"x\" \"y\"|)" "(\"x\" |\"y\")" "(|\"x\" \"y\")"
     "|(\"x\" \"y\")" "|(\"x\" \"y\")")
    ("(\"x\" \"y\")|" "|(\"x\" \"y\")" "|(\"x\" \"y\")")

    ("|#\\(" "|#\\(")
    ("#|\\(" "|#\\(" "|#\\(")
    ("#\\|(" "|#\\(" "|#\\(")
    ("#\\(|" "|#\\(" "|#\\(")

    ("|#\\)" "|#\\)")
    ("#|\\)" "|#\\)" "|#\\)")
    ("#\\|)" "|#\\)" "|#\\)")
    ("#\\)|" "|#\\)" "|#\\)")

    ("|#\\\\" "|#\\\\")
    ("#|\\\\" "|#\\\\" "|#\\\\")
    ("#\\|\\" "|#\\\\" "|#\\\\")
    ("#\\\\|" "|#\\\\" "|#\\\\")

    ("|#\\;" "|#\\;")
    ("#|\\;" "|#\\;" "|#\\;")
    ("#\\|;" "|#\\;" "|#\\;")
    ("#\\;|" "|#\\;" "|#\\;")))

(paredit-test 'paredit-join-sexps
  '(("|ab cd" error)
    ("a|b cd" error)
    ("ab| cd" "ab|cd" error)
    ("ab |cd" "ab|cd" error)
    ("ab c|d" error)
    ("ab cd|" error)

    ("|x (y)" error)
    ("x| (y)" error)
    ("x |(y)" error)
    ("x (|y)" error)
    ("x (y|)" error)
    ("x (y)|" error)

    ("|(x ((y)\n    (z)))" error)
    ("(|x ((y)\n    (z)))" error)
    ("(x| ((y)\n    (z)))" error)
    ("(x |((y)\n    (z)))" error)
    ("(x (|(y)\n    (z)))" error)
    ("(x ((|y)\n    (z)))" error)
    ("(x ((y)|\n    (z)))" "(x ((y|\n     z)))")
    ("(x ((y)\n|    (z)))" "(x ((y\n|     z)))")
    ("(x ((y)\n |   (z)))" "(x ((y\n |    z)))")
    ("(x ((y)\n  |  (z)))" "(x ((y\n  |   z)))")
    ("(x ((y)\n   | (z)))" "(x ((y\n   |  z)))")
    ;++ I don't think this is right.  The point shouldn't move right.
    ("(x ((y)\n    |(z)))" "(x ((y\n     |z)))")
    ("(x ((y)\n    (|z)))" error)
    ("(x ((y)\n    (z|)))" error)
    ("(x ((y)\n    (z)|))" error)
    ("(x ((y)\n    (z))|)" error)
    ("(x ((y)\n    (z)))|" error)

    ("|(ab cd) (ef \"gh\")" error)
    ("(|ab cd) (ef \"gh\")" error)
    ("(a|b cd) (ef \"gh\")" error)
    ("(ab| cd) (ef \"gh\")" "(ab|cd) (ef \"gh\")" error)
    ("(ab |cd) (ef \"gh\")" "(ab|cd) (ef \"gh\")" error)
    ("(ab c|d) (ef \"gh\")" error)
    ("(ab cd|) (ef \"gh\")" error)
    ("(ab cd)| (ef \"gh\")" "(ab cd| ef \"gh\")" "(ab cd|ef \"gh\")" error)
    ("(ab cd) |(ef \"gh\")" "(ab cd |ef \"gh\")" "(ab cd|ef \"gh\")" error)
    ("(ab cd) (|ef \"gh\")" error)
    ("(ab cd) (e|f \"gh\")" error)
    ("(ab cd) (ef| \"gh\")" error)
    ("(ab cd) (ef |\"gh\")" error)
    ("(ab cd) (ef \"g|h\")" error)
    ("(ab cd) (ef \"gh\"|)" error)
    ("(ab cd) (ef \"gh\")|" error)

    ("|() \"\"" error)
    ("(|) \"\"" error)
    ("()| \"\"" error)
    ("() |\"\"" error)
    ("() \"|\"" error)
    ("() \"\"|" error)

    ("|\"\" ()" error)
    ("\"|\" ()" error)
    ("\"\"| ()" error)
    ("\"\" |()" error)
    ("\"\" (|)" error)
    ("\"\" (|)|" error)

    ("|(x y) [z]" error)
    ("(|x y) [z]" error)
    ("(x| y) [z]" "(x|y) [z]" error)
    ("(x |y) [z]" "(x|y) [z]" error)
    ("(x y|) [z]" error)
    ("(x y)| [z]" error)
    ("(x y) |[z]" error)
    ("(x y) [|z]" error)
    ("(x y) [z|]" error)
    ("(x y) [z]|" error)

    ("|(x)(y)" error)
    ("(|x)(y)" error)
    ("(x|)(y)" error)
    ("(x)|(y)" "(x| y)")
    ("(x)(|y)" error)
    ("(x)(y|)" error)
    ("(x)(y)|" error)

    ("|\"ab\"  \"cd\"" error)
    ("\"|ab\"  \"cd\"" error)
    ("\"a|b\"  \"cd\"" error)
    ("\"ab\"|  \"cd\"" "\"ab|cd\"" error)
    ("\"ab\" | \"cd\"" "\"ab|cd\"" error)
    ("\"ab\"  |\"cd\"" "\"ab|cd\"" error)
    ("\"ab\"  \"|cd\"" error)
    ("\"ab\"  \"c|d\"" error)
    ("\"ab\"  \"cd|\"" error)
    ("\"ab\"  \"cd\"|" error)

    ("|(x ((y)\n    (z)))" error)
    ("(|x ((y)\n    (z)))" error)
    ("(x| ((y)\n    (z)))" error)
    ("(x |((y)\n    (z)))" error)
    ("(x ((|y)\n    (z)))" error)
    ("(x ((y)|\n    (z)))" "(x ((y|\n     z)))" "(x ((y|z)))" error)
    ("(x ((y)\n|    (z)))" "(x ((y\n|     z)))" "(x ((y|z)))" error)
    ("(x ((y)\n |   (z)))" "(x ((y\n |    z)))" "(x ((y|z)))" error)
    ("(x ((y)\n  |  (z)))" "(x ((y\n  |   z)))" "(x ((y|z)))" error)
    ("(x ((y)\n   | (z)))" "(x ((y\n   |  z)))" "(x ((y|z)))" error)
    ("(x ((y)\n    |(z)))" "(x ((y\n     |z)))" "(x ((y|z)))" error)
    ("(x ((y)\n    (|z)))" error)
    ("(x ((y)\n    (z|)))" error)
    ("(x ((y)\n    (z)|))" error)
    ("(x ((y)\n    (z))|)" error)
    ("(x ((y)\n    (z)))|" error)

    ;++ What about comments intervening strings/symbols?
    ("|((x)                                    ;c\n (y))" error)
    ("(|(x)                                    ;c\n (y))" error)
    ("((|x)                                    ;c\n (y))" error)
    ("((x|)                                    ;c\n (y))" error)
    ("((x)|                                    ;c\n (y))"
     "((x|                                     ;c\n  y))")
    ("((x) |                                   ;c\n (y))"
     "((x  |                                   ;c\n  y))")
    ("((x)                 |                   ;c\n (y))"
     "((x                  |                   ;c\n  y))")
    ("((x)                                   | ;c\n (y))"
     "((x                                    | ;c\n  y))")
    ("((x)                                    |;c\n (y))"
     "((x                                     |;c\n  y))")
    ("((x)                                    ;|c\n (y))" error)
    ("((x)                                    ;c|\n (y))" error)
    ("((x)                                    ;c\n| (y))"
     "((x                                     ;c\n|  y))")
    ("((x)                                    ;c\n |(y))"
     "((x                                     ;c\n  |y))")
    ("((x)                                    ;c\n (|y))" error)
    ("((x)                                    ;c\n (y|))" error)
    ("((x)                                    ;c\n (y)|)" error)
    ("((x)                                    ;c\n (y))|" error)))

(paredit-test 'paredit-meta-doublequote
  '(("|(fo \"ba\\\" bz\" qx)" "\"|(fo \\\"ba\\\\\\\" bz\\\" qx)\"")
    ("(|fo \"ba\\\" bz\" qx)" "(\"|fo\" \"ba\\\" bz\" qx)")
    ("(f|o \"ba\\\" bz\" qx)" "(f \"|o\" \"ba\\\" bz\" qx)")
    ;++ Should the space be left there after the `"'?
    ("(fo| \"ba\\\" bz\" qx)" "(fo \"| \\\"ba\\\\\\\" bz\\\"\" qx)")
    ("(fo |\"ba\\\" bz\" qx)" "(fo \"|\\\"ba\\\\\\\" bz\\\"\" qx)")
    ("(fo \"|ba\\\" bz\" qx)" "(fo \"ba\\\" bz\"| qx)")
    ("(fo \"b|a\\\" bz\" qx)" "(fo \"ba\\\" bz\"| qx)")
    ("(fo \"ba|\\\" bz\" qx)" "(fo \"ba\\\" bz\"| qx)")
    ("(fo \"ba\\|\" bz\" qx)" "(fo \"ba\\\" bz\"| qx)")
    ("(fo \"ba\\\"| bz\" qx)" "(fo \"ba\\\" bz\"| qx)")
    ("(fo \"ba\\\" |bz\" qx)" "(fo \"ba\\\" bz\"| qx)")
    ("(fo \"ba\\\" b|z\" qx)" "(fo \"ba\\\" bz\"| qx)")
    ("(fo \"ba\\\" bz|\" qx)" "(fo \"ba\\\" bz\"| qx)")
    ;++ Should the space be left there after the `"'?
    ("(fo \"ba\\\" bz\"| qx)" "(fo \"ba\\\" bz\" \"| qx\")")
    ("(fo \"ba\\\" bz\" |qx)" "(fo \"ba\\\" bz\" \"|qx\")")
    ("(fo \"ba\\\" bz\" q|x)" "(fo \"ba\\\" bz\" q \"|x\")")
    ("(fo \"ba\\\" bz\" qx|)" "(fo \"ba\\\" bz\" qx \"|\")")
    ("(fo \"ba\\\" bz\" qx)|" "(fo \"ba\\\" bz\" qx) \"|\"")

    ;++ Full tests...
    ("(foo |(bar #\\x \"baz \\\\ quux\") zot)"
     "(foo \"|(bar #\\\\x \\\"baz \\\\\\\\ quux\\\")\" zot)")))

;++ Copy tests from `paredit-meta-doublequote'...

(paredit-test 'paredit-meta-doublequote-and-newline
  '(("(foo \"bar |baz\" quux)"
     "(foo \"bar baz\"\n     |quux)")
    ("(foo |(bar #\\x \"baz \\\\ quux\") zot)"
     "(foo \"|(bar #\\\\x \\\"baz \\\\\\\\ quux\\\")\" zot)")))

(paredit-test 'paredit-splice-sexp
  '(("|(f (g\n    h))" error)
    ("(|f (g\n    h))" "|f (g\n   h)")
    ("(f| (g\n    h))" "f| (g\n   h)")
    ("(f |(g\n    h))" "f |(g\n   h)")
    ("(f (|g\n    h))" "(f |g\n   h)")
    ("(f (g|\n    h))" "(f g|\n   h)")
    ("(f (g\n|    h))" "(f g\n|   h)")
    ("(f (g\n |   h))" "(f g\n |  h)")
    ("(f (g\n  |  h))" "(f g\n  | h)")
    ("(f (g\n   | h))" "(f g\n   |h)")
    ("(f (g\n    |h))" "(f g\n   |h)")
    ("(f (g\n    h|))" "(f g\n   h|)")
    ("(f (g\n    h)|)" "f (g\n   h)|")
    ("(f (g\n    h))|" error)

    ;; Omit whitespace if appropriate.
    ("|(f (\n    h))" error)
    ("(|f (\n    h))" "|f (\n   h)")
    ("(f| (\n    h))" "f| (\n   h)")
    ("(f |(\n    h))" "f |(\n   h)")
    ("(f (|\n    h))" "(f |h)")
    ("(f (\n|    h))" "(f |h)")
    ("(f (\n |   h))" "(f |h)")
    ("(f (\n  |  h))" "(f |h)")
    ("(f (\n   | h))" "(f |h)")
    ("(f (\n    |h))" "(f |h)")
    ("(f (\n    h|))" "(f h|)")
    ("(f (\n    h)|)" "f (\n   h)|")
    ("(f (\n    h))|" error)

    ;; But leave comments intact.
    ("(f (|   ;xy\n    h))" "(f |;xy\n h)")
    ("(f ( |  ;xy\n    h))" "(f |;xy\n h)")
    ("(f (  | ;xy\n    h))" "(f |;xy\n h)")
    ("(f (   |;xy\n    h))" "(f |;xy\n h)")
    ("(f (   ;|xy\n    h))" error)
    ("(f (   ;x|y\n    h))" error)
    ("(f (   ;xy|\n    h))" error)
    ("(f (   ;xy\n|    h))" "(f ;xy\n| h)")
    ("(f (   ;xy\n |   h))" "(f ;xy\n |h)")
    ("(f (   ;xy\n  |  h))" "(f ;xy\n |h)")
    ("(f (   ;xy\n   | h))" "(f ;xy\n |h)")
    ("(f (   ;xy\n    |h))" "(f ;xy\n |h)")
    ("(f (   ;xy\n    h|))" "(f ;xy\n h|)")

    ;; Don't touch indentation outside a limited scope.
    ("(foo (|bar)\n          baz)" "(foo |bar\n          baz)")
    ("(foo (b|ar)\n          baz)" "(foo b|ar\n          baz)")
    ("(foo (ba|r)\n          baz)" "(foo ba|r\n          baz)")
    ("(foo (bar|)\n          baz)" "(foo bar|\n          baz)")
    ("  (foo\n  (|bar baz))" "  (foo\n  |bar baz)")
    ("  (foo\n  (b|ar baz))" "  (foo\n  b|ar baz)")
    ("  (foo\n  (ba|r baz))" "  (foo\n  ba|r baz)")
    ("  (foo\n  (bar| baz))" "  (foo\n  bar| baz)")
    ("  (foo\n  (bar |baz))" "  (foo\n  bar |baz)")
    ("  (foo\n  (bar b|az))" "  (foo\n  bar b|az)")
    ("  (foo\n  (bar ba|z))" "  (foo\n  bar ba|z)")
    ("  (foo\n  (bar baz|))" "  (foo\n  bar baz|)")
    ("  (foo (|(bar\n         baz)\n        quux)\n zot)"
     "  (foo |(bar\n        baz)\n       quux\n zot)")
    ("  (foo ((|bar\n         baz)\n        quux)\n zot)"
     "  (foo (|bar\n        baz\n        quux)\n zot)")
    ("  (foo ((b|ar\n         baz)\n        quux)\n zot)"
     "  (foo (b|ar\n        baz\n        quux)\n zot)")
    ("  (foo ((ba|r\n         baz)\n        quux)\n zot)"
     "  (foo (ba|r\n        baz\n        quux)\n zot)")
    ("  (foo ((ba|r\n         baz)\n        quux)\n zot)"
     "  (foo (ba|r\n        baz\n        quux)\n zot)")
    ("  (foo ((bar|\n         baz)\n        quux)\n zot)"
     "  (foo (bar|\n        baz\n        quux)\n zot)")
    ("  (foo ((bar\n|         baz)\n        quux)\n zot)"
     "  (foo (bar\n|        baz\n        quux)\n zot)")
    ("  (foo ((bar\n |        baz)\n        quux)\n zot)"
     "  (foo (bar\n |       baz\n        quux)\n zot)")
    ("  (foo ((bar\n  |       baz)\n        quux)\n zot)"
     "  (foo (bar\n  |      baz\n        quux)\n zot)")
    ("  (foo ((bar\n   |      baz)\n        quux)\n zot)"
     "  (foo (bar\n   |     baz\n        quux)\n zot)")
    ("  (foo ((bar\n    |     baz)\n        quux)\n zot)"
     "  (foo (bar\n    |    baz\n        quux)\n zot)")
    ("  (foo ((bar\n     |    baz)\n        quux)\n zot)"
     "  (foo (bar\n     |   baz\n        quux)\n zot)")
    ("  (foo ((bar\n      |   baz)\n        quux)\n zot)"
     "  (foo (bar\n      |  baz\n        quux)\n zot)")
    ("  (foo ((bar\n       |  baz)\n        quux)\n zot)"
     "  (foo (bar\n       | baz\n        quux)\n zot)")
    ("  (foo ((bar\n        | baz)\n        quux)\n zot)"
     "  (foo (bar\n        |baz\n        quux)\n zot)")
    ("  (foo ((bar\n         |baz)\n        quux)\n zot)"
     "  (foo (bar\n        |baz\n        quux)\n zot)")

    ("  (foo ((bar\n         b|az)\n        quux)\n zot)"
     "  (foo (bar\n        b|az\n        quux)\n zot)")
    ("  (foo ((bar\n         ba|z)\n        quux)\n zot)"
     "  (foo (bar\n        ba|z\n        quux)\n zot)")
    ("  (foo ((bar\n         baz|)\n        quux)\n zot)"
     "  (foo (bar\n        baz|\n        quux)\n zot)")
    ("  (foo ((bar\n         baz)|\n        quux)\n zot)"
     "  (foo (bar\n        baz)|\n       quux\n zot)")
    ("  (foo ((bar\n         baz)\n|        quux)\n zot)"
     "  (foo (bar\n        baz)\n|       quux\n zot)")
    ("  (foo ((bar\n         baz)\n |       quux)\n zot)"
     "  (foo (bar\n        baz)\n |      quux\n zot)")
    ("  (foo ((bar\n         baz)\n  |      quux)\n zot)"
     "  (foo (bar\n        baz)\n  |     quux\n zot)")
    ("  (foo ((bar\n         baz)\n   |     quux)\n zot)"
     "  (foo (bar\n        baz)\n   |    quux\n zot)")
    ("  (foo ((bar\n         baz)\n    |    quux)\n zot)"
     "  (foo (bar\n        baz)\n    |   quux\n zot)")
    ("  (foo ((bar\n         baz)\n     |   quux)\n zot)"
     "  (foo (bar\n        baz)\n     |  quux\n zot)")
    ("  (foo ((bar\n         baz)\n      |  quux)\n zot)"
     "  (foo (bar\n        baz)\n      | quux\n zot)")
    ("  (foo ((bar\n         baz)\n       | quux)\n zot)"
     "  (foo (bar\n        baz)\n       |quux\n zot)")
    ("  (foo ((bar\n         baz)\n        |quux)\n zot)"
     "  (foo (bar\n        baz)\n       |quux\n zot)")
    ("  (foo ((bar\n         baz)\n        q|uux)\n zot)"
     "  (foo (bar\n        baz)\n       q|uux\n zot)")
    ("  (foo ((bar\n         baz)\n        qu|ux)\n zot)"
     "  (foo (bar\n        baz)\n       qu|ux\n zot)")
    ("  (foo ((bar\n         baz)\n        quu|x)\n zot)"
     "  (foo (bar\n        baz)\n       quu|x\n zot)")
    ("  (foo ((bar\n         baz)\n        quux|)\n zot)"
     "  (foo (bar\n        baz)\n       quux|\n zot)")

    ;; But adjust the whole form's indentation if we change the operator.
    ("((|let) ((a b))\n       c)" "(|let ((a b))\n  c)")
    ("((l|et) ((a b))\n       c)" "(l|et ((a b))\n  c)")
    ("((le|t) ((a b))\n       c)" "(le|t ((a b))\n  c)")
    ("((let|) ((a b))\n       c)" "(let| ((a b))\n  c)")

    ;; Uh oh -- you can really lose here.
    ("\"|foo\\\"bar\"" error)
    ;++ ("(\"|foo\\\;bar\")" error)
    ))

(paredit-test 'paredit-forward-slurp-sexp
  '(("|" error)
    ("|()" error)
    ;; ("(|)" error)                    ;++ Urk...
    ("()|" error)
    ("|() foo" error)
    ("(|) foo" "(|foo)")
    ("()| foo" error)
    ("() |foo" error)
    ("() f|oo" error)
    ("() fo|o" error)
    ("() foo|" error)
    ("|(foo) bar" error)
    ("(|foo) bar" "(|foo bar)")
    ("(f|oo) bar" "(f|oo bar)")
    ("(fo|o) bar" "(fo|o bar)")
    ("(foo|) bar" "(foo| bar)")
    ("(foo)| bar" error)
    ("(foo) |bar" error)
    ("(foo) b|ar" error)
    ("(foo) ba|r" error)
    ("(foo) bar|" error)
    ("|\"\"" error)
    ;; ("\"|\"" error)                  ;++ Urk...
    ("\"\"|" error)
    ("|\"\" foo" error)
    ("\"|\" foo" "\"|foo\"")
    ("\"\"| foo" error)
    ("\"\" |foo" error)
    ("\"\" f|oo" error)
    ("\"\" fo|o" error)
    ("\"\" foo|" error)
    ("|\"foo\" bar" error)
    ("\"|foo\" bar" "\"|foo bar\"")
    ("\"f|oo\" bar" "\"f|oo bar\"")
    ("\"fo|o\" bar" "\"fo|o bar\"")
    ("\"foo|\" bar" "\"foo| bar\"")
    ("\"foo\"| bar" error)
    ("\"foo\" |bar" error)
    ("\"foo\" b|ar" error)
    ("\"foo\" ba|r" error)
    ("\"foo\" bar|" error)
    ("|\"\" \"\"" error)
    ("\"|\" \"\"" "\"|\\\"\\\"\"")
    ("\"\"| \"\"" error)
    ("\"\" |\"\"" error)
    ;; ("\"\" \"|\"" error)             ;++ Urk...
    ("\"\" \"\"|" error)
    ("|(#\\x) y" error)
    ("(|#\\x) y" "(|#\\x y)")
    ("(#|\\x) y" "(#|\\x y)")
    ("(#\\|x) y" "(#\\|x y)")
    ("(#\\x|) y" "(#\\x| y)")
    ("(#\\x)| y" error)
    ("(#\\x) |y" error)
    ("(#\\x) y|" error)
    ("|(\"x\") y" error)
    ("(|\"x\") y" "(|\"x\" y)")
    ("(\"|x\") y" "(\"|x\" y)" "(\"|x y\")")
    ("(\"x|\") y" "(\"x|\" y)" "(\"x| y\")")
    ("(\"x\"|) y" "(\"x\"| y)")
    ("(\"x\")| y" error)
    ("(\"x\") |y" error)
    ("(\"x\") y|" error)))

(paredit-test 'paredit-backward-slurp-sexp
  '(("|" error)
    ("|()" error)
    ;; ("(|)" error)                    ;++ Urk...
    ("()|" error)
    ("|foo ()" error)
    ("f|oo ()" error)
    ("fo|o ()" error)
    ("foo| ()" error)
    ("foo |()" error)
    ("foo (|)" "(foo|)")
    ("foo ()|" error)
    ("|foo (bar)" error)
    ("f|oo (bar)" error)
    ("fo|o (bar)" error)
    ("foo| (bar)" error)
    ("foo |(bar)" error)
    ("foo (|bar)" "(foo |bar)")
    ("foo (b|ar)" "(foo b|ar)")
    ("foo (ba|r)" "(foo ba|r)")
    ("foo (bar|)" "(foo bar|)")
    ("foo (bar)|" error)
    ("|\"\"" error)
    ;; ("\"|\"" error)                  ;++ Urk...
    ("\"\"|" error)
    ("|foo \"\"" error)
    ("f|oo \"\"" error)
    ("fo|o \"\"" error)
    ("foo| \"\"" error)
    ("foo |\"\"" error)
    ("foo \"|\"" "\"foo|\"")
    ("foo \"\"|" error)
    ("|foo \"bar\"" error)
    ("f|oo \"bar\"" error)
    ("fo|o \"bar\"" error)
    ("foo| \"bar\"" error)
    ("foo |\"bar\"" error)
    ("foo \"|bar\"" "\"foo |bar\"")
    ("foo \"b|ar\"" "\"foo b|ar\"")
    ("foo \"ba|r\"" "\"foo ba|r\"")
    ("foo \"bar|\"" "\"foo bar|\"")
    ("foo \"bar\"|" error)
    ("|\"\" \"\"" error)
    ;; ("\"|\" \"\"" error)             ;++ Urk...
    ("\"\"| \"\"" error)
    ("\"\" |\"\"" error)
    ("\"\" \"|\"" "\"\\\"\\\"|\"")
    ("\"\" \"\"|" error)
    ("|x (#\\y)" error)
    ("x| (#\\y)" error)
    ("x |(#\\y)" error)
    ("x (|#\\y)" "(x |#\\y)")
    ("x (#|\\y)" "(x #|\\y)")
    ("x (#\\|y)" "(x #\\|y)")
    ("x (#\\y|)" "(x #\\y|)")
    ("x (#\\y)|" error)
    ("|x (\"y\")" error)
    ("x| (\"y\")" error)
    ("x |(\"y\")" error)
    ("x (|\"y\")" "(x |\"y\")")
    ("x (\"|y\")" "(x \"|y\")" "(\"x |y\")")
    ("x (\"y|\")" "(x \"y|\")" "(\"x y|\")")
    ("x (\"y\"|)" "(x \"y\"|)")
    ("x (\"y\")|" error)))

(let ((current-prefix-arg 2))
  (paredit-test 'paredit-forward-slurp-sexp
    '(("(foo|) bar baz" "(foo| bar baz)")))
  (paredit-test 'paredit-backward-slurp-sexp
    '(("foo bar (|baz)" "(foo bar |baz)")))
  (paredit-test 'paredit-forward-barf-sexp
    '(("(foo| bar baz)" "(foo|) bar baz")
      ("(foo |bar baz)" "(foo) |bar baz")))
  (paredit-test 'paredit-backward-barf-sexp
    '(("(foo bar| baz)" "foo bar| (baz)")
      ("(foo bar |baz)" "foo bar (|baz)"))))

(let ((current-prefix-arg -2))
  (paredit-test 'paredit-forward-slurp-sexp
    '(("(foo| bar baz)" "(foo|) bar baz")
      ("(foo |bar baz)" "(foo) |bar baz")))
  (paredit-test 'paredit-backward-slurp-sexp
    '(("(foo bar| baz)" "foo bar| (baz)")
      ("(foo bar |baz)" "foo bar (|baz)")))
  (paredit-test 'paredit-forward-barf-sexp
    '(("(foo|) bar baz" "(foo| bar baz)")))
  (paredit-test 'paredit-backward-barf-sexp
    '(("foo bar (|baz)" "(foo bar |baz)"))))

(let ((current-prefix-arg '(4)))
  (paredit-test 'paredit-forward-slurp-sexp
    '(("(foo|) bar baz" "(foo| bar baz)")
      ("(foo| bar) baz" "(foo| bar baz)")))
  (paredit-test 'paredit-backward-slurp-sexp
    '(("foo bar (|baz)" "(foo bar |baz)")
      ("foo (bar |baz)" "(foo bar |baz)")))
  (paredit-test 'paredit-forward-barf-sexp
    '(("(foo| bar baz)" "(foo|) bar baz")
      ("(foo |bar baz)" "(foo) |bar baz")
      ("(foo b|ar baz)" "(foo b|ar) baz")))
  (paredit-test 'paredit-backward-barf-sexp
    '(("(foo ba|r baz)" "foo (ba|r baz)")
      ("(foo bar| baz)" "foo bar| (baz)")
      ("(foo bar |baz)" "foo bar (|baz)"))))

(defun paredit-canary-indent-method (state indent-point normal-indent)
  (check-parens)
  nil)

(put 'paredit-canary 'scheme-indent-function 'paredit-canary-indent-method)

;;; Check for regressions the indentation behaviour of forward slurping
;;; and barfing.

(paredit-test 'paredit-forward-slurp-sexp
  '(("(paredit-canary|)\n(lose)"
     "(paredit-canary|\n (lose))")))

(paredit-test 'paredit-forward-barf-sexp
  '(("(paredit-canary|  ;\n (lose))")
    ("(paredit-canary|  ;\n)\n(lose)")))

(paredit-test 'paredit-convolute-sexp
  '(("(let ((x 5) (y 3)) |(frob (zwonk)) (wibblethwop))" error)
    ("(let ((x 0)) (progn| x))" "(progn |(let ((x 0)) x))")
    ;; Should the space be left inside the LET?  In both cases?
    ("(let ((x 0)) (progn| ))" "(progn |(let ((x 0)) ))")
    ("(let ((x 0)) (progn|))" "(progn |(let ((x 0)) ))")
    ;; One space should definitely be left between A and B here.
    ("(let ((x 0)) a(progn|)b)" "(progn |(let ((x 0)) a b))")
    ("(let ((x 0)) a (progn|) b)" "(progn |(let ((x 0)) a b))")
    ("(let ((x 0)) a (progn| ) b)" "(progn |(let ((x 0)) a b))")
    ("(let ((x 0)) a (progn |) b)" "(progn |(let ((x 0)) a b))")))

(paredit-test 'paredit-raise-sexp
  `((,(concat
       "(let ((x 5))\n  (let ((y 3))\n    |(foo bar\n         baz)\n"
       "    (quux))\n   (wrong indent))")
     "(let ((x 5))\n  |(foo bar\n       baz)\n   (wrong indent))")
    ("(define (f x #!optional\n (|wrong indent))\n  (+ 1 2))"
     "(define (f x #!optional\n |wrong)\n  (+ 1 2))")))
