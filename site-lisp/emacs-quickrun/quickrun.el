;;; quickrun.el --- Run commands quickly

;; Copyright (C) 2011, 2012 by Syohei YOSHIDA

;; Author: Syohei YOSHIDA <syohex@gmail.com>
;; URL: https://github.com/syohex/emacs-quickrun
;; Version: 1.0

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

;; quickrun.el executes editing buffer. quickrun.el selects commands to execute
;; buffer automatically. Please see https://github.com/syohex/emacs-quickrun
;; for more information.
;;
;; This package respects `quickrun.vim' developed by thinca
;;   - https://github.com/thinca/vim-quickrun
;;
;; To use this package, add these lines to your .emacs file:
;;     (require 'quickrun)
;;
;; And you call 'M-x quickrun'.
;;

;;; History:

;; Version 1.0  2012/04/30 syohex
;; Fixed PHP CR problem(Thanks to mat)

;; Version 0.9  2012/04/08 syohex
;; Fix problem of not removing temporary file on Windows.

;; Version 0.8  2012/03/19 syohex
;; Support Dart and Elixir

;; Version 0.7  2012/02/14 syohex
;; Support Mozilla Rust language(Thanks to koko1000ban).

;; Version 0.6  2012/02/14 syohex
;; Implement 'multi' outputter.
;; Change outputter:buffer behavior, not popup-buffer.

;; Version 0.5  2012/02/08 syohex
;; Add quickrun group and modify global variable with `customize'

;; Version 0.4  2012/01/18 syohex
;; Fix command-alist of emacs lisp and update its sample
;; Fix case of that scroll-conservatively is not zero.

;; Version 0.3  2012/01/12 syohex
;; Support command line arguments that contain spaces or tabs
;; Add Common Lisp command-alist(ccl and sbcl)

;; Version 0.2  2012/01/06 syohex
;; Fix for Windows(Thanks to leoncamel)

;; Version 0.1  2011/12/31 syohex
;; init version


;;; Code:

(eval-when-compile
  (require 'cl))

(require 'ansi-color)

(defgroup quickrun nil
  "Execute buffer quickly"
  :group 'processes
  :prefix 'quickrun)

(defcustom quickrun-timeout-seconds 10
  "Timeout seconds for running too long process"
  :type 'integer
  :group 'quickrun)

(defcustom quickrun-debug nil
  "Enable debug message"
  :type 'boolean
  :group 'quickrun)

(defconst quickrun/buffer-name "*quickrun*")

;;
;; language command parameters
;;

(defvar quickrun/language-alist
  '(("c/gcc" . ((:command . "gcc")
                (:exec    . ("%c %o -o %e %s" "%e %a"))
                (:compile-only . "%c -Wall -Werror %o -o %e %s")
                (:remove . ("%e"))
                (:description . "Compile C file with gcc and execute")))

    ("c/clang" . ((:command . "clang")
                  (:exec    . ("%c %o -o %e %s" "%e %a"))
                  (:compile-only . "%c -Wall -Werror %o -o %e %s")
                  (:remove  . ("%e"))
                  (:description . "Compile C file with llvm/clang and execute")))

    ("c/cl" . ((:command . "cl")
               (:exec    . ("%c %o %s /nologo /Fo%n.obj /Fe%n.exe"
                            "%n %a"))
               (:compile-only . "%c %o %s /Wall /nologo /Fo%n.obj /Fe%n.exe")
               (:remove  . ("%n.obj" "%n.exe"))
               (:description . "Compile C file with VC++/cl and execute")))

    ("c++/g++" . ((:command . "g++")
                  (:exec    . ("%c %o -o %e %s" "%e %a"))
                  (:compile-only . "%c -Wall -Werror %o -o %e %s")
                  (:remove  . ("%e"))
                  (:description . "Compile C++ file with g++ and execute")))

    ("c++/clang++" . ((:command . "clang++")
                      (:exec    . ("%c %o -o %e %s" "%e %a"))
                      (:compile-only . "%c -Wall -Werror %o -o %e %s")
                      (:remove  . ("%e"))
                      (:description . "Compile C++ file with llvm/clang++ and execute")))

    ("c++/cl" . ((:command . "cl")
                 (:exec    . ("%c %o %s /nologo /Fo%n.obj /Fe%n.exe"
                              "%n %a"))
                 (:compile-only . "%c %o %s /Wall /nologo /Fo%n.obj /Fe%n.exe")
                 (:remove  . ("%n.obj" "%n.exe"))
                 (:description . "Compile C++ file with VC/cl and execute")))

    ("objc" . ((:command . "gcc")
               (:exec    . ((lambda ()
                              (cond ((string= system-type "darwin")
                                     "%c %o -o %e %s -framework foundation")
                                    (t "%c %o -o %e %s -lobjc")))
                            "%e %a"))
               (:remove  . ("%e"))
               (:description . "Compile Objective-C file with gcc and execute")))

    ("d" . ((:command . "dmd")
            (:exec    . ("%c %o -of%e %s" "%e %a"))
            (:remove  . ("%e" "%n.o"))
            (:description . "Compile D language file and execute")))

    ("java" . ((:command . "java")
               (:compile-only . "javac -Werror %o %s")
               (:exec    . ("javac %o %s" "%c %N %a"))
               (:remove  . ("%n.class"))
               (:description . "Compile Java file and execute")))

    ("perl" . ((:command . "perl") (:compile-only . "%c -wc %s")
               (:description . "Run Perl script")))
    ("ruby" . ((:command . "ruby") (:compile-only . "%c -wc %s")
               (:description . "Run Ruby script")))
    ("python" . ((:command . "python") (:compile-only . "pyflakes %s")
                 (:description . "Run Python script")))
    ("php" . ((:command . "php") (:compile-only . "%c -l %s")
              (:description . "Run PHP script")))

    ("emacs" . ((:command . "emacs")
                (:exec    . "%c -q --no-site-file --batch -l %s")
                (:description . "Run Elisp as script file")))
    ("lisp/clisp" . ((:command . "clisp")
                     (:description . "Run Lisp file with clisp")))
    ("lisp/sbcl" . ((:command . "sbcl")
                    (:exec . "%c --script %s %a")
                    (:description . "Run Lisp file with sbcl")))
    ("lisp/ccl" . ((:command . "ccl")
                   (:exec . "%c --load %s --eval '(quit)'")
                   (:description . "Run Lisp file with ccl")))
    ("scheme/gosh" . ((:command . "gosh")
                      (:description . "Run Scheme file with gosh(Gauche)")))

    ("clojure/jark"        . ((:command . "jark")
                              (:description . "Run Clojure file with jark")))
    ("clojure/clj-env-dir" . ((:command . "clj-env-dir")
                              (:description . "Run Clojure file with clj-env-dir")))

    ("javascript/node" . ((:command . "node")
                          (:description . "Run Javascript file with node.js")))
    ("javascript/v8" . ((:command . "v8")
                        (:description . "Run Javascript file with v8")))
    ("javascript/js" . ((:command . "js")
                        (:description . "Run Javascript file with js(Rhino)")))
    ("javascript/jrunscript" . ((:command . "jrunscript")
                                (:description . "Run Javascript file with jrunscript")))
    ("javascript/phantomjs" . ((:command . "phantomjs")
                               (:description . "Run Javascript file with phantomjs")))
    ("javascript/cscript" . ((:command . "cscript")
                             (:exec . "%c //e:jscript %o %s %a")
                             (:cmdopt . "//Nologo")
                             (:description . "Run Javascript file with cscript")))

    ("coffee" . ((:command . "coffee")
                 (:description . "Run Coffee script")))

    ("markdown/Markdown.pl" . ((:command . "Markdown.pl")
                               (:description . "Convert Markdown to HTML with Markdown.pl")))
    ("markdown/bluecloth"   . ((:command . "bluecloth")
                               (:cmdopt  . "-f")
                               (:description . "Convert Markdown to HTML with bluecloth")))
    ("markdown/kramdown"    . ((:command . "kramdown")
                               (:description . "Convert Markdown to HTML with kramdown")))
    ("markdown/pandoc"      . ((:command . "pandoc")
                               (:exec . "%c --from=markdown --to=html %o %s %a")
                               (:description . "Convert Markdown to HTML with pandoc")))
    ("markdown/redcarpet"   . ((:command . "redcarpet")
                               (:description . "Convert Markdown to HTML with redcarpet")))

    ("haskell" . ((:command . "runghc")
                  (:description . "Run Haskell file with runghc(GHC)")))

    ("go/8g"  .  ((:command . "8g")
                  (:exec    . ("%c %o -o %n.8 %s"
                               "8l -o %e %n.8"
                               "%e %a"))
                  (:remove  . ("%e" "%n.8"))
                  (:description . "Compile Go file with 8g(x86) and execute")))
    ("go/6g"  .  ((:command . "6g")
                  (:exec    . ("%c %o -o %n.6 %s"
                               "6l -o %e %n.6"
                               "%e %a"))
                  (:remove  . ("%e" "%n.6"))
                  (:description . "Compile Go file with 6g(x64) and execute")))
    ("go/5g"  .  ((:command . "5g")
                  (:exec    . ("%c %o -o %n.5 %s"
                               "5l -o %e %n.5"
                               "%e %a"))
                  (:remove  . ("%e" "%n.5"))
                  (:description . "Compile Go file with 5g(ARM) and execute")))

    ("io" . ((:command . "io")
             (:description . "Run IO Language script")))
    ("lua" . ((:command . "lua")
              (:description . "Run Lua script")))
    ("groovy" . ((:command . "groovy")
                 (:description . "Run Groovy")))
    ("scala" . ((:command . "scala")
                (:description . "Run Scala file with scala command")))
    ("sass" . ((:command . "sass")
               (:exec    . "%c %o --no-cache %s")
               (:description . "Convert SASS to CSS")))
    ("less" . ((:command . "lessc")
               (:description . "Convert LESS to CSS")))

    ("erlang" . ((:command . "escript")
                 (:description . "Run Erlang file with escript")))
    ("ocaml" . ((:command . "ocamlc")
                (:exec    . ("%c %o -o %e %s"
                             "%e %a"))
                (:remove  . ("%e" "%n.cmi" "%n.cmo"))
                (:description . "Compile Ocaml file with ocamlc and execute")))

    ("shellscript" . ((:command . (lambda () sh-shell))
                      (:description . "Run Shellscript file")))
    ("awk" . ((:command . "awk")
              (:exec    . "%c %o -f %s %a")
              (:description . "Run AWK script")))

    ("rust" . ((:command . "rustc")
               (:exec . ("%c %o -o %e %s" "%e %a"))
               (:compile-only . "%c --no-trans --warn-unused-imports %o -o %e %s")
               (:remove . ("%e"))
               (:description . "Compile rust and execute")))

    ("dart/checked" . ((:command . "dart")
                       (:cmdopt  . "--enable-type-checks")
                       (:description . "Run dart with '--enable-type-checks' option")))
    ("dart/production" . ((:command . "dart")
                          (:description . "Run dart as without '--enable-type-checks' option")))

    ("elixir" . ((:command . "elixir")
                 (:description . "Run Elixir script")))
    )
  "List of each programming languages information.
Parameter form is (\"language\" . parameter-alist). parameter-alist has
5 keys and those values , :command, :exec, :remove.
:command pair is mandatory, other pairs are optional. Associated value
should be string or a function which returns a string object.

Assosiated values are
:command = Program name which is used compiled or executed source code.
:exec    = Exec command template. If you omit this parameter, quickrun
           use default parameter \"%c %o %s %a\".
:remove  = Remove files or directories templates.
           Compiler or executor generates temporary files,
           you should specified this parameter.
           If value is List, quickrun removes each element.
Every pair should be dot-pair.

See explanation of quickrun/template-place-holders
if you set your own language configuration.
")

(defvar quickrun-file-alist
  '(("\\.c$" . "c")
    ("\\.\\(cpp\\|cxx\\|C\\|cc\\)$" . "c++")
    ("\\.m$" . "objc")
    ("\\.\\(pl\\|pm\\)$" . "perl")
    ("\\.rb$" . "ruby")
    ("\\.py$" . "python")
    ("\\.php$" . "php")
    ("\\.\\(el\\|elisp\\)$" . "emacs")
    ("\\.\\(lisp\\|lsp\\)$" . "lisp")
    ("\\.\\(scm\\|scheme\\)$" . "scheme")
    ("\\.js$" . "javascript")
    ("\\.clj$" . "clojure")
    ("\\.erl$" . "erlang")
    ("\\.ml$" . "ocaml")
    ("\\.go$" . "go")
    ("\\.io$" . "io")
    ("\\.lua$" . "lua")
    ("\\.hs$" . "haskell")
    ("\\.java$" . "java")
    ("\\.d$" . "d")
    ("\\.\\(md\\|markdown\\|mdown\\|mkdn\\)$" . "markdown")
    ("\\.coffee$" . "coffee")
    ("\\.scala$" . "scala")
    ("\\.groovy$". "groovy")
    ("\\.sass$" . "sass")
    ("\\.less$" . "less")
    ("\\.\\(sh\\|bash\\|zsh\\|csh\\|csh\\)$" . "shellscript")
    ("\\.awk$" . "awk")
    ("\\.rs$" . "rust")
    ("\\.dart$" . "dart/checked")
    ("\\.exs?$" . "elixir"))
  "Alist of (file-regexp . key)")

(defvar quickrun/major-mode-alist
  '((c-mode . "c")
    (c++-mode . "c++")
    (objc-mode . "objc")
    ((perl-mode cperl-mode) . "perl")
    (ruby-mode . "ruby")
    (python-mode . "python")
    (php-mode . "php")
    (emacs-lisp-mode . "emacs")
    (lisp-mode . "lisp")
    (scheme-mode . "scheme")
    ((javascript-mode js-mode js2-mode) . "javascript")
    (clojure-mode . "clojure")
    (erlang-mode . "erlang")
    ((ocaml-mode tuareg-mode) . "ocaml")
    (go-mode . "go")
    (io-mode . "io")
    (lua-mode . "lua")
    (haskell-mode . "haskell")
    (java-mode . "java")
    (d-mode . "d")
    (markdown-mode . "markdown")
    (coffee-mode . "coffee")
    (scala-mode . "scala")
    (groove-mode . "groovy")
    (sass-mode . "sass")
    ((less-mode less-css-mode) . "less")
    (sh-mode . "shellscript")
    (awk-mode . "awk")
    (rust-mode . "rust")
    (dart-mode . "dart/checked")
    (elixir-mode . "elixir"))
  "Alist of major-mode and langkey")

(defun quickrun/decide-file-type (filename)
  (let ((from-quickrun-alist
         (assoc-default filename quickrun-file-alist 'string-match))
        (from-major-mode
         (quickrun/find-lang-from-alist quickrun/major-mode-alist major-mode)))
    (or from-quickrun-alist from-major-mode)))

(defun quickrun/find-lang-from-alist (alist param)
  (loop for pair in alist
        for lang = (car pair)
        when (if (listp lang)
                 (member param lang)
               (string= param lang))
        return (cdr pair)))

(defun quickrun/command-info (lang)
  (or quickrun-option-cmd-alist
      (assoc-default lang quickrun/language-alist)
      (throw 'quickrun
             (format "not found [%s] language information" lang))))

;;
;; Compile Only
;;
(defun quickrun/compilation-start (cmd)
  (let ((program (car (split-string cmd))))
    (quickrun/check-has-command program)
    (setf compilation-finish-functions #'quickrun/compilation-finish-func)
    (compilation-start cmd t (lambda (x) quickrun/buffer-name))))

(defun quickrun/compilation-finish-func (buffer str)
  (quickrun/remove-temp-files))

;;
;; Execute
;;
(defvar quickrun/timeout-timer nil)

(defun quickrun/exec (cmd-lst)
  (let ((next-cmd  (car cmd-lst))
        (rest-cmds (cdr cmd-lst)))
    (ignore-errors
      (let ((process (quickrun/exec-cmd next-cmd))
            (outputter (or quickrun-option-outputter
                           #'quickrun/default-outputter)))
        (when quickrun-option-input-file
          (quickrun/process-send-file process))
        (set-process-sentinel process
                              (quickrun/make-sentinel rest-cmds outputter))))))

(defun quickrun/exec-cmd (cmd)
  (and quickrun-debug (message "Quickrun Execute: %s" cmd))
  (let ((program (car (split-string cmd)))
        (buf (get-buffer-create quickrun/buffer-name)))
    (quickrun/check-has-command program)
    (with-current-buffer buf
      (erase-buffer))
    (let ((proc-name (format "quickrun-process-%s" program))
          (process-connection-type nil))
      (lexical-let ((process (start-process-shell-command proc-name buf cmd)))
        (if (>= quickrun-timeout-seconds 0)
            (setq quickrun/timeout-timer
                  (run-at-time quickrun-timeout-seconds nil
                               #'quickrun/kill-process process)))
        process))))

(defun quickrun/kill-process (process)
  (when (eq (process-status process) 'run)
    (kill-process process))
  (let ((buf (get-buffer-create quickrun/buffer-name)))
    (with-current-buffer buf
      (insert (format "\nTime out %s(running over %d second)"
                      (process-name process)
                      quickrun-timeout-seconds)))
    (quickrun/remove-temp-files)
    (pop-to-buffer buf)))

(defun quickrun/remove-temp-files ()
  (dolist (file quickrun/remove-files)
    (cond
     ((file-directory-p file) (delete-directory file t))
     ((file-exists-p file) (delete-file file)))))

(defun quickrun/popup-output-buffer ()
  (let ((buf (get-buffer quickrun/buffer-name))
        (outputter quickrun-option-outputter))
    (unless (quickrun/defined-outputter-p outputter)
      (pop-to-buffer buf)
      ;; Copy buffer local variable
      (setq quickrun-option-outputter outputter))))

;;
;; Predefined outputter
;;

(defvar quickrun/defined-outputter-symbol
  `(
    (message  . ,#'quickrun/defined-outputter-message)
    (browser  . ,#'quickrun/defined-outputter-browser)
    (null     . ,#'quickrun/defined-outputter-null)
    ))

(defvar quickrun/defined-outputter-symbol-with-arg
  `(
    ("^file:"     . ,#'quickrun/defined-outputter-file)
    ("^buffer:"   . ,#'quickrun/defined-outputter-buffer)
    ("^variable:" . ,#'quickrun/defined-outputter-variable)
    ))

(defun quickrun/default-outputter ()
  (ansi-color-apply-on-region (point-min) (point-max)))

(defun quickrun/outputter-multi-p (outputter)
  (and (not (functionp outputter)) (listp outputter)
       (eq (car outputter) 'multi)))

(defun quickrun/defined-outputter-p (outputter)
  (cond ((quickrun/outputter-multi-p outputter) t)
        ((or (symbolp outputter) (stringp outputter))
         (let ((name (or (and (symbolp outputter) (symbol-name outputter))
                         outputter)))
           (or (assoc outputter quickrun/defined-outputter-symbol)
               (assoc-default name
                              quickrun/defined-outputter-symbol-with-arg
                              'string-match))))))

(defun quickrun/defined-outputter-file (file)
  (write-region (point-min) (point-max) file))

(defun quickrun/defined-outputter-message ()
  (message "%s"
           (buffer-substring-no-properties (point-min) (point-max))))

(defun quickrun/defined-outputter-browser ()
  (browse-url-of-region (point-min) (point-max)))

(defun quickrun/defined-outputter-null ()
  (let (buf (get-buffer quickrun/buffer-name))
   (delete-region (point-min) (point-max))
   (kill-buffer buf)))

(defun quickrun/defined-outputter-buffer (bufname)
  (let ((buf (get-buffer-create bufname))
        (curbuf (current-buffer))
        (str (buffer-substring (point-min) (point-max))))
    (with-current-buffer buf
      (insert str))))

(defun quickrun/defined-outputter-variable (varname)
  (let ((symbol (intern varname))
        (value (buffer-substring (point-min) (point-max))))
    (set symbol value)))

(defun quickrun/apply-outputter (op)
  (let ((buf (get-buffer quickrun/buffer-name))
        (outputters (or (and (quickrun/outputter-multi-p op) (cdr op))
                        (list op))))
    (dolist (outputter outputters)
      (let ((outputter-func outputter))
        (when (symbolp outputter)
          (lexical-let* ((name (symbol-name outputter))
                         (func (assoc-default outputter
                                              quickrun/defined-outputter-symbol))
                         (func-with-arg
                          (assoc-default name
                                         quickrun/defined-outputter-symbol-with-arg
                                         'string-match)))
            (cond (func (setq outputter-func func))
                  (func-with-arg
                   (if (string-match ":\\(.*\\)$" name)
                       (setq outputter-func
                             (lambda ()
                               (funcall func-with-arg
                                        (match-string 1 name)))))))))
        (with-current-buffer buf
          (funcall outputter-func))))))

(defun quickrun/process-send-file (process)
  (let ((buf (find-file-noselect quickrun-option-input-file)))
    (with-current-buffer buf
        (send-string process
                     (buffer-substring-no-properties
                      (point-min) (point-max)))
        (process-send-eof process))))

(defun quickrun/make-sentinel (cmds outputter)
  (lexical-let ((rest-commands cmds)
                (outputter-func outputter))
    (lambda (process state)
      (let ((status (process-status process))
            (exit-status (process-exit-status process))
            (buf (process-buffer process)))
        (cond ((eq status 'exit)
               (if quickrun/timeout-timer
                   (cancel-timer quickrun/timeout-timer))
               (delete-process process)
               (cond ((and (= exit-status 0) rest-commands)
                      (quickrun/exec rest-commands))
                     (t
                      (quickrun/apply-outputter outputter-func)
                      (if (> scroll-conservatively 0)
                          (recenter))
                      (quickrun/remove-temp-files)))))))))

;;
;; Composing command
;;
(defconst quickrun/template-place-holders
  '("%c" "%o" "%s" "%a" "%d" "%n" "%N" "%e" "%E")
  "A list of place holders of each language parameter.
Place holders are beginning with '%' and replaced by:
%c: :command parameter
%o: command options
%s: source code
%a: program argument
%d: directory name
%n: abosolute path of source code without extension
%N: source code name without extension
%e: abosolute path of source code with exeutable extension(.exe, .out, .class)
%E: source code name with executable extension
")

(defun quickrun/executable-suffix (command)
  (cond ((string= command "java") ".class")
        ((quickrun/windows-p) ".exe")
        (t ".out")))

(defun quickrun/place-holder-info (cmd cmdopt src args)
  (let* ((without-extension (file-name-sans-extension src))
         (dirname (file-name-directory (expand-file-name src)))
         (directory (substring dirname 0 (- (length dirname) 1)))
         (executable-suffix (quickrun/executable-suffix cmd))
         (executable-name (concat without-extension executable-suffix)))
    `(("%c" . ,cmd)
      ("%o" . ,cmdopt)
      ("%s" . ,src)
      ("%n" . ,(expand-file-name without-extension))
      ("%N" . ,without-extension)
      ("%d" . ,directory)
      ("%e" . ,(expand-file-name executable-name))
      ("%E" . ,executable-name)
      ("%a" . ,args))))

(defconst quickrun/default-tmpl-alist
  '((:exec . "%c %o %s %a")))

(defun quickrun/extract-template (key cmd-info &optional take-list)
  (let ((tmpl (or (assoc-default key cmd-info)
                  (assoc-default key quickrun/default-tmpl-alist))))
    (when tmpl
      (cond (take-list
             (let ((tmpl-lst (or (and (listp tmpl) tmpl)
                                 (list tmpl))))
               (mapcar (lambda (x) (quickrun/eval-parameter x)) tmpl-lst)))
            (t
             (quickrun/eval-parameter tmpl))))))

(defun quickrun/eval-parameter (param)
  (cond ((functionp param)
         (let ((ret (funcall param)))
           (cond ((stringp ret) ret)
                 ((symbolp ret) (symbol-name ret))
                 (t
                  (throw 'quickrun
                         "template function should return symbol or string")))))
        (t param)))

(defun quickrun/check-has-command (cmd)
  (let ((program (car (split-string cmd)))) ; for "/usr/bin/env prog"
    (unless (executable-find program)
      (throw 'quickrun (format "'%s' not found" program)))))

(defun quickrun/get-shebang (src)
  (with-temp-buffer
    (insert-file-contents src)
    (goto-char (point-min))
    (if (looking-at "#![ \t]*\\(.*\\)$")
        (buffer-substring-no-properties (match-beginning 1)
                                        (match-end 1)))))

(defun quickrun/template-argument (cmd-info src)
  (let ((cmd (or quickrun-option-command
                 (and quickrun-option-shebang (quickrun/get-shebang src))
                 (quickrun/eval-parameter (assoc-default :command cmd-info))
                 (throw 'quickrun "Not found :command parameter")))
        (cmd-opt (or quickrun-option-cmdopt
                     (quickrun/extract-template :cmdopt cmd-info) ""))
        (arg (or quickrun-option-args
                 (quickrun/extract-template :args cmd-info) "")))
    (quickrun/place-holder-info cmd cmd-opt src arg)))

(defun quickrun/fill-templates (cmd-key src)
  (let* ((cmd-info (quickrun/command-info cmd-key))
         (tmpl-arg (quickrun/template-argument cmd-info src))
         (info (make-hash-table)))
    ;; take one parameter
    (dolist (key `(:compile-only))
      (let ((tmpl (quickrun/extract-template key cmd-info)))
        (if tmpl
            (puthash key (quickrun/fill-template tmpl tmpl-arg) info))))
    ;; take one or more parameters
    (dolist (key `(:exec :remove))
      (let ((tmpl (quickrun/extract-template key cmd-info t)))
        (if tmpl
            (puthash key
                     (mapcar (lambda (x) (quickrun/fill-template x tmpl-arg))
                             tmpl) info))))
    ;; function parameter
    (dolist (key `(:outputter))
      (let ((func (assoc-default :outputter cmd-info)))
        (if (and func (or (functionp func) (symbolp func)))
            (puthash key func info))))
    info))

(defun quickrun/fill-template (tmpl info)
  (let ((place-holders quickrun/template-place-holders)
        (str tmpl)
        (case-fold-search nil))
    (dolist (holder place-holders str)
      (let ((rep (assoc-default holder info)))
        (setq str (replace-regexp-in-string holder rep str t))))))

;;
;; initialize
;;
(defun quickrun/windows-p ()
  (or (string= system-type "ms-dos")
      (string= system-type "windows-nt")
      (string= system-type "cygwin")))

(defconst quickrun/support-languages
  '("c" "c++" "objc" "perl" "ruby" "python" "php" "emacs" "lisp" "scheme"
    "javascript" "clojure" "erlang" "ocaml" "go" "io" "haskell" "java" "d"
    "markdown" "coffee" "scala" "groovy" "sass" "less" "shellscript" "awk"
    "lua" "rust" "dart" "elixir")
  "Programming languages and Markup languages supported as default
by quickrun.el. But you can register your own command for some languages")

(defvar quickrun/command-key-table
  (make-hash-table :test #'equal))

(defun quickrun-set-default (lang key)
  "Set `key' as default key in programing language `lang'"
  (interactive)
  (unless (assoc key quickrun/language-alist)
    (error "%s is not registered." key))
  (puthash lang key quickrun/command-key-table))

(defun* quickrun-add-command (key alist &key default mode)
  (cond ((not key) (error "undefined 1st argument 'key'"))
        ((not alist) (error "undefined 2nd argument 'command alist'"))
        ((not (assoc :command alist))
         (error "not found :command parameter in language alist")))
  (push (cons key (copy-alist alist)) quickrun/language-alist)
  (let ((cmd-key (or default key)))
    (if default
        (puthash cmd-key key quickrun/command-key-table))
    (if mode
        (push (cons mode cmd-key) quickrun/major-mode-alist))
    key))

(defun quickrun/find-executable (candidates)
  (loop for candidate in candidates
        when (executable-find candidate)
        return candidate))

(defun quickrun/set-command-key (lang candidates)
  (let ((executable (quickrun/find-executable candidates)))
    (when executable
      (let ((cmd-key (concat lang "/" executable)))
        (puthash lang cmd-key quickrun/command-key-table)))))

(defun quickrun/append-commands-if-windows (cmds lst)
  (if (quickrun/windows-p)
      (append lst cmds)
    lst))

(defconst quicklang/lang-candidates
  `(("c" . ,(quickrun/append-commands-if-windows '("cl") '("gcc" "clang")))
    ("c++" . ,(quickrun/append-commands-if-windows '("cl") '("g++" "clang++")))
    ("javascript" . ("node" "v8" "js" "jrunscript" "cscript"))
    ("lisp" . ("clisp" "sbcl" "ccl"))
    ("scheme" . ("gosh"))
    ("markdown" . ("Markdown.pl" "kramdown" "bluecloth" "redcarpet" "pandoc"))
    ("clojure" . ("jark" "clj-env-dir"))
    ("go" . ("8g" "6g" "5g")))
  "Candidates of language which has some compilers or interpreters")

(defun quickrun/init-command-key-table ()
  "Decide command for programing language which has multiple candidates"
  (dolist (lang quickrun/support-languages)
    (puthash lang lang quickrun/command-key-table))
  (loop for (lang . candidates) in quicklang/lang-candidates
        do
        (quickrun/set-command-key lang candidates)))

(quickrun/init-command-key-table)

;;
;; main
;;
;;;###autoload
(defun quickrun (&optional start end)
  "Run commands quickly for current buffer"
  (interactive)
  (let ((beg (or start (point-min)))
        (end (or end (point-max)))
        (quickrun-timeout-seconds (or quickrun-option-timeout-seconds
                                      quickrun-timeout-seconds)))
    (let ((has-error (catch 'quickrun
                       (quickrun/common beg end)
                       nil)))
      (when has-error
        (message "%s" has-error)
        (quickrun/remove-temp-files)))))

(defun quickrun-with-arg (arg)
  "Run commands quickly for current buffer with arguments"
  (interactive
   (list (read-string "QuickRun Arg: ")))
  (let ((quickrun-option-args arg))
    (quickrun)))

(defun quickrun-with-input-file (file)
  (interactive "fInput File: ")
  (let ((quickrun-option-input-file file))
   (quickrun)))

(defvar quickrun/last-cmd-key nil)

(defun quickrun/prompt ()
  (let ((default-value (or quickrun-option-cmdkey quickrun/last-cmd-key))
        (prompt "QuickRun Lang"))
    (completing-read (format "QuickRun Lang%s: "
                             (or (and default-value
                                      (format "[Default: %s]" default-value))
                                 ""))
                     quickrun/language-alist
                     nil nil nil nil default-value)))

(defun quickrun-region (start end)
  (interactive "r")
  (quickrun start end))

(defvar quickrun/compile-only-flag nil)

(defun quickrun-compile-only ()
  (interactive)
  (let ((quickrun/compile-only-flag t))
    (quickrun)))

(defvar quickrun/remove-files nil)

(defun quickrun/add-remove-files (files)
  (if (listp files)
      (setq quickrun/remove-files (append files quickrun/remove-files))
    (push files quickrun/remove-files)))

(defun quickrun/temp-name (src)
  (let* ((extension (file-name-extension src))
         (suffix (or (and extension (concat "." extension)) "")))
    (concat (make-temp-name "qr_") suffix)))

(defun quickrun/command-key (src)
  (let ((file-type (quickrun/decide-file-type src)))
    (or (and current-prefix-arg (quickrun/prompt))
        (and quickrun-option-cmd-alist "_user_defined") ;; setting dummy value
        quickrun-option-cmdkey
        (gethash file-type quickrun/command-key-table)
        file-type
        (quickrun/prompt))))

(defun quickrun/copy-region-to-tempfile (start end dst)
  ;; Suppress write file message
  (let ((str (buffer-substring-no-properties start end)))
    (with-temp-file dst
      (insert str)))
  (quickrun/add-remove-files dst))

(defun quickrun/kill-quickrun-buffer ()
  (if (get-buffer quickrun/buffer-name)
      (kill-buffer quickrun/buffer-name)))

(defun quickrun/common (start end)
  (let* ((orig-src (file-name-nondirectory (buffer-file-name)))
         (cmd-key (quickrun/command-key orig-src))
         (src (quickrun/temp-name orig-src)))
    (quickrun/kill-quickrun-buffer)
    (unless (local-variable-p 'quickrun/last-cmd-key)
      (make-local-variable 'quickrun/last-cmd-key))
    (setq quickrun/last-cmd-key cmd-key)
    (if (or (string= cmd-key "java") quickrun/compile-only-flag)
        (setq src orig-src)
      (quickrun/copy-region-to-tempfile start end src))
    (let ((cmd-info-hash (quickrun/fill-templates cmd-key src)))
      (quickrun/add-remove-files (gethash :remove cmd-info-hash))
      (unless quickrun-option-outputter
        (setq quickrun-option-outputter (gethash :outputter cmd-info-hash)))
      (cond (quickrun/compile-only-flag
             (let ((cmd (gethash :compile-only cmd-info-hash)))
               (unless cmd
                 (throw 'quickrun
                        (format "%s does not support quickrun-compile-only"
                                cmd-key)))
               (quickrun/compilation-start cmd)))
            (t
             (when (quickrun/exec (gethash :exec cmd-info-hash))
               (quickrun/popup-output-buffer)))))))

;;
;; anything
;;

(defvar anything-c-source-quickrun
  '((name . "Choose Command-Key")
    (volatile)
    (candidates . (lambda ()
                    (loop for (cmd-key . cmd-info) in quickrun/language-alist
                          collect (quickrun/anything-candidate cmd-key cmd-info))))
    (action . (("Run this cmd-key" . quickrun/anything-action-default))))
  "anything source of `quickrun'")

(defun quickrun/anything-candidate (cmd-key cmd-info)
  (let ((description (or (assoc-default :description cmd-info) "")))
    (cons (format "%-25s %s" cmd-key description) cmd-key)))

(defun quickrun/anything-action-default (cmd-key)
  (let ((quickrun-option-cmdkey cmd-key))
    (quickrun)))

;;;###autoload
(defun anything-quickrun ()
  (interactive)
  (unless (featurep 'anything)
    (error "anything is not installed."))
  (anything anything-c-source-quickrun))

;;
;; file local variable
;; Based on shadow.el. https://raw.github.com/mooz/shadow.el/master/shadow.el
;;
(defmacro quickrun/defvar (name &optional value safep doc)
  "Define buffer-local and safe-local variable."
  (declare (indent defun))
  `(progn
     (defvar ,name ,value ,doc)
     (make-variable-buffer-local (quote ,name))
     ;; Suppress file local variable warning
     ,(when safep
        `(put (quote ,name) 'safe-local-variable (quote ,safep)))))

(quickrun/defvar quickrun-option-cmd-alist
                 nil listp
                 "Specify command alist directly as file local variable")

(quickrun/defvar quickrun-option-command
                 nil stringp
                 "Specify command directly as file local variable")

(quickrun/defvar quickrun-option-cmdkey
                 nil stringp
                 "Specify language key directly as file local variable")

(quickrun/defvar quickrun-option-cmdopt
                 nil stringp
                 "Specify command option directly as file local variable")

(quickrun/defvar quickrun-option-args
                 nil stringp
                 "Specify command argument directly as file local variable")

(defun quickrun/outputter-p (x)
  (lambda (x) (or (functionp x) (symbolp x) (stringp x)
                  (quickrun/outputter-multi-p x))))

(quickrun/defvar quickrun-option-outputter
                 nil quickrun/outputter-p
                 "Specify format function output buffer as file local variable")

(quickrun/defvar quickrun-option-shebang
                 t booleanp
                 "Select using command from schebang as file local variable")

(quickrun/defvar quickrun-option-input-file
                 nil file-exists-p
                 "Select using command from schebang as file local variable")

(quickrun/defvar quickrun-option-timeout-seconds
                 nil integerp
                 "Timeout seconds as file local variable")

(provide 'quickrun)
;;; quickrun.el ends here
