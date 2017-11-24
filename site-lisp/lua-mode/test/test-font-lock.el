;; -*- flycheck-disabled-checkers: (emacs-lisp-checkdoc) -*-

(load (concat (file-name-directory (or load-file-name (buffer-file-name)
                                       default-directory))
              "utils.el") nil 'nomessage 'nosuffix)

(require 'buttercup)

(describe "Fontification of built-ins"
  (it "fontifies built-ins"
    (expect "table.sort(foobar)"
            :to-be-fontified-as
            '(("table" builtin "sort" builtin))))

  (it "fontifies built-ins with spaces between members"
    (expect "\
table.sort(foobar)
   table  .sort(foobar)
   table.  sort(foobar)"
            :to-be-fontified-as
            '(("table" builtin "sort" builtin)
              ("table" builtin "sort" builtin)
              ("table" builtin "sort" builtin))))

  (it "doesn't fontify things that look like built-ins"
    (expect "\
foo.table.sort(foobar)
foo.  table.sort(foobar)
foo  .table.sort(foobar)
foo:table.sort(foobar)
foo:  table.sort(foobar)
foo  :table.sort(foobar)

_table.sort(foobar)
   table_.sort(foobar)"
            :to-be-fontified-as
            '(nil nil nil nil nil nil nil nil nil)))

  (it "fontifies built-in class if method is not built-in"
    (expect "\
   table  ._sort(foobar)
   table.  sort_(foobar)"
            :to-be-fontified-as
            '(("table" builtin) ("table" builtin))))

  (it "fontifies built-ins after concatenation operator"
    (expect "a .. table.concat(foobar, delim)"
            :to-be-fontified-as
            '(("table" builtin "concat" builtin)))))


(describe "Fontification of constants"
  (it "fontifies constants"
    (expect "a = { nil, true, false}"
            :to-be-fontified-as
            '(("nil" constant "true" constant "false" constant))))

  (it "fontifies constants used as attributes"
    (expect "a = { nil, true, false}"
            :to-be-fontified-as
            '(("nil" constant "true" constant "false" constant)))))

(describe "Fontification of keywords"
  (it "fontifies keywords"
    (expect "do foo(5) end"
            :to-be-fontified-as
            '(("do" keyword "end" keyword)))

    (expect "_do foo(5) end_"
            :to-be-fontified-as
            '(nil))
    )
  (it "fontifies keywords used as attributes"
     ;; Hint user that keywords cannot be used like that
    (expect "foo(5).end"
            :to-be-fontified-as
            '(("end" keyword)))
    (expect "foo(5):end"
            :to-be-fontified-as
            '(("end" keyword)))))


(describe "Fontification of function headers"
  (it "fontifies simple headers"
    (expect
     ;; Check all defun variants, check embedded defuns
     "\
function foo()
  function bar() end
  local function baz() end
  qux = function() end
  local quux = function() end
end"
     :to-be-fontified-as
     '(("function" keyword "foo" function-name)
       ("function" keyword "bar" function-name "end" keyword)
       ("local" keyword "function" keyword "baz" function-name "end" keyword)
       ("qux" function-name "function" keyword "end" keyword)
       ("local" keyword "quux" function-name "function" keyword "end" keyword)
       ("end" keyword))))

  (it "fontifies headers inside tables"
    (expect
     "\
somefunc {
  function() end,
  foobar = function() end,
  [\"quxquux\"] = function() end
}"
     :to-be-fontified-as
     '(nil
       ("function" keyword "end" keyword)
       ("foobar" function-name "function" keyword "end" keyword)
       ("\"quxquux\"" string "function" keyword "end" keyword)
       nil)))

  (it "does not fail on issue #59 again"
    (expect
     "\
local foo = function()
   ;
end
-- and
local function foo()
   ;
end"
     :to-be-fontified-as
     '(("local" keyword "foo" function-name "function" keyword)
       nil
       ("end" keyword)
       ("-- " comment-delimiter "and" comment)
       ("local" keyword "function" keyword "foo" function-name)
       nil
       ("end" keyword))))

  (it "does not choke on function names with underscores"
   (expect
     ;; Check all defun variants, check embedded defuns
     "\
function foo()
  function bar_bar() end
  local function baz_baz() end
  qux_qux = function() end
  local quux_quux = function() end
end"
     :to-be-fontified-as
     '(("function" keyword "foo" function-name)
       ("function" keyword "bar_bar" function-name "end" keyword)
       ("local" keyword "function" keyword "baz_baz" function-name "end" keyword)
       ("qux_qux" function-name "function" keyword "end" keyword)
       ("local" keyword "quux_quux" function-name "function" keyword "end" keyword)
       ("end" keyword)))))


(describe "Fontification of goto labels"
  (it "fontifies simple goto labels"
    (expect
     "\
goto foo
::foo::"
     :to-be-fontified-as
     '(("goto" keyword "foo" constant)
       ("::foo::" constant))))

  (it "fontifies ::labels:: written after code"
    (expect
     "\
local foo = 'test' ::f12o::
goto f12o"
     :to-be-fontified-as
     '(("local" keyword "foo" variable-name "'test'" string "::f12o::" constant)
       ("goto" keyword "f12o" constant))))

  (it "fontifies labels with spaces before and after \"::\""
    ;; With spaces after and before "::"
    (expect ":: foo ::"
     :to-be-fontified-as
     '((":: foo ::" constant))))

  ;; Don't font lock labels when substring "goto" appears as a suffix
  ;; of another variable
  (it "does not fontify after symbols ending with \"goto\""
    (expect "JUNKgoto foo" :to-be-fontified-as '(nil))))


(describe "Fontification of LuaDoc keywords"
  (it "works"
    (expect "\
-- @author foo baz
-- @copyright foo baz
-- @field foo baz
-- @param foo baz
-- @release foo baz
-- @return foo baz
-- @see foo baz
-- @usage foo baz
-- @class foo baz
-- @description foo baz
-- @name foo baz"
            :to-be-fontified-as
            '(("-- " comment-delimiter "@author" keyword " foo baz" comment)
              ("-- " comment-delimiter "@copyright" keyword " foo baz" comment)
              ("-- " comment-delimiter "@field" keyword " foo baz" comment)
              ("-- " comment-delimiter "@param" keyword " " comment
               "foo" variable-name " baz" comment)
              ("-- " comment-delimiter "@release" keyword " foo baz" comment)
              ("-- " comment-delimiter "@return" keyword " foo baz" comment)
              ("-- " comment-delimiter "@see" keyword " foo baz" comment)
              ("-- " comment-delimiter "@usage" keyword " foo baz" comment)
              ("-- " comment-delimiter "@class" keyword
               " " comment "foo" variable-name " baz" comment)
              ("-- " comment-delimiter "@description" keyword " foo baz" comment)
              ("-- " comment-delimiter "@name" keyword " " comment
               "foo" variable-name " baz" comment)))))
