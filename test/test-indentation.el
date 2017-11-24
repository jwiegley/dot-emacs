;; -*- flycheck-disabled-checkers: (emacs-lisp-checkdoc) -*-
(load (concat (file-name-directory (or load-file-name (buffer-file-name)
                                       default-directory))
              "utils.el") nil 'nomessage 'nosuffix)

(describe "Assignment indentation"
  (it "is sane"
    (lua--reindent-like "\
foo = 10

bar = 20"))
  (it "adds continuation before ="
   (lua--reindent-like "\
foo
   = 10

bar = 20"))

  (it "adds continuation after ="
    (lua--reindent-like "\
foo =
   10
bar = 20"))


  ;; (ert-deftest lua-indentation-assignment-with-commas ()
  ;;   (lua--reindent-like "\
  ;; foo,
  ;;    baz = 10, 20

  ;; bar = 20")
  ;;    (lua--reindent-like "\
  ;; foo, baz
  ;;    = 10, 20

  ;; bar = 20")

  ;;    (lua--reindent-like "\
  ;; foo, baz = 10,
  ;;    20

  ;; bar = 20")

  ;;    (lua--reindent-like "\
  ;; foo,
  ;;    baz =
  ;;    10, 20")

  ;;    (lua--reindent-like "\
  ;; foo, baz =
  ;;    10,
  ;;    20

  ;; bar = 20")

  ;;    (lua--reindent-like "\
  ;; local
  ;;    x = 5")

  ;;    (lua--reindent-like "\
  ;; local
  ;;    x,
  ;;    y = 10, 20")

  ;;    (lua--reindent-like "\
  ;; local
  ;;    x,
  ;;    y =
  ;;    10,
  ;;    20"))

  (it "does not accumulate indentation after the expression (issue #33)"
    (lua--reindent-like "\
a =
   {
   }

b =
   {
   },


a = {
   table_elt_indented
}

a = a +
   5 +
   10

this_should_be_unindented()

-- here foobar should be indented as simple continuation statement
a = a +
   dosmth(
   ) +
   foobar

a =
   do_smth(
      do_smth_arg
   )

b =
   {
      table_elt0_indented,
      table_elt1_indented
   }

this_should_be_unindented_too =
   {
   }

this_should_be_unindented_three = etc")))


(describe "Continuation lines"
  (it "are indented if broken in the middle of \"foo.bar\" and \"qux:quux\""
    (lua--reindent-like "\
foo123
   .bar:baz(xyz)")
    (lua--reindent-like "\
foo123.
   bar:baz(xyz)")
    (lua--reindent-like "\
foo123.bar
   :baz(xyz)")
    (lua--reindent-like "\
foo123.bar:
   baz(xyz)")
    (lua--reindent-like "\
foo123.bar
   .baz
   .qux
   :quux(xyz)"))

  (it "are indented after return"
    (expect (lua--reindent-like "\
return
   123"))
    (expect (lua--reindent-like "\
do
   return
      123
end"))
    (expect (lua--reindent-like "\
do
   return
      x +
      y
end")))

  (it "are not indented if \"return\" returns no values"
    (expect (lua--reindent-like "\
do
   return
end

foo = bar"))

    (expect (lua--reindent-like "\
if foo == bar then
   return
else
   foo = bar
end"))

    (expect (lua--reindent-like "\
if foo == bar then
   return
elseif foo != bar then
   foo = bar
end"))

    (expect (lua--reindent-like "\
repeat
   return
until foo == bar")))

  (it "are indented before/after binary operators"
    (let ((binops '("+"  "-"  "*"  "/"  "^"  "%"  ".."
                    "<"  "<="  ">"  ">="  "=="  "~="
                    "and"  "or")))
      (cl-dolist (binop binops)
        (lua--reindent-like (replace-regexp-in-string "BINOP" binop "\
a = foo BINOP
   bar" 'fixedcase))
        (lua--reindent-like (replace-regexp-in-string "BINOP" binop "\
a = foo
   BINOP bar" 'fixedcase)))))


  (it "are not indented after ellipsis"
    (lua--reindent-like "\
function x(...)
   a, b = 1, ...
   return b
end"))

  (xit "are indented before/after unary operators"
    (expect (lua--reindent-like "\
foo = bar
   -#some_str"))

    (cl-dolist (unop '("-" "#" "not "))
      (expect (lua--reindent-like (replace-regexp-in-string "<>" unop  "\
foobar(qux,
       <>quux)")))
      (expect (lua--reindent-like (replace-regexp-in-string "<>" unop "\
foobar(qux, xyzzy
          <>quux)")))
      (expect (lua--reindent-like (replace-regexp-in-string "<>" unop "\
foobar(
   <>quux)")))
      (expect (lua--reindent-like (replace-regexp-in-string "<>" unop "\
x = {qux,
     <>quux}")))
      (expect (lua--reindent-like (replace-regexp-in-string "<>" unop "\
x = {qux;
     <>quux}")))
      (expect (lua--reindent-like (replace-regexp-in-string "<>" unop "\
x = {qux, xyzzy
        <>quux}")))
      (expect (lua--reindent-like (replace-regexp-in-string "<>" unop "\
x = {
   <>quux
}")))))

  (it "indents function call arguments in continuation part"
    (expect (lua--reindent-like "\
x = foo(123,
        456)
   + bar(
      qux,
      quux)")))

  (xit "are indented in block-intros"
    (expect (lua--reindent-like "\
while
   foo do
   a = a + 1
end

a = 0"))

    (expect (lua--reindent-like "\
for k, v
   in pairs(bar) do
   a = a + 1
end

a = 0"))

    (expect (lua--reindent-like "\
for k, v
   in pairs(bar) do a = a + 1 end

a = 0"))))


(describe "Block indentation"
  (it "works for do ... end blocks"
    ;; FIXME: test split block-intro indentations
    (expect (lua--reindent-like "\
do
   a = a + 1
end

a = 0"))

    (expect (lua--reindent-like "\
do a = a + 1 end

a = 0"))

    (expect (lua--reindent-like "\
do a = a + 1
end

a = 0")))


  (it "works for while ... do ... end blocks"
    (expect (lua--reindent-like "\
while foo do
   a = a + 1
end

a = 0"))

    (expect (lua--reindent-like "\
while foo
do
   a = a + 1
end

a = 0"))

    (expect (lua--reindent-like "\
while
   foo
do
   a = a + 1
end

a = 0"))

    (expect (lua--reindent-like "\
while foo do a = a + 1 end

a = 0"))

    (expect (lua--reindent-like "\
while
   x +
   y > 0
do
   a = a + 1
end

a = 0")))


  (it "works for repeat ... until blocks"
    (expect (lua--reindent-like "\
repeat
   a = a + 1
until foo

a = 0"))

    (expect (lua--reindent-like "\
repeat
   a = a + 1
until
   foo

a = 0"))

    (expect (lua--reindent-like "\
repeat
   a = a + 1
until
   not
   foo

a = 0"))

    (expect (lua--reindent-like "\
repeat a = a + 1 until not foo

a = 0")))



  (it "works for \"for ... do\" block "
    (expect (lua--reindent-like "\
for k, v in pairs(bar) do
   a = a + 1
end

a = 0"))

    (expect (lua--reindent-like "\
for k, v in pairs(bar)
do
   a = a + 1
end

a = 0"))

    (expect (lua--reindent-like "\
for k, v in pairs(bar) do a = a + 1 end

a = 0"))

    (expect (lua--reindent-like "\
for y = 0, 10 do
   a = a + 1
end

a = 0"))

    (expect (lua--reindent-like "\
for y = 0, 10
do
   a = a + 1
end

a = 0"))

    (expect (lua--reindent-like "\
for y = 0, 10 do a = a + 1 end

a = 0")))

  (it "works for conditionals"
    (expect (lua--reindent-like "\
if foo then
   a = a + 1
end

a = 0"))

    (expect (lua--reindent-like "\
if foo then a = a + 1 end

a = 0"))

    (expect (lua--reindent-like "\
if foo then
   a = a + 1
else
   a = a + 2
end

a = 0"))


    (expect (lua--reindent-like "\
if foo then
   a = a + 1
elseif bar then
   a = a + 2
elseif baz then
   a = a + 3
end

a = 0"))

    (expect (lua--reindent-like "\
if foo then a = a + 1 else
   a = a + 2
end"))))

(describe "Function indentation"
  (it "indents function call arguments"
    (expect (lua--reindent-like "\
foobar(
   a, b, c)"))
    (expect (lua--reindent-like "\
foobar(
   a,
   b, c)"))

    (expect (lua--reindent-like "\
foobar(
   a, b, c
)"))

    (expect (lua--reindent-like "\
foobar(a,
       b,
       c)"))

    (expect (lua--reindent-like "\
foobar{
   a, b, c
}")))


  (xit "indents nested tables"
    (expect (lua--reindent-like "\
foobar({
   a, b, c
})"))

    (expect (lua--reindent-like "\
foobar(a, {
   b,
   c
})"))

    (expect (lua--reindent-like "\
foobar(
   a,
   {
      b,
      c
   })"))

    (expect (lua--reindent-like "\
foobar(a,
       {
          b,
          c
       })"))

    (expect (lua--reindent-like "\
foobar(a,
       {
          b,
          c
       }
)"))

    (expect (lua--reindent-like "\
foobar(
   {
      a,
      b
   },
   c, d
)"))))




(ert-deftest lua-indentation-defun ()
  ;; 	 [local] function funcname funcbody
  ;; FIXME: add
  )

(ert-deftest lua-indentation-alignment ()
  ;; FIXME: add
  )

(ert-deftest lua-indentation-tablector ()
  ;; FIXME: add
  )

(ert-deftest lua-indentation-continuation-spans-over-empty-lines ()
  ;; FIXME: add
  ;; FIXME: check comment-only lines too
  )


(ert-deftest lua-indentation-keywords-with-special-characters ()
  (expect (lua--reindent-like "\
do
   foobar = _do
end")))


(describe "Goto label indentation"
  (it "is sane"
   (expect (lua--reindent-like "\
::foo::
::bar::

::baz::

a = 0")))

  (it "does not affect indentation when put on a separate line"
   (expect (lua--reindent-like "\
for z=1,10 do
   ::foo::
   bar
end

a = 0")))

  (xit "does not affect indentation before block modifiers"
   (expect (lua--reindent-like "\
::foo:: for z=1,10 do
   bar
end

a = 0")))

  (it "does not affect indentation after block modifiers"
   (expect (lua--reindent-like "\
for z=1,10 do  ::foo::
   bar
end

a = 0")))

  (it "reindents according to luawiki examples"
    (expect (lua--reindent-like "\
for z=1,10 do
   ::foo::
   for y=1,10 do  ::bar
      for x=1,10 do
         if x^2 + y^2 == z^2 then
            print('found a Pythagorean triple:', x, y, z)
            goto done
            goto done2
         end
      end
      ::done2::
   end
end

::done::"))

    (expect (lua--reindent-like "\
-- 5.2.0-beta-rc2
for z=1,10 do
   for y=1,10 do
      for x=1,10 do
         if x^2 + y^2 == z^2 then
            print('found a Pythagorean triple:', x, y, z)
            print('now trying next z...')
            goto zcontinue
         end
      end
   end
   ::zcontinue::
end"))

    (expect (lua--reindent-like "\
-- Lua 5.2.0-beta-rc2
for x=1,5 do ::redo::
   print(x .. ' + 1 = ?')
   local y = tonumber(io.read'*l')
   if y ~= x + 1 then goto redo end
end"))

    (expect (lua--reindent-like "\
-- 5.2.0-beta-rc1
::a::
print 'A'
if math.random() < 0.3 then goto c end
::b::
print 'B'
if math.random() < 0.5 then goto a end
::c::
print 'C'
if math.random() < 0.1 then goto a else goto b end
"))

    (expect (lua--reindent-like "\
-- 5.2.0-beta-rc2 - factorial with tail recursion simulated with goto's
-- (warning: there's no need to do this)
function fact_(n, ans)
   ::call::
   if n == 0 then
      return ans
   else
      n, ans = n - 1, ans * n
      goto call
   end
end
print(fact_(5, 1)) --> 120"))

    (expect (lua--reindent-like "\
-- 5.2.0-beta-rc2
function f()
   if not g() then goto fail end
   if not h() then goto cleanup_g end
   if not i() then goto cleanup_h end
   do return true end    -- need do/end?

   ::cleanup_h::
   undo_h()
   ::cleanup_g::
   undo_g()
   ::fail::
   return false
end"))

    (expect (lua--reindent-like "\
-- 5.2.0-beta-rc2
::redo::
for x=1,10 do
   for y=1,10 do
      if not f(x,y) then goto continue end
      if not g(x,y) then goto skip end
      if not h(x,y) then goto redo end
      ::continue::
   end
end ::skip::
print('foo')"))))
