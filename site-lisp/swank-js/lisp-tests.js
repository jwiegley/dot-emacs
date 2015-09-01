// -*- mode: js2; js-run: t -*-
//
// Copyright (c) 2010 Ivan Shvedunov. All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions
// are met:
//
// * Redistributions of source code must retain the above copyright
// notice, this list of conditions and the following disclaimer.
//
// * Redistributions in binary form must reproduce the above
// copyright notice, this list of conditions and the following
// disclaimer in the documentation and/or other materials
// provided with the distribution.
//
// THIS SOFTWARE IS PROVIDED BY THE AUTHOR 'AS IS' AND ANY EXPRESSED
// OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
// WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
// ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
// DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
// DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE
// GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
// INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
// WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
// NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
// SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

var lisp = require("./lisp");
var assert = require("assert");
var S = lisp.S, cons = lisp.cons, consp = lisp.consp, car = lisp.car, cdr = lisp.cdr,
    nil = lisp.nil, nullp = lisp.nullp, listp = lisp.listp, list = lisp.list,
    reverse = lisp.reverse, append = lisp.append, repr = lisp.repr,
    StringInputStream = lisp.StringInputStream,
    readFromString = lisp.readFromString,
    fromLisp = lisp.fromLisp,
    toLisp = lisp.toLisp;

assert.equal(S("zzz"), S("zzz"));
assert.deepEqual(cons(1, cons(2, cons(3, nil))), list(1, 2, 3));
assert.equal("abc", car(cons("abc", "def")));
assert.equal("def", cdr(cons("abc", "def")));
assert.equal(nil, list());
assert.ok(consp(cons(1, 2)));
assert.ok(!consp(nil));
assert.ok(listp(cons(1, 2)));
assert.ok(listp(list(1, 2)));
assert.ok(listp(nil));
assert.ok(nullp(nil));
assert.ok(!nullp(cons(1, 2)));
assert.ok(!nullp(1));
assert.deepEqual(list(), reverse(list()));
assert.deepEqual(list(1), reverse(list(1)));
assert.deepEqual(list(3, 2, 1), reverse(list(1, 2, 3)));
assert.deepEqual(nil, append(nil, nil));
assert.deepEqual(list(1), append(list(1), nil));
assert.deepEqual(list(1), append(nil, list(1)));
assert.deepEqual(list(1, 2, 3), append(list(1, 2), list(3)));
assert.deepEqual(list(1, 2, 3, 4), append(list(1, 2), list(3, 4)));

var s = new StringInputStream("abc");
assert.equal(0, s.pos());
assert.equal("a", s.getc());
assert.equal(1, s.pos());
assert.equal("b", s.readchar());
assert.equal(2, s.pos());
assert.equal("c", s.readchar());
assert.equal(3, s.pos());
assert.equal(null, s.getc());
assert.equal(3, s.pos());
assert["throws"](function () { s.readchar(); });
assert.equal(3, s.pos());
s.ungetc("c");
assert.equal(2, s.pos());
assert.equal("c", s.getc());
assert.equal(3, s.pos());
assert["throws"](function () { s.ungetc("z"); });
assert.equal(3, s.pos());
s.ungetc("c");
s.ungetc("b");
assert.equal(1, s.pos());
assert.equal("b", s.getc());
assert.equal("c", s.getc());
assert.equal(3, s.pos());
s.ungetc("c");
s.ungetc("b");
s.ungetc("a");

assert.equal(0, s.pos());
assert["throws"](function () { s.ungetc("z"); });
assert["throws"](function () { s.ungetc(""); });
assert.equal(0, s.pos());
assert.equal("a", s.readchar());
assert.equal("b", s.readchar());
assert.equal("c", s.readchar());
assert.equal(3, s.pos());

s = new StringInputStream("");
assert.equal(0, s.pos());
assert["throws"](function () { s.ungetc("z"); });
assert["throws"](function () { s.ungetc(""); });
assert.equal(null, s.getc());
assert["throws"](function () { s.readchar(); });
assert.equal(0, s.pos());

function test_read (str, o) {
  assert.equal(str, repr(o));
  var rs = readFromString(str);
  assert.deepEqual(o, rs);
  assert.equal(str, repr(rs));
};

test_read("zzz", S("zzz"));
test_read("'zzz", list(S("quote"), S("zzz")));
test_read('"zzz"', "zzz");
test_read('"zz\nz"', "zz\nz");
test_read('\'"zzz"', list(S("quote"), "zzz"));
test_read('"z\\"z\\\\z"', "z\"z\\z");
test_read("nil", nil);
test_read("(1)", list(1));
test_read("(1 2)", list(1, 2));
test_read("(1 2 4.25)", list(1, 2, 4.25));
test_read("(1 2 eprst)", list(1, 2, S("eprst")));
test_read('(1 2 eprst ("abra" "kodabra"))',
          list(1, 2, S("eprst"), list("abra", "kodabra")));
test_read('(1 2 eprst ("abra" . "kodabra"))',
          list(1, 2, S("eprst"), cons("abra", "kodabra")));
test_read('(1 2 eprst ("abra" "kodabra" .schwabbra))',
          list(1, 2, S("eprst"), list("abra", "kodabra", S(".schwabbra"))));
test_read('(1 2 eprst ("abra" "kodabra" .schwabbra . QQQ))',
          list(1, 2, S("eprst"),
               cons("abra",cons("kodabra", cons(S(".schwabbra"), S("QQQ"))))));
test_read('(1 2 eprst \'("abra" "kodabra" .schwabbra . QQQ))',
          list(1, 2, S("eprst"),
               list(S("quote"),
                    cons("abra", cons("kodabra", cons(S(".schwabbra"), S("QQQ")))))));
test_read("(1 2 3)", list(1, 2, 3));
test_read("(1 2 3 (4 5 6))", list(1, 2, 3, list(4, 5, 6)));
test_read("((4 5 6) . 7)", cons(list(4, 5, 6), 7));
test_read("((4 5 6) 7 8 . :eprst)",
          cons(list(4, 5, 6), cons(7, cons(8, S(":eprst")))));
test_read("((4 5 6) 7 8 . swank:connection-info)",
          cons(list(4, 5, 6), cons(7, cons(8, S("swank:connection-info")))));

var CONV_ERROR = {};

function test_conversion(spec, source, expectedResult, reconverted) {
  var r, l = readFromString(source);
  try {
    r = spec === null ? fromLisp(l) : fromLisp(l, spec);
  } catch (e) {
    if (e instanceof TypeError && /^error converting/.test(e.message))
      r = CONV_ERROR;
    else
      throw e;
  }
  assert.deepEqual(expectedResult, r);
  if (r !== CONV_ERROR)
    assert.equal(reconverted || source, repr(spec === null ? toLisp(r) : toLisp(r, spec)));
}

test_conversion("N", "1", 1);
test_conversion("K", ":abc", "abc");
test_conversion("K", "nil", null);
test_conversion("B", "t", true);
test_conversion("B", "nil", false);
test_conversion("B", "123", true, "t");
test_conversion("B", ":zzz", true, "t");
test_conversion("@", '(test nil () 123 "456" :zzz (1 2 3) (4 . 5))',
                ["test", null, null, 123, "456", ":zzz", [1, 2, 3], [4, 5]],
                '("test" nil nil 123 "456" ":zzz" (1 2 3) (4 5))');
test_conversion(null, '(test nil () 123 "456" :zzz (1 2 3) (4 . 5))',
                ["test", null, null, 123, "456", ":zzz", [1, 2, 3], [4, 5]],
                '("test" nil nil 123 "456" ":zzz" (1 2 3) (4 5))');
test_conversion(["N:one"], "(1)", { one: 1 });
test_conversion(["N:one", "N:two", "N:three"], "(1 2 3)", { one: 1, two: 2, three: 3 });
test_conversion(["N:one", "N:two", "N:three"], "(1 2)", CONV_ERROR);
test_conversion(["N:one", "N:two", "s:zzz"], '(1 2 "qqqq")', { one: 1, two: 2, zzz: "qqqq" });
test_conversion(["N:one", "N:two", "s:zzz"], '(1 2 3)', CONV_ERROR);
test_conversion(["N:one", "N:two", "s:zzz"], '(1 2 :RRR)', CONV_ERROR);
test_conversion(["S:op", "_:form", "_:packageName", "_:threadId", "N:id"],
                '(:emacs-rex (swank:connection-info) "COMMON-LISP-USER" t 1)',
                { op: ":emacs-rex",
                  form: list(S("swank:connection-info")),
                  packageName: "COMMON-LISP-USER",
                  threadId: S("t"),
                  id: 1 });
test_conversion(["@:x"], "(test)", { x: "test" }, '("test")');
test_conversion(["@:x"], '((test 123 "456" :zzz (1 2 3) (4 . 5)))',
                { x: ["test", 123, "456", ":zzz", [1, 2, 3], [4, 5]] },
                '(("test" 123 "456" ":zzz" (1 2 3) (4 5)))');
test_conversion(["S:name", "R:args"], '(test)',
                { name: "test",
                  args: [] });
test_conversion(["S:name", "R:args"], '(test :abc :def "QQQ" 123)',
                { name: "test",
                  args: [":abc", ":def", "QQQ", 123] },
                '(test ":abc" ":def" "QQQ" 123)');
test_conversion(["S:name", "R*:args"], '(test)',
                { name: "test",
                  args: [] });
test_conversion(["S:name", "R*:args"], '(test :abc :def (123 . 456))',
                { name: "test",
                  args: [S(":abc"), S(":def"), cons(123, 456)] });

test_conversion(["N:n", "D:dict"], '(42.25 ())',
                { n: 42.25, dict: {} },
                '(42.25 nil)');
test_conversion(["N:n", "D:dict"], '(42.25 (:x 3))',
                { n: 42.25, dict: { x: 3 } });
test_conversion(["N:n", "D:dict"], '(42.25 (:x))', CONV_ERROR);
test_conversion(["N:n", "D:dict"], '(42.25 (:x :y :z))', CONV_ERROR);
test_conversion(["N:n", "D:dict"], '(42.25 (:x 3 :abc "fff" :zzz qwerty))',
                { n: 42.25, dict: { x: 3, abc: "fff", zzz: "qwerty" }},
                '(42.25 (:abc "fff" :x 3 :zzz "qwerty"))');
test_conversion(["N:n", "D*:dict"], '(42.25 ())',
                { n: 42.25, dict: {} },
                '(42.25 nil)');
test_conversion(["N:n", "D*:dict"], '(42.25 (:x 3))',
                { n: 42.25, dict: { x: 3 } });
test_conversion(["N:n", "D*:dict"], '(42.25 (:x))', CONV_ERROR);
test_conversion(["N:n", "D*:dict"], '(42.25 (:x :y :z))', CONV_ERROR);
test_conversion(["N:n", "D*:dict"], '(42.25 (:x 3 :abc "fff" :zzz qwerty))',
                { n: 42.25, dict: { x: 3, abc: "fff", zzz: S("qwerty") } },
                '(42.25 (:abc "fff" :x 3 :zzz qwerty))');

test_conversion(["N:n", "RD:dict"], '(42.25)',
                { n: 42.25, dict: {} });
test_conversion(["N:n", "RD:dict"], '(42.25 :x 3)',
                { n: 42.25, dict: { x: 3 } });
test_conversion(["N:n", "RD:dict"], '(42.25 :x)', CONV_ERROR);
test_conversion(["N:n", "RD:dict"], '(42.25 :x 3 :abc "fff" :zzz qwerty)',
                { n: 42.25, dict: { x: 3, abc: "fff", zzz: "qwerty" }},
                '(42.25 :abc "fff" :x 3 :zzz "qwerty")');
test_conversion(["N:n", "RD*:dict"], '(42.25)',
                { n: 42.25, dict: {} });
test_conversion(["N:n", "RD*:dict"], '(42.25 :x 3)',
                { n: 42.25, dict: { x: 3 } });
test_conversion(["N:n", "RD*:dict"], '(42.25 :x)', CONV_ERROR);
test_conversion(["N:n", "RD*:dict"], '(42.25 :x 3 :abc "fff" :zzz qwerty)',
                { n: 42.25, dict: { x: 3, abc: "fff", zzz: S("qwerty") } },
                '(42.25 :abc "fff" :x 3 :zzz qwerty)');

test_conversion({ x: "N", "abc-def": "D:abcDef", name: "S", rrr: "_:r1", qqq: "_" },
                '(:abc-def (:x 3 :y 9) :x 42 :name :abcd :rrr "whatever" :unused 99)',
                { x: 42, abcDef: { x: 3, y: 9 }, name: ":abcd", r1: "whatever" },
                '(:abc-def (:x 3 :y 9) :name :abcd :rrr "whatever" :x 42)');

// > and >* tell arrayValue to consume the next argument as type value
test_conversion(["S:name", ">:dict", { x: "N", y: "S" }],
                '(:somename (:x 32 :y :zzz))',
                { name: ":somename", dict: { x: 32, y: ":zzz" } });
test_conversion(["S:name", ">*:dict", { x: "N", y: "S" }],
                '(:somename :x 32 :y :zzz)',
                { name: ":somename", dict: { x: 32, y: ":zzz" } });

test_conversion({ x: "N", l: { name: "theList", spec: ["S:name", "N:n", "K:keyword"] },
                  d: { name: "dict1", spec: { a: "N", b: "N" } },
                  d2: { spec: { a: "N", b: "N" } }},
                '(:x 99 :l (zzz 42 :eprst) :d (:a 11 :b 12) :d2 (:a 1 :b 2))',
                { x: 99,
                  theList: { name: "zzz", n: 42, keyword: "eprst" },
                  dict1: { a: 11, b: 12 },
                  d2: { a: 1, b : 2 } },
                '(:d (:a 11 :b 12) :d2 (:a 1 :b 2) :l (zzz 42 :eprst) :x 99)');

assert.equal("(:abc 12 :def 4242)", repr(toLisp({ abc: 12, def: 4242 }, "@")));
assert.equal("(:abc 19)", repr(toLisp({ x: 19 }, [S(":abc"), "N:x"])));
assert.equal("(abc 19 :def)", repr(toLisp({ x: 19 }, [S("abc"), "N:x", S(":def")])));
assert.equal("nil", repr(toLisp(null, "@")));
assert.equal("nil", repr(toLisp(null, "_")));

// TBD: toLisp should use "@" as spec by default
