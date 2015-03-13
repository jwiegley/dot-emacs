// -*- mode: js2; js-run: t -*-
//
// Copyright (c) 2012 Robert Krahn. All rights reserved.
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

var Completion = require("./completion").Completion;
var assert = require("assert");

function addObjectToGlobal(name, obj, callback) {
  var global = Function('return this')();
  global[name] = obj;
  try {
    callback();
  } finally {
    delete global[name];
  }
}

var completion = new Completion({ enumerablePropsOnly: true });
var name = "foooTestTopLevelString";
addObjectToGlobal(
  name, {}, function () {
    assert.deepEqual({ values: [ name ], partial: name },
                     completion.complete("foooTestTopLev"));
    assert.deepEqual({ values: [], partial: "bbbb" },
                     completion.complete("bbbb"));
  });

name = "testPropCompletion";
addObjectToGlobal(
  name, { foo: { bar: {} } }, function () {
    assert.deepEqual({ values: [ "testPropCompletion.foo.bar" ],
                       partial: "testPropCompletion.foo.bar" },
                     completion.complete("testPropCompletion.foo.b"));
    assert.deepEqual({ values: [], partial: "testPropCompletion.foo.baz" },
                     completion.complete("testPropCompletion.foo.baz"));
    assert.deepEqual({ values: [], partial: "testPropCompletion.fooz.bar.qqq" },
                     completion.complete("testPropCompletion.fooz.bar.qqq"));
  });

name = "testCompleteEverything";
addObjectToGlobal(
  name, { foo: {}, bar: {} }, function () {
    assert.deepEqual(
      { values: [ "testCompleteEverything.bar", "testCompleteEverything.foo" ],
        partial: "testCompleteEverything." },
      completion.complete("testCompleteEverything."));
  });

// include non-enumerable properties
assert.ok(new Completion().complete("Obj").values.indexOf("Object") >= 0);
