// -*- mode: js3 -*-
//
// Copyright (c) 2012 Robert Krahn. All rights reserved.
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

function addObjectToWindow(nameInWindow, obj, callback) {
  window[nameInWindow] = obj;
  try {
    callback();
  } finally {
    delete window[nameInWindow];
  }
}

function assert(val, msg) {
  if (!val) throw new Error(msg || "Assertion failed");
}

assert.equal = function equal(expected, actual, msg) {
  assert(expected == actual,
         "Assertion failed: '" + actual + "' is not '" +
         expected + "' " + (msg ? msg : ''));
};

function test(testCase) {
  for (var name in testCase) {
    if (testCase.hasOwnProperty(name) && name.match(/^test/)) {
      console.log("Running " + name);
      try {
        testCase[name]();
      } catch (e) {
        console.error("Test " + name + " not successful: " + e);
      } finally {
        testCase.tearDown && testCase.tearDown();
      }
    }
  }
  var msg = "tests of " + testCase.name + " finished";
  console.log(msg);
  return msg;
}

var completion = new Completion({ enumerablePropsOnly: true });

test({
  name: 'completion tests',

  testCompletionOfTopLevelString: function() {
    // "foooTestTopLev" -> ["foooTestTopLevelString"]
    var name = "foooTestTopLevelString";
    addObjectToWindow(name, {}, function() {
      var result = completion.complete("foooTestTopLev");
      assert.equal(name, result.partial, "result.partial");
      assert.equal(1, result.values.length, "result.values.length");
      assert.equal(name, result.values[0], "Result wrong?");
    });
  },

  testCompletionOfProperty: function() {
    // "testPropCompletion.foo.b" -> ["testPropCompletion.foo.bar"]
    var name = "testPropCompletion";
    addObjectToWindow(name, {foo: {bar: {}}}, function() {
      var result = completion.complete("testPropCompletion.foo.b");
      assert.equal("testPropCompletion.foo.bar", result.partial,
                   "result.partial");
      assert.equal(1, result.values.length, "result.values.length");
      assert.equal("testPropCompletion.foo.bar", result.values[0],
                   "Result wrong?");
    });
  },

  testCompletionOfEverything: function() {
    // "testCompleteEverything." -> ["testCompleteEverything.foo", "testCompleteEverything.bar"]
    var name = "testCompleteEverything";
    addObjectToWindow(name, {foo: {}, bar: {}}, function() {
      var result = completion.complete("testCompleteEverything.");
      assert.equal("testCompleteEverything.", result.partial, "result.partial");
      assert.equal(2, result.values.length, "result,values.length");
      assert.equal("testCompleteEverything.bar",
                   result.values[0], "Result 1 wrong? " + result);
      assert.equal("testCompleteEverything.foo",
                   result.values[1], "Result 2 wrong? " + result);
    });
  }
});

test({
  name: 'CSS embed tests',

  tearDown: function() {
    var style = document.getElementById('swank-js-css');
    style && style.parentNode.removeChild(style);
  },

  testCreatesStyleElement: function() {
    var styleString = "body { margin: 10px }";
    SwankJS.embedCSS(styleString);
    var el = document.getElementById('swank-js-css');
    assert(el, 'no style element created');
    assert.equal(styleString, el.textContent);
  },

  testExtendsStyleElement: function() {
    var styleString1 = "body { margin: 10px }",
        styleString2 = "body { margin: 12px }";
    SwankJS.embedCSS(styleString1);
    SwankJS.embedCSS(styleString2);
    var el = document.getElementById('swank-js-css');
    assert.equal(styleString1 + '\n' + styleString2, el.textContent);
  },

  testClean: function() {
    var styleString = "body { margin: 10px }";
    SwankJS.embedCSS(styleString);
    SwankJS.removeEmbeddedCSS();
    var el = document.getElementById('swank-js-css');
    assert(!el, 'style elemet not removed');
  }

});