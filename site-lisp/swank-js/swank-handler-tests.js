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

var swh = require("./swank-handler");
var readFromString = require("./lisp").readFromString;
var config = require("./config");
var util = require("util");
var assert = require("assert");

var cfg = new config.FakeConfig();
var expected = [];
var executive = new swh.Executive({ config: cfg, pid: 4242 });
var handler = new swh.Handler(executive);

handler.on(
  "response", function (response) {
    // console.log("=> %s", response);
    assert.ok(expected.length > 0);
    assert.ok(typeof(response) == "string");
    // console.log("response: %s", response);
    var expectedResponse = expected.shift();
    if (expectedResponse instanceof RegExp)
      assert.ok(expectedResponse.test(response));
    else
      assert.equal(expectedResponse, response,
                   "got response " + response + " instead of " + expectedResponse);
  });

function expect () {
  for (var i = 0; i < arguments.length; ++i)
    expected.push(arguments[i]);
}

function verifyExpectations () {
  // console.log("expected: %s\n", expected.map(JSON.stringify).join("\n"));
  assert.equal(0, expected.length);
}

function request (str) {
  for (var i = 1; i < arguments.length; ++i)
    expected.push(arguments[i]);
  handler.receive(readFromString(str));
  verifyExpectations();
}

request('(:emacs-rex (swank:connection-info) "COMMON-LISP-USER" t 1)',
        '(:return (:ok (:encoding (:coding-systems ("utf-8-unix")) ' +
                       ':lisp-implementation (:name "JS" :type "JS" :version "1.5") ' +
                       ':package (:name "NODE" :prompt "NODE") ' +
                       ':pid 4242 :version "2012-02-12")) ' +
        '1)');

// currently we just ignore swank-require
request('(:emacs-rex (swank:swank-require \'(swank-listener-hooks swank-indentation)) "COMMON-LISP-USER" t 2)',
        '(:return (:ok nil) 2)');

request('(:emacs-rex (swank:create-repl nil) "COMMON-LISP-USER" t 3)',
        '(:return (:ok ("NODE" "NODE")) 3)');

request('(:emacs-rex (swank:listener-eval "3 * 10\n") "NODE" :repl-thread 4)',
        '(:return (:ok (:values "30")) 4)');

request('(:emacs-rex (swank:listener-eval "undefined") "NODE" :repl-thread 5)',
        '(:return (:ok nil) 5)');

request('(:emacs-rex (swank:autodoc \'("zzzz" swank::%cursor-marker%) :print-right-margin 236)' +
        ' "COMMON-LISP-USER" :repl-thread 6)',
        '(:return (:ok :not-available) 6)');

request('(:emacs-rex (swank:listener-eval "_swank.output(\'hello world\\\\n\')") "NODE" :repl-thread 7)',
        '(:write-string "hello world\n")',
        '(:return (:ok nil) 7)');

request('(:emacs-rex (swank:listener-eval "_swank.output(1234)") "NODE" :repl-thread 8)',
        '(:write-string "1234")',
        '(:return (:ok nil) 8)');

request('(:emacs-rex (swank:listener-eval "zzz") "NODE" :repl-thread 9)',
        /^\(:write-string "ReferenceError: zzz is not defined(.|\n)*"\)$/,
        '(:return (:ok nil) 9)');

// TBD: debugger

function FakeRemote (name) {
  this.name = name;
};

util.inherits(FakeRemote, swh.Remote);

FakeRemote.prototype.prompt = function prompt () {
  return "FAKE";
};

FakeRemote.prototype.kind = function kind () {
  return "test";
};

FakeRemote.prototype.id = function id () {
  return this.name;
};

FakeRemote.prototype.evaluate = function evaluate (id, str) {
  this.sendResult(id, [ "R:" + this.name + ":" + str.replace(/^\s*|\s*$/g, "") ]);
};

request('(:emacs-rex (js:list-remotes) "NODE" :repl-thread 10)',
        '(:return (:ok ((1 :direct "node.js" t))) 10)');

expect('(:write-string "Remote attached: (test) test/localhost:8080\n")');
var r1 = new FakeRemote("test/localhost:8080");
executive.attachRemote(r1);
verifyExpectations();

request('(:emacs-rex (js:list-remotes) "NODE" :repl-thread 11)',
        '(:return (:ok ((1 :direct "node.js" t) (2 :test "test/localhost:8080" nil))) 11)');

expect('(:write-string "Remote attached: (test) test/localhost:9999\n")');
var r2 = new FakeRemote("test/localhost:9999");
executive.attachRemote(r2);
verifyExpectations();

request('(:emacs-rex (js:list-remotes) "NODE" :repl-thread 12)',
        '(:return (:ok ((1 :direct "node.js" t) ' +
        '(2 :test "test/localhost:8080" nil) ' +
        '(3 :test "test/localhost:9999" nil))) 12)');

request('(:emacs-rex (swank:listener-eval "3 * 10\n") "NODE" :repl-thread 13)',
        '(:return (:ok (:values "30")) 13)');

request('(:emacs-rex (js:select-remote 2 nil) "NODE" :repl-thread 14)',
        '(:new-package "FAKE" "FAKE")',
        '(:write-string "Remote selected: (test) test/localhost:8080\n")',
        '(:return (:ok nil) 14)');

request('(:emacs-rex (js:list-remotes) "NODE" :repl-thread 15)',
        '(:return (:ok ((1 :direct "node.js" nil) ' +
        '(2 :test "test/localhost:8080" t) ' +
        '(3 :test "test/localhost:9999" nil))) 15)');

request('(:emacs-rex (swank:listener-eval "3 * 10\n") "NODE" :repl-thread 16)',
        '(:return (:ok (:values "R:test/localhost:8080:3 * 10")) 16)');

expect('(:write-string "Remote detached: (test) test/localhost:8080\n")',
       '(:new-package "NODE" "NODE")',
       '(:write-string "Remote selected (auto): (direct) node.js\n")');
r1.disconnect();
verifyExpectations();

request('(:emacs-rex (swank:listener-eval "3 * 10\n") "NODE" :repl-thread 17)',
        '(:return (:ok (:values "30")) 17)');

// TBD: add higher-level functions for testing remotes

request('(:emacs-rex (js:list-remotes) "NODE" :repl-thread 18)',
        '(:return (:ok ((1 :direct "node.js" t) ' +
        '(3 :test "test/localhost:9999" nil))) 18)');

expect('(:write-string "Remote detached: (test) test/localhost:9999\n")');
r2.disconnect();
verifyExpectations();

request('(:emacs-rex (swank:listener-eval "3 * 10\n") "NODE" :repl-thread 19)',
        '(:return (:ok (:values "30")) 19)');

request('(:emacs-rex (js:list-remotes) "NODE" :repl-thread 20)',
        '(:return (:ok ((1 :direct "node.js" t))) 20)');

request('(:emacs-rex (js:select-remote 2 nil) "NODE" :repl-thread 21)',
        '(:write-string "WARNING: bad remote index\n")',
        '(:return (:ok nil) 21)');

request('(:emacs-rex (swank:listener-eval "3 * 10\n") "NODE" :repl-thread 22)',
        '(:return (:ok (:values "30")) 22)');

request('(:emacs-rex (js:select-remote 1 nil) "NODE" :repl-thread 23)',
        '(:write-string "WARNING: remote already selected: (direct) node.js\n")',
        '(:return (:ok nil) 23)');

assert.equal(null, cfg.getNow("stickyRemote"));

// test sticky remote selection
expect('(:write-string "Remote attached: (test) test/localhost:8001\n")');
var r3 = new FakeRemote("test/localhost:8001");
executive.attachRemote(r3);
verifyExpectations();

request('(:emacs-rex (js:list-remotes) "NODE" :repl-thread 24)',
        '(:return (:ok ((1 :direct "node.js" t) (4 :test "test/localhost:8001" nil))) 24)');

request('(:emacs-rex (js:select-remote 4 t) "NODE" :repl-thread 25)',
        '(:new-package "FAKE" "FAKE")',
        '(:write-string "Remote selected (sticky): (test) test/localhost:8001\n")',
        '(:return (:ok nil) 25)');

assert.equal("(test) test/localhost:8001", cfg.getNow("stickyRemote"));

expect('(:write-string "Remote detached: (test) test/localhost:8001\n")',
       '(:new-package "NODE" "NODE")',
       '(:write-string "Remote selected (auto): (direct) node.js\n")');
r3.disconnect();
verifyExpectations();

expect('(:write-string "Remote attached: (test) test/localhost:8001\n")',
       '(:new-package "FAKE" "FAKE")',
       '(:write-string "Remote selected (auto): (test) test/localhost:8001\n")');
var r5 = new FakeRemote("test/localhost:8001");
executive.attachRemote(r5);
verifyExpectations();

assert.equal("(test) test/localhost:8001", cfg.getNow("stickyRemote"));

request('(:emacs-rex (js:select-remote 1 nil) "NODE" :repl-thread 26)',
        '(:new-package "NODE" "NODE")',
        '(:write-string "Remote selected: (direct) node.js\n")',
        '(:return (:ok nil) 26)');

request('(:emacs-rex (js:select-remote 5 nil) "NODE" :repl-thread 27)',
        '(:new-package "FAKE" "FAKE")',
        '(:write-string "Remote selected: (test) test/localhost:8001\n")',
        '(:return (:ok nil) 27)');

assert.equal(null, cfg.getNow("stickyRemote"));

expect('(:write-string "Remote detached: (test) test/localhost:8001\n")',
       '(:new-package "NODE" "NODE")',
       '(:write-string "Remote selected (auto): (direct) node.js\n")');
r5.disconnect();
verifyExpectations();

expect('(:write-string "Remote attached: (test) test/localhost:8001\n")');
var r6 = new FakeRemote("test/localhost:8001");
executive.attachRemote(r6);
verifyExpectations();

assert.equal(null, cfg.getNow("stickyRemote"));

request('(:emacs-rex (js:set-target-url "http://localhost:1234/") "NODE" :repl-thread 28)',
        '(:return (:ok nil) 28)');

assert.equal("http://localhost:1234/", cfg.getNow("targetUrl"));

request('(:emacs-rex (js:set-target-url "zzz") "NODE" :repl-thread 29)',
        '(:write-string "WARNING: the URL must contain host and port\n")',
        '(:return (:ok nil) 29)');

assert.equal("http://localhost:1234/", cfg.getNow("targetUrl"));

assert.equal(null, cfg.getNow("slimeVersion"));

request('(:emacs-rex (js:set-slime-version "2010-11-28") "NODE" :repl-thread 30)',
        '(:return (:ok nil) 30)');

assert.equal("2010-11-28", cfg.getNow("slimeVersion"));

// TBD: use ## instead of numbers in the tests above (request() should take care of it)
// TBD: test output from an inactive remote
// TBD: are out-of-order results for :emacs-rex ok? look at slime sources

/*

list/select remotes along the lines of

catching errors on the client: window.onerror
http://stackoverflow.com/questions/951791/javascript-global-error-handling
*/

// TBD: add \n to messages from remotes / executive
