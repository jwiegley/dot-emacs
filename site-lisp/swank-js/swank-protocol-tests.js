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

var swp = require("./swank-protocol");
var lisp = require("./lisp");
var Buffer = require('buffer').Buffer;
var assert = require("assert");
var S = lisp.S, list = lisp.list, nil = lisp.nil;

var expected = [];

var parser = new swp.SwankParser(
  function onMessage (message) {
    assert.ok(expected.length > 0);
    var expectedMessage = expected.shift();
    assert.deepEqual(expectedMessage, message);
  });

function feed (text) {
  for (var i = 1; i < arguments.length; ++i)
    expected.push(arguments[i]);
  parser.execute(new Buffer(text));
  assert.equal(0, expected.length);
}

// dispatch: see dispatch-event in swank.lisp
feed("000");
feed("03b");
feed("(:emacs-rex (swank:connection-info) \"COMMON-LISP-USER\" t 1)",
     list(S(":emacs-rex"), list(S("swank:connection-info")),
          "COMMON-LISP-USER", S("t"), 1));

feed("0");
feed("0");
feed("0");
feed("03b(:emacs-rex (swank:connection-info)");
feed(" \"COMMON-LISP-USER\" t 1)000",
     list(S(":emacs-rex"), list(S("swank:connection-info")),
          "COMMON-LISP-USER", S("t"), 1));

feed("03b(:emacs-rex (swank:connection-info)");
feed(" \"COMMON-LISP-USER\" t 1");
feed(")",
     list(S(":emacs-rex"), list(S("swank:connection-info")),
          "COMMON-LISP-USER", S("t"), 1));
feed('000047(:emacs-rex (:listener-eval "\\"\u0439\u0446\u0443\\"") "FIREFOX-9.0" :repl-thread 4)',
     list(S(":emacs-rex"),
                        list(S(":listener-eval"),
                             '"\u0439\u0446\u0443"'),
                        "FIREFOX-9.0", S(":repl-thread"), 4));

assert.equal(
  "000015(:return (:ok nil) 1)",
  swp.buildMessage(list(S(":return"), list(S(":ok"), nil), 1)).toString());

assert.equal(
  '000047(:emacs-rex (:listener-eval "\\"\u0439\u0446\u0443\\"") "FIREFOX-9.0" :repl-thread 4)',
  swp.buildMessage(list(S(":emacs-rex"),
                        list(S(":listener-eval"),
                             '"\u0439\u0446\u0443"'),
                        "FIREFOX-9.0", S(":repl-thread"), 4)).toString());
