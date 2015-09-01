// -*- mode: js2; js-run: "swank-handler-tests.js" -*-
//
// Copyright (c) 2010 Ivan Shvedunov. All rights reserved.
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

var EventEmitter = require("events").EventEmitter;
var Script = require('vm').Script;
var evalcx = Script.runInContext;
var util = require("util");
var url = require("url");
var assert = require("assert");
var lisp = require("./lisp");
var S = lisp.S, list = lisp.list, consp = lisp.consp, car = lisp.car, cdr = lisp.cdr,
    repr = lisp.repr, fromLisp = lisp.fromLisp, toLisp = lisp.toLisp;
var Completion = require("./completion").Completion;

var DEFAULT_SLIME_VERSION = "2012-02-12";

// hack for require.resolve("./relative") to work properly.
module.filename = process.cwd() + '/repl';
// hack for repl require to work properly with node_modules folders
module.paths = require('module')._nodeModulePaths(module.filename);

function Handler (executive) {
  this.executive = executive;
  var self = this;
  this.executive.on("output", function (str) { self.output(str); });
  this.executive.on("newPackage", function (name) { self.newPackage(name); });
};

util.inherits(Handler, EventEmitter);

Handler.prototype.receive = function receive (message) {
  // FIXME: error handling
  console.log("Handler.prototype.receive(): %s", repr(message).replace(/\n/, "\\n"));
  if (!consp(message) || car(message) != S(":emacs-rex")) {
    console.log("bad message: %s", message);
    return;
  }
  var d, expr;
  try {
    d = fromLisp(message, ["S:op", ">:form",
                           ["S:name", "R*:args"],
                           "_:package", "_:threadId", "N:id"]);
  } catch (e) {
    if (e instanceof TypeError) {
      console.log("failed to parse %s: %s", message, e);
      return; // FIXME
    }
    throw e;
  }

  var r = { status: ":ok", result: null };
  var self = this;
  var cont = function cont () {
    self.sendResponse({ r: r, id: d.id },
                      [S(":return"), ">:r", ["S:status", "_:result"], "N:id"]);
  };

  switch (d.form.name) {
  case "swank:connection-info":
    this.executive.connectionInfo(
      function (info) {
        console.log("info = %j", info);
        r.result = toLisp(
          info,
          { "pid": "N:pid",
            "encoding": { name: "encoding",
                          spec: { "coding-systems": "@:codingSystems" } },
            "package": { name: "packageSpec", spec: { name: "s", prompt: "s" } },
            "lisp-implementation": {
              name: "implementation",
              spec: { type: "s", name: "s", version: "s" } },
            "version": "s:version" });
        cont();
      });
    return;
  case "swank:create-repl":
    r.result = toLisp(this.executive.createRepl(), ["s:packageName", "s:prompt"]);
    break;
  case "swank:autodoc":
    r.result = S(":not-available");
    break;
  case "js:list-remotes":
    // FIXME: support 'list of similar elements' type spec
    r.result = toLisp(
      this.executive.listRemotes().map(
        function (item) {
          return toLisp(item, ["N:index", "K:kind", "s:id", "B:isActive"]);
        }, this));
    break;
  case "js:select-remote":
    if (d.form.args.length != 2) {
      console.log("bad args len for SWANK:SELECT-REMOTE -- %s", d.form.args.length);
      return; // FIXME
    }
    // FIXME: get rid of spaghetti
    var remoteIndex, sticky;
    try {
      // FIXME: args should be a cons / NIL
      remoteIndex = fromLisp(d.form.args[0], "N");
      sticky = fromLisp(d.form.args[1]);
    } catch (e) {
      if (e instanceof TypeError) {
        console.log("can't parse arg -- %s", d.form.args[0]);
        return; // FIXME
      }
      throw e;
    }
    this.executive.selectRemote(remoteIndex, sticky);
    break;
  case "js:set-target-url":
  case "js:set-slime-version":
    if (d.form.args.length != 1) {
      console.log("bad args len for JS:SET-TARGET-URL -- %s", d.form.args.length);
      return; // FIXME
    }
    try {
      expr = fromLisp(d.form.args[0], "s");
    } catch (e) {
      if (e instanceof TypeError) {
        console.log("can't parse arg -- %s", d.form.args[0]);
        return; // FIXME
      }
      throw e;
    }
    this.executive[d.form.name == "js:set-target-url" ? "setTargetUrl" : "setSlimeVersion"](expr);
    break;
  case "swank:interactive-eval":
  case "swank:interactive-eval-region":
  case "swank:listener-eval":
    if (d.form.args.length != 1) {
      console.log("bad args len for SWANK:LISTENER-EVAL -- %s", d.form.args.length);
      return; // FIXME
    }
    try {
      expr = fromLisp(d.form.args[0], "s");
    } catch (e) {
      if (e instanceof TypeError) {
        console.log("can't parse arg -- %s", d.form.args[0]);
        return; // FIXME
      }
      throw e;
    }
    this.executive.listenerEval(
      expr, function (values) {
        if (values.length)
          r.result = toLisp({ values: values }, [S(":values"), "R:values"]);
        cont();
      });
    return;
  case "swank:fuzzy-completions":
    // TBD
    r.result = toLisp([[], []], "@");
    cont();
    return;
  case "swank:simple-completions":
    var prefix = d.form.args[0];
    var objStr = fromLisp(prefix, "@");
    console.log("Called " + "swank:simple-completions: " + objStr);
    this.executive.listenerCompletion(
      objStr, function (result) {
        r.result = toLisp([ result.values, result.partial ], "@");
        cont();
      });
    return;
  default:
    // FIXME: handle unknown commands
  }
  cont();
};

Handler.prototype.output = function output (str) {
  this.sendResponse([S(":write-string"), str]);
};

Handler.prototype.newPackage = function newPackage (name) {
  this.sendResponse([S(":new-package"), name, name]);
};

Handler.prototype.sendResponse = function sendResponse(response, spec)
{
  this.emit("response", repr(toLisp(response, spec || "@")));
};

function Remote () {};

util.inherits(Remote, EventEmitter);

Remote.prototype.prompt = function prompt () {
  return "JS";
};

Remote.prototype.kind = function kind () {
  throw new Error("must override Remote.prototype.kind()");
};

Remote.prototype.id = function id () {
  throw new Error("must override Remote.prototype.id()");
};

Remote.prototype.evaluate = function evaluate (id, str) {
  throw new Error("must override Remote.prototype.evaluate()");
};

Remote.prototype.completer = function completer () {
  return new Completion();
};

Remote.prototype.completion = function completion (id, str) {
  console.log("complete: " + str);
  this.sendResult(id, this.completer().complete(str));
};

Remote.prototype.fullName = function fullName () {
  return "(" + this.kind() + ") " + this.id();
};

Remote.prototype.disconnect = function disconnect () {
  this.emit("disconnect");
};

Remote.prototype.detachSelf = function detachSelf () {
  this.removeAllListeners("output");
  this.removeAllListeners("disconnect");
  this.removeAllListeners("result");
};

Remote.prototype.output = function output (str) {
  this.emit("output", String(str));
};

Remote.prototype.setIndex = function setIndex (n) {
  this._index = n;
};

Remote.prototype.index = function index () {
  return this._index;
};

Remote.prototype.sendResult = function sendResult (id, values) {
  this.emit("result", id, values);
};

function DefaultRemote () {
  this.context = Script.createContext();
  for (var i in global) this.context[i] = global[i];
  this.context.module = module;
  this.context.require = function(id, options) {
    // Remove module from cache if reload is requested.
    if (options && options.reload)
      delete require.cache[require.resolve(id)];
    return require(id);
  }
  var self = this;
  this.context._swank = {
    output: function output (arg) {
      self.output(arg);
    }
  };
}

util.inherits(DefaultRemote, Remote);

DefaultRemote.prototype.completer = function completer () {
  return new Completion(
    {
      global: this.context,
      evaluate: function (str) {
        return evalcx(str, this.context, "repl");
      }.bind(this)
    });
};

DefaultRemote.prototype.prompt = function prompt () {
  return "NODE";
};

DefaultRemote.prototype.kind = function kind () {
  return "direct";
};

DefaultRemote.prototype.id = function id () {
  return "node.js";
};

DefaultRemote.prototype.evaluate = function evaluate (id, str) {
  var r;
  try {
    r = evalcx(str, this.context, "repl");
  } catch (e) {
    r = undefined;
    this.output(e.stack);
  }
  this.sendResult(id, r === undefined ? [] : [util.inspect(r)]);
};

// TBD: rename Executive to Dispatcher
function Executive (options) {
  options = options || {};
  assert.ok(options.hasOwnProperty("config") && options.config);
  this.config = options.config;
  this.pid = options.hasOwnProperty("pid") ? options.pid : null;
  this.remotes = [];
  this.attachRemote(new DefaultRemote());
  this.activeRemote = this.remotes[0];
  this.pendingRequests = {};
};

util.inherits(Executive, EventEmitter);

Executive.nextId = 1; // request id counter is global in order to avoid inter-connection conflicts

Executive.nextRemoteIndex = 1;

Executive.prototype.attachRemote = function attachRemote (remote) {
  assert.ok(this.remotes.indexOf(remote) < 0);
  remote.setIndex(Executive.nextRemoteIndex++);

  var self = this;
  remote.on(
    "output", function (str) {
      if (remote == self.activeRemote)
        self.emit("output", str);
    });
  remote.on(
    "disconnect", function (str) {
      self.handleDisconnectRemote(remote);
    });
  remote.on(
    "result", function (id, values) {
      if (!self.pendingRequests[id]) {
        self.emit("output", "WARNING: received late result from " + remote.fullName() + "\n");
        return;
      }
      try {
        self.pendingRequests[id](values);
      } finally {
        delete self.pendingRequests[id];
      }
    });
  this.remotes.push(remote);
  this.emit("output", "Remote attached: " + remote.fullName() + "\n");

  this.config.get(
    "stickyRemote",
    function (stickyRemote) {
      if (stickyRemote !== null &&
          (!self.activeRemote || self.activeRemote.fullName() != stickyRemote) &&
          remote.fullName() == stickyRemote)
        self.selectRemote(remote.index(), true, true);
    });
};

Executive.prototype.handleDisconnectRemote = function handleDisconnectRemote (remote) {
  remote.detachSelf();
  var index = this.remotes.indexOf(remote);
  if (index < 0) {
    this.emit("output", "WARNING: disconnectRemote() called for an unknown remote: " + remote.fullName() + "\n");
    return;
  }
  this.remotes.splice(index, 1);
  this.emit("output", "Remote detached: " + remote.fullName() + "\n");
  if (remote == this.activeRemote)
    this.selectRemote(this.remotes[0].index(), false, true);
};

Executive.prototype.connectionInfo = function connectionInfo (cont) {
  var self = this;
  var prompt = this.activeRemote.prompt();
  this.config.get(
    "slimeVersion",
    function (slimeVersion) {
      cont({ pid: self.pid === null ? process.pid : self.pid,
             encoding: { codingSystems: [ "utf-8-unix" ] },
             packageSpec: { name: prompt, prompt: prompt },
             implementation: { type: "JS", name: "JS", version: "1.5" },
             version: slimeVersion || DEFAULT_SLIME_VERSION });
    });
};

Executive.prototype.createRepl = function createRepl () {
  var prompt = this.activeRemote.prompt();
  return { packageName: prompt, prompt: prompt };
};

Executive.prototype.listenerEval = function listenerEval (str, cont) {
  var id = Executive.nextId++;
  this.pendingRequests[id] = cont;
  this.activeRemote.evaluate(id, str);
};

Executive.prototype.listenerCompletion = function listenerCompletion(str, cont) {
  var id = Executive.nextId++;
  this.pendingRequests[id] = cont;
  this.activeRemote.completion(id, str);
};

Executive.prototype.listRemotes = function listRemotes () {
  return this.remotes.map(
    function (remote) {
      return { index: remote.index(), kind: remote.kind(), id: remote.id(),
               isActive: remote === this.activeRemote };
    }, this);
};

Executive.prototype.selectRemote = function selectRemote (index, sticky, auto) {
  // TBD: sticky support (should autoselect the remote with message upon attachment)
  for (var i = 0; i < this.remotes.length; ++i) {
    var remote = this.remotes[i];
    if (remote.index() == index) {
      if (remote == this.activeRemote) {
        this.emit("output", "WARNING: remote already selected: " + remote.fullName() + "\n");
        return;
      }
      this.activeRemote = remote;
      if (!auto)
        this.config.set("stickyRemote", sticky ? remote.fullName() : null);
      this.emit("newPackage", remote.prompt());
      this.emit("output", "Remote selected" + (auto ? " (auto)" : sticky ? " (sticky)" : "") +
                ": " + remote.fullName() + "\n");
      return;
    }
  }
  this.emit("output", "WARNING: bad remote index\n");
};

Executive.prototype.setTargetUrl = function setTargetUrl (targetUrl) {
  var parsedUrl = null;
  try {
    parsedUrl = url.parse(targetUrl);
  } catch (e) {}
  if (parsedUrl && parsedUrl.hostname)
    this.config.set("targetUrl", targetUrl);
  else
    this.emit("output", "WARNING: the URL must contain host and port\n");
};

Executive.prototype.setSlimeVersion = function setSlimeVersion (slimeVersion) {
  this.config.set("slimeVersion", slimeVersion);
};

exports.Handler = Handler;
exports.Remote = Remote;
exports.Executive = Executive;
