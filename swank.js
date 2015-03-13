#!/usr/bin/env node
// -*- mode: js2 -*-
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

var net = require("net"), http = require('http'), io = require('socket.io'), util = require("util"),
    url = require('url'), fs = require('fs');
var swh = require("./swank-handler");
var swp = require("./swank-protocol");
var ua = require("./user-agent");
var config = require("./config");

var DEFAULT_TARGET_HOST = "localhost";
var DEFAULT_TARGET_PORT = 8080;
var CONFIG_FILE_NAME = "~/.swankjsrc";

var cfg = new config.Config(CONFIG_FILE_NAME);
var executive = new swh.Executive({ config: cfg });

var swankServer = net.createServer(
  function (stream) {
    var handler = new swh.Handler(executive);
    var parser = new swp.SwankParser(
      function onMessage (message) {
        handler.receive(message);
      });
    handler.on(
      "response", function (response) {
        var responseBuf = swp.buildMessage(response);
        console.log("response: %s", responseBuf.toString());
        stream.write(responseBuf);
      });
    stream.on(
      "data", function (data) {
        parser.execute(data);
      });
    stream.on(
      "end", function () {
        // FIXME: notify handler -> executive
        // TBD: destroy the handler
        handler.removeAllListeners("response");
      });
  });
swankServer.listen(process.argv[2] || 4005, process.argv[3] || "localhost");

function BrowserRemote (clientInfo, client) {
  var userAgent = ua.recognize(clientInfo.userAgent);
  this.name = userAgent.replace(/ /g, "") + (clientInfo.address ? (":" + clientInfo.address) : "");
  this._prompt = userAgent.toUpperCase().replace(/ /g, '-');
  this.pendingRequests = {};
  this.client = client;
  this.client.on(
    "message", function(m) {
      // TBD: handle parse errors
      // TBD: validate incoming message (id, etc.)
      m = JSON.parse(m);
      if (m.op !== "ping") // don't show pings
        console.log("message from browser: %s", JSON.stringify(m));
      switch(m.op) {
      case "output":
        this.output(m.str);
        break;
      case "result":
        if (!this.pendingRequests.hasOwnProperty(m.id)) {
          console.log("WARNING: late result response from the browser");
          break;
        }
        delete this.pendingRequests[m.id];
        if (m.error) {
          this.output(m.error + "\n");
          this.sendResult(m.id, []);
        } else
          this.sendResult(m.id, m.values);
        this.sweepRequests();
        break;
      case "ping":
        this.client.send(JSON.stringify({ "pong": m.id }));
        break;
      default:
        console.log("WARNING: cannot interpret the client message");
      }
    }.bind(this));
    this.client.on(
      "disconnect", function() {
        console.log("client disconnected: %s", this.id());
        this.disconnect();
      }.bind(this));
}

util.inherits(BrowserRemote, swh.Remote);

BrowserRemote.prototype.REQUEST_TIMEOUT = 3000;

BrowserRemote.prototype.sweepRequests = function sweepRequests (all) {
  Object.keys(this.pendingRequests).forEach(
    function (id) {
      if (all || this.pendingRequests[id] < new Date().getTime() - this.REQUEST_TIMEOUT) {
        console.log("request %s didn't finish", id);
        this.sendResult(id, []);
        delete this.pendingRequests[id];
      }
    }, this);
};

BrowserRemote.prototype.prompt = function prompt () {
  return this._prompt;
};

BrowserRemote.prototype.kind = function kind () {
  return "browser";
};

BrowserRemote.prototype.id = function id () {
  return this.name;
};

BrowserRemote.prototype.evaluate = function evaluate (id, str) {
  this.client.send(JSON.stringify({ "id": id, "code": str }));
  this.pendingRequests[id] = new Date().getTime();
};

BrowserRemote.prototype.completion = function completion (id, str) {
  this.client.send(JSON.stringify({ "id": id, "completion": str }));
  this.pendingRequests[id] = new Date().getTime();
};

BrowserRemote.prototype.disconnect = function disconnect () {
  this.sweepRequests(true);
  swh.Remote.prototype.disconnect.call(this);
};

// proxy code from http://www.catonmat.net/http-proxy-in-nodejs

function HttpListener (cfg) {
  this.config = cfg;
}

HttpListener.prototype.clientVersion = "0.1";

HttpListener.prototype.cachedFiles = {};

HttpListener.prototype.clientFiles = {
  'json2.js': 'client/json2.js',
  'stacktrace.js': 'client/stacktrace.js',
  'swank-js.js': 'client/swank-js.js',
  'load.js': 'client/load.js',
  'swank-js-inject.js': 'client/swank-js-inject.js',
  'browser-tests.js': 'client/browser-tests.js',
  'test.html': 'client/test.html',
  'completion.js': 'completion.js'
};

HttpListener.prototype.types = {
  html: "text/html; charset=utf-8",
  js: "text/javascript; charset=utf-8"
};

HttpListener.prototype.scriptBlock =
    new Buffer('<script type="text/javascript" src="/swank-js/swank-js-inject.js"></script>');

HttpListener.prototype.findClosingTag = function findClosingTag (buffer, name) {
  // note: this function is suitable for <head> and <body> tags,
  // because they don't contain any repeating letters, but
  // it will not work for tags that have such letters
  var chars = [];
  var endChar = ">".charCodeAt(0);
  name = "</" + name.toLowerCase();
  for (var i = 0; i < name.length; ++i)
    chars.push(name.charCodeAt(i));
  var A_CODE = "A".charCodeAt(0), Z_CODE = "Z".charCodeAt(0), CODE_INC = "a".charCodeAt(0) - A_CODE;
  function codeToLower (x) {
    return x >= A_CODE && x <= Z_CODE ? x + CODE_INC : x;
  }
  for (i = 0; i < buffer.length - chars.length - 1;) {
    var found = true;
    if (buffer[i++] != chars[0]) // note: no lowercasing for matching against '<'
      continue;

    for (var j = 1; j < chars.length; ++j, ++i) {
      if (codeToLower(buffer[i]) != chars[j]) {
        found = false;
        break;
      }
    }
    if (found) {
      for (var k = i; k < buffer.length; ++k) {
        if (buffer[k] == endChar)// note: no lowercasing for matching against '>'
          return i - chars.length;
      }
    }
  }
  return -1;
};

HttpListener.prototype.injectScripts = function injectScripts (buffer, url) {
  var p = this.findClosingTag(buffer, "head");
  if (p < 0) {
    p = this.findClosingTag(buffer, "body");
    if (p < 0) {
      // html blocks without head / body tags aren't that uncommon
      // console.log("WARNING: unable to inject script block: %s", url);
      return buffer;
    }
  }
  var newBuf = new Buffer(buffer.length + this.scriptBlock.length);
  buffer.copy(newBuf, 0, 0, p);
  this.scriptBlock.copy(newBuf, p, 0);
  buffer.copy(newBuf, p + this.scriptBlock.length, p);
  return newBuf;
};

HttpListener.prototype.proxyRequest = function proxyRequest (request, response) {
  var self = this;
  this.config.get(
    "targetUrl",
    function (targetUrl) {
      self.doProxyRequest(targetUrl, request, response);
    });
};

HttpListener.prototype.doProxyRequest = function doProxyRequest (targetUrl, request, response) {
  var self = this;
  var headersSent = false;
  var done = false;

  var hostname = DEFAULT_TARGET_HOST;
  var port = DEFAULT_TARGET_PORT;
  var parsedUrl = null;
  try {
    parsedUrl = url.parse(targetUrl);
  } catch (e) {}
  if (parsedUrl && parsedUrl.hostname) {
    hostname = parsedUrl.hostname;
    port = parsedUrl.port ? parsedUrl.port - 0 : 80;
  }

  request.headers["host"] = hostname + (port == 80 ? "" : ":" + port);
  delete request.headers["accept-encoding"]; // we don't want gzipped pages, do we?

  // note on http client error handling:
  // http://rentzsch.tumblr.com/post/664884799/node-js-handling-refused-http-client-connections
  var proxy = http.createClient(port, hostname);
  proxy.addListener(
    'error', function handleError (e) {
      console.log("proxy error: %s", e);
      if (done)
        return;
      if (headersSent) {
        response.end();
        return;
      }
      response.writeHead(502, {'Content-Type': 'text/plain; charset=utf-8'});
      response.end("swank-js: unable to forward the request");
  });

  console.log("PROXY: %s %s", request.method, request.url);
  var proxyRequest = proxy.request(request.method, request.url, request.headers);

  proxyRequest.addListener(
    'response', function (proxyResponse) {
      var contentType = proxyResponse.headers["content-type"];
      var statusCode = proxyResponse.statusCode;
      console.log("==> status %s", statusCode);
      var headers = {};
      for (k in proxyResponse.headers) {
        if (proxyResponse.headers.hasOwnProperty(k))
          headers[k] = proxyResponse.headers[k];
      }
      var chunks = proxyResponse.statusCode == 200 && contentType && /^text\/html\b|^application\/xhtml\+xml/.test(contentType) ?
        [] : null;
      if (chunks === null) {
        // FIXME: without this, there were problems with redirects.
        // I don't quite understand why...
        response.writeHead(statusCode, headers);
        headersSent = true;
      }
      proxyResponse.addListener(
        'data', function (chunk) {
          if (chunks !== null) {
            chunks.push(chunk);
            return;
          }
          if (!headersSent) {
            response.writeHead(statusCode, headers);
            headersSent = true;
          }
          response.write(chunk, 'binary');
        });
      proxyResponse.addListener(
        'end', function() {
          if (chunks !== null) {
            console.log("^^MOD: %s %s", request.method, request.url);
            var buf = new Buffer(chunks.reduce(function (s, chunk) { return s += chunk.length; }, 0));
            var p = 0;
            chunks.forEach(
              function (chunk) {
                chunk.copy(buf, p, 0);
                p += chunk.length;
              });
            buf = self.injectScripts(buf, request.url);
            headers["content-length"] = buf.length;
            response.writeHead(statusCode, headers);
            headersSent = true;
            response.write(buf, 'binary');
          } else if (!headersSent) {
            response.writeHead(statusCode, headers);
            headersSent = true;
          }

          response.end();
          done = true;
        });
    });
  request.addListener(
    'data', function(chunk) {
      proxyRequest.write(chunk, 'binary');
    });
  request.addListener(
    'end', function() {
      proxyRequest.end();
    });
};

HttpListener.prototype.sendCachedFile = function sendCachedFile (req, res, path) {
  if (req.headers['if-none-match'] == this.clientVersion) {
    res.writeHead(304);
    res.end();
  } else {
    res.writeHead(200, this.cachedFiles[path].headers);
    res.end(this.cachedFiles[path].content, this.cachedFiles[path].encoding);
  }
};

HttpListener.prototype.notFound = function notFound (res) {
  res.writeHead(404, {'Content-Type': 'text/plain; charset=utf-8'});
  res.end("file not found");
};

HttpListener.prototype.serveClient = function serveClient(req, res) {
  var self = this;
  var path = url.parse(req.url).pathname, parts, cn;
  // console.log("%s %s", req.method, req.url);
  if (path && path.indexOf("/swank-js/") != 0) {
    // console.log("--> proxy");
    this.proxyRequest(req, res);
    return;
  }
  var file = path.substr(1).split('/').slice(1);
  var localPath = this.clientFiles[file];
  if (req.method == 'GET' && localPath !== undefined) {
    // TBD: reenable caching, check datetime of the file
    // if (path in this.cachedFiles){
    //   this.sendCachedFile(req, res, path);
    //   return;
    // }

    fs.readFile(
      __dirname + '/' + localPath, function(err, data) {
        if (err) {
          console.log("error: %s", err);
          self.notFound(res);
        } else {
          var ext = localPath.split('.').pop();
          self.cachedFiles[localPath] = {
            headers: {
              'Content-Length': data.length,
              'Content-Type': self.types[ext],
              'ETag': self.clientVersion
            },
            content: data,
            encoding: ext == 'swf' ? 'binary' : 'utf8'
          };
          self.sendCachedFile(req, res, localPath);
        }
      });
  } else {
    console.log("bad request for /swank-js/ path");
    this.notFound(res);
  }
};

var httpListener = new HttpListener(cfg);
var httpServer = http.createServer(httpListener.serveClient.bind(httpListener));

httpServer.listen(8009);
io = io.listen(httpServer);

io.sockets.on(
  "connection", function (client) {
    // new client is here!
    console.log("client connected");
    function handleHandshake (message) {
      message = JSON.parse(message);
      client.removeListener("message", handleHandshake);
      if (!message.hasOwnProperty("op") || message.op != "handshake")
        console.warn("WARNING: skipping pre-handshake message: %j", message);
      else {
        var address = null;
        if (client.connection && client.connection.remoteAddress)
          address = client.connection.remoteAddress || "noaddress";
        var remote = new BrowserRemote({ address: address, userAgent: message.userAgent || "" }, client);
        executive.attachRemote(remote);
        console.log("added remote: %s", remote.fullName());
      }
    };
    client.on("message", handleHandshake);
  });

// TBD: handle reader errors

// function location determination:
// for code loaded from scripts: direct (if possible)
// for 'compiled' code: load the code by adding <script> tag loaded from the swank-js' webserver, its name should encode the real path and line offset
// for code entered via REPL: none
// PREPROCESS STACK TRACES!!!
// https://github.com/emwendelin/Javascript-Stacktrace
// ALSO: http://blog.yoursway.com/2009/07/3-painful-ways-to-obtain-stack-trace-in.html -- onerror in ie gives the innermost frame
// it should be also possible to 'soft-trace' functions so that they extend Exception objects with caller info as it passes through them
// TBD: unix domain sockets, normal slime startup
// TBD: http request logging (for specific remote)
// TBD: sudden disconnections (flashsocket), sometimes after lots of output (?) --
// Error: You are trying to call recursively into the Flash Player which is not allowed. In most cases the JavaScript setTimeout function, can be used as a workaround.
// TBD: autoreconnect + connection error handling
// ALSO: are htmlfile, jsonp-polling modes etc supposed to disconnect after each message?
// TBD: add SwankJS scripts to all passing html pages (into <head> or <body>)
// TBD: it should be possible to serve local files instead of proxying
// (maybe using https://github.com/felixge/node-paperboy )
// TBD: handle edge case: new sticky remote connects, old sticky remote disconnects
// (late disconnect) - as of now, swank-js switches to node.js, but it should
// instead upon remote detachment see whether another remote with the same name
// is available
// TBD: handle/add X-Forwarded-For headers
// TBD: fix all assert calls: we need (actual, expected) not (expected, actual)
// TBD: invoke SwankJS.setup() only when DOM is ready (at least in IE)
// TBD: timeouts for browser requests
