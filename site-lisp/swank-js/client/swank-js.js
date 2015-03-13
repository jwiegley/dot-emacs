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

var SwankJS = {
  socket: null,
  connected: false,
  bufferedOutput: [],
  pingId: 1,
  lastMessageTime: 0,
  pingIntervalId: null,
  reconnectIntervalId: null,
  pingEnabled: true,
  evaluating: false
};

SwankJS.CONNECTION_TIMEOUT = 3000;
SwankJS.RECONNECT_ATTEMPT_INTERVAL = 2000;
SwankJS.PING_INTERVAL = 900;

// TBD: check message contents
// TBD: exception handling
// TBD: trim stack trace excluding everything starting from swankjs_evaluate line

SwankJS.debug = function debug () {
  if (!window.console)
    return;
  var debug = console.debug || console.log;
  if (!debug || typeof debug !== "function")
    return;
  var args = [];
  for (var i = 0; i < arguments.length; ++i)
    args.push(arguments[i]);
  debug.apply(console, args);
};

SwankJS.setPingEnabled = function setPingEnabled (enable) {
  enable = !!enable;
  if (this.pingEnabled == enable)
    return;
  this.pingEnabled = enable;
  if (this.pingEnabled)
    this.startPing();
  else
    this.stopPing();
};

SwankJS.makeSocketHandler = function makeSocketHandler (func) {
  var self = this;
  var socket = self.socket;
  return function socketHandler () {
    if (self.socket != socket)
      return;
    var args = [];
    for (var i = 0; i < arguments.length; ++i)
      args[i] = arguments[i];
    func.apply(self, args);
  };
};

SwankJS.url = null;

SwankJS.setupSocket = function setupSocket (url) {
  if (url)
    this.url = url;
  this.socket = io.connect(this.url, { "force new connection": true });
  var self = this;
  this.socket.on(
    "connect",
    this.makeSocketHandler(
      function() {
        if (self.reconnectIntervalId !== null) {
          clearInterval(self.reconnectIntervalId);
          self.reconnectIntervalId = null;
        }
        self.connected = true;
        self.debug("connected");
        self.socket.send(JSON.stringify({ "op": "handshake", "userAgent": navigator.userAgent }));
        if (self.bufferedOutput.length > 0) {
          for (var i = 0; i < self.bufferedOutput.length; ++i)
            self.output(self.bufferedOutput[i]);
          self.bufferedOutput = [];
        }
        self.lastMessageTime = new Date().getTime();
        self.startPing();
      }));
  this.socket.on(
    "message",
    this.makeSocketHandler(
      function swankjs_evaluate (m) {
        var props;
        m = JSON.parse(m);
        self.lastMessageTime = new Date().getTime();
        if (m.hasOwnProperty("pong"))
          return;

        if (m.hasOwnProperty("completion")) {
          try {
            var result = self.completion.complete(m.completion);
          } catch(e) {
            self.socket.send(JSON.stringify({
              "op": "result",
              "id": m.id,
              "error": "Err listing properties\n" + swank_printStackTrace({ e: e }).join("\n")}));
          }
          self.debug("properties = %s", result);
          self.socket.send(
            JSON.stringify({
              "op": "result",
              "id": m.id,
              "error": null,
              "values": result}));
          return;
        }

        self.debug("eval: %o", m);
        // JS reentrancy is possible. I've observed it when using XSLTProcessor
        self.evaluating = true;
        try {
          var r = window.eval(m.code);
        } catch (e) {
          var message = String(e);
          if (message == "[object Error]") {
            try {
              message = "ERROR: " + e.message;
            } catch(e1) {}
          }
          self.debug("error = %s", message);
          self.socket.send(
            JSON.stringify(
              { "op": "result",
                "id": m.id,
                "error": message + "\n" + swank_printStackTrace({ e: e }).join("\n")
              }
            )
          );
          return;
        } finally {
          // don't let the connection break due to missed pings when evaluation takes too long
          self.lastMessageTime = new Date().getTime();
          self.evaluating = false;
        }
        self.debug("result = %s", String(r));
        self.socket.send(
          JSON.stringify(
            { "op": "result",
              "id": m.id,
              "error": null,
              "values": [String(r)]
            }
          )
        );
      }));
  this.socket.on(
    "disconnect",
    this.makeSocketHandler(
      function() {
        self.debug("disconnected");
        self.connected = false;
      }));
};

SwankJS.setup = function setup (url) {
  try {
    if (parent.window && parent.window.document !== document && parent.window.SwankJS)
      return;
  } catch (e) {}
  // TBD: swank-js should proxy all requests to autoadd its scripts
  // (this way, the dynamic script loading stuff isn't necessary)
  // and to make flashsocket swf load from the same url as the
  // web app itself.
  // Don't forget about 'Host: ' header though!
  this.lastMessageTime = new Date().getTime();
  this.completion = new Completion();
  this.setupSocket(url);
};

SwankJS.startPing = function startPing () {
  var self = this;
  if (this.pingIntervalId === null && this.pingEnabled && this.connected)
    this.pingIntervalId = setInterval(
      function () {
        self.ping();
      }, this.PING_INTERVAL);
};

SwankJS.stopPing = function stopPing () {
  if (this.pingIntervalId !== null) {
    clearInterval(this.pingIntervalId);
    this.pingIntervalId = null;
  }
};

SwankJS.ping = function ping () {
  if (!this.pingEnabled) {
    this.stopPing();
    return;
  }

  if (this.evaluating)
    return;

  var self = this;
  if (new Date().getTime() > this.lastMessageTime + this.CONNECTION_TIMEOUT) {
    this.debug("ping timeout");
    if (this.pingIntervalId !== null) {
      this.stopPing();
      this.reconnectIntervalId = setInterval(
        function () {
          self.reconnect();
        }, this.RECONNECT_ATTEMPT_INTERVAL);
    }
  } else if (this.connected) {
    this.socket.send(
      JSON.stringify({ "op": "ping", "id": this.pingId++ })
    );
  }
};

SwankJS.reconnect = function reconnect () {
  this.debug("reconnecting");
  if (this.socket) {
    try {
      this.socket.disconnect();
    } catch (e) {}
    this.socket = null;
  }
  this.setupSocket();
};

// useful functions for the REPL / web apps

SwankJS.output = function output (str) {
  if (this.socket && this.connected)
    this.socket.send(JSON.stringify({ "op": "output", "str": str }));
  else
    this.bufferedOutput.push(str);
};

SwankJS.reload = function reload () {
  document.location.reload(true);
};

SwankJS.refreshCSS = function refreshCSS (filename) {
  SwankJS.output("refreshing css: " + (filename || "<all>") + "\n");
  var links = document.getElementsByTagName('link');
  for (var i = 0; i < links.length; i++) {
    var link = links[i];
    if (link.rel.toLowerCase().indexOf('stylesheet') == -1 || !link.href) continue;
    var h = link.href.replace(/(&|\?)forceReload=\d+/, ""),
        hrefFilename = h.replace(/^.*\//g, "");
    if (filename && hrefFilename != filename) continue;
    link.href = h + (h.indexOf('?') >= 0 ? '&' : '?') + 'forceReload=' +
      (Date.now ? Date.now() : +new Date());
    if (filename) return;
  }
  if (filename) {
    SwankJS.output("WARNING: <link> not found: " + filename + "\n");
  }
};

SwankJS.cssElementId = 'swank-js-css';
SwankJS.embedCSS = function embedCSS(cssString) {
  var el = document.getElementById(this.cssElementId);
  if (!el) {
    el = document.createElement('style');
    el.setAttribute('type', 'text/css');
    el.setAttribute('id', this.cssElementId);
    document.getElementsByTagName('head')[0].appendChild(el);
  } else {
    el.textContent += '\n';
  }
  el.textContent += cssString;
};

SwankJS.removeEmbeddedCSS = function removeEmbeddedCSS() {
  var el = document.getElementById(this.cssElementId);
  el && el.parentNode && el.parentNode.removeChild(el);
};

SwankJS.disconnect = function disconnect () {
  // used by bookmarklets
  this.socket.disconnect();
  this.stopPing();
  if (this.reconnectIntervalId !== null) {
    clearInterval(this.reconnectIntervalId);
    this.reconnectIntervalId = null;
  }
};

/*
// we may need this later

SwankJS.makeScriptElement = function makeScriptElement (src, content) {
  var script = document.createElement("script");
  script.type = "text/javascript";
  if (src)
    script.src = src;
  else {
    var text = document.createTextNode(content);
    script.appendChild(text);
  }
  return script;
};
*/

// TBD: look at document.location.href, if it's not localhost,
// don't do setup, otherwise do it on DOM load (see how prototypejs etc does it)