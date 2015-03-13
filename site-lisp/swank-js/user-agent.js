// -*- mode: js2; js-run: "user-agent-tests.js" -*-
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

var RX_TABLE = [
    [ /^.*(Firefox|Chrome|chromeframe|Conkeror|SeaMonkey)\/(\d+\.\d+).*$/, "$1 $2"],
    [ /^.*Firefox.*$/, "Firefox" ],
    [ /^.*Opera.*Version\/(\d+\.\d+).*$/, "Opera $1" ],
    [ /^.*Opera[/ ](\d+\.\d+).*$/, "Opera $1" ],
    [ /^.*Android (\d+\.\d+).*$/, "Android $1" ],
    [ /^.*iPhone;.*OS (\d+(?:_\d+)*).*$/, "iPhone $1" ],
    [ /^.*iPad;.*OS (\d+(?:_\d+)*).*$/, "iPad $1" ],
    [ /^.*iPod;.*$/, "iPod" ],
    [ /^.*Version\/(\d+\.\d+).*Safari.*$/, "Safari $1" ],
    [ /^.*Qt\/(\d+\.\d+).*$/, "QtWeb $1" ],
    [ /^.*WebKit.*$/, "WebKit" ],
    [ /^.*Gecko.*$/, "Gecko" ],
    [ /^.*MSIE (\d+\.\d+).*$/, "MSIE $1" ]
];

exports.recognize = function recognize (name) {
  // console.log("name=%s", name);
  for (var i = 0; i < RX_TABLE.length; ++i) {
    var r = name.replace(RX_TABLE[i][0], RX_TABLE[i][1]);
    // console.log("m=%s r=%s", RX_TABLE[i][0], r);
    if (r != name)
      return r.replace(/chromeframe/, "ChromeFrame").replace(/_/g, ".");
  }
  return "unknown";
};
