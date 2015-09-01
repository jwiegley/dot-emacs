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

var assert = require("assert");
var useragent = require("./user-agent");

// for reference: http://www.pgts.com.au/cgi-bin/psql?agent_main
var USER_AGENT_TESTS = [
  [ "Firefox 0.9",     "Mozilla/5.0 (Windows; U; Windows NT 5.1; en-US; rv:1.7) Gecko/20040707 Firefox/0.9.2 StumbleUpon/1.998" ],
  [ "Firefox 1.5",     "Mozilla/5.0 (Windows NT 5.1; U; SV1; MEGAUPLOAD 1.0; ru; rv:1.8.0) Gecko/20060728 Firefox/1.5.0 Opera 9.23" ],
  [ "Firefox 2.0",     "Mozilla/5.0 (X11; U; Linux i686; en-US; rv:1.8.1.13) Gecko/20081108 Firefox/2.0.0.13" ],
  [ "Firefox 3.6",     "Mozilla/5.0 (Windows; U; Windows NT 5.1; ru; rv:1.9.2.3) Gecko/20100401 Firefox/3.6.3" ],
  [ "Firefox 3.5",     "Mozilla/5.0 (Windows; U; Windows NT 5.1; ru; rv:1.9.1.5) Gecko/20091102 Firefox/3.5.5" ],
  [ "Firefox 3.0",     "Mozilla/5.0 (Windows; U; Windows NT 5.1; ru; rv:1.9.0.6) Gecko/2009011913 Firefox/3.0.6" ],
  [ "Firefox 4.0",     "Mozilla/5.0 (Windows NT 5.1; rv:2.0b6) Gecko/20100101 Firefox/4.0b6" ],
  [ "Firefox",         "Mozilla/5.0 (Windows; U; Windows NT 5.1; ru; ToolKit; rv:1.9.0.8) Gecko/2009032609 Firefox MRA 5.5 (build 02842);" ],
  [ "Opera 11.00",     "Opera/9.80 (Windows NT 6.1; U; en) Presto/2.6.37 Version/11.00" ],
  [ "Opera 10.62",     "Opera/9.80 (Windows NT 5.1; U; ru) Presto/2.6.30 Version/10.62" ],
  [ "Opera 9.50",      "Opera/9.50 (Windows NT 6.0; U; MRA 5.5 (build 02842); ru)" ],
  [ "Opera 8.01",      "Opera/8.01 (J2ME/MIDP; Opera Mini/3.1.9427/1724; ru; U; ssr)" ],
  [ "Opera 7.0",       "Mozilla/4.0 (compatible; MSIE 6.0; MSIE 5.5; Windows NT 4.0) Opera 7.0 [en]" ],
  [ "Opera 6.0",       "Mozilla/4.0 (compatible; MSIE 5.0; Windows 2000) Opera 6.0 [en]" ],
  [ "Opera 5.11",      "Mozilla/4.0 (compatible; MSIE 5.0; Windows ME) Opera 5.11 [en]" ],
  [ "Chrome 6.0",      "Mozilla/5.0 (Windows; U; Windows NT 5.1; en-US) AppleWebKit/534.3 (KHTML, like Gecko) Chrome/6.0.472.63 Safari/534.3" ],
  [ "ChromeFrame 6.0", "Mozilla/4.0 (compatible; MSIE 8.0; Windows NT 6.1; Trident/4.0; SLCC2; .NET CLR 2.0.50727; .NET CLR 3.5.30729; .NET CLR 3.0.30729; Media Center PC 6.0) chromeframe/6.0.472.63" ],
  [ "Safari 4.0",      "Mozilla/5.0 (Macintosh; U; Intel Mac OS X 10_6_2; ru-ru) AppleWebKit/531.21.8 (KHTML, like Gecko) Version/4.0.4 Safari/531.21.10" ],
  [ "iPhone 3.1.3",    "Mozilla/5.0 (iPhone; U; CPU iPhone OS 3_1_3 like Mac OS X; en-us) AppleWebKit/528.18 (KHTML, like Gecko) Mobile/7E18" ],
  [ "iPad 3.2.2",      "Mozilla/5.0 (iPad; U; CPU OS 3_2_2 like Mac OS X; ru-ru) AppleWebKit/531.21.10 (KHTML, like Gecko) Version/4.0.4 Mobile/7B500 Safari/531.21.10" ],
  [ "iPod",            "Mozilla/5.0 (iPod; U; CPU like Mac OS X; en) AppleWebKit/420.1 (KHTML, like Gecko) Version/3.0 Mobile/3A101a Safari/419.3" ],
  [ "QtWeb 4.7",       "Mozilla/5.0 (X11; U; Linux x86_64; C) AppleWebKit/533.3 (KHTML, like Gecko) Qt/4.7.0 Safari/533.3" ],
  [ "WebKit",          "Mozilla/5.0 (X11; U; Linux x86_64; C) AppleWebKit/533.3 (KHTML, like Gecko) Safari/533.3" ], // made up
  [ "WebKit",          "Mozilla/5.0 (X11; U; Linux x86_64; C) AppleWebKit/533.3 (KHTML, like Gecko)" ], // made up
  [ "WebKit",          "Midori/0.2 (X11; Linux; U; en-us) WebKit/531.2+" ],
  [ "Conkeror 0.9",    "Mozilla/5.0 (X11; U; Linux x86_64; en-US; rv:1.9.2.10) Gecko/20100915 Conkeror/0.9.2" ],
  [ "Gecko",           "Mozilla/5.0 (X11; U; Linux i686; en-US; rv:1.4b) Gecko/20030516 Mozilla Firebird/0.6" ],
  [ "SeaMonkey 2.0",   "Mozilla/5.0 (X11; U; Linux i686; en-US; rv:1.9.1.4) Gecko/20091028 SeaMonkey/2.0" ],
  [ "Android 2.2",     "Mozilla/5.0 (Linux; U; Android 2.2; en-us; Droid Build/FRG22D) AppleWebKit/533.1 (KHTML, like Gecko) Version/4.0 Mobile Safari/533.1"],
  [ "Android 1.6",     "Mozilla/5.0 (Linux; U; Android 1.6; en-us; T-Mobile G1 Build/DMD64) AppleWebKit/528.5+ (KHTML, like Gecko) Version/3.1.2 Mobile Safari/525.20.1"],
  [ "MSIE 9.0",        "Mozilla/5.0 (compatible; MSIE 9.0; Windows NT 6.1; Trident/5.0)" ],
  [ "MSIE 8.0",        "Mozilla/4.0 (compatible; MSIE 8.0; Windows NT 5.1; Trident/4.0; GTB5; MRSPUTNIK 2, 3, 0, 104; MRA 5.6 (build 03392); .NET CLR 2.0.50727; .NET CLR 3.0.04506.648; .NET CLR 3.5.21022; .NET CLR 3.0.4506.2152; .NET CLR 3.5.30729)" ],
  [ "MSIE 7.0",        "Mozilla/4.0 (compatible; MSIE 7.0; Windows NT 5.1; InfoPath.2; .NET CLR 2.0.50727; .NET CLR 3.0.4506.2152; .NET CLR 3.5.30729)" ],
  [ "MSIE 6.0",        "Mozilla/4.0 (compatible; MSIE 6.0; Windows NT 5.1; SV1; InfoPath.2; .NET CLR 2.0.50727)" ],
  [ "MSIE 5.01",       "Mozilla/4.0 (compatible; MSIE 5.01; Windows NT 5.0)" ],
  [ "MSIE 5.5",        "Mozilla/4.0 (compatible; MSIE 5.5; Windows 98)" ],
  [ "MSIE 4.01",       "Mozilla/4.0 (compatible; MSIE 4.01; Windows 95)" ],
  [ "MSIE 4.01",       "Mozilla/4.0 (compatible; MSIE 4.01; Digital AlphaServer 1000A 4/233; Windows NT; Powered By 64-Bit Alpha Processor)" ],
  [ "MSIE 3.0",        "Mozilla/2.0 (compatible; MSIE 3.0B; Windows NT)" ],
  [ "MSIE 3.0",        "Mozilla/2.0 (compatible; MSIE 3.0B; Windows NT)" ],
  [ "MSIE 3.02",       "Mozilla/2.0 (compatible; MSIE 3.02; Windows CE; 240x320)" ],
  [ "MSIE 3.01",       "Mozilla/2.0 (compatible; MSIE 3.01; Windows 98)" ],
  [ "MSIE 2.0",        "Mozilla/1.22 (compatible; MSIE 2.0d; Windows NT)" ],
  [ "MSIE 1.5",        "Mozilla/1.22 (compatible; MSIE 1.5; Windows NT)" ],
  [ "MSIE 1.0",        "Mozilla/1.0 (compatible; MSIE 1.0; Windows 3.11)" ], // made up
  [ "unknown",         "don't know" ],
  [ "unknown",         "" ]
];

USER_AGENT_TESTS.forEach(
  function (item) {
    var actual = useragent.recognize(item[1]);
    assert.equal(
      item[0], actual,
      "got " + actual + " instead of " + item[0] + " for " + item[1]);
  });
