// -*- mode: js2; js-run: "swank-protocol-tests.js" -*-
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

var readFromString = require("./lisp").readFromString;

const HEADER_LEN = 6;
const DUMMY_HEADER = "000000";
const MAX_MESSAGE_SIZE = 10 * 1024 * 1024;

function SwankParser (onMessage) {
  this.onMessage = onMessage;
  this.resetBuffer();
};

// FIXME: proper error handling (handle both packet parsing and reader errors)

SwankParser.prototype.resetBuffer = function resetBuffer (len, handler) {
  len = len || HEADER_LEN;
  this.needChars = len;
  this.handleData = handler || this.handleHeader;
  this.stash = new Buffer(len);
  this.pos = 0;
};

SwankParser.prototype.execute = function execute (buffer) {
  var offset = 0;
  while (offset < buffer.length)
    offset += this.handleContent(buffer, offset);
};

SwankParser.prototype.handleContent = function handleContent (buffer, offset) {
  var newPos = Math.min(this.needChars, this.pos + buffer.length - offset);
  var bytesToCopy = newPos - this.pos;
  buffer.copy(this.stash, this.pos, offset, offset + bytesToCopy);
  this.pos = newPos;
  if (this.pos == this.needChars)
    this.handleData();
  return bytesToCopy; // stashLen + newPos - stashLen
};

SwankParser.prototype.handleHeader = function handleHeader () {
  var count = parseInt(this.stash.toString(), 16) || 0;
  if (count > 0 && count < MAX_MESSAGE_SIZE)
    this.resetBuffer(count, this.handleMessage);
  else
    this.resetBuffer();
};

SwankParser.prototype.handleMessage = function handleMessage (str) {
  this.onMessage(readFromString(this.stash.toString())); // FIXME: handle errors
  this.resetBuffer();
};

function buildMessage (obj) {
  var str = obj.toString();
  var lenStr = "" + Buffer.byteLength(str).toString(16);
  while (lenStr.length < HEADER_LEN)
    lenStr = "0" + lenStr;
  return lenStr + str;
};

exports.SwankParser = SwankParser;
exports.buildMessage = buildMessage;
