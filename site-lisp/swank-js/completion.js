// -*- mode: js2; js-run: "completion-tests.js" -*-
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

// some ideas from WebKit inspector
// http://trac.webkit.org/browser/trunk/Source/WebCore/inspector/front-end/ConsoleView.js?rev=104822#L354

function Completion (options) {
  // http://stackoverflow.com/questions/3277182/how-to-get-the-global-object-in-javascript
  this.options = options || {};
  this.global = this.options.hasOwnProperty("global") ? options.global :
    Function('return this')();
  this.evaluate = this.options.hasOwnProperty("evaluate") ? options.evaluate : null;
};

Completion.prototype.enumerate = function enumerate (obj, func) {
  for (var name in obj)
    func(name);
};

if (Object.getOwnPropertyNames && ({}).__proto__) {
  Completion.prototype.getAllProperties = function getAllProperties (obj, func) {
    for (; obj; obj = obj.__proto__)
      Object.getOwnPropertyNames(obj).forEach(func);
  };
} else {
  Completion.prototype.getAllProperties = Completion.prototype.enumerate;
}

Completion.prototype.dotCompletion = function dotCompletion (str, regex, skipPrefix) {
  var getProps = this.options.hasOwnProperty("enumerablePropsOnly") &&
    this.options.enumerablePropsOnly ? this.enumerate.bind(this) :
    this.getAllProperties.bind(this);
  var addPrefix = skipPrefix ? "" : str + ".";
  var obj;
  try {
    obj = str === null ? this.global : this.evaluate ? this.evaluate(str) : this.global.eval(str);
  } catch (e) {
    console.log("completion eval error: %s", e);
    obj = null;
  }
  if (!obj)
    return [];
  var r = [];
  getProps(
    obj, function (name) {
      if (regex) {
        if (name.match(regex))
          r.push(addPrefix + name);
      } else {
        r.push(addPrefix + name);
      }
    });

  return r;
};

Completion.prototype.nameCompletion = function nameCompletion(str) {
  var dotIndex = str.lastIndexOf(".");
  var parent = dotIndex >= 0 ? str.substring(0, dotIndex) : null;
  var strToComplete = str.substring(dotIndex + 1, str.length);
  // console.log("dotIndex %s, strToComplete %s", dotIndex, strToComplete);
  return this.dotCompletion(parent, new RegExp("^" + strToComplete), dotIndex < 0);
};

Completion.prototype.doCompletion = function doCompletion (str) {
  var end_idx = str.length - 1;
  return (str[end_idx] == ".") ? this.dotCompletion(str.substring(0, end_idx)) : this.nameCompletion(str);
};

Completion.prototype.complete = function complete (prefix) {
  var values = this.doCompletion(prefix);
  values.sort();
  var partial = values.length ? values[0] : prefix;
  if (values.length > 1) {
    var last = values[values.length - 1], n = last.length;
    while (partial && last.indexOf(partial) < 0)
      partial = partial.substring(0, --n);
  }
  return { values: values, partial: partial };
};

exports.Completion = Completion;
