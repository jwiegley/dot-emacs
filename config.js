// -*- mode: js2 -*-
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

var path = require("path"), fs = require("fs");

function Config (fileName) {
  this.fileName = fileName;
  if (/^~\//.test(this.fileName))
    this.fileName = path.join(process.env.HOME || "/", this.fileName.substring(2));
  this.config = null;
}

Config.prototype.loadConfig = function loadConfig (cont) {
  var self = this;
  if (!this.config) {
    fs.readFile(
      self.fileName, "utf-8", function (err, data) {
        self.config = {};
        if (!err) {
          try {
            self.config = JSON.parse(data);
          } catch (e) {}
        }
        cont(self.config);
      });
  } else
    cont(this.config);
};

Config.prototype.saveConfig = function saveConfig (cont) {
  if (!this.config)
    return;
  var self = this;
  fs.writeFile(
    this.fileName, JSON.stringify(this.config), "utf8",
    function (err) {
      if (err)
        console.warn("error writing config file %s: %s", self.fileName, err);
      cont();
    });
};

Config.prototype.get = function get (name, cont) {
  this.loadConfig(
    function (cfg) {
      cont(cfg.hasOwnProperty(name) ? cfg[name] : undefined);
    });
};

Config.prototype.set = function set (name, value, cont) {
  var self = this;
  cont = cont || function () {};
  this.loadConfig(
    function (cfg) {
      cfg[name] = value;
      self.saveConfig(cont);
    });
};

function FakeConfig (values) {
  this.config = values || {};
}

FakeConfig.prototype.getNow = function getNow (name) {
  return this.config.hasOwnProperty(name) ? this.config[name] : undefined;
};

FakeConfig.prototype.get = function get (name, cont) {
  cont(this.config.hasOwnProperty(name) ? this.config[name] : undefined);
};

FakeConfig.prototype.set = function set (name, value, cont) {
  this.config[name] = value;
  if (cont) cont();
};

exports.Config = Config;
exports.FakeConfig = FakeConfig;
