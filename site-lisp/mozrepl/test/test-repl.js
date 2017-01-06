var expect = require("chai").expect;

require('mozfee/node_modules/coffee-script');
var Mozrepl = require('mozfee/lib/mozrepl').Mozrepl;

var jpm_utils = require("jpm/lib/utils");
var jpm_run = require("jpm/lib/run");

var path = require("path");

var mozrepl;

var static = require('node-static');

var file = new static.Server("./test/fixtures/");

require('http').createServer(function (request, response) {
    request.addListener('end', function () {
        file.serve(request, response);
    }).resume();
}).listen(8080);

var getManifest = jpm_utils.getManifest();
getManifest.then(function(manifest) {
  jpm_run(manifest, {
    verbose: process.env.VERBOSE,
    prefs: "./test/fixtures/test-prefs.json",
    binary: process.env.FIREFOX_BIN || "/usr/bin/firefox"
  });
});

beforeEach(function(done) {
  this.timeout(20000);

  mozrepl = new Mozrepl();

  var retries = 3;
  var retry_interval = 2000;

  function retry() {
    mozrepl.connect();
  }

  mozrepl.on("connect", function() {
    mozrepl.eval("content.location = 'http://localhost:8080';", function() {
      setTimeout(done, 1500);
    });
  });
  mozrepl.on("error", function() {
    if (retries > 0) {
      console.log("RETRY");
      retries -= 1;
      setTimeout(retry, retry_interval);
    } else {
      throw Error("Error connecting to mozrepl");
    }
  });

  retry();
});

afterEach(function () {
  mozrepl.close();
});

describe("repl API", function() {

  describe("browser privileged context", function () {
    it("should be connected", function(done) {
      mozrepl.eval("'hello' + 'world'", function (err, result) {
        expect(result).to.be.equal('"helloworld"');
        done();
      });
    });

    describe("repl.whereAmI", function() {

      it("should work correctly in a ChromeWindow", function(done) {
        mozrepl.eval(mozrepl.repl_name + ".whereAmI()", function (err, result) {
          expect(err).to.not.exist;
          expect(result.indexOf("[object ChromeWindow] - Document title: \"") == 0).to.be.true;
          done();
        });
      })
    });
  });

  describe("content privileged context", function () {
    beforeEach(function (done) {
      mozrepl.eval(mozrepl.repl_name + ".enter(content)", function (err, result) {
        expect(err).to.not.exist;
        done();
      });
    });

    it("should be working correctly in content", function(done) {
      mozrepl.eval("'hello' + 'world'", function (err, result) {
        expect(result).to.be.equal('"helloworld"');
        done();
      });
    });

    describe("repl.whereAmI", function() {

      it("should work correctly in a DOM Window", function(done) {
        mozrepl.eval(mozrepl.repl_name + ".whereAmI()", function (err, result) {
          expect(err).to.not.exist;
          expect(result.trim()).to.be.equal("[object Window]");
          done();
        });
      })
    });
  });
});
