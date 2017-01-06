/*
 * Copyright 2006-2011 by Massimiliano Mirra
 *
 * This file is part of MozRepl.
 *
 * MozRepl is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by the
 * Free Software Foundation; either version 3 of the License, or (at your
 * option) any later version.
 *
 * MozRepl is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 * The interactive user interfaces in modified source and object code
 * versions of this program must display Appropriate Legal Notices, as
 * required under Section 5 of the GNU General Public License version 3.
 *
 * Author: Massimiliano Mirra, <bard [at] hyperstruct [dot] net>
 *
 */


// GLOBAL DEFINITIONS
// ----------------------------------------------------------------------

const Cc = Components.classes;
const Ci = Components.interfaces;
const loader = Cc['@mozilla.org/moz/jssubscript-loader;1']
    .getService(Ci.mozIJSSubScriptLoader);
const srvPref = Cc['@mozilla.org/preferences-service;1']
    .getService(Ci.nsIPrefService)
    .getBranch('extensions.mozrepl.');

var util = {};
loader.loadSubScript('chrome://mozrepl/content/util.js', util);

const DEBUG = false;


// CORE
// ----------------------------------------------------------------------

function onOutput() {
    throw new Error('onInput callback must be assigned.');
}

function onQuit() {
    throw new Error('onQuit callback must be assigned.');
}

function init(context) {
    var _this = this;

    this._name            = chooseName('repl', context);
    this._creationContext = context;
    this._hostContext     = context;
    this._workContext     = context;
    this._creationContext[this._name] = this;

    this._contextHistory = [];
    this._inputBuffer = '';

    this._emergencyExit = function(event) {
        _this.print('Host context unloading! Going back to creation context.')
        _this.home();
    }

    this.__defineGetter__(
        'repl', function() {
            return this;
        });

    this._env = {};
    this._savedEnv = {};

    this.setenv('printPrompt', true);
    this.setenv('inputMode', 'syntax');

    this._interactorClasses = {};
    this._interactorStack = [];

    this.defineInteractor('javascript', javascriptInteractor);
    this.loadInit();

    var defaultInteractorClass = (this._interactorClasses[srvPref.getCharPref('defaultInteractor')] ||
                                  this._interactorClasses['javascript']);
    var defaultInteractor = new defaultInteractorClass(this);

    this._interactorStack = [defaultInteractor];
    defaultInteractor.onStart(this);
}


// ENVIRONMENT HANDLING
// ----------------------------------------------------------------------

function setenv(name, value) {
    this._env[name] = value;
    return value;
}
setenv.doc =
    'Takes a name and a value and stores them so that \
they can be later retrieved via setenv(). Some, such as \
"printPrompt"/boolean, affect there way the REPL works.';


function getenv(name) {
    return this._env[name];
}
getenv.doc =
    'Given a name, returns a value previously stored via \
setenv().';


function pushenv() {
    var name;
    for(var i=0, l=arguments.length; i<l; i++) {
        name = arguments[i];
        this._savedEnv[name] = this._env[name];
    }
}
pushenv.doc =
    'Takes one or more names of values previously stored \
via setenv(), and stores them so that they can be later \
restored via popenv().';


function popenv() {
    var name;
    for(var i=0, l=arguments.length; i<l; i++) {
        name = arguments[i];
        if(name in this._savedEnv) {
            this._env[name] = this._savedEnv[name];
            delete this._savedEnv[name];
        }
    }
}
popenv.doc =
    'Takes one or more names of values previously pushed \
via popenv() and restores them, overwriting the current ones.';


// OUTPUT
// ----------------------------------------------------------------------

function represent(thing) {
    var represent = arguments.callee;
    var s;
    switch(typeof(thing)) {
    case 'string':
        s = '"' + thing + '"';
        break;
    case 'number':
        s = thing;
        break;
    case 'object':
        var names = [];
        for(var name in thing)
            names.push(name);

        s = thing;
        if(names.length > 0) {
            s += ' - {';
            s += names.slice(0, 7).map(function(n) {
                var repr = n + ': ';
                try {
                    if(thing[n] === null)
                        repr += 'null';
                    else if(typeof(thing[n]) == 'object')
                        repr += '{...}';
                    else
                        repr += represent(thing[n]);
                } catch(e) {
                    repr += '[Exception!]'
                }
                return repr;
            }).join(', ');
            if(names.length > 7)
                s += ', ...'
            s += '}';
        }
        break;
    case 'function':
        s = 'function() {...}';
        break;
    default:
        s = thing;
    }
    return s;
}

function print(data, appendNewline) {
    var string = data == undefined ?
        '\n' :
        data + (appendNewline == false ? '' : '\n');

    this.onOutput(string);
}
print.doc =
    'Converts an object to a string and prints the string. \
Appends a newline unless false is given as second parameter.';


// SCRIPT HANDLING
// ----------------------------------------------------------------------

function loadInit() {
    try {
        var initUrl = Cc['@mozilla.org/preferences-service;1']
            .getService(Ci.nsIPrefBranch)
            .getCharPref('extensions.mozrepl.initUrl');

        if(initUrl)
            this.load(initUrl, this);

    } catch(e) {
        Components.utils.reportError('MozRepl: could not load initialization file ' + initUrl + ': ' + e);
    }
}

function load(url, arbitraryContext) {
    try {
        return loader.loadSubScript(
            url, arbitraryContext || this._workContext);
    } catch(e) {
        throw new LoadedScriptError(e);
    }
}
load.doc =
    'Loads a chrome:// or file:// script into the current context, \
or optionally into an arbitrary context passed as a second parameter.';


// CONTEXT NAVIGATION
// ----------------------------------------------------------------------

function enter(context, wrapped) {
    if (wrapped != true && context.wrappedJSObject != undefined)
      context = context.wrappedJSObject;

    this._contextHistory.push(this._workContext);

    if(isTopLevel(context))
        this._migrateTopLevel(context);
    this._workContext = context;

    return this._workContext;
}
enter.doc =
    'Makes a new context the current one.  After this, new definitions \
(variables, functions etc.) will be members of the new context. \
Remembers the previous context, so that you can get back to it with \
leave().';

function back() {
    // do sanity check to prevent re-entering stale contextes

    var context = this._contextHistory.pop();
    if(context) {
        if(isTopLevel(context))
            this._migrateTopLevel(context);
        this._workContext = context;
        return this._workContext;
    }
}
back.doc =
    "Returns to the previous context.";


function home() {
    return this.enter(this._creationContext);
}
home.doc =
    'Returns to the context where the REPL was created.';


// MISC
// ----------------------------------------------------------------------

function quit() {
    this.currentInteractor().onStop && this.currentInteractor().onStop(this);
    delete this._hostContext[this._name];
    delete this._creationContext[this._name];
    this.onQuit();
}
quit.doc =
    'Ends the session.';


function rename(name) {
    if(name in this._hostContext)
        this.print('Sorry, name already exists in the context repl is hosted in.');
    else if(name in this._creationContext)
        this.print('Sorry, name already exists in the context was created.')
    else {
        delete this._creationContext[this._name];
        delete this._hostContext[this._name];
        this._name = name;
        this._creationContext[this._name] = this;
        this._hostContext[this._name] = this;
    }
}
rename.doc =
    'Renames the session.';


// CONTEXT EXPLORING
// ----------------------------------------------------------------------

function inspect(obj, maxDepth, name, curDepth) {
// adapted from ddumpObject() at
// http://lxr.mozilla.org/mozilla/source/extensions/sroaming/resources/content/transfer/utility.js

    function crop(string, max) {
        string = string.match(/^(.+?)(\n|$)/m)[1];
        max = max || 70;
        return (string.length > max-3) ?
            string.slice(0, max-3) + '...' : string;
    }

    if(name == undefined)
        name = '<' + typeof(obj) + '>';
    if(maxDepth == undefined)
        maxDepth = 0;
    if(curDepth == undefined)
        curDepth = 0;
    if(maxDepth != undefined && curDepth > maxDepth)
        return;

    var i = 0;
    for(var prop in obj) {
        if(obj instanceof Ci.nsIDOMWindow &&
           (prop == 'java' || prop == 'sun' || prop == 'Packages')) {
            this.print(name + "." + prop + "=[not inspecting, dangerous]");
            continue;
        }

        try {
            i++;
            if(obj[prop] === null)
                this.print(name + "." + prop + '=null');
            else if(typeof(obj[prop]) == "object") {
                if(obj.length != undefined)
                    this.print(name + "." + prop + "=[probably array, length "
                               + obj.length + "]");
                else
                    this.print(name + "." + prop + "=[" + typeof(obj[prop]) + "]");

                this.inspect(obj[prop], maxDepth, name + "." + prop, curDepth+1);
            }
            else if(typeof(obj[prop]) == "function")
                this.print(name + "." + prop + "=[function]");
            else if(typeof(obj[prop]) == "xml") {
                let s = obj[prop].toXMLString().replace(/>\n\s*/g, ' ');
                this.print(name + "." + prop + "=" + (s.length > 100 ? s.slice(0, 97) + '...' : s));
            }
            else
                this.print(name + "." + prop + "=" + obj[prop]);

            if(obj[prop] && obj[prop].doc && typeof(obj[prop].doc) == 'string')
                this.print('    ' + crop(obj[prop].doc));

        } catch(e) {
            this.print(name + '.' + prop + ' - Exception while inspecting.');
        }
    }
    if(!i)
        this.print(name + " is empty");
}
inspect.doc =
    "Lists members of a given object.";


function look() {
    this.inspect(this._workContext, 0, 'this');
}
look.doc =
    "Lists objects in the current context.";


function highlight(context, time) {
    context = context || this._workContext;
    time = time || 1000;
    if(!context.QueryInterface)
        return;

    const NS_NOINTERFACE = 0x80004002;

    try {
        context.QueryInterface(Ci.nsIDOMXULElement);
        var savedBorder = context.style.border;
        context.style.border = 'thick dotted red';
        Cc['@mozilla.org/timer;1']
            .createInstance(Ci.nsITimer)
            .initWithCallback(
                {notify: function() {
                        context.style.border = savedBorder;
                    }}, time, Ci.nsITimer.TYPE_ONE_SHOT);
    } catch(e if e.result == NS_NOINTERFACE) {}
}
highlight.doc =
    "Highlights the passed context (or the current, if none given) if it is \
a XUL element.";


function whereAmI() {
    var context = this._workContext;
    var desc = '';
    desc += context;
    if(context.document && context.document.title)
        desc += ' - Document title: "' + context.document.title + '"';
    if(context.nodeName)
        desc += ' - ' + context.nodeName;
    this.print(desc);
    this.highlight();
}
whereAmI.doc =
    "Returns a string representation of the current context.";


function search(criteria, context) {
    context = context || this._workContext;

    var matcher;

    if(typeof(criteria) == 'function')
        matcher = criteria;
    else if(typeof(criteria.test) == 'function')
        matcher = function(name) { return criteria.test(name); }
    else
        matcher = function(name) { return name == criteria; }

    for(var name in context)
        if(matcher(name))
            this.print(name);
}
search.doc =
    "Searches for a member in the current context, or optionally in an \
arbitrary given as a second parameter.";


function doc(thing) {
    this.print(util.docFor(thing));

    var url = util.helpUrlFor(thing);
    if(url) {
        this.print('Online help found, displaying...');
        Cc['@mozilla.org/embedcomp/window-watcher;1']
            .getService(Ci.nsIWindowWatcher)
            .openWindow(null, url, 'help',
                        'width=640,height=600,scrollbars=yes,menubars=no,' +
                        'toolbar=no,location=no,status=no,resizable=yes', null);
    }
}
doc.doc =
    'Looks up documentation for a given object, either in the doc string \
(if present) or on XULPlanet.com.';

// COMMON CHROME ENVIRONMENT UTILITY FUNCTIONS
// ----------------------------------------------------------------------

function reloadChrome() {
    try {
      Cc["@mozilla.org/chrome/chrome-registry;1"].
        getService(Ci.nsIXULChromeRegistry).reloadChrome();
    } catch(e) { this.print('Exception while reloading chrome: '+e); }
}
reloadChrome.doc = "Reload all chrome packages";

function setDebugPrefs(enabled) {
    try {
      var dbgPrefs = ["nglayout.debug.disable_xul_cache",
      	              "javascript.options.showInConsole",
                      "browser.dom.window.dump.enabled"];

      var prefs = Cc["@mozilla.org/preferences-service;1"]
          .getService(Ci.nsIPrefBranch);

      for each (let pname in dbgPrefs) {
          prefs.setBoolPref(pname, enabled);
      }
    } catch(e) { this.print('Exception while setting debugging preferences: '+e); }
}
setDebugPrefs.doc = "Enable/Disable common debugging preferences";

// INTERACTOR HANDLING
// ----------------------------------------------------------------------

function defineInteractor(name, proto) {
    this._interactorClasses[name] = function() {}
    this._interactorClasses[name].prototype = proto;
}
defineInteractor.doc = 'Defines a new interactor.';

function currentInteractor() {
    return this._interactorStack[this._interactorStack.length-1];
}

function popInteractor() {
    if(this._interactorStack.length == 1)
        throw new Error('Cannot leave last interactor.');
    this.currentInteractor().onStop && this.currentInteractor().onStop(this);
    this._interactorStack.pop();
    this.currentInteractor().onResume && this.currentInteractor().onResume(this);
}

function pushInteractor(interactorName) {
    var interactorClass = this._interactorClasses[interactorName];
    if(typeof(interactorClass) == 'undefined')
        throw new Error('Interactor <' + interactorName + '> not defined.');
    else {
        this.currentInteractor().onSuspend && this.currentInteractor().onSuspend(this);

        var newInteractor = new interactorClass(this);
        this._interactorStack.push(newInteractor);
        newInteractor.onStart(this);
    }
}
pushInteractor.__defineGetter__('doc', function() {
    var intNames = [];
    for(var intName in this._interactorClasses)
        intNames.push(intName);
    return 'Sets the current interactor. (Currently defined: "' + intNames.join('", "') + '")';
});


// JAVASCRIPT INTERACTOR
// ----------------------------------------------------------------------

var javascriptInteractor = {
    onStart: function(repl) {
        debug('start');

        Cc['@mozilla.org/observer-service;1']
            .getService(Ci.nsIObserverService)
            .notifyObservers(null, "startupcache-invalidate", null);

        this._inputBuffer = '';

        if(srvPref.getBoolPref('interactor.javascript.printWelcome')) {
            repl.print('');
            repl.print('Welcome to MozRepl.');
            repl.print('');
            repl.print(' - If you get stuck at the "...>" prompt, enter a semicolon (;) at the beginning of the line to force evaluation.');
            repl.print(' - If you get errors after every character you type, see http://github.com/bard/mozrepl/wikis/troubleshooting (short version: stop using Microsoft telnet, use netcat or putty instead)');
            repl.print('');
            repl.print('Current working context: ' + (repl._workContext instanceof Ci.nsIDOMWindow ?
                                                      repl._workContext.document.location.href :
                                                      repl._workContext));
            repl.print('Current input mode: ' + repl._env['inputMode']);

            repl.print('');
        }

        if(repl._name != 'repl') {
            repl.print('Hmmm, seems like other repl\'s are running in repl context.');
            repl.print('To avoid conflicts, yours will be named "' + repl._name + '".');
        }

        repl._prompt();
    },

    onStop: function(repl) {},

    onSuspend: function(repl) {},

    onResume: function(repl) {},

    getPrompt: function(repl) {
        return repl._name + '> ';
    },

    handleInput: function(repl, input) {
        debug('input', input);

        if(input.match(/^\s*$/) && this._inputBuffer.match(/^\s*$/)) {
            repl._prompt();
            return;
        }

        const inputSeparators = {
            line:      /\n/m,
            multiline: /\n--end-remote-input\n/m,
        };

        function handleError(e) {
            var realException = (e instanceof LoadedScriptError ? e.cause : e);

            repl.print('!!! ' + realException + '\n');
            if(realException) {
                repl.print('Details:')
                repl.print();
                for(var name in realException) {
                    var content = String(realException[name]);
                    if(content.indexOf('\n') != -1)
                        content = '\n' + content.replace(/^(?!$)/gm, '    ');
                    else
                        content = ' ' + content;

                    repl.print('  ' + name + ':' + content.replace(/\s*\n$/m, ''));
                }
                repl.print();
            }

            repl._prompt();
        }

        switch(repl.getenv('inputMode')) {
        case 'line':
        case 'multiline':
            this._inputBuffer += input;
            var [chunk, rest] = scan(this._inputBuffer, inputSeparators[repl.getenv('inputMode')]);
            while(chunk) {
                try {
                    var result = repl.evaluate(chunk);
                    if(this != undefined)
                        repl.print(repl.represent(result));
                    repl._prompt();
                } catch(e) {
                    handleError(e);
                }

                [chunk, rest] = scan(rest, inputSeparators[repl.getenv('inputMode')]);
            }
            this._inputBuffer = rest;
            break;

        case 'syntax':
            if(/^\s*;\s*$/.test(input)) {
                try {
                    var result = repl.evaluate(this._inputBuffer);
                    if(result != undefined)
                        repl.print(repl.represent(result));
                    repl._prompt();
                } catch(e) {
                    handleError(e);
                }

                this._inputBuffer = '';
            } else {
                this._inputBuffer += input;
                try {
                    var result = repl.evaluate(this._inputBuffer);
                    if(result != undefined)
                        repl.print(repl.represent(result));
                    repl._prompt();
                    this._inputBuffer = '';
                } catch(e if e.name == 'SyntaxError') {
                    // ignore and keep filling the buffer
                    repl._prompt(repl._name.replace(/./g, '.') + '> ');
                } catch(e) {
                    handleError(e);
                    this._inputBuffer = '';
                }
            }
        }
    }
};

// INTERNALS
// ----------------------------------------------------------------------

function _migrateTopLevel(context) {
    if(this._hostContext instanceof Ci.nsIDOMWindow)
        this._hostContext.removeEventListener('unload', this._emergencyExit, false);

    this._hostContext[this._name] = undefined;

    this._hostContext = context;

    // build the repl exposed api from the calculated exposed props (in chrome/content/server.js)
    var replAPI = {};
    for (var k of Object.keys(this.repl.__exposedProps__)) {
      var v = this.repl[k];

      if (typeof v == "function") {
        replAPI[k] = v.bind(this);
      }
    }

    // FIX repl api injection in content privileged contexts
    this._hostContext[this._name] = Cu.cloneInto(replAPI, this._hostContext, {
      cloneFunctions: true
    });

    if(this._hostContext instanceof Ci.nsIDOMWindow)
        this._hostContext.addEventListener('unload', this._emergencyExit, false);
}

function _prompt(prompt) {
    if(this.getenv('printPrompt'))
        if(prompt) {
            this.print(prompt, false);
        } else {
            if(typeof(this.currentInteractor().getPrompt) == 'function')
                this.print(this.currentInteractor().getPrompt(this), false);
            else
                this.print('> ', false);
        }
}

function receive(input) {
    this.currentInteractor().handleInput(this, input);
}


// UTILITIES
// ----------------------------------------------------------------------

function debug() {
    if(DEBUG) {
        var s = 'D, MOZREPL : ' + Array.prototype.slice.call(arguments).join(' :: ');
        if(!s.match(/\n$/))
            s += '\n';
        dump(s);
    }
}

function formatStackTrace(exception) {
    var trace = '';
    if(exception.stack) {
        var calls = exception.stack.split('\n');
        for each(var call in calls) {
            if(call.length > 0) {
                call = call.replace(/\\n/g, '\n');

                if(call.length > 200)
                    call = call.substr(0, 200) + '[...]\n';

                trace += call.replace(/^/mg, '\t') + '\n';
            }
        }
    }
    return trace;
}

function chooseName(basename, context) {
    if(basename in context) {
        var i = 0;
        do { i++ } while(basename + i in context);
        return basename + i;
    } else
        return basename;
}

function isTopLevel(object) {
    return (object instanceof Ci.nsIDOMWindow ||
            'wrappedJSObject' in object ||
            'NSGetModule' in object ||
            'EXPORTED_SYMBOLS' in object ||
            (object.__parent__ && 'EXPORTED_SYMBOLS' in object.__parent__));
}

function scan(string, separator) {
    var match = string.match(separator);
    if(match)
        return [string.substring(0, match.index),
                string.substr(match.index + match[0].length)];
    else
        return [null, string];
}

function evaluate(code) {
    var _ = arguments.callee;
    if(typeof(_.TMP_FILE) == 'undefined') {
        _.TMP_FILE = Cc['@mozilla.org/file/directory_service;1']
            .getService(Ci.nsIProperties)
            .get('ProfD', Ci.nsIFile);
        _.TMP_FILE.append('mozrepl.tmp.js');

        _.TMP_FILE_URL = Cc['@mozilla.org/network/io-service;1']
            .getService(Ci.nsIIOService)
            .getProtocolHandler('file')
            .QueryInterface(Ci.nsIFileProtocolHandler)
            .getURLSpecFromFile(_.TMP_FILE);
    }

    var fos = Cc['@mozilla.org/network/file-output-stream;1']
        .createInstance(Ci.nsIFileOutputStream);
    fos.init(_.TMP_FILE, 0x02 | 0x08 | 0x20, 0o600, 0);
    var os = Cc['@mozilla.org/intl/converter-output-stream;1']
        .createInstance(Ci.nsIConverterOutputStream);
    os.init(fos, 'UTF-8', 0, 0x0000);
    os.writeString(code);
    os.close();

    if(typeof(_.cacheKiller) == 'undefined')
        _.cacheKiller = 0;

    _.cacheKiller++;
    var scriptUrl = _.TMP_FILE_URL + '?' + _.cacheKiller;
    debug('evaluate', scriptUrl);
    var result = loader.loadSubScript(scriptUrl, this._workContext, 'UTF-8');

    this.$$ = result;
    return result;
};

// We wrap exceptions in scripts loaded by repl.load() (thus also by
// Emacs Moz interaction mode) into a LoadScriptError exception, so
// that SyntaxError's don't interfere with the special use we make of
// them in the javascriptInteractor.handleInput, i.e. to detected
// unfinished input.

function LoadedScriptError(cause) {
    this.cause = cause;
}
