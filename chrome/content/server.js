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
    .getService(Ci.nsIPrefService);
const srvObserver = Cc['@mozilla.org/observer-service;1']
    .getService(Ci.nsIObserverService);
const pref = srvPref.getBranch('extensions.mozrepl.');


function REPL() {
    // FIX #37 (https://github.com/bard/mozrepl/issues/37)
    // needed by toolkit >= 17.0
    // http://blog.mozilla.org/addons/2012/08/20/exposing-objects-to-content-safely/
    this.__exposedProps__ = this.__exposedProps__ || _generateExposedProps(this.__proto__);
};
loader.loadSubScript('chrome://mozrepl/content/repl.js', REPL.prototype);

function _generateExposedProps(obj) {
    var props = {};
    Object.keys(obj).filter(function (k) k[0] !== '_').
        forEach(function (k) {
            props[k] = 'r';
        });
    return props;
}

// STATE
// ----------------------------------------------------------------------

var serv;
var contextWindowType;


// CODE
// ----------------------------------------------------------------------

var sessions = {
    _list: [],

    add: function(session) {
        this._list.push(session);
    },

    remove: function(session) {
        var index = this._list.indexOf(session);
        if(index != -1)
            this._list.splice(index, 1);
    },

    get: function(index) {
        return this._list[index];
    },

    quit: function() {
        this._list.forEach(
            function(session) { session.quit; });
        this._list.splice(0, this._list.length);
    }
};


function start(port, loopbackOnly) {
    if(typeof(loopbackOnly) == 'undefined')
        loopbackOnly = true;
    
    try {
        serv = Cc['@mozilla.org/network/server-socket;1']
            .createInstance(Ci.nsIServerSocket);
        serv.init(port, loopbackOnly, -1);
        serv.asyncListen(this);
        log('I, MOZREPL : Listening : ' + (loopbackOnly ? '127.0.0.1' : '0.0.0.0') + ':' + port);
    } catch(e) {
        log('E, MOZREPL : Error : ' + e);
    }
}

function onSocketAccepted(serv, transport) {
    try {
        var outstream = transport.openOutputStream(Ci.nsITransport.OPEN_BLOCKING , 0, 0);
        var outstreamutf8 = Cc['@mozilla.org/intl/converter-output-stream;1']
            .createInstance(Ci.nsIConverterOutputStream);
        outstreamutf8.init(outstream, 'UTF-8', 0, 0);

        var instream = transport.openInputStream(0, 0, 0);
        var instreamutf8 = Cc['@mozilla.org/intl/converter-input-stream;1']
            .createInstance(Ci.nsIConverterInputStream);
        instreamutf8.init(instream, 'UTF-8', 1024, 0);
    } catch(e) {
        log('E, MOZREPL : Error : ' + e);
    }

    var context = Cc['@mozilla.org/appshell/window-mediator;1']
        .getService(Ci.nsIWindowMediator)
        .getMostRecentWindow(typeof(contextWindowType) !== 'undefined' ?
                             contextWindowType : pref.getCharPref('startingContext'));

    if(context === null) {
        context = Cc["@mozilla.org/appshell/appShellService;1"]
            .getService(Ci.nsIAppShellService)
            .hiddenDOMWindow.wrappedJSObject;
    }

    var session = new REPL();
    session.onOutput = function(string) {
        outstreamutf8.writeString(string);
    };
    session.onQuit = function() {
        log('I, MOZREPL : Client closed connection : ' + transport.host + ':' + transport.port);        
        instream.close();
        outstream.close();
        sessions.remove(session);
    };
    session.init(context);

    log('I, MOZREPL : Client connected : ' + transport.host + ':' + transport.port +
        ' : ' + (context instanceof Ci.nsIDOMWindow ?
                 context.document.location.href : context));

    var pump = Cc['@mozilla.org/network/input-stream-pump;1']
        .createInstance(Ci.nsIInputStreamPump);
    pump.init(instream, -1, -1, 0, 0, false);
    pump.asyncRead({
        onStartRequest: function(request, context) {},
        onStopRequest: function(request, context, status) {
                session.quit();
            },
        onDataAvailable: function(request, context, inputStream, offset, count) {
            var str = {}
            instreamutf8.readString(count, str)
            session.receive(str.value);
            }
        }, null);

    sessions.add(session);
}

function onStopListening(serv, status) {
}


function stop() {
    log('I, MOZREPL : Closing.');
    serv.close();
    sessions.quit();
    serv = undefined;
}

function isActive() {
    if(serv)
        return true;
}

function observe(subject, topic, data) {
    switch(topic) {
    case 'profile-after-change':
        srvObserver.addObserver(this, 'network:offline-status-changed', false);
        if(srvPref.getBranch('network.').getBoolPref('online') &&
           pref.getBoolPref('autoStart'))
            this.start(pref.getIntPref('port'),
                       pref.getBoolPref('loopbackOnly'));

        break;
    case 'network:offline-status-changed':
        switch(data) {
        case 'online':
            if(pref.getBoolPref('autoStart'))
                this.start(pref.getIntPref('port'),
                           pref.getBoolPref('loopbackOnly'));
            break;
        case 'offline':
            if(isActive())
                this.stop();
            break;
        }
        break;
    case 'quit-application-granted':
	this.stop();
    }
}

function setContextWindowType(windowType) {
    contextWindowType = windowType;
}

// UTILITIES
// ----------------------------------------------------------------------

function log(msg) {
    if(! pref.getBoolPref('noLog')) {
      dump(msg + '\n');
    }
}

