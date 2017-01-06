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

const Cc = Components.classes;
const Ci = Components.interfaces;
const Cr = Components.results;
const Cu = Components.utils;

const CATEGORY = 'c-mozrepl';
const CLASS_ID = Components.ID('{f62cbe68-ee70-4264-8586-66df185244f5}');
const CONTRACT_ID = '@mozilla.org/commandlinehandler/general-startup;1?type=repl';
const INTERFACE = Ci.nsICommandLineHandler;

Cu.import("resource://gre/modules/XPCOMUtils.jsm");

const srvPref = Components.classes['@mozilla.org/preferences-service;1']
    .getService(Components.interfaces.nsIPrefService)
    .getBranch('extensions.mozrepl.');


function MozReplCommandLineHandler() {}

MozReplCommandLineHandler.prototype = {
    classDescription: "MozRepl command line handler",
    classID: CLASS_ID,
    contactID: CONTRACT_ID,
    QueryInterface: XPCOMUtils.generateQI([Ci.nsICommandLineHandler]),

    handle: function(cmdLine) {
        var start, port, contextWindowType;
        try {
            port = cmdLine.handleFlagWithParam('repl', false);
        } catch (e) {
            start = cmdLine.handleFlag('repl', false)
        }

        try {
            contextWindowType = cmdLine.handleFlagWithParam('repl-context', false);
        } catch(e) {}

        if(start || port || contextWindowType) {
            port = parseInt(port) || srvPref.getIntPref('port');
            var loopbackOnly = srvPref.getBoolPref('loopbackOnly');

            var service = Cc['@hyperstruct.net/mozlab/mozrepl;1']
                .getService(Ci.nsIMozRepl)
                .wrappedJSObject;

            if(contextWindowType)
                service.setContextWindowType(contextWindowType);

            service.start(port, loopbackOnly);
        }
    },

    helpInfo: ['-repl [PORT]       Start REPL (PORT defaults to 4242).\n',
               '-repl-context      Start in the context gives as window type (see XUL windowtype attribute).\n'
              ].join('')
};

/**
* XPCOMUtils.generateNSGetFactory was introduced in Mozilla 2 (Firefox 4).
* XPCOMUtils.generateNSGetModule is for Mozilla 1.9.2 (Firefox 3.6).
*/
if (XPCOMUtils.generateNSGetFactory)
    var NSGetFactory = XPCOMUtils.generateNSGetFactory([MozReplCommandLineHandler]);
else
    var NSGetModule = XPCOMUtils.generateNSGetModule([MozReplCommandLineHandler]);
