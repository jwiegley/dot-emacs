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

const Ci = Components.interfaces;
const Cc = Components.classes;
const pref = Cc['@mozilla.org/preferences-service;1']
    .getService(Ci.nsIPrefService)
    .getBranch('extensions.mozrepl.');


// GLOBAL STATE
// ----------------------------------------------------------------------

var server;


// INITIALIZATION
// ----------------------------------------------------------------------

function initOverlay() {
    server = Cc['@hyperstruct.net/mozlab/mozrepl;1'].getService(Ci.nsIMozRepl);

    // upgradeCheck(
    //     'mozrepl@hyperstruct.net',
    //     'extensions.mozrepl.version', {
    //         onFirstInstall: function() {
    //             openURL('http://hyperstruct.net/projects/mozlab/news');
    //         },

    //         onUpgrade: function() {
    //             openURL('http://hyperstruct.net/projects/mozlab/news');
    //         }
    //     });
}

function togglePref(prefName) {
    pref.setBoolPref(prefName, !pref.getBoolPref(prefName));
}

function toggleServer(sourceCommand) {
    if(server.isActive())
        server.stop();
    else
        server.start(pref.getIntPref('port'),
                     pref.getBoolPref('loopbackOnly'));
}

function updateMenu(xulPopup) {
    document.getElementById('mozrepl-command-toggle')
        .setAttribute('label', server.isActive() ? 'Stop' : 'Start');
    document.getElementById('mozrepl-command-listen-external')
        .setAttribute('checked', !pref.getBoolPref('loopbackOnly'));
    document.getElementById('mozrepl-command-autostart')
        .setAttribute('checked', pref.getBoolPref('autoStart'));
}

function changePort() {
    var value = window.prompt('Choose listening port', pref.getIntPref('port'));
    if(value)
        pref.setIntPref('port', value);
}

function openHelp() {
    openURL('http://github.com/bard/mozrepl/wikis/home');
}

function openURL(url) {
    if(typeof(getBrowser().addTab) == 'function')
        // XXX bard: apparently needed otherwise it won't have any
        // effect when called from an onload handler
        setTimeout(function() {
            getBrowser().selectedTab = getBrowser().addTab(url)
        }, 500);
    else
        Cc['@mozilla.org/uriloader/external-protocol-service;1']
            .getService(Ci.nsIExternalProtocolService)
            .loadUrl(Cc['@mozilla.org/network/io-service;1']
                     .getService(Ci.nsIIOService)
                     .newURI(url, null, null));
}

function upgradeCheck(id, versionPref, actions) {
    const pref = Cc['@mozilla.org/preferences-service;1']
    .getService(Ci.nsIPrefService);

    function getExtensionVersion(id) {
        return Cc['@mozilla.org/extensions/manager;1']
        .getService(Ci.nsIExtensionManager)
        .getItemForID(id).version;
    }

    function compareVersions(a, b) {
        return Cc['@mozilla.org/xpcom/version-comparator;1']
        .getService(Ci.nsIVersionComparator)
        .compare(curVersion, prevVersion);
    }

    var curVersion = getExtensionVersion(id);
    if(curVersion) {
        var prevVersion = pref.getCharPref(versionPref);
        if(prevVersion == '') {
            if(typeof(actions.onFirstInstall) == 'function')
                actions.onFirstInstall();
        } else {
            if(compareVersions(curVersion, prevVersion) > 0)
                if(typeof(actions.onUpgrade) == 'function')
                    actions.onUpgrade();
        }

        pref.setCharPref(versionPref, curVersion);
    }
}
