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


function constructor(server) {
    this._server = server;
    window.addEventListener(
        'load', function(event) {
            document
                .getElementById('mozrepl-command-toggle')
                .setAttribute('label',
                              server.isActive() ? 'Stop Repl' : 'Start Repl');
        }, false);
}

function toggleServer(sourceCommand) {
    var pref = Components
        .classes['@mozilla.org/preferences-service;1']
        .getService(Components.interfaces.nsIPrefService)
        .getBranch('extensions.mozrepl.');

    var port = pref.getIntPref('port');
    var loopbackOnly = pref.getBoolPref('loopbackOnly');

    if(this._server.isActive()) {
        this._server.stop();
        sourceCommand.setAttribute('label', 'Start Repl');
    }
    else {
        this._server.start(port, loopbackOnly);
        sourceCommand.setAttribute('label', 'Stop Repl');
    }
}

