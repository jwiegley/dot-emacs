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


/* ---------------------------------------------------------------------- */
/*                      Component specific code                           */

const CLASS_ID = Components.ID('{57f4284b-1f9b-4990-8525-9ed5cbb23e01}');
const CLASS_NAME = 'MozRepl Server XPCOM';
const CONTRACT_ID = '@hyperstruct.net/mozlab/mozrepl;1';
const SOURCE = 'chrome://mozrepl/content/server.js';
const INTERFACE = Components.interfaces.nsIMozRepl;

/* ---------------------------------------------------------------------- */
/*                           Template code                                */

const Cc = Components.classes;
const Ci = Components.interfaces;
const Cr = Components.results;
const Cu = Components.utils;
const loader = Cc['@mozilla.org/moz/jssubscript-loader;1']
    .getService(Ci.mozIJSSubScriptLoader);

Components.utils.import("resource://gre/modules/XPCOMUtils.jsm");

function MozRepl() {
    this.wrappedJSObject = this;
}

MozRepl.prototype = {
  classDescription: CLASS_NAME,
  classID: CLASS_ID,
  contactID: CONTRACT_ID,
  QueryInterface: XPCOMUtils.generateQI([
    INTERFACE,
    Ci.nsISupports,  
    Ci.nsIObserver
  ]),

  reload: function() {
    loader.loadSubScript(SOURCE, this.__proto__);
  }
};
loader.loadSubScript(SOURCE, MozRepl.prototype);

if (XPCOMUtils.generateNSGetFactory) /* Gecko 2 */
    var NSGetFactory = XPCOMUtils.generateNSGetFactory([MozRepl]);
else { /* Gecko 1.9.2 */
    // The following line, contrary to what the documentation says,
    // does not appear to work, so we use the old verbiage.
    //
    // var NSGetModule = XPCOMUtils.generateNSGetModule([MozRepl]);

    var Factory = {
        createInstance: function(aOuter, aIID) {
            if(aOuter != null)
                throw Cr.NS_ERROR_NO_AGGREGATION;
            var component = new MozRepl();

            return component.QueryInterface(aIID);
        }
    };

    var Module = {
        _firstTime: true,
    
        registerSelf: function(aCompMgr, aFileSpec, aLocation, aType) {
            if (this._firstTime) {
                this._firstTime = false;
                throw Components.results.NS_ERROR_FACTORY_REGISTER_AGAIN;
            };
    
            aCompMgr = aCompMgr.QueryInterface(Ci.nsIComponentRegistrar);
            aCompMgr.registerFactoryLocation(
                CLASS_ID, CLASS_NAME, CONTRACT_ID, aFileSpec, aLocation, aType);
    
            var catMan = Cc['@mozilla.org/categorymanager;1'].
                getService(Ci.nsICategoryManager);
            catMan.addCategoryEntry('app-startup', 'MozRepl', 'service,' + CONTRACT_ID, true, true);
        },
    
        unregisterSelf: function(aCompMgr, aLocation, aType) {pp
            aCompMgr = aCompMgr.QueryInterface(Ci.nsIComponentRegistrar);
            aCompMgr.unregisterFactoryLocation(CLASS_ID, aLocation);
    
            var catMan = Cc['@mozilla.org/categorymanager;1'].
                getService(Ci.nsICategoryManager);
            catMan.deleteCategoryEntry('app-startup', 'service,' + CONTRACT_ID, true);
        },
    
        getClassObject: function(aCompMgr, aCID, aIID) {
            if (!aIID.equals(Ci.nsIFactory))
                throw Cr.NS_ERROR_NOT_IMPLEMENTED;
    
            if (aCID.equals(CLASS_ID))
                return Factory;
    
            throw Cr.NS_ERROR_NO_INTERFACE;        
        },
    
        canUnload: function(aCompMgr) { return true; }
    };
    
    var NSGetModule = function(aCompMgr, aFileSpec) { return Module; }
}
