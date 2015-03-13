// ==UserScript==
// @name           Live BDO reloader
// @description    Include tag to load js from local bdb server
// @author         Raimon Grau Cuscó <raimonster@gmail.com>
// @include        http://localhost*
// @version        0.1
// @license        LGPL http://www.gnu.org/licenses/lgpl.html
// ==/UserScript==

var head = document.getElementsByTagName('head').item(0);
var tag = document.createElement('script');

tag.setAttribute('src','http://localhost:9090/bdo');
tag.setAttribute('type','text/javascript');

head.appendChild(tag);
