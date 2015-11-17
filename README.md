Zotelo helps you efficiently export and synchronize local databases (bib, rdf, html, json etc) and [Zotero](http://www.zotero.org) collections directly from emacs.

Zotelo can be used in conjunction with any emacs mode but is primarily intended
for `LaTeX`/`BibTeX` users of
[RefTeX](http://staff.science.uva.nl/~dominik/Tools/reftex/reftex-nutshell.html).


Installation
============

Install `zotelo` from [Melpa](https://melpa.org/) or put [zotelo.el](https://raw.github.com/vitoshka/zotelo/master/zotelo.el) into your emacs path.

Install [MozRepl](https://addons.mozilla.org/en-US/firefox/addon/mozrepl/) extension for Firefox and start it (you can also configure it for auto-start).

Activate `zotelo-minor-mode` in `LaTeX` mode:

```lisp
(add-hook 'TeX-mode-hook 'zotelo-minor-mode)
```

Similarly you can activate `zotelo` in org mode if you use it to draft your LaTeX papers.

Usage
=====

_*Key-map*_
```
C-c z c         zotelo-set-collection (also "C-c z s")
C-c z e         zotelo-export-secondary
C-c z r         zotelo-reset
C-c z t         zotelo-set-translator
C-c z u         zotelo-update-database
```

In order to export a zotero collection you need first to associate it with the
current buffer with `C-c z c` (`zotelo-set-collection`). Select `*ALL*` to
export the whole Zotero library.

Zotelo uses [IDO](http://www.emacswiki.org/emacs/InteractivelyDoThings ) interface for the collection selection:

![set_collection](https://github.com/vitoshka/zotelo/raw/master/img/set_collection.png)

![zotero_collection](https://github.com/vitoshka/zotelo/raw/master/img/zotero_collection.png)

After modifying your zotero collection from the zotero interface, update the the
local database file with `C-c z u` (`zotelo-update-database`).

Exported File Names
-------------------

If the current file contains any of the following bibliography declarations:

```tex
\bibliography{file1, file2, ...}
\zotelo{file1, file2, ...}
\nobibliography{file1, file2, ...}
```

`zotelo` exports the associated Zotero collection as a `file1.xxx` file,
otherwise it exports into `[current-file-name].xxx`. The extension `xxx` depends
on the current translator (`BibTeX` by default). Use `zotelo-set-translator`
(`C-c z t`) to choose the translator. To set the translator permanently
customize `zotelo-default-translator` variable.


Multiple Databases and Collections
----------------------------------

You can list several files in `\thebibliography{...}` list. The first file is the primary database which you set with `C-c z s` and update with `C-c z u`. All others are secondary databases. 

Usually one database is enough, but for some projects you might want to use several zotero collections. Use `zotelo-export-secondary` (bound to `C-c z e`) to export any zotero collection into one of the secondary files.  You will be asked to select a file and a collection to export. This way you can have as many databases and zotero collections as you want. 

Troubleshooting
===============

If for whatever reason zotelo stoped working, try to reset the Moz-Repl
collection with `C-c z r`. If that doesn't help, switch to
`*moz-command-output*` buffer. Normally you should see something like

```
....> ":MozOK:"
repl> 
```

Also see the buffer `*zoteloMozRepl*`, this is a primary buffer where mozrepl
outputs it's messages. Normally it should be showing only the startup message.

To further investigate your problem. Toggle `M-x zotelo-verbose RET` and try the
problematic `C-c z u`. If case of an error, go to *messages* buffer. You should
see womething akin to:


```javascript

zotelo message on [Mon Apr  9 18:44:53 2012]
Executing command: 

(moz-command (format zotelo--export-collection-js '/home/vitoshka/works/disposition_effect/disposition.bib' 119))

translated as:

var filename=('/home/vitoshka/works/disposition_effect/disposition.bib');
var id = 119;
var prefs = Components.classes['@mozilla.org/preferences-service;1'].getService(Components.interfaces.nsIPrefService).getBranch('extensions.zotero.');
var recColl = prefs.getBoolPref('recursiveCollections');
prefs.setBoolPref('recursiveCollections', true);
var file = Components.classes['@mozilla.org/file/local;1'].createInstance(Components.interfaces.nsILocalFile);
file.initWithPath(filename);
var zotero = Components.classes['@zotero.org/Zotero;1'].getService(Components.interfaces.nsISupports).wrappedJSObject;
var collection = true;
var translator = new zotero.Translate('export');
if (id != 0){ //not all collections
collection = zotero.Collections.get(id);
translator.setCollection(collection);
};
if(collection){
translator.setLocation(file);
translator.setTranslator('9cb70025-a888-4a29-a210-93ec52da40d4');
translator.translate();
out=':MozOK:';
}else{
out='Collection with the id ' + id + ' does not exist.';
};
prefs.setBoolPref('recursiveCollections', recColl);
out;
```

You can execute this javascript within
[moz-repl.el](https://github.com/bard/mozrepl/wiki/Emacs-integration) or
directly in firefox within a
[firebug](https://addons.mozilla.org/en-US/firefox/addon/firebug/) console.

