fudge-discover.el is a subset of my http://github.com/phillord/assess
package, with the namespace, erm, fudged to something else.

If you wish to use my assess package, you do not need to go to such
lengths. I need to do such hackery here because (the rest of) assess
uses m-buffer, and introducing a circular dependency at this point
makes life really complicated.

https://github.com/phillord/m-buffer-el/pull/6
