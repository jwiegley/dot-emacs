Butler -- Emacs Integration for Jenkins (And maybe Hudson)
======

Install
=======

Add butler.el to your load path. Add the following to your .emacs file: `(require 'butler)`. Butler will be distributed to a ELPA repo soon.

Dependencies
------------

* json.el
    * Should be distributed with Emacs.
* web.el
    * Available in Marmalade.

Getting Started
===============

Butler contains a list of servers conveniently named butler-servers. Add servers in the following manor:

```elisp
(add-to-list butler-servers
             '(jenkins "SERVER-NAME"
                       (server-address . "https://jenkins-addres")
                       (server-user . "user")
                       (server-password . "pass")))
```

Butler also supports putting credentials in an encrypted authinfo file, like gnus.

Use the following code to set that up:

```elisp
(add-to-list butler-servers
             '(jenkins "SERVER-NAME"
                       (server-address . "https://jenkins-addres")
                       (auth-file . "~/.authinfo.gpg")))
```

The following line should exist in ~/.authinfo.gpg:

```
machine SERVER-NAME login username password password
```


In the future, the first variable will indicate what type of CI server is being used. Currently it's ignored.

View the list of servers with `M-x butler-status`. Refresh the list with `g`, and trigger the job under the point with `t`.

Coming Soon
===========

* Indication of what jobs are running
* Console output.
* Job history.
* Job watching.


FAQ
===

1. Why?
    * Because I missed Jenkins integration when I left Eclipse for Emacs (again).
2. Why does it display an error at the bottom when I refresh?
    * web.el is being tricky. I might replace it with the native url.el package.
3. What if I want to use a Jenkins view instead of seeing everything?
    * Server-address can be either the base url for your server, or the url for the view.
4. Can I have multiple servers?
    * There's a bug affecting the rendering of multiple servers at the moment. I'm working on it.
5. Does it support Hudson/Travis/my-favorite-CI?
    * I've only tested with Jenkins at the moment. Since Jenkins and Hudson are so closely related, theoretically it should be fine. Please contact me if Hudson doesn't work.
    * I currently do not support other server types, sorry.
6. Do you support anything other than basic auth?
    * No.
