swank-js
========

** IMPORTANT NOTE **
The primary swank-js source repository is now [https://github.com/swank-js/swank-js](https://github.com/swank-js/swank-js).


swank-js provides [SLIME](http://common-lisp.net/project/slime/) REPL
and other development tools for in-browser JavaScript and
[Node.JS](http://nodejs.org). It consists of SWANK backend and
accompanying SLIME contrib. [Socket.IO](http://socket.io/) is used to
communicate with wide range of web browsers.

Motivation
----------

From my experience an ability to use REPL for JavaScript debugging and
interactive development is very helpful when developing Web
applications. Previously I was using a heavily patched
[MozRepl](https://github.com/bard/mozrepl/wiki/) version that was
adapted for in-browser JavaScript. Primary downsides of that approach
were extreme instability of communication between Emacs and the
browser, the lack of cross-browser support and the lack of good RPC
between Emacs and JS that can be used to develop some handy
extensions.

I knew there exists [slime-proxy](https://github.com/3b/slime-proxy)
project that provides such functionality for
[Parenscript](http://common-lisp.net/project/parenscript/). The
problem is that most of us including myself can't use Lisp all the
time and a lot of code needs to be developed using languages like
plain JavaScript (as opposed to Parenscript), Python and so on. My
first thought was to adapt slime-proxy for use with plain JS, but then
I decided to roll my own SWANK backend using Node.JS. I wanted to find
out what this buzz around Node.JS is about and perhaps steal an
idea or two from there for use in my Lisp projects. Another reason was
availability of [Socket.IO](http://socket.io/) and an example of
[tiny http server proxy](http://www.catonmat.net/http-proxy-in-nodejs).

Some people may prefer Firebug or built-in browser development tools
to Emacs-based development, but for example in case of mobile browsers
you don't have much choice. At some point I did try swank-js with an
colleague's iPhone and it worked, which is not too unexpected given
that Socket.IO has good cross-browser support.

Status
------

As of now swank-js provides REPL with an ability to work with multiple
browser connections, supports dynamic updates of JavaScript code using
C-c C-c / C-M-x, provides debug output function and an ability to
reload web pages in the browser or refresh their CSS using Emacs
commands.

Many aspects of full-fledged SWANK backends aren't implemented yet,
there's no debugger/completion/autodoc and so on, but as I plan to use
swank-js a lot in future there's a good chance many of these features
will be eventually added.

Installation
------------

1. Install [Node.JS](http://nodejs.org) and [npm](http://npmjs.org/)

2. Install swank-js from npm:

        npm install -g swank-js

3. Get recent [SLIME](http://common-lisp.net/project/slime/) from its CVS
or the [git mirror](http://git.boinkor.net/gitweb/slime.git). The backend
was verified to work with SLIME 2012-02-12, it may or may not work with
other versions, but note that breaking change in the protocol was introduced
in SLIME 2011-11-27.

4. Make sure you have latest [js2-mode](http://code.google.com/p/js2-mode/).
Add it to your .emacs:

        (add-to-list 'load-path "/path/to/js2-mode/directory")
        (autoload 'js2-mode "js2-mode" nil t)
        (add-to-list 'auto-mode-alist '("\\.js$" . js2-mode))

5. Create symbolic link to slime-js.el in the contrib subdirectory of
SLIME project.

6. Install [js2-mode](http://code.google.com/p/js2-mode/) into emacs from
   http://tromey.com/elpa/

7. In your .emacs, add the following lines (you may use other key for
slime-js-reload; also, if you're already using SLIME, just add slime-js
to the list of contribs, otherwise adjust the load-path item):

        (global-set-key [f5] 'slime-js-reload)
        (add-hook 'js2-mode-hook
                  (lambda ()
                    (slime-js-minor-mode 1)))

8. If you're using CSS mode, you may want to add the following lines too:

        (add-hook 'css-mode-hook
                  (lambda ()
                    (define-key css-mode-map "\M-\C-x" 'slime-js-refresh-css)
                    (define-key css-mode-map "\C-c\C-r" 'slime-js-embed-css)))

Usage
-----

If you want to use swank from the node project just add following to your
package.json file:

        "devDependencies": {
          "swank-js": ">=0.0.1"
        },
        "scripts": {
          "swank": "node node_modules/swank-js"
        }

Once this is done you should be able to run up a swank for this project by
running:

        npm run swank

Alternatively you can install swank-js globally by running:

        npm install -g swank-js

Once installed you could run it from you project directory:

        swank-js

Make SLIME connect to the backend using `M-x slime-connect` and
specifying `localhost` and port `4005`. You will see REPL buffer
with the following prompt:

    NODE>

This means that you're currently talking to Node.JS. You may play
around with it by running some JavaScript expressions.

If you get warning about SLIME version mismatch, you may make it
disappear until the next SLIME upgrade by typing *,js-slime-version*
at the REPL and entering your SLIME version (e.g. 2010-11-13).

### Connecting to a web browser ###

Point your web browser to

    http://localhost:8009/swank-js/test.html
You will see the following message appear in the REPL (browser name
and version may differ):

    Remote attached: (browser) Firefox3.6:127.0.0.1

This means that the browser is now connected. Several browsers can
connect simultaneously and you can switch between them and Node.JS
REPL using *,select-remote* REPL shortcut. To use it, press ','
(comma) and type *select-remote* (completion is supported). You will
see "Remote:" prompt. Press TAB to see completions. Select your
browser in the list by typing its name or clicking on the
completion. The following message will appear:

    NODE>
    Remote selected: (browser) Firefox3.6:127.0.0.1
    FIREFOX-3.6>

After that, you can interactively evaluate expressions in your
browser. To go back to Node.JS repl, switch back to node.js/direct
remote.

    FIREFOX-3.6> document.body.nodeName
    BODY
    FIREFOX-3.6> alert("test!")
    FIREFOX-3.6>

When working with browser, you may use F5 to reload the page. swank-js
connection with browser is lost in this case, but to solve this
problem you may use *,sticky-select-remote* instead of
*,select-remote*. This way swank-js will remember your selection and
automagically attach to the browser whenever it connects. If you press
F5 after using *,sticky-select-remote*, you will see that browser
briefly disconnects but then connects again:

    Remote detached: (browser) Firefox3.6:127.0.0.1
    FIREFOX-3.6>
    Remote selected (auto): (direct) node.js
    Remote attached: (browser) Firefox3.6:127.0.0.1
    NODE>
    Remote selected (auto): (browser) Firefox3.6:127.0.0.1
    FIREFOX-3.6>

The sticky remote selection is saved in the config file, ~/.swankjsrc,
so you don't need to do *,sticky-select-remote* after restarting the
browser.


### Connecting to a remote page ###

Now, let's try to make it work with an actual site. swank-js acts as a
proxy between your browser and the site so it can inject necessary
script tags into HTML pages and avoid cross-domain HTTP request
problems. Let's point it to [reddit](http://www.reddit.com). Type
*,target-url* and then *http://www.reddit.com* (www. part is
important, otherwise it will redirect to www.reddit.com skipping the
proxy). Point your browser to http://localhost:8009, you'll see reddit
frontpage load. If you didn't do *,select-remote* or
*,sticky-select-remote* yet do it now and select your browser from the
list of remotes. Now you can execute JavaScript in the context of
reddit:

    FIREFOX-3.6> $(".sitetable a.title").map(function(n) { return (n + 1) + ". " + $(this).text(); }).get().join("\n")
    1. Wikileaks currently under a mass DDOS attack
    2. Munich University - Jealous
    ...

Let's make a function from it. Create a file test.js somewhere and
make sure it uses js2-mode (if it doesn't, switch it to js2-mode using
M-x js2-mode). Type the following there:

    function listRedditTitles () {
      $(".sitetable a.title").map(
        function (n) {
          SwankJS.output((n + 1) + ". " + $(this).text() + "\n");
        }).get().join("\n");
    }

Note SwankJS.output() function being used there. It allows you to send
debug print to SLIME REPL.

Move the point somewhere into the middle of the listRedditTitles() function
and press C-M-x. Now you may try it out in the REPL:

    FIREFOX-3.6> listRedditTitles()
    1. Wikileaks currently under a mass DDOS attack
    2. Munich University - Jealous
    ...

You may edit the function definition and update it using C-M-x any
number of times.


### Hacking CSS ###

#### By updating a file ####

Now let's try some CSS hacking. Create a directory named zzz and start
a Web server in it from your command prompt:

    $ mkdir zzz && cd zzz && python -mSimpleHTTPServer

Create a file named a.css there and make sure it uses css-mode (like
with js2-mode, you can force it with M-x css-mode). Add some CSS rules
to this file:

    body {
        background: green;
    }

Now let's add the stylesheet to the reddit page:

    FIREFOX-3.6> $('head').append('<link rel="stylesheet" href="http://localhost:8000/a.css" type="text/css" />');
    [object Object]

You will see some parts of the page become green. Now, change green to
blue in the CSS file and press C-M-x (it will save the file
automatically):

    body {
        background: blue;
    }

You will see the page become blue, maybe after some flickering as all
CSS used on the page is reloaded. This way you may update CSS in an
AJAX application without reloading the page, which is often rather
handy. Unlike editing CSS in Firebug in case when you're editing CSS
of your own application changes will not disappear upon page reload
(with reddit page you'll have to readd the stylesheet).


#### By embedding CSS ####

Alternatively to just try out a snippet of CSS you can select some CSS code and hit `C-c C-r`. This will send the code snippet (or the content of the whole buffer) to the browser and embed it inside a style element.

To remove the embedded CSS run the command with a prefix `C-u C-c C-r`.


### Embedding swank-js in a page ###

This is useful for automatically connecting to a web page you develop
locally without using the *,target-url* command and without changing
the document URL for that page. When `node swank.js` is running embed

    <script type="text/javascript" src="http://localhost:8009/swank-js/swank-js-inject.js"></script>

and you are ready to go!

### Swank js as a bookmarklet ###

You can bookmark
<a href="javascript:(function(d)%7Bwindow.swank_server%3D%27http%3A%2F%2Flocalhost%3A8009%2F%27%3Bif(!d.getElementById(%27swank-js-inj%27))%7Bvar%20h%3Dd.getElementsByTagName(%27head%27)%5B0%5D%2Cs%3Dd.createElement(%27script%27)%3Bs.id%3D%27swank-js-inj%27%3Bs.type%3D%27text%2Fjavascript%27%3Bs.src%3Dswank_server%2B%27swank-js%2Fswank-js-inject.js%27%3Bh.appendChild(s)%3B%7D%7D)(document)%3B">
swank connect</a> /
<a
href="javascript:(function()%7BSwankJS.disconnect()%3B%7D)()%3B">swank
disconnect</a>
links and use them on any page you'd like to play with.

Troubleshooting
---------------

I've noticed that flashsocket Socket.IO transport does exhibit some
instability. You may want to try other transports by changing the
socketio cookie, e.g.:

    document.cookie = "socketio=xhr-polling"

Be careful not to lose connection to the browser though especially in
case of REPL-less browser like IE6/7 or you'll have to type something
like

    javascript:void(document.cookie = "socketio=flashsocket")

in the address bar.

In case of IE, increasing the maximum number of HTTP connections may
help with non-Flash transports, although I didn't try it yet. To do it
add DWORD value MaxConnectionsPer1_0Server to the following registry
key:

    HKEY\_CURRENT\_USER\Software\Microsoft\Windows\CurrentVersion\Internet Settings

License
-------

swank-js is distributed under X11-style license. See LICENSE file.
