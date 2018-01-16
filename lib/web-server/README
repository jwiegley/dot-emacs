                           Emacs Web Server

DESCRIPTION
    A web server in Emacs running handlers written in Emacs Lisp.

REQUIREMENTS
    Emacs 24.3 or later.

STATUS
    Supports HTTP GET and POST requests including URL-encoded
    parameters, multipart/form data and file uploads.  Supports web
    sockets.  Reasonably performant, faster than Elnode [1].  This is
    a new project without much extended use so there are likely bugs
    and potentially security issues.  That said it consists of little
    more than HTTP header parsing logic perched atop Emacs' existing
    network process primitives, so it should be fairly robust.

    [1]  http://eschulte.github.io/emacs-web-server/benchmark/

USAGE
    See the examples/ directory in this repository for examples
    demonstrating usage.  The Emacs web-server is also used to run a
    paste server [2], serve editable Org-mode pages [3] and serve
    files for Cask [4].

    [2]  https://github.com/eschulte/el-sprunge
    [3]  https://github.com/eschulte/org-ehtml
    [4]  https://github.com/cask/cask

    Available from the GNU ELPA [5].  The tutorials page [6] walks
    through usage scenarios including installing the Emacs web-server
    and running it behind a proxy.

    [5]  http://elpa.gnu.org/
    [6]  http://eschulte.github.io/emacs-web-server/tutorials/

    Run `make check' to run the included test suite.

DOCUMENTATION
    Run `make doc' to build the texinfo documentation, also available
    online [6].

    [6]  http://eschulte.github.io/emacs-web-server
