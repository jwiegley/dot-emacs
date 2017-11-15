This package lets you access the GNU Bug Tracker from within Emacs.

It defines the command `M-x debbugs-gnu' for listing bugs, and the
command `M-x debbugs-gnu-search' for bug searching.  The command
`M-x debbugs-gnu-usertags' shows existing user tags on bugs, whilst
the command `M-x debbugs-gnu-patches' lists bugs containing a patch.
In order to show bugs with known numbers, `M-x debbugs-gnu-bugs' could
be used.

If you prefer the listing of bugs as TODO items of `org-mode', you
could use the commands `M-x debbugs-org', `M-x debbugs-org-search',
`M-x debbugs-org-patches' and `M-x debbugs-org-bugs' instead.

A minor mode `debbugs-browse-mode' let you browse URLs to the GNU Bug
Tracker as well as bug identifiers prepared for `bug-reference-mode'.

All these commands are described in the Debbugs User Guide, accessible via
(info "(debbugs-ug)")

This package works by implementing basic functions to access a Debbugs
SOAP server (see <http://wiki.debian.org/DebbugsSoapInterface>).  It
implements the SOAP functions "get_bugs", "newest_bugs", "get_status",
"get_usertag", "get_bug_log" and "search_est".  The SOAP function
"get_versions" is not implemented (yet).

You can connect to other debbugs servers by customizing the variable
`debbugs-port'.
