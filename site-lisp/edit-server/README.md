About
=====

Edit with Emacs is an addon for webextension compatible browsers like
Google's Chrome(ium), Opera or Firefox that allows you to edit text
areas on your browser in a more full featured editor. It does this in
conjunction with an "Edit Server" which services requests by the
browser. This is because extensions cannot spawn new processes as a
security measure.

The extension packages native elisp version that can be run inside
GNU Emacs itself, just follow the instructions from the options page
of the extension. It has been known to work with GNU Emacs and
Aquamacs (MacOS); it is presently not compatible with XEmacs.

Other example edit servers can be found at the project homepage. There
is no reason why other server scripts could not spawn other editors
and currently a number of servers support the simple URL based
protocol.

This extension is licensed under the GPL v3 and development versions
can be found at: http://github.com/stsquad/emacs_chrome

Installing
==========

If you just want to install Edit with Emacs you can simply visit the
Chrome Store at:

https://chrome.google.com/webstore/detail/edit-with-emacs/ljobjlafonikaiipfkggjbhkghgicgoh

You then have the option of installing the packaged edit-server from the
options page or alternatively you can install the latest version from
MELPA if you have it enabled in Emacs 24+.

If you would like to help with the development of Edit with Emacs the
easiest way is to fork the github repository (https://github.com/stsquad/emacs_chrome)
and clone it to your development system. The in Chrome(ium) go to:

Tools->Extensions
Select "Developer Mode"
Click "Load Unpacked Extension"

and point it at the cloned repository.

Hacking
=======

This modeline should be used in every source file to keep indentation
consistent:

    // -*- tab-width: 4; indent-tabs-mode: nil; c-basic-offset: 4 -*-

This tells both emacs use spaces instead of tabs and use a basic indentation
of 4 spaces.

There is also a universal .editorconfig which should enforce this.

The code has a fair amount of whitespace damage. Please don't submit
mega-patches to clean it up, just fixup the local code as you go. It
makes history harder to navigate as well as potentially introducing
changes in the noise.

There is currently a minimal Travis-CI control file which essentially
ensures the edit-server.el still compiles. Additions to the test
coverage are always welcome ;-)

[![Build Status](https://travis-ci.org/stsquad/emacs_chrome.png?branch=master)](https://travis-ci.org/stsquad/emacs_chrome)

Submitting to Store
===================

* Test
* Tag vX.Y
* git archive --format zip --output emacs_chrome_X.Y.zip vX.Y
* Upload that

History
=======

Dave Hilley [wrote the original proof of concept](https://web.archive.org/web/20130719135014/http://www.thegibson.org/blog/archives/689) 
that showed it could be done. [I](http://www.bennee.com/~alex) then hacked around with the Javascript
to make the behaviour more like the classic It's All Text add-on available to Firefox.

Authors
=======

Edit with Emacs is open source and is brought to you thanks to
contributions from the following people:

David Hilley
Alex Bennée
Riccardo Murri
Niels Giesen
Wei Hu
Ævar Arnfjörð Bjarmason
Chris Houser
Robert Goldman
Phil Pennock
Sudish Joseph
IRIE Shinsuke
Nelson Elhage
David J. Biesack
Christopher Browne
Mark Shroyer
Remco van 't Veer
John Croisant
Tim Cuthbertson
Ryszard Szopa
Kazuya Sakakihara
Steve Purcell
Dale Sedivec
Jonas Bernoulli
Le Wang
Mike Shulman
Matt Walker
Aaron Schrab
Adam Spiers
Dato Simó
Philippe Vaucher
Eli Barzilay
Marc Tamsky
Attila Lendvai
Daniel Kraus

Other Code
==========

This extensions takes advantage of the jQuery library
to do a lot of the heavy lifting in searching the page
for elements. You can find it at:

http://jquery.com/

It uses John Resig's jQuery Colour Animation plug-in
to do the colour fades of the elements. It can be found
at:

https://github.com/jquery/jquery-color

The settings code uses Frank Kohlhepp's excellent
fancy-settings library. This can be found at:

https://github.com/frankkohlhepp/fancy-settings

The textarea code uses the rather nifty mutation summary
library by Google. This can be found at:

https://code.google.com/p/mutation-summary/
