# emacs-sos

[![License](http://img.shields.io/:license-gpl3-blue.svg)](http://www.gnu.org/licenses/gpl-3.0.html)
[![Flattr This](http://button.flattr.com/flattr-badge-large.png)](https://flattr.com/submit/auto?fid=y0jx3j&url=https%3A%2F%2Fgithub.com%2Fomouse%2Femacs-sos)

StackOverflow Search (SOS) mode for Emacs.

## Installation

### Install using MELPA

    M-x package-install RET sos

[![MELPA](http://melpa.org/packages/sos-badge.svg)](http://melpa.org/#/sos)

### Install using Github

    git clone https://github.com/omouse/emacs-sos.git
    M-x load-file RET "/path/to/clone/sos.el"

## Usage

Invoked with the `sos` command

    M-x sos

Enter your query and search results are displayed with their excerpts in an org-mode buffer:

    M-x sos RET why is emacs so awesome? RET

In the search results buffer, if you have a question at point, you can use `sos-answer` to retrieve all answers for that question. *You can also press "A" on the question to run `sos-answer`*.

    M-X sos-answer

## How Does It Look

![emacs sos search results screenshot](https://github.com/omouse/emacs-sos/raw/master/emacs-sos-screenshot.png)

## Alternatives to sos-mode

There's an alternative to sos-mode floating out there: [sx.el](https://github.com/vermiculus/sx.el/) which uses the Stack Exchange API and works with more than just StackOverflow.

Someone has created a command-line tool for viewing StackOverflow questions: [how2](https://github.com/santinic/how2). It's written in Node.js which is okay but what a strange choice for a command-line tool. It also has modal windows within the terminal which is strange. It includes a [StackExchange API for Node.js](https://github.com/santinic/how2/tree/master/lib/stackexchange).

List of alternatives:

* [sx.el](https://github.com/vermiculus/sx.el/)
* [how2](https://github.com/santinic/how2)
* [wat](https://github.com/dthree/wat)
* [howdoi](https://github.com/gleitz/howdoi)

## Copyright and License

Licensed under the GNU GPL v3, see [LICENSE](./LICENSE) for full text of license.

Copyright (C) 2014-2016 Rudolf Olah <omouse@gmail.com>
