- [navi-mode.el &#x2014; major-mode for easy buffer-navigation](#navi-mode.el-&#x2014;-major-mode-for-easy-buffer-navigation)
  - [MetaData](#metadata)
  - [Commentary](#commentary)
    - [About navi-mode](#about-navi-mode)
    - [Usage](#usage)
    - [Installation](#installation)
    - [Emacs Version](#emacs-version)
  - [ChangeLog](#changelog)



# navi-mode.el &#x2014; major-mode for easy buffer-navigation<a id="sec-1"></a>

Author: Thorsten Jolitz <tjolitz AT gmail DOT com>
Version: 2.0
URL: <https://github.com/tj64/navi>

## MetaData<a id="sec-1-1"></a>

    copyright: Thorsten Jolitz
    
    copyright-years: 2013+
    
    version: 2.0
    
    licence: GPL 2 or later (free software)
    
    licence-url: http://www.gnu.org/licenses/
    
    part-of-emacs: no
    
    author: Thorsten Jolitz
    
    author_email: tjolitz AT gmail DOT com
    
    git-repo: https://github.com/tj64/navi.git
    
    git-clone: git://github.com/tj64/navi.git
    
    inspiration: occur-mode org-mode
    
    keywords: emacs navigation remote-buffer-control

## Commentary<a id="sec-1-2"></a>

### About navi-mode<a id="sec-1-2-1"></a>

Navi-mode, as its name suggests, enables super-fast navigation and
easy structure-editing in Outshine or Org buffers via one-key
bindings in associated read-only **Navi** buffers.

You can think of a navi-buffer as a kind of 'remote-control' for an
(adecuately) outline-structured original-buffer. Besides navigation
and structure-editing, many common commands can be executed in the
original-buffer without (necessarily) leaving the navi-buffer. When
switching to the original-buffer and coming back after some
modifications, the navi-buffer is always reverted (thus
up-to-date).

Besides the many things that can be done from a navi-buffer, its
main benefit is to offer a flexible but persistent and rock-solid
overview side-by-side to the details of the original buffer. There
can be many different navi-buffers alive at the same time, each one
of them firmly connected to its associated original
buffer. Switching between the 'twin-buffers' is easy and
fast. Typically, an outline-structured original buffer in
'show-all' visibility state shares a splitted window with its
associated navi-buffer that either shows headlines, keywords, or a
combination of both. Instead of cycling visibility in the original
buffer itself it is often more convenient to quickly switch to its
navi-buffer and use its many different (over-)views.

Navi-mode is implemented on top of occur-mode and thus uses occur
as its 'search-engine'. It does not aim to replace occur-mode or to
compete with it, it rather specializes occur-mode for a certain
use-case. Using navi-mode for remotely controlling Outshine and Org
buffers does in no way interfere with occasionally calling 'M-x
occur' on these buffers.

Navi-mode is part of the Outshine project, consisting of the three
libraries outshine.el, outorg.el and navi-mode.el. For navi-mode to
work, the original buffer must be either an org-mode buffer or have
outline-minor-mode with outshine extensions activated (and be
structured with outshine headers, i.e. outcommented Org headers).

### Usage<a id="sec-1-2-2"></a>

Navi-mode is a special read-only mode (line e.g. occur-mode and
dired-mode), thus all its core commands have one-key
bindings. However, the command \`navi-edit-mode' makes the
navi-buffer editable. The edits are directly applied in the
associated original buffer. With command \`navi-cease-edit' the
default read-only mode is turned on again.

Navi-mode's functionality can be divided into the following
categories:

-   **headline searches:** keys '1' to '8' show all headlines up to that level

-   **keyword searches:** e.g. key 'f' shows functions in many major-modes

-   **combined headline and keyword searches:** e.g. 'C-3 v' shows
    variables and headlines up to level 3

-   **navigation commands:** e.g. keys 'n' and 'p' move to the
    next/previous line in the navi-buffer. These commands are
    especially useful in combination with keys 'd', 'o' and 's' that
    show the current position in the original buffer (or switch to
    it).

-   **action commands:** call functions on the thing-at-point in the
    navi-buffer, to be executed in the 'twin-buffer'.

Besides the mentioned fundamental outline-heading-searches (8
outline-levels) and the 5 basic keyword-searches (:FUN, :VAR, :DB,
:OBJ and :ALL), all languages can have their own set of searches
and keybindings (see customizable variables \`navi-key-mappings' and
\`navi-keywords').

Use 'M-s n' (\`navi-search-and-switch') to open a navi-buffer and
immediately switch to it. The new navi-buffer will show the
first-level headings of the original-buffer, with point at the
first entry. Here is an overview over the available commands in the
navi-buffer:

-   Show headlines (up-to) different levels:

<table border="2" cellspacing="0" cellpadding="6" rules="groups" frame="hsides">


<colgroup>
<col  class="left" />

<col  class="left" />

<col  class="left" />
</colgroup>
<thead>
<tr>
<th scope="col" class="left">key</th>
<th scope="col" class="left">command</th>
<th scope="col" class="left">function-name</th>
</tr>
</thead>

<tbody>
<tr>
<td class="left">1 &#x2026; 8</td>
<td class="left">show levels 1 to 8</td>
<td class="left">navi-generic-command</td>
</tr>
</tbody>
</table>

-   Navigate up and down in the search results shown in the navi-buffer:

<table border="2" cellspacing="0" cellpadding="6" rules="groups" frame="hsides">


<colgroup>
<col  class="left" />

<col  class="left" />

<col  class="left" />
</colgroup>
<thead>
<tr>
<th scope="col" class="left">key</th>
<th scope="col" class="left">command</th>
<th scope="col" class="left">function-name</th>
</tr>
</thead>

<tbody>
<tr>
<td class="left">p</td>
<td class="left">previous</td>
<td class="left">occur-prev</td>
</tr>


<tr>
<td class="left">n</td>
<td class="left">next</td>
<td class="left">occur-next</td>
</tr>


<tr>
<td class="left">DEL</td>
<td class="left">down page</td>
<td class="left">scroll-down-command</td>
</tr>


<tr>
<td class="left">SPC</td>
<td class="left">up page</td>
<td class="left">scroll-up-command</td>
</tr>
</tbody>
</table>

-   Revert the navi-buffer (seldom necessary), show help for the
    user-defined keyword-searches, and quit the navi-buffer and switch-back
    to the original-buffer:

<table border="2" cellspacing="0" cellpadding="6" rules="groups" frame="hsides">


<colgroup>
<col  class="left" />

<col  class="left" />

<col  class="left" />
</colgroup>
<thead>
<tr>
<th scope="col" class="left">key</th>
<th scope="col" class="left">command</th>
<th scope="col" class="left">function-name</th>
</tr>
</thead>

<tbody>
<tr>
<td class="left">g</td>
<td class="left">revert buffer</td>
<td class="left">navi-revert-function</td>
</tr>


<tr>
<td class="left">h</td>
<td class="left">show help</td>
<td class="left">navi-show-help</td>
</tr>


<tr>
<td class="left">q</td>
<td class="left">quit navi-mode and switch</td>
<td class="left">navi-quit-and-switch</td>
</tr>
</tbody>
</table>

-   Switch to the original-buffer and back to the navi-buffer, display an
    occurence in the original-buffer or go to the occurence:

<table border="2" cellspacing="0" cellpadding="6" rules="groups" frame="hsides">


<colgroup>
<col  class="left" />

<col  class="left" />

<col  class="left" />
</colgroup>
<thead>
<tr>
<th scope="col" class="left">key</th>
<th scope="col" class="left">command</th>
<th scope="col" class="left">function-name</th>
</tr>
</thead>

<tbody>
<tr>
<td class="left">M-s n</td>
<td class="left">launch navi-buffer</td>
<td class="left">navi-search-and-switch</td>
</tr>


<tr>
<td class="left">M-s s</td>
<td class="left">switch to other buffer</td>
<td class="left">navi-switch-to-twin-buffer</td>
</tr>


<tr>
<td class="left">M-s M-s</td>
<td class="left">&#xa0;</td>
<td class="left">&#xa0;</td>
</tr>


<tr>
<td class="left">s</td>
<td class="left">&#xa0;</td>
<td class="left">&#xa0;</td>
</tr>


<tr>
<td class="left">d</td>
<td class="left">display occurrence</td>
<td class="left">occur-mode-display-occurrence</td>
</tr>


<tr>
<td class="left">o</td>
<td class="left">goto occurrence</td>
<td class="left">navi-goto-occurrence-other-window</td>
</tr>
</tbody>
</table>

-   Structure editing on subtrees and visibility cycling

<table border="2" cellspacing="0" cellpadding="6" rules="groups" frame="hsides">


<colgroup>
<col  class="left" />

<col  class="left" />

<col  class="left" />
</colgroup>
<thead>
<tr>
<th scope="col" class="left">key</th>
<th scope="col" class="left">command</th>
<th scope="col" class="left">function-name</th>
</tr>
</thead>

<tbody>
<tr>
<td class="left">TAB</td>
<td class="left">cycle subtrees</td>
<td class="left">navi-cycle-subtree</td>
</tr>


<tr>
<td class="left"><backtab></td>
<td class="left">cycle buffer</td>
<td class="left">navi-cycle-buffer</td>
</tr>


<tr>
<td class="left">+</td>
<td class="left">Demote Subtree</td>
<td class="left">navi-demote-subtree</td>
</tr>


<tr>
<td class="left">-</td>
<td class="left">promote subtree</td>
<td class="left">navi-promote-subtree</td>
</tr>


<tr>
<td class="left">^</td>
<td class="left">move up subtree (same level)</td>
<td class="left">navi-move-up-subtree</td>
</tr>


<tr>
<td class="left"><</td>
<td class="left">move down subtree (same level)</td>
<td class="left">navi-move-down-subtree</td>
</tr>
</tbody>
</table>

-   Miscancellous actions on subtrees (there are more &#x2026;)

<table border="2" cellspacing="0" cellpadding="6" rules="groups" frame="hsides">


<colgroup>
<col  class="left" />

<col  class="left" />

<col  class="left" />
</colgroup>
<thead>
<tr>
<th scope="col" class="left">key</th>
<th scope="col" class="left">command</th>
<th scope="col" class="left">function-name</th>
</tr>
</thead>

<tbody>
<tr>
<td class="left">m</td>
<td class="left">mark thing at point</td>
<td class="left">navi-mark-thing-at-point-and-switch</td>
</tr>


<tr>
<td class="left">c</td>
<td class="left">copy thing at point</td>
<td class="left">navi-copy-thing-at-point-to-register-s</td>
</tr>


<tr>
<td class="left">k</td>
<td class="left">kill thing at point</td>
<td class="left">navi-kill-thing-at-point</td>
</tr>


<tr>
<td class="left">y</td>
<td class="left">yank killed/copied thing</td>
<td class="left">navi-yank-thing-at-point-from-register-s</td>
</tr>


<tr>
<td class="left">u</td>
<td class="left">undo last change</td>
<td class="left">navi-undo</td>
</tr>


<tr>
<td class="left">r</td>
<td class="left">narrow to thing at point</td>
<td class="left">navi-narrow-to-thing-at-point</td>
</tr>


<tr>
<td class="left">w</td>
<td class="left">widen</td>
<td class="left">navi-widen</td>
</tr>


<tr>
<td class="left">l</td>
<td class="left">query-replace</td>
<td class="left">navi-query-replace</td>
</tr>


<tr>
<td class="left">i</td>
<td class="left">isearch</td>
<td class="left">navi-isearch</td>
</tr>


<tr>
<td class="left">e</td>
<td class="left">edit as org (outorg)</td>
<td class="left">navi-edit-as-org</td>
</tr>


<tr>
<td class="left">.</td>
<td class="left">call fun on thing at point</td>
<td class="left">navi-act-on-thing-at-point</td>
</tr>
</tbody>
</table>

-   Furthermore, there are five (semantically) predefined keyword-searches:

<table border="2" cellspacing="0" cellpadding="6" rules="groups" frame="hsides">


<colgroup>
<col  class="left" />

<col  class="left" />

<col  class="left" />
</colgroup>
<thead>
<tr>
<th scope="col" class="left">key</th>
<th scope="col" class="left">keyword-symbol</th>
<th scope="col" class="left">searches for</th>
</tr>
</thead>

<tbody>
<tr>
<td class="left">f</td>
<td class="left">:FUN</td>
<td class="left">functions, macros etc.</td>
</tr>


<tr>
<td class="left">v</td>
<td class="left">:VAR</td>
<td class="left">vars, consts, customs etc.</td>
</tr>


<tr>
<td class="left">x</td>
<td class="left">:OBJ</td>
<td class="left">OOP (classes, methods etc)</td>
</tr>


<tr>
<td class="left">b</td>
<td class="left">:DB</td>
<td class="left">DB (store and select)</td>
</tr>


<tr>
<td class="left">a</td>
<td class="left">:ALL</td>
<td class="left">all</td>
</tr>
</tbody>
</table>

-   And (potentially) many more user-defined keyword-searches

(example Emacs Lisp):

    [KEY] : [SEARCH]
    ================
                            a : ALL
                            f : FUN
                            v : VAR
                            x : OBJ
                            b : DB
                            F : defun
                            V : defvar
                            C : defconst
                            G : defgroup
                            U : defcustom
                            A : defadvice
                            W : defalias
                            M : defmarcro
                            D : defface
                            S : defstruct
                            B : defsubst
                            L : defclass
                            I : define
                            J : declare
                            K : global-set-key
                            T : add-to-list
                            Q : setq
                            H : add-hook
                            O : hook
                            X : lambda
                            Z : ert
                            R : require

-   Headline-searches and keyword-searches can be combined, e.g.

    C-2 f

in an Emacs Lisp (outshine-)buffer shows all headlines up-to level 2 as
well as all function, macro and advice definitions in the original-buffer,

    C-5 a

shows all headlines up-to level 5 as well as all functions, variables,
classes, methods, objects, and database-related definitions. The exact
meaning of the standard keyword-searches 'f' and 'a' must be defined with a
regexp in the customizable variable \`navi-keywords' (just like the
user-defined keyword-searches).

When exploring a (potentially big) original buffer via navi-mode, a common
usage pattern is the following:

1.  type e.g '2'  and go to the relevant headline
2.  type 'r' and e.g. '3' in sequence to narrow buffers to the subtree at
    point and show one deeper level of headlines
3.  do your thing in the narrowed subtree
4.  type e.g. '2' and 'w' to first reduce the headline levels shown and
    then widen the buffers again.

### Installation<a id="sec-1-2-3"></a>

Install the three required libraries:

<table border="2" cellspacing="0" cellpadding="6" rules="groups" frame="hsides">


<colgroup>
<col  class="left" />

<col  class="left" />
</colgroup>
<tbody>
<tr>
<td class="left">navi-mode.el</td>
<td class="left">[navi-mode](https://github.com/tj64/navi)</td>
</tr>


<tr>
<td class="left">outshine.el</td>
<td class="left">[outshine](https://github.com/tj64/outshine)</td>
</tr>


<tr>
<td class="left">outorg.el</td>
<td class="left">[outorg](https://github.com/tj64/outorg)</td>
</tr>
</tbody>
</table>

from the package-manager via MELPA or clone their github-repos. Follow
the installation instructions in \`outshine.el' and \`outorg.el'.

Then install \`navi-mode.el' by adding

    (require 'navi-mode)

to your .emacs file.

### Emacs Version<a id="sec-1-2-4"></a>

\`navi-mode.el' works with [GNU Emacs 24.2.1 (x86\_64-unknown-linux-gnu,
GTK+ Version 3.6.4) of 2013-01-20 on eric]. No attempts of testing
with older versions or other types of Emacs have been made (yet).

## ChangeLog<a id="sec-1-3"></a>

<table border="2" cellspacing="0" cellpadding="6" rules="groups" frame="hsides">


<colgroup>
<col  class="left" />

<col  class="left" />

<col  class="right" />
</colgroup>
<thead>
<tr>
<th scope="col" class="left">date</th>
<th scope="col" class="left">author(s)</th>
<th scope="col" class="right">version</th>
</tr>
</thead>

<tbody>
<tr>
<td class="left"><span class="timestamp-wrapper"><span class="timestamp">&lt;2014-09-20 Sa&gt;</span></span></td>
<td class="left">Thorsten Jolitz</td>
<td class="right">2.0</td>
</tr>


<tr>
<td class="left"><span class="timestamp-wrapper"><span class="timestamp">&lt;2013-05-03 Fr&gt;</span></span></td>
<td class="left">Thorsten Jolitz</td>
<td class="right">1.0</td>
</tr>


<tr>
<td class="left"><span class="timestamp-wrapper"><span class="timestamp">&lt;2013-03-11 Mo&gt;</span></span></td>
<td class="left">Thorsten Jolitz</td>
<td class="right">0.9</td>
</tr>
</tbody>
</table>
