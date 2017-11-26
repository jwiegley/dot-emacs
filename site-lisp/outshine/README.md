- [outshine.el &#x2014; outline with outshine outshines outline](#outshine.el-&#x2014;-outline-with-outshine-outshines-outline)
  - [MetaData](#metadata)
  - [Commentary](#commentary)
    - [About outshine](#about-outshine)
    - [History and Credits](#history-and-credits)
    - [Installation](#installation)
    - [Usage](#usage)
    - [Emacs Version](#emacs-version)
  - [ChangeLog](#changelog)

# outshine.el &#x2014; outline with outshine outshines outline<a id="sec-1"></a>

Maintainer: Adam Porter
Version: 2.0
URL: <https://github.com/alphapapa/outshine>

## MetaData<a id="sec-1-1"></a>

    copyright: Thorsten_Jolitz
    
    copyright-from: 2013+
    
    version: 2.0
    
    licence: GPL 2 or later (free software)
    
    licence-url: http://www.gnu.org/licenses/
    
    part-of-emacs: no
    
    authors: Thorsten_Jolitz Carsten_Dominik Per_Abrahamsen
    
    credits: Fabrice_Niessen Alexander_Vorobiev Jonas_Bernoulli
    
    inspiration: outline-magic outxxtra out-xtra
    
    keywords: emacs outlines file_structuring
    
    git-repo: https://github.com/alphapapa/outshine.git
    
    git-clone: git://github.com/alphapapa/outshine.git

## Commentary<a id="sec-1-2"></a>

### About outshine<a id="sec-1-2-1"></a>

Outshine attempts to bring the look&feel of Org-mode to the (GNU
Emacs) world outside of the Org major-mode. It is an extension of
outline-minor-mode (Org-mode itself derives from outline-mode), so
there is no such thing like an 'outshine mode', only
\`outline-minor-mode' with outshine extensions loaded.

Outshine is major-mode agnostic. At least in theory, it should work
out-of-the-box with all major-modes, even those not yet written, as
long as these modes have comment syntax defined. In real life there
are some major-modes where outshine just works, others that need
some minor tweaks to make outshine work, and a few that need
special handling.

An outshine file is structured just like an org file, only that the
headlines are outcommented with the current major-mode's comment
syntax. We call these outcommented org headers 'outshine
headers'. The different headline levels are fontified like in
Org-mode, and many of the outline-navigation, visibility cycling
and structure editing commands known from Org-mode work in outshine
too. An Org-mode user will feel right at home in an outshine
buffer, the look&feel should be pretty similar, only the
keybindings differ. Since outshine extends a minor-mode it has to
avoid conflicts with major-mode keymaps by using a rather unusual
prefix that is still easy to type (M-#). But the Org-mode
speed-commands have been ported to outshine too, and they use
exactly the same (one-key) bindings like in Org-mode.

There is a distinction between the library 'outshine.el' and the
'Outshine Project' (or 'Outshine Suite') which contains 3
libraries:

-   **outshine.el:** The core library. The \`outshine-hook-function'
    must be added to the \`outline-minor-mode-hook' to
    activate its extensions when outline-minor-mode
    is loaded.

-   **outorg.el:** Major-mode for toggling between the
    programming-mode view and the org-mode view of
    outshine buffers, i.e. buffers structured with
    outshine headers that have outline-minor-mode with
    outshine extensions activated.

-   **navi-mode.el:** Occur-based major-mode for super-fast
    buffer-navigation and buffer-remote-control with
    one-key-bindings from an associated read-only
    **Navi** buffer. Navi-mode allows to have the
    (outshine- or org-) buffer overview side by side
    with the buffer details, and it gives many
    different kinds of overviews (these views are
    actually customizable). With point in the **Navi**
    overview buffer, many actions in the associated
    original (outshine- or org-) buffer can be
    triggered without leaving the **Navi** buffer.

Note that there is a fourth library 'poporg.el' from François
Pinard, which allows to edit function docstrings in temporary
Org-mode buffers and thus nicely complements 'outorg.el'.

Together these libraries enable a lightweight kind of 'literate
programming' that turns the usual implementation of the concept
upside-down: instead of using a text-mode as default and taking
extra action to edit and execute source-code, with Outshine the
programming-mode is the default mode and the text-mode
(i.e. Org-mode) only called when needed. This is much simpler, it
treats Org-mode and Programming-mode simply as two different views
on the same (outshine) file while making it easy to switch between
these views.

### History and Credits<a id="sec-1-2-2"></a>

The original author of outshine.el is Thorsten Jolitz, who transferred
maintainership to Adam Porter in April 2017.

The outshine.el library merges, modifies and extends two existing
extension-libraries for \`outline' (minor) mode: \`outline-magic' (by
Carsten Dominik) and \`out-xtra' (by Per Abrahamsen). It offers all the
functionality of \`outline-magic' (with some tiny changes and fixes)
and parts of the functionality of \`out-xtra', together with many new
features and ideas.

See \`outline-magic.el' (<https://github.com/tj64/outline-magic>) for
detailled instructions on the usage of the additional outline
functions introduced by \`outline-magic'.

Furthermore, \`outshine.el' includes some functions and keybindings
from \`outline-mode-easy-bindings'
(<http://emacswiki.org/emacs/OutlineMinorMode>).  Unfortunately, no
author is given for that library, so I cannot credit the person who
wrote it.

### Installation<a id="sec-1-2-3"></a>

There are three ways to get outshine.el (and the other Outshine
libraries):

1.  Clone the git repos or fork them on github
    (<https://github.com/alphapapa>)

2.  Use the package manager to install them (from MELPA).

3.  Simply download the raw .el files from github and copy them to a
    location where Emacs can find them. This is not really recommended,
    since easy updating is not possible this way.

Note that since version 2.0, outshine.el depends on outorg.el and
navi-mode.el depends on both, outshine.el and outorg.el. So the order
of installation should be 

1.  outorg
2.  outshine
3.  navi-mode (optional)

Put this in your init.el or '.emacs' to get started:

    #+begin_src emacs-lisp
      (require 'outshine)
      (add-hook 'outline-minor-mode-hook 'outshine-hook-function)
    #+end_src

Add this to your init file if you always want outshine for emacs-lisp
buffers (recommended):

    #+begin_src emacs-lisp
      (add-hook 'emacs-lisp-mode-hook 'outline-minor-mode)
    #+end_src

It makes sense to add 'outline-minor-mode' to the hooks of other
major-modes too, e.g.

    #+begin_src emacs-lisp
     (add-hook 'LaTeX-mode-hook 'outline-minor-mode)
     (add-hook 'picolisp-mode-hook 'outline-minor-mode)
     (add-hook 'clojure-mode-hook 'outline-minor-mode)
     (add-hook 'ess-mode-hook 'outline-minor-mode)
     (add-hook 'ledger-mode-hook 'outline-minor-mode)
     (add-hook 'message-mode-hook 'outline-minor-mode)
    #+end_src

or whatever your favorite Emacs modes are. Then you can structure and
handle all your source-files just like Org files, allowing for a
uniform approach to file structuring independent from the (text or
programming) mode.

Outline(-minor)-mode comes with a rather unusable prefix key
out-of-the-box. You need to set the outshine prefix (M-#) in your init
file before (!) outline-mode is loaded to enable the outshine
keybindings:

    #+begin_src emacs-lisp
     (defvar outline-minor-mode-prefix "\M-#")
    #+end_src

### Usage<a id="sec-1-2-4"></a>

1.  Basic Usage

    The outshine.el extensions to outline-minor-mode aim to make its
    use more similar to Org-mode. Given a correctly structured outshine
    buffer, outline-navigation, structure-editing and visibility
    cycling with outshine should make an Org-mode user feel right at
    home.
    
    Try C-h m (describe-mode) and C-h b (describe-bindings) in an
    outshine buffer to find out more about the available functions and
    their keybindings.
    
    The very useful Org speed-commands have been ported to outshine,
    here a quote from the
    [Org-mode manual](http://orgmode.org/manual/Speed-keys.html) that
    describes what they do:
    
    > Single keys can be made to execute commands when the cursor is at
    > the beginning of a headline, i.e., before the first star.
    
    To activate speed-keys, put this in your init-file:
    
        #+BEGIN_SRC emacs-lisp
         (setq outshine-use-speed-commands t)
        #+END_SRC
    
    Call \`outshine-speed-command-help' to get an overview over the
    available functionality and the keybindings.
    
    Note that outshine works with 'imenu' (\`outshine-imenu') and has
    extra functionality to show the number of hidden lines in folded
    headlines (\`outshine-show-hidden-lines-cookies'). There are a few
    utility commands for latex-mode too
    (\`outshine-latex-insert-header',
    \`outshine-latex-insert-headers-in-buffer' and
    \`outshine-TeX-command-region-on-subtree')

2.  Extended Usage (outshine-use-outorg)

    Outshine's basic usage is mostly based on its own implementation,
    i.e. code from existing extensions to outline-minor-mode, new code
    written for outshine, as well as code ported from Org-mode to
    outshine.
    
    Its extended use aims to make outshine headers more 'intelligent',
    i.e. make them know about TODO items, tags, properties, dates and
    times. This is done via the \`outshine-use-outorg' function that
    uses outorg to first convert an outshine buffer/subtree to
    org-mode, then call an Org function on it, and finally convert the
    edited buffer/subtree back to outshine. The outshine-use-outorg
    concept turns outshine into a kind of org-minor-mode without
    actually reimplementing Org functionality, just by reusing it with
    the help of outorg.
    
    This is still work in progress. Not all Org commands make sense in
    an outshine buffer. Not all work out-of-the-box. Since there are
    many Org commands, it will take some time to check them one-by-one
    and filter out those that make sense with outshine (and fix them if
    necessary).

### Emacs Version<a id="sec-1-2-5"></a>

Outshine works with GNU Emacs 24 or later. No attempts of testing
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
<td class="left"><span class="timestamp-wrapper"><span class="timestamp">&lt;2013-02-20 Mi&gt;</span></span></td>
<td class="left">Thorsten Jolitz</td>
<td class="right">0.9</td>
</tr>
</tbody>
</table>
