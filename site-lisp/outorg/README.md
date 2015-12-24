- [outorg.el &#x2014; Org-style comment editing](#outorg.el-&#x2014;-org-style-comment-editing)
  - [MetaData](#metadata)
  - [Commentary](#commentary)
    - [About outorg](#about-outorg)
    - [Usage](#usage)
    - [Installation](#installation)
    - [Bugs and Shortcomings](#bugs-and-shortcomings)
    - [Tests](#tests)
    - [Emacs Version](#emacs-version)
  - [ChangeLog](#changelog)



# outorg.el &#x2014; Org-style comment editing<a id="sec-1"></a>

Author: Thorsten Jolitz <tjolitz AT gmail DOT com>
Version: 2.0
URL: <https://github.com/tj64/outorg>

## MetaData<a id="sec-1-1"></a>

    copyright: Thorsten Jolitz
    
    copyright-years: 2013+
    
    version: 2.0
    
    licence: GPL 2 or later (free software)
    
    licence-url: http://www.gnu.org/licenses/
    
    part-of-emacs: no
    
    author: Thorsten Jolitz
    
    author_email: tjolitz AT gmail DOT com
    
    inspiration: org-src
    
    keywords: emacs org-mode comment-editing
    
    git-repo: https://github.com/tj64/outorg
    
    git-clone: git://github.com/tj64/outorg.git

## Commentary<a id="sec-1-2"></a>

### About outorg<a id="sec-1-2-1"></a>

Outorg is for editing comment-sections of source-code files in
temporary Org-mode buffers. It turns conventional
literate-programming upside-down in that the default mode is the
programming-mode, and special action has to be taken to switch to the
text-mode (i.e. Org-mode). 

Outorg depends on Outshine, i.e. outline-minor-mode with outshine
extensions activated. An outshine buffer is structured like an
org-mode buffer, only with outcommented headlines. While in
Org-mode text is text and source-code is 'hidden' inside of special
src-blocks, in an outshine buffer source-code is source-code and
text is 'hidden' as comments.

Thus org-mode and programming-mode are just two different views on
the outshine-style structured source-file, and outorg is the tool
to switch between these two views. When switching from a
programming-mode to org-mode, the comments are converted to text
and the source-code is put into src-blocks. When switching back
from org-mode to the programming-mode, the process is reversed -
the text is outcommented again and the src-blocks that enclose the
source-code are removed.

When the code is more important than the text, i.e. when the task
is rather 'literate PROGRAMMING' than 'LITERATE programming', it is
often more convenient to work in a programming-mode and switch to
org-mode once in a while than vice-versa. Outorg is really fast,
even big files with 10k lines are converted in a second or so, and
the user decides if he wants to convert just the current subtree
(done instantly) or the whole buffer. Since text needs no session
handling or variable passing or other special treatment, the outorg
approach is much simpler than the Org-Babel approach. However, the
full power of Org-Babel is available once the **outorg-edit-buffer**
has popped up.

### Usage<a id="sec-1-2-2"></a>

Outorg (like outshine) assumes that you set
\`outline-minor-mode-prefix' in your init-file to 'M-#':

    ;; must be set before outline is loaded
    (defvar outline-minor-mode-prefix "\M-#")

Outorg's main command is 

    M-# # (or M-x outorg-edit-as-org)

to be used in source-code buffers where \`outline-minor-mode' is
activated with \`outshine' extensions. The Org-mode edit-buffer popped
up by this command is called **outorg-edit-buffer** and has
\`outorg-edit-minor-mode' activated, a minor-mode with only 2 commands:

    M-# (outorg-copy-edits-and-exit)
    C-x C-s (outorg-save-edits-to-tmp-file)

If you want to insert Org-mode source-code or example blocks in
comment-sections, i.e. you don't want outorg to remove the
enclosing blocks, simply outcomment them in the outorg-edit buffer
before calling \`outorg-copy-edits-and-exit'.

Note that outorg only treats 'active' src-blocks in a special way -
the blocks whose Babel language is equal to the major-mode of the
associated programming-mode buffer. All other (src-) blocks are
treated like normal text.

Note further that outorg uses example-blocks as 'fallback' when it
cannot find the major-mode of the programming-mode buffer in the
\`org-babel-load-languages'. In this case you should not use
example-blocks for other tasks, since they will be removed when
exiting the **outorg-edit-buffer**, use e.g. quote-blocks or
verse-blocks instead.

### Installation<a id="sec-1-2-3"></a>

You can get outorg.el either from Github (see section MetaData) or
via MELPA. It depends on outshine.el, so you have to install and
configure outshine first to make outorg work.

Installation is easy, simply insert

    (require 'outorg)

in your init file. When you use navi-mode.el too, the third Outshine
library, it suffices to (require 'navi), since it requires the other
two libraries. 

### Bugs and Shortcomings<a id="sec-1-2-4"></a>

Outorg started out purely line-based, it only worked with
'one-line' comments, i.e. with comment-sections like those produced
by \`comment-region' (a command that comments or uncomments each
line in the region). It was enhanced later on to recognize comment
regions too, i.e. those special multi-line comments found in many
programming languages. But using outorg on such multi-line comments
will probably change their syntax back to 'single-line', whenever
\`comment-region' uses this style.

### Tests<a id="sec-1-2-5"></a>

A special kind of test has been developed for outorg using the
\`ert-buffer' library, the so called 'conversion test'. It has the
following steps:

1.  programming-mode -> org-mode

2.  edit in org-mode, store undo-information

3.  org-mode -> programming-mode

4.  programming-mode -> org-mode (again)

5.  undo edits

6.  org-mode -> programming-mode (again)

After these 4 conversions, the original programming-mode buffer
must be unchanged when the conversion process is perfect, i.e. does
not introduce any changes itself. See \`outorg-test.el' for details.

### Emacs Version<a id="sec-1-2-6"></a>

Outorg works with GNU Emacs 24.2.1 or later. No attempts of testing
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
<td class="left"><span class="timestamp-wrapper"><span class="timestamp">&lt;2013-02-11 Mo&gt;</span></span></td>
<td class="left">Thorsten Jolitz</td>
<td class="right">0.9</td>
</tr>
</tbody>
</table>
