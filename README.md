- [What is gitpatch](#org173272d)
  - [Installation](#org0c24685)
  - [Configure](#orgeae6b5c)
  - [Usage](#org852955e)
    - [gitpatch-mail](#orgcc5adf7)


<a id="org173272d"></a>

# What is gitpatch

Gitpatch is git-format patch toolkit, which let user easy handle git-format patch without exit Emacs.

1.  Send patch with \`gitpatch-mail'

    \`gitpatch-mail' can quick send a git-format patch file from magit, dired or ibuffer buffer.


<a id="org0c24685"></a>

## Installation

1.  Config melpa source, please read: <http://melpa.org/#/getting-started>
2.  M-x package-install RET gitpatch RET


<a id="orgeae6b5c"></a>

## Configure

    (require 'gitpatch)
    (setq gitpatch-mail-attach-patch-key "C-c i")


<a id="org852955e"></a>

## Usage


<a id="orgcc5adf7"></a>

### gitpatch-mail

1.  Move the point to the patch-name in magit-status, dired or ibuffer buffer.
2.  M-x gitpatch-mail
3.  Select an email address as TO Field, if you set \`gitpatch-mail-database'.
4.  Add another patch with "C-c i" by default (Optional).
5.  Edit and send email.

NOTE: User can config \`gitpatch-mail' in other type buffer with the help of \`gitpatch-mail-get-patch-functions'


Converted from gitpatch.el by [el2org](https://github.com/tumashu/el2org) .