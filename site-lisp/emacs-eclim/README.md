## Overview
[Eclim](http://eclim.org) is an Eclipse plugin which exposes Eclipse
features through a server interface.  When this server is started, the
command line utility eclim can be used to issue requests to that
server. 

Emacs-eclim uses the eclim server to integrate eclipse with
emacs. This project wants to bring some of the invaluable features
from eclipse to emacs. Please note, emacs-eclim **is limited to mostly java support at this time.**

It is also possible to start and stop the eclim daemon from emacs using the
`eclimd` package.

You can ask questions or discuss new features at our [Google Group](https://groups.google.com/forum/#!forum/emacs-eclim)

> *NOTE: This project is currently unmaintained. We are looking for a new [maintainer](https://github.com/senny/emacs-eclim/issues/155).*

## A note about Eclim versions

Prior to version 1.7.3, eclim used a proprietary protocol for
communication with the eclim server. If you are running one of these
older versions, you need version 0.1 of emacs-eclim.

Eclim versions 1.7.3 and later however, serves responses using a
standard JSON format. These are supported by emacs-eclim versions 0.2
and later.

Emacs-eclim versions are tagged with the appropriate version
number. You can see and download previous releases
[here](https://github.com/senny/emacs-eclim/tags).

## Installation

1. [Download and install](http://eclim.org/install.html) eclim.
1. Install emacs-eclim. You have two options:
   * Installation from the [MELPA][melpa] package archive. Just add
   the archive to `package-archives` if you haven't already, and then
   install emacs-eclim with the `package-install` command.
   * Manual installation from GitHub. 
       1. (`git clone git://github.com/senny/emacs-eclim.git`)
       1. Add `(add-to-list 'load-path "/path/to/emacs-eclim/")` to your startup script.
1. Add the following code to your emacs startup script

```lisp
(require 'eclim)
(global-eclim-mode)
```

If you want to control eclimd from emacs, also add:

```lisp
(require 'eclimd)
```


## Configuration

### Eclipse installation

Emacs-eclim tries its best to locate your Eclipse installation.  If
you have Eclipse installed in a non-standard location
(i.e. ~/nonStandard/eclipse or /opt/eclipse) you may specify the paths manually by adding this to your startup script:

```lisp
(custom-set-variables
  '(eclim-eclipse-dirs '("~/nonStandard/eclipse"))
  '(eclim-executable "~/nonStandard/eclipse/eclim"))
```

### Displaying compilation error messages in the echo area

When the cursor is positioned on an error marker in a code buffer,
emacs-eclim uses the local help feature in emacs to display the
corresponding error message in the echo area. You can either invoke
`(display-local-help)` manually or activate automatic display of local
help by adding the following to .emacs:

```lisp
(setq help-at-pt-display-when-idle t)
(setq help-at-pt-timer-delay 0.1)
(help-at-pt-set-timer)
```

### Configuring auto-complete-mode

If you wish to use [auto-complete-mode] with emacs-eclim, add the
following to your .emacs:

```lisp
;; regular auto-complete initialization
(require 'auto-complete-config)
(ac-config-default)

;; add the emacs-eclim source
(require 'ac-emacs-eclim-source)
(ac-emacs-eclim-config)
```

### Configuring company-mode

Emacs-eclim can integrate with [company-mode] to provide pop-up
dialogs for auto-completion. To activate this, you need to add the
following to your .emacs:

```lisp
(require 'company)
(require 'company-emacs-eclim)
(company-emacs-eclim-setup)
(global-company-mode t)
```

### Configuring eclimd module

When `emacs-eclim` is configured correctly, you don't need to modify the
configuration for the `eclimd` package. Still, there are some configurable
variables you can tweak:

1. `eclimd-executable`: This variable is used for locating the `eclimd`
   executable file. You can set it to `nil` ("Same directory as eclim-executable
   variable" choice in customization screen) to indicate that the executable is in
   the same directory as the `eclim` program. Alternatively, you can give it a
   string value ("Custom value" choice in customization screen) to specify the
   location of the executable.

1. `eclimd-default-workspace`: When `start-eclimd` is executed, it will ask for
   the workspace directory to use. The default value for this question is
   controlled by this variable.

1. `eclimd-wait-for-process`: Normally, when `start-eclimd` starts the eclimd
   process, it pauses emacs until `eclimd` is ready to accept commands. If you
   change the value of this variable to `nil`, `start-eclimd` will return as
   soon as `eclimd` is started. Eclimd startup takes several seconds, so if you
   change the default value of this variable, `emacs-eclim` commands will fail
   until `eclimd` is ready.

## Dependencies
* [s.el](https://github.com/magnars/s.el) for string manipulation functions
* json.el (part of emacs as of version 23)

## Optional dependencies
* A recent version (0.6.0 or later) of [yasnippet]
* A recent version (tested with 0.5) of [company-mode]
* A recent version (tested with 1.4) version of [auto-complete-mode]
* ido-mode (part of emacs as of version 22)

## Usage
To get started just launch the eclim executable that the placed in
your Eclipse installation directory.

* [Projects](http://wiki.github.com/senny/emacs-eclim/projects)
* [Code Completion](http://wiki.github.com/senny/emacs-eclim/code-completion)
* [Java](http://wiki.github.com/senny/emacs-eclim/java)
* [Ant](http://wiki.github.com/senny/emacs-eclim/ant)
* [Maven](http://wiki.github.com/senny/emacs-eclim/maven)
* [Problems and Errors](http://wiki.github.com/senny/emacs-eclim/problems-and-errors)

### Controlling eclimd

When you import the `eclimd` package, you will have access to two commands:
`start-eclimd`, and `stop-eclimd`.

`start-eclimd` will ask for a workspace directory, and it will attempt to start
`eclimd` program with the entered workspace directory. The configurable variable
`eclimd-default-workspace` controls the default value of this directory. After
`start-eclimd` runs the daemon, it will monitor its log output, and wait for the
message that indicates that it is ready to accept commands. This is done to
prevent failures with `emacs-eclim` commands while `eclimd` is starting up.
While `start-eclimd` is waiting for the daemon to be ready, emacs will not
accept any user input. To prevent this pause, you can modify the configurable
variable `eclimd-wait-for-process`.

Normally, simply killing the buffer `*eclimd*` will allow you to stop the eclimd
daemon. However, there is a command to perform a graceful shutdown:
`stop-eclimd`. You should use this command when you wish to stop the `eclimd`
program.

## Press

Read more about emacs-eclim:

* [Enterprise Java Development in Emacs](http://www.skybert.net/emacs/java/), \[Torstein Krause Johansen\]
* [The Ballad of Emacs-Eclim](http://mulli.nu/2012/02/02/the-ballad-of-emacs-eclim.html), \[Fredrik Appelberg\]
* [Emacs and Java](http://blog.senny.ch/blog/2012/10/13/emacs-and-java-journey-of-a-hard-friendship/), \[Yves Senn\]
* [Java Autocompletion for Emacs](http://root42.blogspot.ch/2012/08/java-autocompletion-for-emacs.html), \[root42\]
* [Eclim: Eclipse Meets Vim And Emacs](http://faruk.akgul.org/blog/eclim-eclipse-meets-vim-emacs/), \[Faruk Akgul\]

## Contributing

Have a quick look at our [Contribution Guidelines](CONTRIBUTING.md)
and hack away.

[yasnippet]:http://code.google.com/p/yasnippet/
[company-mode]:http://nschum.de/src/emacs/company-mode/
[auto-complete-mode]:http://cx4a.org/software/auto-complete/
[melpa]:http://melpa.milkbox.net/
[repo]:https://github.com/senny/emacs-eclim

[![githalytics.com alpha](https://cruel-carlota.pagodabox.com/1d9209f5584dec16ce325c6d70631963 "githalytics.com")](http://githalytics.com/senny/emacs-eclim)
