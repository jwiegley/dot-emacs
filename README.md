hsenv - Virtual Haskell Environment
===================================

What is it?
-----------
hsenv is a tool (inspired by Python's virtualenv)
to create isolated Haskell environments.


What does it do?
----------------
It creates a sandboxed environment in a .hsenv/ subdirectory of your project,
which, when activated, allows you to use regular Haskell tools (ghc, ghci,
ghc-pkg, cabal) to manage your Haskell code and environment. It's possible to
create an environment, that uses a different GHC version than your currently
installed system GHC version. Very simple emacs integration mode is included.

Basic usage
-----------
First, choose a directory where you want to keep your
sandboxed Haskell environment, usually a good choice is a directory containing
your cabalized project (if you want to work on a few projects
(perhaps an app and its dependent library), just choose any of them,
it doesn't really matter). Enter that directory:

```bash
cd ~/projects/foo
```

Next, create your new isolated Haskell environment
(this is a one-time-only (per environment) step):

```bash
hsenv
```

Now, every time you want to use this environment, you have to activate it:

```bash
source .hsenv/bin/activate
```

That's it! Now it's possible to use all regular Haskell tools like usual, but
it won't affect your global/system Haskell environment, and also your per-user
environment (from ~/.cabal and ~/.ghc) will stay the same. All cabal-installed
packages will be private to this environment, and the external environments
(global and user) will not affect it (this environment will only inherit very
basic packages, mostly ghc and Cabal and their deps).

When you're done working with this environment, enter command `deactivate_hsenv`,
or just close the current shell (with exit).

```bash
deactivate_hsenv
```

Named vs Unnamed Environments
-----------------------------

By default, hsenv creates an "unnamed" environment, but sometimes for
particular use cases you might want to create different environments under
the same directory. This is achievable creating a "named" environment. To
do that, just pass the flag `--name=<ENVIRONMENT_NAME>` to hsenv:

```bash
hsenv --name=<ENVIRONMENT_NAME>
```

This will make hsenv generate a folder of the form `.hsenv_<ENVIRONMENT_NAME>`.

Customization
-------------

If you want to customize activation and deactivation, create one or more of the
following files in ~/.hsenv/bin/: pre-activate, post-activate, pre-deactivate,
post-deactivate. These shell scripts will be sourced automatically by the main
activation script.

Advanced usage
--------------
Here's the most advanced usage of hsenv. Let's say you want to:

* Hack on a json library
* Do so comfortably
* Use your own version of the parsec library
* And do all this using the nightly version of GHC

First, download the binary distribution of GHC for your platform
(e.g. ghc-7.3.20111105-i386-unknown-linux.tar.bz2).

Create a directory for you environment:

```bash
mkdir /tmp/test
cd /tmp/test
```

Then, create a new environment using that GHC:

```bash
hsenv --name=test --ghc=/path/to/ghc-7.3.20111105-i386-unknown-linux.tar.bz2
```

Activate it:

```bash
source .hsenv_test/bin/activate
```

Download a copy of json library and your private version of parsec:

```bash
darcs get http://patch-tag.com/r/Paczesiowa/parsec
cabal unpack json
```

Install parsec:

```bash
cd parsec2
cabal install
```

Install the rest of the json deps:

```bash
cd ../json-0.5
cabal install --only-dependencies
```

Now, let's say you want to hack on Parsec module of json library.
Open it in emacs:

```bash
emacsclient Text/JSON/Parsec.hs
```

Activate the virtual environment (hsenv must be required earlier):

```
M-x hsenv-activate <RET> /tmp/test/ <RET>
```

Edit some code and load it in ghci using 'C-c C-l'. If it type checks,
you can play around with the code using nightly version of ghci running
in your virtual environment. When you're happy with the code, exit emacs
and install your edited json library:

```bash
cabal install
```

And that's it.

Fetching and downloading a remote version of GHC
------------------------------------------------

Recent versions of hsenv include the possibility to automatically download and
install a GHC version directly from the GHC main repository. To do that, all
you need to do is to pass the desired version of GHC you want to install:

```bash
hsenv --ghc=7.4.1
```

Or a valid URL pointing to a compressed GHC archive:

```bash
hsenv --ghc=http://www.haskell.org/ghc/dist/7.6.3/ghc-7.6.3-x86_64-apple-darwin.tar.bz2
```

Misc
----

hsenv has been tested on Linux, Mac OS X, and FreeBSD systems, but it should
work on any POSIX platform. The external (from tarball) GHC feature requires
a binary GHC distribution compiled for your platform which that can be
extracted with tar and installed with "./configure --prefix=PATH; make
install".

FAQ
---
**Q: Can I use it together with tools like cabal-dev or capri?**

A: No. All these tools work more or less the same (wrapping cabal command,
   setting GHC_PACKAGE_PATH env variable), so something will probably break.


**Q: Using GHC from tarball fails with a bunch of make tool gibberish on
FreeBSD. What do I do?**

A: Try the '--make-cmd=gmake' switch.


**Q: Can I use hsenv inside hsenv?**

A: No. It may be supported in future versions.


**Q: Does it work on x64 systems?**

A: Yes.


**Q: Will it work on Mac?**

A: Yes.


**Q: Will it work on Windows?**

A: I really doubt it would even compile. I don't have access to any Windows
   machines, so you're on your own, but patches/ideas/questions are welcome.
   Maybe it would work on Cygwin.


**Q: Does it require Bash?**

A: No, it should work with any POSIX-compliant shell. It's been tested with
   bash, bash --posix, dash, zsh and ksh.


**Q: Can I use it with a different haskell package repository than hackage?**

A: Yes, just adjust the url in .hsenv/cabal/config file.


**Q: How do I remove the whole virtual environment?**

A: If it's activated - 'deactivate_hsenv' it. Then, delete
   the .hsenv/ directory.


**Q: Is every environment completely separate from other environments and
   the system environment?**

A: Yes. The only (minor) exception is ghci history - there's only one
   per user history file. Also, if you alter your system's GHC, then
   virtual environments using system's GHC copy will probably break.
   Virtual environments using GHC from a tarball should continue to work.


**Q: Can I share one cabalized project directory among multiple environments
(e.g. build a cabalized project in the same directory using different
environments)?**

A: Yes. hsenv also overrides cabal with a wrapper, that will force using
different build directories, so there shouldn't be even any recompilation
between different environments.


**Q: Is it possible to activate an environment upon entering its directory?**

A: Yes, if you really know what you're doing. Here's a snippet for bash, which
   will activate both named and unnamed environments:

```bash
    function precmd() {
        if [[ -z $HSENV ]]; then
            NUMBER_OF_ENVS=$(find . -maxdepth 1 -type d -name ".hsenv*" | wc -l)
            case ${NUMBER_OF_ENVS} in
                "0") ;;
                "1") source .hsenv*/bin/activate;;
                *) echo multiple environments, manual activaton required;;
            esac
        fi
    }
    export PROMPT_COMMAND=precmd
```


**Q: Can I use hsenv on a machine, that doesn't have cabal binary (from
     cabal-install package) installed?**

A: Yes. Just use the '--bootstrap-cabal' switch. In fact, you can use hsenv on
   a machine that doesn't have anything Haskell-related installed - just
   combine '--ghc=' and '--bootstrap-cabal' options.
