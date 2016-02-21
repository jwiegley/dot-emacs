# Proof General — Organize your proofs! 

Proof General is a generic Emacs interface for proof assistants.
The aim of the Proof General project is to provide a powerful, generic
environment for using interactive proof assistants.

This is version 4.4pre of Proof General.

## Setup

Remove old versions of Proof General, then download and install the new release from GitHub:

```
git clone https://github.com/ProofGeneral/PG ~/.emacs.d/lisp/PG
cd ~/.emacs.d/lisp/PG
make
```

Then add the following to your `.emacs`:

```
;; Open .v files with Proof General's Coq mode
(load "~/.emacs.d/lisp/PG/generic/proof-site")
```

If Proof General complains about a version mismatch, make sure that the shell's `emacs` is indeed your usual Emacs. If not, run the Makefile again with an explicit path to Emacs. On Mac in particular you'll probably need something like

```
make clean; make EMACS=/Applications/Emacs.app/Contents/MacOS/Emacs
```

## More info

See

    INSTALL	     for installation details.
    COPYING	     for license details.
    COMPATIBILITY    for version compatibility information.
    REGISTER	     for registration information (please register).
    FAQ, doc/	     for documentation of Proof General.

    <prover>/README  for additional prover-specific notes

Links:

    Wiki:		  http://proofgeneral.inf.ed.ac.uk/wiki
    Lists:		  http://proofgeneral.inf.ed.ac.uk/mailinglist

* Supported proof assistants:  Coq, Isabelle, LEGO, PhoX
* Experimental (less useful):  CCC,ACL2,HOL98,Hol-Light,Lambda-Clam,Shell,Twelf
* Obsolete instances:  Demoisa,Lambda-Clam,Plastic

A few example proofs are included in each prover subdirectory.  The
"root2" proofs of the irrationality of the square root of 2 were
proofs written for Freek Wiedijk's challenge in his comparison of
different theorem provers, see http://www.cs.kun.nl/~freek/comparison/.  
Those proof scripts are copyright by their named authors.  
(NB: most of these have rusted)
