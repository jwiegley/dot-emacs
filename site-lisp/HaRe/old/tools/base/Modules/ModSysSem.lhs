> module ModSysSem(mProgram) where
>
> import Modules
> import CheckModules
> import ModSysAST
> import NamesEntities
> import Relations(Rel,emptyRel)

The semantics of a Haskell program
==================================
\label{SemProg}

Having defined the meaning of imports and exports, and how to detect errors,
we can now glue everything together and define the meaning of a Haskell
program.

The semantics of a Haskell program (with respect to the module system)
is a mapping from a collection of modules to their corresponding in-scope
and export relations.  It can be given by a function of type:

> mProgram ::
>   [Module] -> Either [[ModSysErr]]
>		       [(Rel QName Entity,Rel Name Entity)]

Given a list of modules, the function either reports a list of
errors found in each module, or returns the in-scope and export
relations of the modules. There is a one-to-one correspondence between
positions in the module list and positions in the resulting lists.

Using the functions defined Sections~\ref{Sem} and \ref{Err},
we define the function #mProgram# as follows:

> mProgram modules
>   | not (all null errs) = Left errs
>   | otherwise           = Right rels
>   where
>   rels = computeInsOuts (const emptyRel) modules
>   errs = zipWith (chkModule expsOf) inscps modules
>
>   (inscps,exps) = unzip rels
>   expsOf m      = lookup m mod_exps
>   mod_exps      = map modName modules `zip` exps


It is assumed that implicit imports of the Prelude
\cite[Section 5.6.1]{Haskell98} have been made
explicit before #mProgram# is called. It is also assumed that all
modules in the argument list have unique names.

While the function #mProgram# is sufficient to explain the meaning of a
Haskell program, it would probably not be very practical in a Haskell
implementation, since it does not support separate compilation. Instead of
 #mProgram#, we have implemented a more sophisticated function based on the
same key ingredients: the functions #computeInsOuts# (which supports
separate compilation) and #chkModule#, described in sections \ref{rec-mods} 
and \ref{Err} respectively.
Our Haskell front-end processes modules one
strongly connected component at a time, caches module interfaces
between runs, and has better error handling.  We omit the
implementation of these practical details from this presentation.

% Section~\ref{rec-mods}
