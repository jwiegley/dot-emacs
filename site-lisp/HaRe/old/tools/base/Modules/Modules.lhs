>module Modules(computeInsOuts,inscope,mImp',mExpListEntry) where
>
>import Relations
>import NamesEntities
>import ModSysAST
>import Data.Maybe (isNothing)
>import Set60204
 
The semantics of imports and exports
====================================
\label{Sem}

Now we are ready to present a method for computing the in-scope
and export relations of the modules in a program.  The process
proceeds in two stages.  In this section we compute the relations, ignoring
any errors that might occur (e.g. ambiguous or undefined exports).
In Section~\ref{Err}, we check that each computed relation satisfies a number
of additional requirements and produce appropriate error messages if
any problems are detected.  This approach simplifies the specification
as we can concentrate on a single issue at a time.  It also results in
better error messages being reported to the users of our prototype system,
because the module system analysis can continue, even in the presence
of ambiguities. In Section~\ref{SemProg} we glue everything together.

The computation phase, described in the remainder of this section,
is itself split in three parts: first we describe 
how to export/import a single entity, next we present how to combine the 
meaning of entity specifications to obtain the meaning of complete import
and export specifications. Finally, we describe how 
to handle mutually recursive modules.


Importing or exporting an entity
--------------------------------

We already noted the similarity in the abstract syntax for exporting
and importing an entity---they both made use of the #EntSpec# data structure.
It is therefore not surprising that those two cases are handled in
essentially the same manner.  Our goal is to determine which
name-entity pairs in an in-scope or export relation satisfy
a certain #EntSpec# specification.  The function #mEntSpec# formalizes 
this process.

>mEntSpec :: (Ord j,ToSimple j) => 
>   Bool ->           -- is it a hiding import?
>   Rel j Entity ->   -- the original relation
>   EntSpec j         -- the specification
>     -> Rel j Entity -- the subset satisfying the specification
>
>mEntSpec isHiding rel (Ent x subspec) =
>   unionRels [mSpec, mSub]
>   where
>   mSpec   = restrictRng consider (restrictDom (== x) rel)
>   allSubs = owns `unionMapSet` rng mSpec
>   subs    = restrictRng (`memberS` allSubs) rel
>   mSub    = 
>     case subspec of
>       Nothing        -> emptyRel
>       Just AllSubs   -> subs
>       Just (Subs xs) -> 
>         restrictDom ((`elem` xs) . toSimple) subs
>
>   consider
>     | isHiding && isNothing subspec = const True
>     | otherwise                     = not . isCon

\begin{ex} Before we describe #mEntSpec# in detail,
we present an example of how it is going to be used.  Consider the module:

|  module M (f, M.List(..), Show(showList)) where
|  import A(g)
|  ...

The function #mEntSpec# is applied to each of the three entries 
in the export list, to determine the subset of the in-scope relation each of 
them matches.  Similarly, it is applied to the entry #g# of the import
list, to determine which of #A#'s exports come in scope.
\end{ex}

The #EntSpec# structure consists of two components:
the ``main'' specification, and possibly a subordinate specification.
The meaning of the entire specification is the union of its components.
The subset of #rel# which matches the ``main'' specification is #mSpec#.
It is computed by restricting the domain of the relation to contain only
names matching the specification.  It turns out we might need to restrict
the range of the relation as well, the reasons for this are discussed shortly.
Typically (but not always!) #mSpec# will be a relation only relating a single
name to an entity, representing the fact that the specification is unambiguous.

Continuing with the example above, #Show# is the ``main'' specification,
and #mSpec# would be:
\begin{align*}
Show              &\mapsto \ent{Show}{Prelude}    
\end{align*}

The meaning of the subordinate specification depends on the meaning
of the ``main'' specification.  The set #allSubs# contains
all subordinate entities of all possible interpretations in #mSpec#.
To compute the subordinates that are in-scope/exported, we restrict #rel#
so that names may only refer to entities in #allSubs# --- the result is #subs#.
In our example #allSubs# would contain the entities of the methods in the
 #Show# class:  
$$
\{ \ent{show}{Prelude}, \ent{showsPrec}{Prelude}, \ent{showList}{Prelude}\}
$$
Now suppose that \ent{showsPrec}{Prelude} is not in scope, perhaps because
the programmer explicitly hid it, when importing the #Prelude#.  
Then #subs# would be:
\begin{align*}
show              &\mapsto \ent{show}{Prelude}     \\
Prelude.show      &\mapsto \ent{show}{Prelude}     \\
showList          &\mapsto \ent{showList}{Prelude} \\
Prelude.showList  &\mapsto \ent{showList}{Prelude}
\end{align*}

Finally, we need to compute what part of #subs# matches the subordinate
specification.  If there was no specification, the result is the empty
relation, if the specification was of the form #AllSubs# we return #subs#,
as by construction it contains all subordinates which are in-scope or exported.
Finally, if a programmer specified an explicit list of subordinates, we need
to restrict #subs# so that it only contains names in the explicitly
provided list.  Since subordinate specifications contain only simple
names (i.e. of type #Name#), and in-scope relations contain possibly
qualified names (i.e. of type #QName#) we first strip any qualifiers
using the method #toSimple#.  This has the effect that a 
subordinate will be exported if it is available in scope with either 
qualified _or_ unqualified name \cite[Section 5.2]{Haskell98}.
In the ongoing example, we had a subordinate name list, containing one name:
 #``showList''#.  So the restricted #subs# relation will be:
\begin{align*}
showList          &\mapsto \ent{showList}{Prelude} \\
Prelude.showList  &\mapsto \ent{showList}{Prelude}
\end{align*}

Next we describe a quirk in the Haskell module system, which
gives rise to the #isHiding# parameter and the auxiliary predicate
 #consider#.  The entities in Haskell may be grouped in two 
non-interchangeable groups: classes and type constructors on the one side,
all other entities on the other.
In the body of a module, it is always possible
to determine which type of entity a name refers to.
A name may refer to two different entities without the risk
of an ambiguity.  A problem occurs with import and export lists, 
as they may not provide enough context.

\begin{ex} It is quite common to use the same name for both a type
and a value constructor, as types and values do not mix:

|  module A (Env) where
|  newtype Env a = Env [(String,a)]

There is no context in the export list to indicate if the programmer intended
to export the type constructor #Env#, the value constructor #Env#, 
or perhaps both. 
\end{ex}

To avoid the potential ambiguity illustrated in the example, Haskell 98
uses the following strategy to decide what is to be imported/exported.

Because only classes and type constructors may ``own'' other
entities, the presence of a subordinate name list indicates that
the programmer is referring to the type or class in scope.
The situation is more complicated if the name does not have a subordinate
list, as then there are two different policies, depending on where
the name occurs.  

The first policy is that names starting with a capital
letter always refer to types or classes.  It is used for names occurring
in the export list of a module, and in non-hiding imports.  So in particular,
in the above example, only the type constructor #Env# will be exported,
and not the value constructor.  This means that in order to export/import
a value constructor, a programmer has to include it in the subordinate
list of the relevant type constructor.  A consequence of this is that
it is not possible to export just a value constructor without
its type.  In practice this is not a very big problem.

The second policy is used for ``hiding'' imports, and it says that 
capital names may refer to _both_ types/classes and value constructors.
One reason for this difference is that it is sometimes useful to _hide_
just a value constructor without hiding its type.  If the first
policy was used for hiding imports this would not be possible.  We note
that if a name refers to both a type and a value constructor, both of
them are hidden.

A (non Haskell 98) alternative to having two separate policies is to 
have a single more flexible policy that applies in both cases.  
Later in the paper (Section \ref{conclusions}) we will describe a simple
modification to the first policy to achieve this.

Here is an example illustrating what the policies do.

\begin{ex}
| import A (Env)          -- import only the type 
| import A hiding (Env)   -- hide the type and the value
| import A hiding (Env()) -- hide only the type 
\end{ex}

To implement this rule we defined the auxiliary predicate #consider#.  The 
parameter #isHiding# tells us if we are in a hiding import (the special case).
If we are, then we consider all entities as valid interpretations 
for the name in the ``main'' specification.   However if we are using
 #mEntSpec# in an export list or a normal import, then we do not consider value
constructors.

\vspace{6mm}
Export relations
----------------

Now that we know how to handle a single entry in the export list,
we are ready to compute the export relation of a module.   This
is the task of the function #exports#.

>exports :: Module -> Rel QName Entity -> Rel Name Entity
>exports mod inscp = 
>   case modExpList mod of
>     Nothing -> modDefines mod
>     Just es -> getQualified `mapDom` unionRels exps
>       where
>       exps = mExpListEntry inscp `map` es

The parameter #inscp# models the in-scope relation of the module.
It is necessary, as the interface of a module is essentially a subset
of #inscp#.  If the programmer omitted the export specification of
a module, we just export the locally defined entities by using the #modDefines#
field of the module under consideration.  Alternatively if an explicit
export list was present,  we take
the union of the meanings of all listed entries.
To obtain a proper export relation we remove all qualifiers.
Note that after removing the qualifiers (or even before that)
we might end up with a relation containing ambiguous names.
This is not valid in Haskell, but we will delay detection of such invalid 
solutions until a later pass.

We have already seen that there are two forms of specification
that may appear in an export list.  If we see an entity specification,
we just use #mEntSpec# to determine the subset of #inscp# which matches it.
The other possibility is that we see an export of the form
 #module M#.  In this case, the Haskell 98 report 
\cite[Section 5.2, item 5]{Haskell98} states that the result is the subset 
of #inscp# containing precisely those entities, 
which may be named with _both_ some simple name #x# _and_ 
a qualified name #M.x# 

>mExpListEntry :: 
>   Rel QName Entity -> ExpListEntry -> Rel QName Entity
>mExpListEntry inscp (EntExp it) = mEntSpec False inscp it
>mExpListEntry inscp (ModuleExp m) = 
>   (qual m `mapDom` unqs) `intersectRel` qs
>   where
>   (qs,unqs) = partitionDom isQual inscp

 
In-scope relations
------------------

In this section we specify how to compute the in-scope relation of a module.
This is done by the function #inscope#:  

>inscope :: Module -> (ModName -> Rel Name Entity) 
>                         -> Rel QName Entity
>inscope m expsOf = unionRels [imports, locals]
>   where
>   defEnts = modDefines m
>   locals  = unionRels 
>               [mkUnqual `mapDom` defEnts,
>                mkQual (modName m) `mapDom` defEnts]
>
>   imports = 
>     unionRels $ map (mImp expsOf) (modImports m)

An entity is in scope if it is either locally defined, 
or if it is imported from another module. It is therefore necessary to 
know what the exports of other modules are.  The parameter #expsOf# 
is a function mapping module names to their exports.

Every locally defined entity may be referred to with at least two names:
the simple name used in its definition, and a qualified name, obtained
by prefixing with the name of the module.  For example if a module #A# 
defines an entity with simple name #f#, a programmer may refer to it as 
either #f# or #A.f# \cite[Section 5.5.1]{Haskell98}.  The part
of the in-scope relation containing local definitions is #locals#.

Import declarations are cumulative \cite[Section 5.3]{Haskell98}
and so the imported entities 
(#imports#) are the union of the entities imported by each declaration.

\begin{ex}
The declarations:
| import A hiding (f)
| import A (f) 
import everything from module #A#, as the first one imports everything
but #f#, while the second one imports just #f#.
\end{ex}

The function #mImp# is used to compute what entities come in scope through
a single import declaration.  
\newpage

>mImp :: (ModName -> Rel Name Entity) -> Import ->
>         Rel QName Entity 
>mImp expsOf imp
>   | impQualified imp  = qs
>   | otherwise         = unionRels [unqs, qs]
>   where
>   qs      = mkQual (impAs imp) `mapDom` incoming
>   unqs    = mkUnqual `mapDom` incoming
>
>   listed  = unionRels $
>               map (mEntSpec isHiding exps) 
>                   (impList imp)
>   incoming
>     | isHiding  = exps `minusRel` listed
>     | otherwise = listed
>
>   isHiding  = impHiding imp
>   exps      = expsOf (impSource imp)

>mImp' :: Rel Name Entity -> Import ->
>            Rel QName Entity 
>mImp' exps imp
>   | impQualified imp  = qs
>   | otherwise         = unionRels [unqs, qs]
>   where
>   qs      = mkQual (impAs imp) `mapDom` incoming
>   unqs    = mkUnqual `mapDom` incoming
>
>   listed  = unionRels $
>               map (mEntSpec isHiding exps) 
>                   (impList imp)
>   incoming
>     | isHiding  = exps `minusRel` listed
>     | otherwise = listed
>
>   isHiding  = impHiding imp


First we define the relation #listed#, which contains exported entities 
matching _any_ of the entity specifications in the list of the import 
declaration.  Next, we compute the subset of the export relation of the 
source module, which matches the specification (#incoming#).  If we have
a normal import, #incoming# is exactly #listed#.  If however we are
dealing with a ``hiding'' import, we need to take all those entities
which are exported, but are _not_ in #listed#.

Having computed #incoming#, we now need to convert it to an
in-scope relation.  To do that, we adjust the names of the entities
according to the import declaration.  If we have a ``qualified'' import,
we introduce only qualified names for the imported entities (#qs#), otherwise
we also add the unqualified names.  The qualified names are computed by
simply qualifying all names in #incoming# with the #impAs# specification
of the declaration.

\vspace{6mm}
Recursive modules
-----------------
\label{rec-mods}

The reader might have noticed that to compute the exports of a module we
need to know what is in scope, and to compute what is in scope we need
to know certain exports.  If we allow for mutually recursive modules, then our
equations become mutually recursive.  In this section, we show how they are
solved.

The idea is that the export and in-scope relations for a
group of mutually recursive modules are computed at the same time (as they all
depend on each other).  This means that the compilation unit of a compiler
is not a single module, but a _strongly connected component_ of mutually
recursive modules.  In fact, one could process _all_ modules at once
and still get the same result, but this will not be very practical for
large systems.  For this reason, we will work with strongly connected 
components of modules, and assume that they are processed in dependency order.

The function #computeInsOuts# computes the in-scope and export
relations of the modules in a strongly connected component.
The argument #otherExps# is a function mapping module names to export relations.
It needs to be defined only for modules in earlier (dependency-wise)
strongly connected components.
\newpage

>computeInsOuts :: 
>   (ModName -> Rel Name Entity) -> [Module] ->
>    [(Rel QName Entity, Rel Name Entity)]
>computeInsOuts otherExps mods = inscps `zip` exps
>   where
>   inscps = computeIs exps
>   exps   = lfpAfter nextExps $ 
>             replicate (length mods) emptyRel
>
>   nextExps = computeEs . computeIs
>
>   computeEs is = zipWith exports mods is
>   computeIs es = map (`inscope` toFun es) mods
>
>   toFun es m   = maybe (otherExps m) (es !!) 
>                        (lookup m mod_ixs)
>   mod_ixs      = map modName mods `zip` [0..]
>
>lfpAfter f x = if fx == x then fx else lfpAfter f fx
>   where 
>   fx = f x

The function #computeInsOuts# starts by assuming that the modules in
the strongly connected component do not export anything.  It then
keeps applying the function #nextExps# to obtain successive approximations
to the exports of each of the modules until a fixed point is reached.
Thus, the export-relations in a strongly connected component are the
least fixed point of the function #nextExps#.  Similarly, the in-scope 
relations are the least fixed point of #computeIs . computeEs#, 
but using the well known fact that $fix (f . g) = f (fix (g . f))$, 
we obtain the definition of #inscps# used above.

The function #nextExps# computes the next approximation to the
exports of each module.  Given the current exports of each module,
it first determines what are the corresponding new in-scope relations,
and based on that computes the new exports.  It makes use of the
helper functions #computeEs# and #computeIs#, which are generalizations of 
 #exports# and #inscope# respectively, to work with strongly connected
components rather than just single modules.

The functions #computeEs# and #computeIs# work in a similar way: they
apply #exports# (or #inscope# respectively) to all modules in  the strongly
connected component.
The main difference between the two is that the export relation of 
a module depends only on the in-scope relation of the same module, 
while the in-scope relation depends on the export relations of many modules. 
As a result, before mapping #inscope# over the strongly
connected component, we need to compute a function that maps
module names to their respective export relations.  This is done by
 #toFun#.  If the module is in the current strongly connected component,
 the result of #toFun# just projects the appropriate export relation.
 Otherwise, we use the parameter #otherExps# to lookup the exports
of a previously processed module.

\begin{ex}
In this example we consider a module that imports itself,
and use the algorithm above to compute its in-scope and export
relations:
|  module A (B.f) where
|  import A as B
|  f = ...

\newpage
We start with an empty export relation, and 
then compute the in-scope relation:  
$$f \mapsto \ent{f}{A}, A.f \mapsto \ent{f}{A}$$ 
Note that this contains only the locally defined names, because #A#
imports only from itself, and we have assumed it does not export anything.
Because the in-scope relation does not relate #B.f# to anything, nothing
is exported again, and so we reach a fixed point.
Thus module #A# does not export anything, and it has one entity in-scope:
$\ent{f}{A}$.  This entity may be referred to by either #A.f#, or just #f#.
\end{ex}

\begin{ex}
This example is a slight variation on the previous one, two modules
are involved: #A# and #B#:
|  module A (B.f) where
|  import A as B
|  import qualified B
|  f = ...
| 
|  module B where
|  f = ...
The dependencies between those two are: #A# depends on #A# and #B#, 
and #B# does not depend on anything, so we first analyze #B#.  Since it
has no export specification, it exports all locally defined names and
nothing else, so we have the following in-scope and export relations:

\begin{tabular}{cc}
in-scope                   & exports     \\ 
$f \mapsto \ent{f}{B}, B.f \mapsto \ent{f}{B}$ & $f \mapsto \ent{f}{B}$
\end{tabular}

Next we analyze module #A#. The steps in the fixed point calculation are:

\begin{tabular}{rcc}
   & in-scope                   & exports     \\ 
1. &                            & $\emptyset$ \\
2. & $f \mapsto \ent{f}{A}, A.f \mapsto \ent{f}{A}, B.f \mapsto \ent{f}{B}$ 
   & $f \mapsto \ent{f}{B}$ \\
3. & $f \mapsto \{ \ent{f}{A}, \ent{f}{B} \}, A.f \mapsto \ent{f}{A}, 
    B.f \mapsto \ent{f}{B}$ 
   & $f \mapsto \ent{f}{B}$ 
\end{tabular}

We start with the empty export relation.  The in-scope relation we
compute contains the locally defined names and also the imports.  In this
case the imports are just $B.f \mapsto \ent{f}{B}$.  On the next iteration,
 $f \mapsto \ent{f}{B}$ gets exported.  So the next in-scope relation contains
more imports: $f \mapsto \ent{f}{B}$, and $B.f \mapsto \ent{f}{B}$, which
came in through the #import A# declaration.  These do not add anything new to
the exports of the module, so we have reached a fixed point.
\end{ex}

We defined the import and export relations of modules in terms
of the least fixed point of a certain function.  To ensure that the
algorithm above terminates, we need to ensure that this least
fixed point exists.  Now we examine this issue in more detail.  

We used lists to represent the in-scope and export relations of a group 
of modules. Since relations may be ordered by inclusion,
we may also order lists (of equal length) of relations by a point-wise
ordering.  In a similar fashion we obtain a lattice structure on the
lists of relations by using the lattice structure of relations point-wise.
The lattice obtained in this way is finite, as each module may only define 
finitely many entities and each entity may only have finitely many names.
Names get associated with entities in two ways: by local declaration,
in which case an entity receives two names (qualified and unqualified);
and by import declaration, in which case an entity receives either one or 
two names.
Since there are only finitely many local and import declarations,
an entity may only have finitely many names. 

It then follows from the Knaster-Tarski theorem \cite{Alg90}, 
that #nextExps# has a least fixed point if it is monotonic with respect to 
the above ordering.  The #inscope# and #exports# functions are monotonic
with respect to the relation ordering, as they are essentially filters that
produce larger outputs when given larger inputs.  
The same holds for #computeEs#, #computeIs#, and their composition #nextExps#.


