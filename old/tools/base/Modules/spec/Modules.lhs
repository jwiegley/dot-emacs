> module Modules where

> import List (partition, nub)
> import Maybe (fromJust)

> -- implementation only
> import QualNames



Module system parameters
========================

The module system is parametrized on four type parameters:

    * The type of identifiers used in the source code of a program (#qn#).
      Those may be qualified or unqualified names.
    
    * The type of module names and name qualifiers (#m#).
      These are used to name modules, in import declarations, export lists,
      and qualified names.

    * The type of simple names (#n#).  Those are used
      to name entities in definitions or when exported.

    * The type of entities (#ent#).  These are the objects referred to by 
      identifiers in the program and are introduced by declarations 
      (functions, type constructors, value constructors, field selectors,
      classes, class methods).


The parameters are not completely arbitrary, in fact there is a close relation
between the first three.  To capture this, we use the class #QualNames#:

| class QualNames qn m n | qn -> m n, m n -> qn where
|   -- observers
|   isQual          :: qn -> Bool
|   getQualifier    :: qn -> m
|   getQualified    :: qn -> n
| 
|   -- constructors
|   mkUnqual        :: n -> qn 
|   mkQual          :: m -> n -> qn 

In order for the types to be suited for the purposes of the module system,
we require that they be related by the #QualNames# class.
This essentially forces #i# to be a type similar to the following:

| data Name m n = Unqualified n | Qualified m n


We also require that there be a special element in #m#, which we shall
call "Main", and a special element in #qn# which shall be denoted as "main".


For the type of entities, we require that there is a way to identify value
constructors,  and that we know the the ownership relation between
entities (e.g. a type constructor may "own" a number of value constructors).
Formally this is captured by the requirement that the type #ent#
be an instance of the following class:

| class Entity ent where
|   isCon   :: ent -> Bool
|   owns    :: ent -> [ent]


Finally, all four types should be in the #Eq# class, i.e. values of the
appropriate types should be comparable for equality. 



The abstract syntax
===================


A Haskell module consists of a name, an export specification, a number
of import declarations and a number of local declarations.  This 
suggests the following data structure:

> data Mod qn m n ent = Mod
>     { modName       :: m
>     , modExport     :: Maybe [ExpListEntry qn m]
>     , modImports    :: [Import m n]
>     , modDefines    :: Rel n ent
>     }                                                 

In the concrete syntax of Haskell, it is valid to just have the module body
(imports and declarations).  This is considered to be an abbreviation for 
a module with name "Main" (i.e. the special element of the #m# type),
and export specification exporting a single entity named "main"
(the special element of the #qn# type).  (sect 5.1. of report)

It is also valid to omit just the export specification (sect 5.2 of report),
but this is not considered to be an abbreviation.  Instead it is a special
kind of specification, one saying that only (and all) locally defined
entities are to be exported.  

> data ExpListEntry qn m    = Ent (EntSpec qn) | ModuleExp m

In an export list a programmer may write two kinds of things - either
the name of an entity with (perhaps) some subordinate names (here modeled
by an #EntSpec#), or the so called "module" export, which in concrete
Haskell syntax is written as #module M# (where #M# is a module alias).

An #EntSpec# consists of the name of an entity, with possibly the
names of some subordinate names.  An explicit list of subordinate names
is modeled with the #Some# component of the #SubSpec# data type,
while a request for all available subordinate names (the #(..)# notation
of Haskell) is modeled using #All#.

> data EntSpec j          = EntSpec j (Maybe (SubSpec j)) deriving Eq
> data SubSpec j          = All | Some [j]                deriving Eq

The #EntSpec# type is in fact shared between export lists and import
declarations, as they are structurally the same.  The only difference 
between the two is the types used to name entities (i.e. the #j# parameter
above).  In the case of an export list we use #qn# (the type of program
identifiers - qualified or not), while in the case of import declarations
we use #n# (the type of simple names).

We note that our abstract syntax is slightly more permissive than Haskell's
as one may add subordinate names to any name, while in Haskell
it is syntactically invalid to add subordinate names to lower case
identifiers.  

This brings us to the data structure used to model import declarations:

> data Import m n     = Import
>     { impQualified  :: Bool
>     , impFrom       :: m 
>     , impAs         :: m
>     , impSpec       :: (ImpMethod, [EntSpec n])
>     }                  
>
> data ImpMethod = Importing | Hiding

An import may be qualified (or not), contains the name of the module from which 
entities are to be imported, an alias to be used in qualified names for entities
which came through this import, and finally a specification of which entities 
are to be imported.  In concrete Haskell terms, the only required field is
the name of the source module, but the omissions of any of the other fields
are considered to be abbreviations as follows:

    * The value of #impQualified# is #False# unless the #qualified#
    keyword was present in the source code, in which case it is #True#.

    * If the #as# clause of a module is omitted, this field gets the same
    value as the #impFrom# field, i.e. the name of the source module
    is used to qualify names.

    * If the import specification is omitted, it is assumed to be
    #(Hiding, [])# (or #hide ()# in Haskell syntax), essentially saying that
    all entities are to be imported.
    


Semantics
=========

The abstract syntax above was nicely structured in the sense that bigger 
pieces were made out of smaller ones.  It would be nice to be able to
give meanings of the bigger pieces in terms of the meanings of the smaller
ones and this is the approach we take.  Each piece of the abstract syntax
is modeled as a relation transformer, i.e. given a relation it
produces a new relation. To put the whole idea in perspective
we first need a brief digression to relations.


Relations
---------

We use relations to model the association between names and entities.
This seems like a natural choice as in a single framework we may
represent undefined names (i.e. names which refer to no entities),
ambiguous names (names referring to more than one entity) and proper
names (referring to exactly one entity).  It is not enough to restrict
ourselves to just using proper names, as there are valid Haskell
programs containing ambiguous names in scope (report section 5.5.2),
of course there is the requirement that such names are not used.
Furthermore, one may use the information provided by the relation to
generate useful error messages.  We model relations as lists of pairs:

> type Rel a b = [(a,b)]

The exports of a module are modeled by a relation between simple names
and entities (i.e. #Rel n ent#), while the names in scope of a module
are modeled as a relation between identifiers and entities (i.e. #Rel qn ent#).
Ultimately our goal is for each module to come up with two relations:

    * the "export" relation of type #Rel n ent#
    * the "in scope" relation of type #Rel qn ent#


Functions used to compute both "exports" and "in scope" relations
-----------------------------------------------------------------

From the structure of a module we know what entities it defines.  Now
we need to consider how may a programmer refer to those entities
(i.e. what is the relation between names and entities defined in a module).
This is specified by the #locals# function, which computes a part
of the "in scope" relation of a module.  When an entity is defined in
a module one may refer to it by either using its simple name 
or by qualifying it with the name of the module 
(report section 5.5.1).  Formally this is:

| locals :: ...
|   => Mod qn m n ent 
|   -> Rel qn ent

> locals mod = [ (mkUnqual n, e) | (n,e) <- defEnts ]
>           ++ [ (mkQual m n, e) | (n,e) <- defEnts ]
>   where
>   m       = modName mod
>   defEnts = modDefines mod

This function is also used to give semantics to modules without an
export specifications.


As we saw above, there is a certain commonality between the structure of
export lists and import declarations, in the sense that they both made
use of the #EntSpec# data type.  It is nice that we (nearly) have this
commonality at the semantic level as well.  When occurring in an export
list and a non-hiding import declaration, #EntSpec#s have essentially the same
meaning.  A difference occurs in the #hiding# case of an import declaration,
in which case it was decided that ambiguities are not important and 
the semantics is slightly more permissive.

The design choice made in Haskell was that the exports of a module should
be unambiguous in the sense that all exported entities have distinct
(simple) names.  The one exception to this rule is that a type and
a data constructor may have the same name.  The reason for this is
practical - although two different entities have the same name, one
may determine from the context which entity is meant, so the ambiguity
is not crucial (as types and data constructors are never interchangeable).
The only situation in which one may not distinguish between such
entities from the context is in an export lists and import declarations.
So in Haskell a different disambiguating mechanism is used in such cases -
the only way to export (or import) a value constructor is as a subordinate 
name.  Unfortunately this is not the case in #hiding# imports, where
if a name refers to more than one entity, all of them are hidden (i.e.
not imported).

To model this asymmetry in Haskell, we add
an additional parameter to the meaning function of #EntSpec#s, namely a
predicate over entities.  As we shall see later this predicate would
either be #not . isCon# (i.e. ignore constructors), or #const True#
for the #hiding# imports case, where everything is treated in the same way.

| mEntSpec :: ...
|   => (ent -> Bool) -> EntSpec j
|   -> Rel j ent -> Rel j ent
 
> mEntSpec p (EntSpec x spec) r = xents ++ xsubs
>   where
>   xents       = [ (y,e) | (y,e) <- r, y == x, p e ]
>
>   xsubs = case spec of 
>       Nothing         -> []
>       Just All        -> allxsubs
>       Just (Some xs)  -> [ (y,e) | (y,e) <- allxsubs, y `elem` xs ]
>
>   allxsubs    = [ (y,e) | (_,xe) <- xents, s <- owns xe, (y,e) <- r, e == s ]

It is not important if the relation passed as a parameter to #mEntSpec# is
an "export" or an "in scope" one.  The idea is that we take all entities
which may be named #x# (#xents#), and then we add
all subordinate entities belonging to entities in #xent# and
satisfy #spec# (#xsubs#).
If there was no specification, then we add no entities,
if the #(..)# specification was used, then we add all the subordinate entities
in scope (#allxsubs#) and finally if an explicit list of entities was provided
we only consider elements of #allxsubs# which conform to the specification.



Export relations
----------------

To compute the exported entities of a module, we need to know what is the 
relation between names and entities in scope of the module (#inscp#).

| exports :: ...
|   => Mod qn m n ent
|   -> Rel qn ent -> Rel n ent

> exports m inscp = [ (getQualified qn, e) | (qn,e) <- exps ]
>   where
>   exps = case modExport m of
>     Nothing   -> locals m
>     Just es   -> concat [ mExpListEntry e inscp | e <- es ]

If the programmer omitted the export specification, we just export the 
locally defined entities using the #locals# function.
Alternatively if an explicit export list was present,  we take
the union of the meanings of all entries in the list.
Finally to obtain an "export" relation, we remove all qualifiers.
Note that after removing the qualifiers (or even before that)
we might end up with a relation containing ambiguous names.
This is not valid in Haskell (except for the special case mentioned in
the previous section), but we choose to handle this and all other error
related issues at a later stage.

There are two different kinds of entries which may occur in an export list are:

    * export entity by qualifier (the so called "module" export).  The
    meaning of such an export specification is described in the report 
    as follows (report 5.2 - item 5 in list):

The form "module M" abbreviates the set of all entities whose unqualified name, e, is in scope, and for which the qualified name M.e is also in scope and refers to the same entity as e.

    * export entity by name, i.e. when the programmer uses the name of an
    entity in the export list with perhaps some subordinate names.  We already
    have a function to handle such situations - #mEntSpec#.  Since a data
    constructors may not be exported on its own (report 5.2 - item 2 in list)
    we pass #not . isCon# as the additional parameter to #mEntSpec#.

| mExpListEntry :: ...
|   => ExpListEntry qn m   
|   -> Rel qn ent -> Rel qn ent

> mExpListEntry (ModuleExp m) inscp =
>               [ (x,ent) | (x,ent) <- unqs, (qual m x,ent) `elem` qs ]
>   where
>   (qs,unqs) = partition (isQual . fst) inscp
>
> mExpListEntry (Ent ispec) inscp = mEntSpec (not . isCon) ispec inscp

 
In scope relations
------------------

To compute what names are in scope within a module, we need to know the
exports of all imported modules.  The parameter #expsOf# is a function
mapping module names to their exports.  
Simply put, the entities in scope of a module are all locally
defined entities and the union of all entities imported through an import
declaration:

| inscope :: ...
|   => Module qn m n ent
|   -> (m -> Rel n ent) -> Rel qn ent 
  
> inscope m expsOf = imports ++ locals m 
>   where
>   imports = concat [ mImp imp (expsOf (impFrom imp)) | imp <- modImports m ]


The meaning of an import declaration is a relation transformer, which 
changes "export" relations to "in scope" ones:

| mImp :: ...
|   => Import m n
|   -> Rel n ent -> Rel qn ent
 
> mImp imp exps 
>   | impQualified imp  = qs
>   | otherwise         = unqs ++ qs
>   where
>   m           = impAs imp
>   qs          = [ (mkQual m n, e) | (n,e) <- incoming ]
>   unqs        = [ (mkUnqual n, e) | (n,e) <- incoming ]
>   incoming    = mImpSpec (impSpec imp) exps

We use the semantic function for import specifications to compute what entities
come in scope (#incoming#), and then we adjust their names appropriately.
In the case of a #qualified# import, we only consider qualified names (#qs#),
otherwise we also add unqualified names (#unqs#).


The meaning of import specifications is computed by #mImpSpec#, which is
essentially a "front end" to the #mEntSpec# function.
We have two cases to consider - "importing" and #hiding# specifications.
In the first case we take the union of the relations corresponding to 
the entity specifications.  We ignore data constructors, as those may
only be imported as subordinate names (#not . isCon#).
For #hiding# specifications we essentially take the complement of
the non-hiding case, except now we do not ignore data constructors.

| mImpSpec :: ...
|   => ImpSpec m n 
|   -> Rel n ent -> Rel n ent
 
> mImpSpec (method, specs) exps = case method of
>   Importing   -> ents (not . isCon)
>   Hiding      -> [ exp | exp <- exps, exp `notElem` ents (const True) ]
>   where
>   ents p = [ x | spec <- specs, x <- mEntSpec p spec exps ]



Iteration
---------

The reader might have noticed that to compute the exports of a module we
need to know what is in scope, and to compute what is in scope we need
to know certain exports.  If we allow for mutually recursive modules, our
equations become mutually recursive and care needs to be taken when
solving them.  The idea is that the "export" and "in scope" relations for a
group of mutually recursive modules are computed at the same time (as they all
depend on each other).  In fact one could process _all_ modules in a 
program together, which is less efficient from an implementation point
of view, but simplifies this presentation as we need not supply the code
for computing groups of mutually recursive modules and dependencies between
those (a standard graph algorithm, followed by a topological sort).

To represent the "in scope" and "exports" relations of a group of modules
we use lists.  Since relations may in general be ordered by inclusion,
we may also order lists (of equal length) of relations as follows:

> (<<=) :: (Eq a, Eq b) => [Rel a b] -> [Rel a b] -> Bool
> xss <<= yss = and (zipWith subEq xss yss)
>   where
>   xs `subEq` ys   = all (`elem` ys) xs 

Note that this order is different from the one usually used in Haskell and
is only well defined on finite lists.  Since Haskell programs only have
finitely many modules this is not a problem.  In fact the lists we deal
with all have the same length, namely the number of modules in the program,
so one could think of them as tuples of relations.

We not only have an ordering structure on the lists of relations, we also
have a lattice structure which is directly inherited from the lattice structure
on the relations (operations defined element-wise as in the ordering above).
The lattice we deal with is finite, as each module may only define finitely
many entities and each entity may only have finitely many names.
Names get associated with entities in two ways:

    * by local declaration, in which case an entity receives two names
    (qualified and unqualified)

    * by import declaration, in which case an entity receives either one or
    two names.

Since there are only finitely many local and import declarations,
an entity may only have finitely many names. 


| computeInsOuts :: ...         
|   => [Mod qn m n ent]       
|   -> [(Rel qn ent, Rel n ent)]

> computeInsOuts otherExps mods = inscps `zip` exps
>   where
>   inscps          = nub `map` computeIs exps 
>   exps            = lfpAfter nextExps (repeat [])
>
>   nextExps        = computeEs . computeIs 
>
>   computeEs is    = zipWith (\m -> nub . exports m) mods is
>   computeIs es    = (\m -> inscope m (toFun es)) `map` mods
> 
>   toFun es m = maybe (otherExps m) (es !!) $ lookup m mod_ixs
>   -- toFun es m = let Just pos = lookup m mod_ixs in es !! pos
>   mod_ixs     = (modName `map` mods) `zip` [0 .. ] 

> lfpAfter :: Eq a => (a -> a) -> (a -> a) 
> lfpAfter f x = let fx = f x in if fx == x then x else lfpAfter f fx

The semantic functions #exports# and #inscope# deal with only one module
at a time, but it is easy to generalize them to work on multiple modules.
Given a list of modules and a list of "in scope" relations we may 
apply #exports# in "parallel" to compute a list of "export" relations
(#computeEs#).

If we are given a list of "export" relations, we may convert it to
a function associating each module with its exports (#toFun#). This
is achieved with the aid of the association list #mod_ixs#, which 
relates modules to their positions in the list (tuple) of modules.
Now that we have a function relating modules to their exports,
we may apply #inscope# to compute the "in scope" relations of the modules
(#computeIs#).

We observe that both #exports# and #inscope# are monotonic with respect to the
relation ordering.  This follows essentially from the monotonicity of
 #mEntSpec# and the definition of "module exports" (the first case
of #mExpListEntry#).  But then #computeEs# and #computeIs# are also monotonic
when lists are ordered as described above, and hence their composition
is monotonic.  Since we work in a finite lattice this is enough to conclude
that the function #nextExps# has a least fixed point.

We may than define the exports of the argument list of modules as the least
fixed point of #nextExps#.  Intuitively, given a list of "export" relations
 #nextExps# will compute what should be in scope in each module, and then based
on that compute a better approximation of what should be exported.
Similarly, the "inscope" relations of the modules may be defined as the
least fixed point of #computeIs . computeEs#, but using the well known
fact $fix (f . g) = f (fix (g . f))$ we obtain the alternative definition
used above.








