Names and Entities
==================
\label{NameEnt}

Having described the Haskell module system as a mechanism for
namespace management, it is natural for us to begin its
specification with a discussion about names and entities.

> {-# LANGUAGE TypeSynonymInstances #-}
> {-# LANGUAGE FlexibleInstances #-}
> module NamesEntities (
>   module NamesEntities,
>   module Ents,
>   module Names
> ) where
>
> --import Set
> import Data.Maybe(isJust)
> import Ents(Entity,isCon,isValue,owns)
> import Names(Name,QName,ModName,
>              getQualified, getQualifier, mkQual, mkUnqual)



Entities
--------

The basic idea is that _names_ in a program refer to _entities_.
Entities get introduced in a program by _declarations_.  For example,
a declaration such as #f x = x + 2# will introduce one entity:
a function named #f#. For the purposes of this paper, we are only interested in
top level entities, as they are manipulated by the module system.
There are at least six varieties of entities in Haskell:
functions, type constructors, value constructors, field labels, classes,
and class methods.  One could perhaps also consider class instances 
to be entities as they are also introduced by declarations.
We do not do that here because, in Haskell 98, there is no way to 
refer to them by name.

The module system specification is parametrized by the type of entities,
so we represent it using an abstract data type:

| data Entity = ... 
| isCon :: Entity -> Bool
| owns  :: Entity -> Set Entity 
|
| instance Ord Entity where ...

The function #isCon# is intended to distinguish between value constructors and
other entities, as they need to be handled differently in 
``hiding'' imports as opposed to normal imports and exports 
(see Section \ref{Sem}).

The function #owns# defines the _subordinate_ relation between entities.
Type constructors ``own'' their value constructors and field labels;
classes ``own'' their methods.

The requirement that entities are in the #Ord# class is stronger than
strictly necessary.  For the module system to work, we only need an equality
operation.  The ordering is required by the implementation of relations
as sets (described in Section \ref{sec-relations}).  

Entities will be written in a different font, and annotated with the 
module where they were originally defined.   
For example \ent{f}{M} refers to the entity #f# originally defined in 
module #M#.



Names
-----

Our specification is also parameterized by the types used to model names.
We distinguish between three different kinds of names:
    * _simple names_ (of type #Name#) are used in
      declarations, and to name entities exported by a module.
    * _program identifiers_ (whose type is #QName#) are used in the main
      text of the program and refer to entities.  They may be either qualified
      or unqualified.
    * _module names_ and _name qualifiers_ (with type #ModName#) are used to 
      name modules, in import declarations, in export lists, and in 
      qualified names.
We use the type #Name# whenever we want to indicate that only simple (i.e. not 
qualified) names are allowed, and #QName# when both simple and qualified names
may be used.  As for entities, the module system only needs equality operations
on names, but to use the #Set# data structure we require the #Ord# instance.

| data Name     = ...
| data ModName  = ...
| data QName    = ...
|
| getQualifier  :: QName -> Maybe ModName
| getQualified  :: QName -> Name
| mkUnqual      :: Name -> QName
| mkQual        :: ModName -> Name -> QName
|
| instance Ord Name where ...
| instance Ord ModName where ...
| instance Ord QName where ...

We define a couple of useful functions to manipulate (possibly qualified) names.
We note that if #qual# is applied to an already qualified name, it will
replace the old qualifier (however in this specification we always apply it
to unqualified names).

> isQual :: QName -> Bool
> isQual = isJust . getQualifier

> qual :: ModName -> QName -> QName
> qual m = mkQual m . getQualified 

It is also convenient to define an overloaded function #toSimple#,
which produces the unqualified part of a name.  It does nothing
on values of type #Name# as they cannot be qualified.  For values of
type #QName# it strips the qualifiers.

> class ToSimple t where
>   toSimple :: t -> Name
>
> instance ToSimple Name where
>   toSimple = id
>
> instance ToSimple QName where
>   toSimple = getQualified

In examples throughout the paper we shall use #String# for #Name#, #ModName#, 
and #QName#.  This is not the case in our prototype implementation, as
it defeats the purpose of having three different types in the first place.  
We made this choice to keep the examples readable.


