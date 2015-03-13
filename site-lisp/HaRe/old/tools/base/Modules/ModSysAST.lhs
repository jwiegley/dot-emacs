> module ModSysAST where
>
> import NamesEntities
> import Relations

Abstract Syntax
===============
\label{AbsSyn}

As described in the Haskell 98 report \cite[Section 5.1]{Haskell98},
a Haskell module consists of a name, an export specification,
a number of import declarations and a number of local definitions.
We use the following data structure to represent modules:

> data Module = Module {
>   modName     :: ModName,
>   modExpList  :: Maybe [ExpListEntry],
>   modImports  :: [Import],
>   modDefines  :: Rel Name Entity }

The concrete syntax of Haskell allows an abbreviated form, where
the module name and the export specification are omitted.
This is an abbreviation for a module with name ``Main'' and an export
specification exporting a single entity named ``main''
\cite[Section 5.1]{Haskell98} and will in our abstract syntax be
represented in its expanded form.

An element of the export specification is
either an entity name or a module name as described by the
data structure #ExpListEntry#.  For entities with subordinate names, 
a programmer may also provide a _subordinate export list_.  
This list is modeled by the data structure #SubSpec#.  
It specifies which of the subordinate entities currently in scope 
are to be exported.

> data ExpListEntry = EntExp (EntSpec QName) 
>                   | ModuleExp ModName
> data EntSpec j    = Ent j (Maybe SubSpec)
> data SubSpec      = AllSubs | Subs [Name] 

\begin{ex}
For the Haskell module:

|  module A (f,C(..),module M) where ...

the field #modExpList# would be:

| Just [EntExp (Ent "f" Nothing),
|       EntExp (Ent "C" (Just AllSubs)),
|       ModuleExp "M"]
\end{ex}

The structure #EntSpec# is used in both import and export lists.
Because qualified names are allowed in export lists,
but not in import lists, we use the parameter #j# to capture the different 
types of #EntSpec#.

At first it may seem that we may eliminate #AllSubs# by thinking
of it as just an abbreviation for all the methods/value constructors
of its owner.  This however is not the case, as its meaning depends
on what entities are currently in scope, and this is one of the things
the module system computes.

The lack of an export list is a special form of export specification: 
one saying that only---and all---locally defined entities are to be exported 
\cite[Section 5.2]{Haskell98}.  It is _not_ an abbreviation for the 
empty export list, or the export list containing only #module M# 
(where #M# is the current module).  We represent this explicitly by 
using the #Maybe# type constructor in the #modExpList# field. 

To make use of entities defined in other modules, programmers have
to supply _import declarations_.  Their purpose it to specify
what entities are to be imported, which module provides the required
entities, and valid ways to refer to the imported entities.

> data Import = Import {
>   impQualified  :: Bool,
>   impSource     :: ModName,
>   impAs         :: ModName,
>   impHiding     :: Bool,
>   impList       :: [EntSpec Name] }

The #impSource# field is the only field that must be specified explicitly
in an import specification.  It specifies the name of the module
from which entities will be imported.  All remaining fields take on
a default value, if not specified explicitly.

There are two flavors of import declarations:
the ones specifying what names are to be imported, and the ones specifying
what names are _not_ to be imported (sometimes called ``hiding'' imports).
The boolean field #impHiding# distinguishes between those two.   

The field #impList# contains the actual specification, which has
structure similar to the export list of a module.  There are two
differences: there are no ``module'' imports, and
all names in the list must be simple.  To capture this similarity we
reuse the #EntSpec# data type.  If this field is omitted the specification is
assumed to be #[]#, and the #impHiding# field is set to #True#.
This has the effect of importing all exported entities of the source module.

Sometimes it is more convenient to qualify names imported from a
module not using the module name, but some other alias instead.  This is 
particularly useful if the name of the source module is quite long and
a programmer needs to refer often to imported entities by their 
qualified names.  The field #impAs# stores this alias.  If the alias
is omitted, this field is assumed to have the same value as the
 #impFrom# fields (i.e. we use the module name in qualified names).

Finally in some situations it might be preferable to only import
entities with their qualified names.  This can be done with the so
called _qualified_ imports.  The field #impQualified# distinguishes
qualified from normal imports.

\begin{ex}
The import:
| import Prelude as P hiding (and,Bool(True))
is represented by the data structure:
| Import {impQualified = False,
|         impSource    = "Prelude",
|         impAs        = "P",
|         impHiding    = True,
|         impList      = [Ent "and" Nothing,
|                         Ent "Bool" (Just (Subs ["True"]))]
|        }
\end{ex}


