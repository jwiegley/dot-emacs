Error Detection
===============
\label{Err}

In the previous section we described how to compute the in-scope and
export relations of mutually recursive modules.  The algorithm produces
a result even for modules containing errors.  
We now examine what properties need to be satisfied by correct solutions,
and how we can detect ``bad'' solutions.

>module CheckModules(ModSysErr(..),chkModule) where
>
>import Relations
>import NamesEntities
>import ModSysAST
> --import Modules
>import Data.List (partition,nub)
>import Data.Maybe(isNothing)

>import Set60204

Even though this specification aims for clarity rather than efficiency
or usability, we believe that it is important not only to detect
invalid solutions, but also to say _why_ they are invalid.   The data type 
 #ModSysErr# classifies the different kinds of problems which might occur.

>data ModSysErr 
>   = UndefinedModuleAlias ModName
>   | UndefinedExport QName
>   | UndefinedSubExport QName Name
>   | AmbiguousExport Name [Entity] 
>   | MissingModule ModName
>   | UndefinedImport ModName Name 
>   | UndefinedSubImport ModName Name Name 
>   deriving Show             

The meanings of the individual errors are as follows:
    * #UndefinedModuleAlias# means that an export list contained an
      entry of the form #module M#, where #M# is not a valid alias.
    * #UndefinedExport# refers to an entry in an export list, for which
      there is no corresponding entry in the symbol table.
    * #UndefinedSubExport# is similar to #UndefinedExport#, except that it
      also reports the owner of the subordinate name.
    * #AmbiguousExport# reports an exported name, together with all
      the possible entities that it might refer to.
    * #MissingModule# is reported when an import declaration refers to
      a module that is missing.
    * #UndefinedImport# is reported when an import declaration attempts
      to import (or hide) an entity that was not exported by the source
      module.  The name of the source module is part of the error.
    * #UndefinedSubImport# is similar to #UndefinedImport#, except that
      it also reports the owner of the undefined subordinate entity.
      We report the owner specified by the programmer in the import list.



%We concentrate on checking a single module and, as a result we do not detect
%errors such as an import from an unknown module.  This check could be 
%done before the module system analysis is performed, either by an external
%tool, or by a separate phase in the compilation pipeline.  
%The validity of an in-scope relation depends on how the names in a module
%are used.  For example, ambiguous names are allowed,
%as long as they are not used anywhere in the program.  Because we have
%abstracted over such uses (by representing them as just entities) we
%do not check the validity of in-scope relations.

In this section we preset functions to validate the import and export 
specifications of a module.  The task of the function #chkModule# is to 
ensure that a module is valid from the point of view of the module system.  
To achieve this we need to check: 
(1) that the module interface is unambiguous; 
(2) that all referenced modules are present, and if so,
     (a) that each import declaration is valid;
     (b) that the export specification is valid.
If some referenced modules are missing, we report that, but skip the remaining
checks, since they might produce bogus error messages.

>chkModule :: 
>   (ModName -> Maybe (Rel Name Entity)) ->
>   Rel QName Entity ->
>   Module ->
>     [ModSysErr]
>
>chkModule expsOf inscp mod
>   = chkAmbigExps mod_exports
>     ++ if null missingModules
>        then chkExpSpec inscp mod
>              ++ [err | (imp,Just exps) <- impSources,
>                        err <- chkImport exps imp]
>        else map MissingModule missingModules
>   where
>   Just mod_exports = expsOf (modName mod)
>
>   missingModules =
>     nub [impSource imp|(imp,Nothing)<-impSources]
>   impSources =
>     [(imp,expsOf (impSource imp))|imp<-modImports mod]


The parameter #expsOf# is a function, which maps module names to their 
export relations.
The parameter #inscp# is the in-scope relation of the module we are checking.
The result of #chkModule# is a list of errors detected in the module.

The export specification and the import declarations are checked by
separate functions. #chkModule#
provides the necessary information to each function, and 
collects their results in a single list of errors.

A module should not contain ambiguities in its interface.  It is however
possible---in fact quite common---to have the same name refer to 
a type constructor and a value constructor.  As we previously discussed,
this is not considered to be an ambiguity as we may determine from the context
which one is meant.

>chkAmbigExps :: Rel Name Entity -> [ModSysErr]
>chkAmbigExps exps = concatMap isAmbig 
>                              (elemsS (dom exps))
>   where
>   isAmbig n = 
>     let (values,types) = partition isValue (applyRel exps n) 
>     in ambig n values ++ ambig n types
>
>   ambig n ents@(_:_:_)    = [AmbiguousExport n ents]
>   ambig n _               = []
 

The function #chkAmbigExps# detects ambiguities in the export relation of 
a module (#exps#). For each name in the domain
of #exps#, we use #applyRel# to compute the list of entities it may refer to.
The function #isAmbig# detects any ambiguities in this list,
considering names in different namespaces separately.  The function
 #isValue# identifies the entities occupying the value namespace.

We have already encountered some similarity between import declaration and
export specifications.  We exploit this again, by using the same function
 #chkEntSpec# to ensure that entries in export and import lists are
defined.  The parameters are essentially the same as in the #mEntSpec#
function of the previous section, but we shall briefly describe them again.
The boolean #isHiding# tells us if we are in the special case of 
hiding imports.  The two functions #errUndef# and #errUndefSub# are new,
and are needed so that we can report different errors for the import 
and export cases.  Finally, we have the specification we are checking, 
and the relation modeling either the exports of the source module, 
or the symbol table of the current module.  

>chkEntSpec :: (Ord j, ToSimple j) =>
>   Bool ->                             -- is it a hiding import?
>   (j -> ModSysErr) ->                 -- report error
>   (j -> Name -> ModSysErr) ->         -- report error
>   EntSpec j ->                        -- the specification
>   Rel j Entity  ->                    -- the relation to check
>   (j->[Entity]) ->                    -- the relation to check
>     [ModSysErr]                       -- detected errors
>
>chkEntSpec isHiding errUndef errUndefSub 
>            (Ent x subspec) rel relfun =
>   case xents of
>     []   -> [errUndef x]
>     ents -> concatMap chk ents
>   where
>   xents = filter consider (relfun x)
>
>   chk ent = 
>     case subspec of
>       Just (Subs subs) -> 
>         map (errUndefSub x)
>             (filter (not . (`memberS` subsInScope)) subs)
>         where
>         subsInScope = 
>           mapS toSimple 
>             $ dom 
>             $ restrictRng (`memberS` owns ent) rel
>       _ -> []
>
>   consider
>     | isHiding && isNothing subspec = const True
>     | otherwise                     = not . isCon

Despite the large number of arguments, the function is quite simple.
We lookup what the name in the specification (#x#) may refer to,
and if nothing was found we report an error.  In case it was defined
we check the subordinate list in two steps.  First we compute 
the names of subordinate entities of #ent# which are also in #rel# 
(#subsInScope#).  Then we make sure that all listed subordinates are 
in #subsInScope#.  We do not consider ambiguities in #chkEntSpec#,
as this is the task of the function #chkAmbigExps#. The predicate
 #consider# has the same role as in #mEntSpec#.

We now describe how to check an export specification. It may
be either implicit or explicit.  Implicit specifications are always correct.
For an explicit specification we need to check all entries in the exports list. 
For entries of the form #module M# we need to ensure that #M# is a valid alias
in this module. An alias is
valid, if it is either introduced by an import declaration, or is
the name of the current module.
For other entries we need to check that the entities
they refer to are defined by using the generic #chkEntSpec#. 

>chkExpSpec :: Rel QName Entity -> Module -> [ModSysErr]
>chkExpSpec inscp mod =
>     case modExpList mod of
>       Nothing   -> []
>       Just exps -> concatMap chk exps
>   where
>   aliases = modName mod : impAs `map` modImports mod
>
>   chk (ModuleExp x)
>     | x `elem` aliases = []
>     | otherwise        = [UndefinedModuleAlias x]
>   chk (EntExp spec) = chkEntSpec False 
>                UndefinedExport UndefinedSubExport 
>                spec inscp (applyRel inscp)

The remaining check we have is the validity of import declarations. 
The process is quite similar to the checks of the export specification
and we have already done all the hard work in #chkEntSpec#.  The function
 #chkImport# just uses #chkEntSpec# to ensure the correctness of the entries
in the specification list of the import.

>chkImport :: Rel Name Entity -> Import -> [ModSysErr]
>chkImport exps imp = concatMap chk (impList imp)
>   where
>   src      = impSource imp
>   chk spec = 
>     chkEntSpec (impHiding imp)
>       (UndefinedImport src) (UndefinedSubImport src)
>       spec exps (applyRel exps)



