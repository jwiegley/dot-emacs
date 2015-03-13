

module RefacRenaming(rename) where

import Prelude hiding (putStrLn)
import System.IO.Unsafe
import AbstractIO (putStrLn)
import Data.Maybe
import Data.List  
import TypeCheck
import RefacUtils 

{-This refactoring renames an indentifier to a user-specified name.
  Conditions: a: the indentifier to be renamed should be defined in the current module.
              b. the user provided name should be a valid name with regard to the name space of the identifier.
              c. the new name should not change the semantics of the program, and should not cause any name 
                 clash/conflict/ambiguity problem in the program. 
  Attention: a. To select an identifier, stop the cursor at the beginning position of any occurrence of the identifier.
             b. Renaming a qualified name will not change the qualifier; 
             c. In current module, an unqualified name won't become qualified after renaming; but, in client modules,
                an unqualified name might become qualified after renaming to avoid ambiguity prolem. In case the new name,
                say 'f', will cause ambiguous occurrence in the current module (this is because the identifier 'f' is
                imported from other modules), the user will be prompted to choose another new name or qualify the use 
                of 'f' before doing renaming.                      
 -}

{-In the current implementation, we assume that module name is same as the file name, but we
  should keep in mind that people also use unnamed modules.
-}
rename args
 = do let fileName  = args!!0
          newName   = args!!1            
          row       = read (args!!2)::Int
          col       = read (args!!3)::Int
      modName <- fileNameToModName fileName
      AbstractIO.putStrLn $ show modName
      (inscps, exps, mod,tokList) <- parseSourceFile fileName 
      

      --AbstractIO.putStrLn x
   --   i <- lift $ ghcTypeCheck "Fish.hs"
   --   AbstractIO.putStrLn i
      let pnt       = locToPNT fileName (row, col) mod   
          defineMod = if isTopLevelPN (pNTtoPN pnt)
                           then (fromJust (hasModName pnt))
                           else modName
      
      unless (pnt /= defaultPNT  && isValidNewName pnt newName) 
         $ error "Invalid cursor position or the new name is invalid!\n" 
      unless (pNTtoName pnt/=newName) $ error "The new name is same as the old name" 
      unless (defineMod == modName ) ( error ("This idenifier is defined in module " ++ modNameToStr defineMod ++ 
                                             ", please do renaming in that module!"))
      if isMainModule modName && pNTtoName pnt == "main"
          then error ("The 'main' function defined in a 'Main' module should not be renamed!")
          else do (mod',((tokList',modified),_))<-doRenaming pnt newName modName mod inscps exps
                                                  ((tokList,unmodified),fileName)
                  if isExported pnt exps  --no matter whether this pn is used or not.
                     then do clients<-clientModsAndFiles modName  --returns [(module name ,filename)] 
                             refactoredClients <- mapM (renameInClientMod pnt newName) clients                           
                             writeRefactoredFiles False $ ((fileName,modified),(tokList',mod')):refactoredClients
                     else writeRefactoredFiles False [((fileName,modified), (tokList',mod'))]

---------Rename a type constructor-------------------------- 
doRenaming oldPNT@(PNT (PN _ (G _ _ _)) (Type _) _) newName modName mod inscps exps env
  =doRenaming' oldPNT newName  mod mod (hsTypeConstrsAndClasses modName) exps env

---------Rename a class name---------------------------------
doRenaming oldPNT@(PNT _ (Class _ _) _) newName modName mod inscps exps env 
  =doRenaming' oldPNT newName  mod mod (hsTypeConstrsAndClasses modName) exps env 

---------Rename a data structure-----------------------------
doRenaming oldPNT@(PNT _ (ConstrOf _  _) _) newName modName mod inscps exps env
  =doRenaming' oldPNT newName mod mod (hsDataConstrs modName)  exps env

---------Rename an instance name-----------------------------
doRenaming oldPNT@(PNT _ (MethodOf i _  _) _) newName modName mod inscps exps env -- Claus
   =runStateT (renameTopLevelVarName oldPNT newName modName inscps  exps mod True True) env

---------Rename a type variable name------------------------------
doRenaming oldPNT@(PNT oldPN@(PN i (S loc)) (Type _) _) newName modName mod inscps exps env
   = do let (before, parent, after)=divideDecls (hsDecls mod) oldPNT
        (parent',toks)<-doRenaming' oldPNT newName parent mod  hsTypeVbls exps  env
        return ((replaceDecls mod (before++parent'++after)),toks) 

---------Rename a field name -------------------------------------
doRenaming oldPNT@(PNT _ (FieldOf con typeInfo) _) newName modName mod inscps exps env 
  =do let (before,parent,after)=divideDecls (hsDecls mod) oldPNT
          siblingNames=siblingFieldNames oldPNT
      (f',d') <- hsFDsFromInside (before++after)  
      if elem newName (siblingNames ++ map pNtoName d')
        then error("Name '"++newName++"'  already existed\n")
        else if elem newName $ fieldNames oldPNT
               then runStateT (renameTopLevelVarName oldPNT newName modName inscps exps mod False False) env
               else runStateT (renameTopLevelVarName oldPNT newName modName inscps exps mod False True) env
--------Rename a value varaible name--------------------------------
doRenaming oldPNT@(PNT oldPN Value loc) newName modName mod inscps exps env 
 = runStateT (applyTP (once_buTP (failTP `adhocTP` renameInMod
                             `adhocTP` renameInMatch
                             `adhocTP` renameInPattern
                             `adhocTP` renameInExp
                             `adhocTP` renameInAlt
                             `adhocTP` renameInStmts)) mod) env
   where 
     -- 1. The name is declared in a module(top level name)
     renameInMod (mod::HsModuleP)
        |isDeclaredIn oldPN mod=renameTopLevelVarName oldPNT newName modName inscps exps mod True True
     renameInMod mod=mzero

     -- 2. The name is declared in a match
     renameInMatch (match::HsMatchP)
        |isDeclaredIn oldPN match=renameLocalVarName oldPN newName match
     renameInMatch match=mzero

     -- 3. The name is declared in a pattern binding.
     renameInPattern (pat:: HsDeclP)
        |isDeclaredIn oldPN pat=renameLocalVarName oldPN newName pat
     renameInPattern pat=mzero
 
     --4.The name is declared in a expression
     renameInExp (exp::HsExpP)
       |isDeclaredIn oldPN exp=renameLocalVarName oldPN newName exp
     renameInExp exp=mzero

     --5.The name is declared in a case alternative
     renameInAlt (alt::HsAltP)
       |isDeclaredIn oldPN alt=renameLocalVarName oldPN newName alt
     renameInAlt alt=mzero

     --6: The name is declared in a statment expression
     renameInStmts (stmts::HsExpP)
       |isDeclaredIn oldPN stmts=renameLocalVarName oldPN newName stmts
     renameInStmts stmts=mzero


doRenaming' oldPNT@(PNT oldPN _ _) newName parent mod fun exps env
 = let (f',d')= fun parent
       (f,d)  =((nub.map pNtoName.filter (not.isQualifiedPN)) f', (nub.map pNtoName) d')
   in if elem newName (d \\ [pNtoName oldPN])
         then error("Name '"++newName++"'  already existed\n")
         else if elem newName f 
               then error ("The new name will cause ambiguous occurrence problem,"
                           ++" please select another new name or qualify the use of "
                           ++ newName ++ " before renaming!\n")             
               else if causeNameClashInExports oldPN newName mod exps
                    then error ("The new name will cause cause conflicting exports, please select another new name!")
                    else runStateT (renamePN oldPN Nothing newName True parent) env 
       
renameTopLevelVarName oldPNT@(PNT oldPN _ _) newName modName inscps exps mod existChecking exportChecking
  =do -- f' contains names imported from other modules; 
      -- d' contains the top level names declared in this module;  
     (f',d') <- hsFDsFromInside mod  
      --filter those qualified free variables in f'
     let (f,d) = ((nub.map pNtoName.filter (not.isQualifiedPN)) f', (nub.map pNtoName) d')
     if elem newName f
       then error ("The new name will cause ambiguous occurrence problem,"
                   ++" please select another new name or qualify the use of ' " 
                   ++ newName ++ "' before renaming!\n")  -- Another implementation option is to add the qualifier
                                                         -- to newName automatically.
       else if existChecking && elem newName (d \\ [pNtoName oldPN])  --only check the declared names here.
             then error ("Name '"++newName++"'  already existed\n") --the same name has been declared in this module.
             else if exportChecking && causeNameClashInExports oldPN newName mod exps
                    then error ("The new name will cause  conflicting exports, please select another new name!") 
                    else if exportChecking && causeAmbiguityInExports oldPN  newName inscps mod
                          then error $"The new name will cause ambiguity in the exports of module "++ show modName ++ ", please select another name!"   
                          else do  -- get all of those declared names visible to oldPN at where oldPN is used.
                                 ds<-hsVisibleNames oldPN mod
                                 -- '\\[pNtoName oldPN]' handles the case in which the new name is same as the old name   
                                 if existChecking && elem newName ((nub (ds `union` f)) \\[pNtoName oldPN])
                                   then error ("Name '"++newName++"'  already existed, or rename '"
                                                ++pNtoName oldPN++ "' to '"++newName++
                                                "' will change the program's semantics!\n")
                                   else if exportChecking && isInScopeAndUnqualified newName inscps
                                          then renamePN oldPN (Just modName) newName True mod
                                          else renamePN oldPN  Nothing newName True mod 

renameLocalVarName oldPN newName t  
  =do (f,d) <- hsFDNamesFromInside t
      if elem newName (d \\ [pNtoName oldPN])  --only check the declared names here.
        then error ("Name '"++newName++"'  already existed\n")
        else do -- get all of those declared names visible to oldPN at where oldPN is used.
                ds<-hsVisibleNames oldPN t
                -- '\\[pNtoName oldPN]' handles the case in which the new name is same as the old name   
                if elem newName ((nub (ds `union` f)) \\[pNtoName oldPN])
                  then error ("Name '"++newName++"'  already existed, or rename '"
                               ++pNtoName oldPN++ "' to '"++newName++
                              "' will change the program's semantics!\n")
                  else renamePN oldPN Nothing newName True t 
      
 
   
renameInClientMod pnt@(PNT oldPN _ _) newName (m, fileName)
  =do (inscps, exps ,mod ,ts) <-parseSourceFile fileName
      let qualifier= hsQualifier pnt inscps 
      if  qualifier == []  --this name is not imported, but it maybe used in the import list
       then 
        do (mod', ((ts',m),f))<-runStateT (renamePN oldPN Nothing newName True mod) ((ts,unmodified), fileName)   
           return ((f,m),(ts',mod'))  
       else
         do if causeNameClashInExports oldPN newName mod exps  
             then error $"The new name will cause conflicting exports in module "++ show m ++ ", please select another name!"
             else do (mod',((ts',modified),f))<-runStateT (do mod'<-qualifyTopLevelVar newName inscps mod
                                                              worker oldPN newName mod' inscps (head qualifier))
                                                           ((ts,unmodified),fileName)
                     return ((f,modified), (ts',mod')) 
          
  where
     qualifyTopLevelVar name inscps t
       = applyTP(full_tdTP(adhocTP idTP atPnt)) t  
        where
           atPnt pnt@(PNT pn ty loc@(N (Just (SrcLoc fileName _  row col))))
              | isTopLevelPNT pnt &&  pNTtoName pnt == name && canBeQualified pnt t 
               = do let qualifier = ghead "qualfyTopLevelVar" $ hsQualifier  pnt inscps                              
                    renamePN pn (Just qualifier) name True pnt
           atPnt x = return x

     worker oldPN newName mod inscps qual  
        = do  vs<-hsVisibleNames oldPN mod   --Does this check names other than variable names?
              if elem newName ((nub vs) \\[pNtoName oldPN])  || isInScopeAndUnqualified newName inscps
                 then renamePN oldPN (Just qual) newName True mod  --rename to qualified Name
                 else do renamePN oldPN Nothing newName True mod 

---------------------------------------------
causeAmbiguityInExports pn  newName inscps mod 
  = isInScopeAndUnqualified (pNtoName pn) inscps &&
    usedWithoutQual newName (hsModExports mod)
   
siblingFieldNames (PNT pn (FieldOf con typeInfo) loc)
  = let cons=constructors typeInfo
        orig1 = pNtoLoc pn
        con=filter (\x->elem orig1 (map pNtoLoc (fromMaybe [] (conFields x)))) cons
    in if con==[] then []
                  else (map pNtoName1 (fromMaybe [] (conFields (head con))))\\ [pNtoName pn]
   where
     pNtoLoc (PN _ orig1) = orig1
     pNtoName1 (PN i _) = i

fieldNames  (PNT pn (FieldOf con typeInfo) _)
 =let cons=constructors typeInfo
  in  (nub. map pNtoName) $ concatMap (fromMaybe [].conFields) cons 
  where  pNtoName (PN i _) = i


isValidNewName oldName newName
 = case oldName of
        (PNT (PN i (G _ _ _)) (Type _) _) ->if isConId newName then True
                                                               else error "Invalid type constructor name!"  
        (PNT _ (Class _ _) _)               ->if isConId newName then True
                                                               else error "Invalid class name!"
        (PNT _ (ConstrOf _  _) _)         ->if isConId newName then True
                                                               else error "Invalid data constructor name!"

        (PNT _ (FieldOf _ _ ) _ )         ->if isVarId newName then True
                                                               else error "Invalid field name!" 

        (PNT _ (MethodOf i _ _) _)          ->if isVarId newName then True 
                                                               else error "Invalid class instance name!"
        
        (PNT (PN i (S loc)) (Type _) _)   ->if isVarId newName then True
                                                               else error "Invalid type variable name!"
 
        (PNT oldPN Value loc)      
          ->  let oldName' = pNTtoName oldName
              in if isVarId oldName' && not (isVarId newName)
                   then error "The new name should be an identifier!"
                   else if isOperator oldName' && not (isOperator newName)
                          then error "The new name should be an operator!"
                          else if (isVarId oldName' && isVarId newName) || 
                                   (isOperator oldName' && isOperator newName)
                                  then True
                                  else error "Invalid new name!"

-- |Divide a declaration list into three parts (before, parent, after) according to the PNT,
-- where 'parent' is the first decl containing the PNT, 'before' are those decls before 'parent'
-- and 'after' are those decls after 'parent'.

divideDecls::[HsDeclP]->PNT->([HsDeclP],[HsDeclP],[HsDeclP])
divideDecls ds pnt
  = let (before,after)=break (\x->findPNT pnt x) ds
    in if (after/=[])
         then (before, [head after], tail after)
         else (ds,[],[]) 
