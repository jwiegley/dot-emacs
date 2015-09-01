-----------------------------------------------------------------------------
-- |
-- Module      :  RefacTypeSig
-- Copyright   :  (c) Christopher Brown 2006
--
-- Maintainer  :  cmb21@kent.ac.uk
-- Stability   :  provisional
-- Portability :  portable
--
-- This module contains a transformation for HaRe.
-- Add type signatures for top-level function definitions

-----------------------------------------------------------------------------

module RefacTypeSig where
 
import PrettyPrint
import PrettyPrint
import PosSyntax
import AbstractIO
import Data.Maybe
import TypedIds
import UniqueNames hiding (srcLoc)
import PNT
import TiPNT
import Data.List
import RefacUtils
import PFE0 (findFile)
import MUtils (( # ))
import RefacLocUtils
-- import System
import System.IO

refacTypeSig args
  = do let fileName   = args!!0

       AbstractIO.putStrLn "refacTypeSig"
       modName1 <- fileNameToModName fileName 

       let modName = convertModName modName1

       -- Parse the input file.
       (inscps, exps, mod, tokList) <- parseSourceFile fileName
       
       let newRefactoredDecls = hsDecls mod
       sigs <- mapM (getSig fileName modName) (filter (/="") (map declToName newRefactoredDecls))

       res <- applyRefac (addTypes (dropWhile (\x -> x == defaultPN) (map (declToPName (map declToName newRefactoredDecls)) newRefactoredDecls)) sigs) (Just (inscps, exps, mod, tokList)) fileName
       -- ((_,m), (newToks, newMod)) <- applyRefac (addType ses modName ) (Just (inscps, exps, mod, tokList)) fileName
           
           
    --   res <- findDefsWithType ses mod
       
    --   AbstractIO.putStrLn $ show res    
        
       writeRefactoredFiles True [res]
       
       (inscps5, exps5, mod5, tokList5) <- parseSourceFile fileName

              
       (mod',((tokList'',modified),_))<-(doCommenting (dropWhile (\x -> x == defaultPN) (map (declToPName (map declToName newRefactoredDecls)) newRefactoredDecls))) fileName mod5 tokList5
              
              
       writeRefactoredFiles True [((fileName, True), (tokList'', mod'))]
           
       AbstractIO.putStrLn "Completed."


doCommenting (x:xs) fileName mod tokList 
    =  runStateT (applyTP ((once_tdTP (failTP `adhocTP` (rmInMod (x:xs) )
                                              ))) mod)
                                                         ((tokList,unmodified),fileName)
                       
           where          
             --1. The definition to be removed is one of the module's top level declarations.
             rmInMod [] mod = return mod
             rmInMod (p:ps) (mod@(HsModule loc name exps imps ds):: HsModuleP)  
                = do ds'<-commentOutTypeSig p ds
                     res2 <- rmInMod ps (HsModule loc name exps imps ds')
                     return res2

addTypes [] _ (_,_,mod) = return mod
addTypes _ [] (_,_,mod) = return mod
addTypes (x:xs) (y:ys) (a,b,mod) = do

                                      mod' <- addTypeSigDecl mod (Just x) ([y], Nothing) True 
                                      
                                      -- commentOutTypeSig x (y:ys)                                   
                                      res <- addTypes xs ys (a,b,mod')
                                      return mod'


{- declToName :: HsDeclP -> String
declToName (Dec (HsFunBind _ ((HsMatch _ pnt _ _ _):xs)))  
 = pNTtoName pnt
declToName (Dec (HsPatBind _ pnt _ _)) = pNTtoName (patToPNT pnt)
declToName _ = "" -}

{- declToPName ::  [ String  ] -> HsDeclP -> PName
declToPName [] _ = defaultPN
declToPName (name: names) d@(Dec (HsFunBind _ ((HsMatch _ pnt _ _ _):xs))) 
 | name == pNTtoName pnt = pNTtoPN pnt
 | otherwise = declToPName  names d
declToPName (name:names) d@(Dec (HsPatBind _ pnt _ _))  -- = pNTtoPN (patToPNT pnt)
 | name == pNTtoName (patToPNT pnt) = pNTtoPN (patToPNT pnt)
 | otherwise = declToPName  names d
declToPName _ _ = defaultPN

-}       
addType ses modName (inscps, exps, mod)
  = do
       res <- findDefsWithType ses mod modName
       return res

convertModName (PlainModule s) = s
convertModName m@(MainModule f) = modNameToStr m        
       
findDefsWithType ses t modName
  = applyTP (stop_tdTP (failTP `adhocTP` inMatch)) t
      where
       inMatch (mat@(Dec (HsFunBind _ ((HsMatch loc1  pnt pats (HsBody e) ds):xs)))::HsDeclP)
         = do
              res3 <- findType pnt t 
              if res3 == [True]
                then do
                       addTypeSigDecl t Nothing ([], Nothing) True

                else do
                        -- create a type signature!
                        res <- getSig  ses modName (pNTtoName pnt)
                        
                        -- addTypeDecl  mat (Just (pNTtoPN pnt))  ([res], Nothing) True
                        
                        addTypeSigDecl t (Just (declToPName [declToName mat] mat)) ([res], Nothing) True
                        --    return [res2]
                       --     inMatch _ = fail "" 
       inMatch (dec@(Dec (HsPatBind _ pnt _ _))::HsDeclP)
         = do
              res3 <- findType (patToPNT pnt) t
              if res3 == [True]
                then
                  return dec
                else do
                  -- create a type signature!
                  res <- getSig  ses modName (pNTtoName (patToPNT pnt))
                        
                  -- addTypeDecl dec (Just (pNTtoPN (patToPNT pnt))) ([res], Nothing) True
                  addTypeSigDecl dec (Just (declToPName [declToName dec] dec)) ([res], Nothing) True

                  
                 --   return [res2]
       inMatch _ = fail ""
{- getSig ses modName name 
 = do
      let types = getTypes name ses modName
      -- error $ show types
      let types1 = cleanTypes (tail types)

      let (context, l) = getContext (head types)
      let types2 = l : types1
   --   let context2 = init context
      let types3 = map (filter (/= '\n')) types2
      let newSig = createTypeSig name context types3
     -- error $ show newSig
      
      return newSig       
getSig name ses modName
 = do
      let types = getTypes name ses modName
      let types1 = cleanTypes (tail types) -- modName

      let (context, l) = getContext (head types) -- modName
      let types2 = l : types1
   --   let context2 = init context
      let newSig = createTypeSig name context types2
     -- error $ show newSig
      
      return newSig -}


 
--createTypeSig :: String -> [String] -> [String] -> HsDeclP
createTypeSig name [] types 
 = Dec (HsTypeSig loc0 [nameToPNT name] [] (createApplication types)) 
createTypeSig name context types  
 = Dec (HsTypeSig loc0 [nameToPNT name] [(Typ (HsTyVar (nameToPNT context)))] (createApplication types)) 
 
 -- (Typ (HsTyVar (nameToTypePNT (head types))) ) )
 

nameToTypePNT :: String -> PNT 
nameToTypePNT id = (PNT (PN (UnQual id) (S loc0)) (Type (TypeInfo {defType = Nothing, constructors = [], fields = []})) (N (Just loc0)))


createApplication [var]
 = (Typ (HsTyVar (nameToTypePNT var)))
createApplication (var:vars)
 = createApplication' (Typ (HsTyVar (nameToTypePNT var))) vars
 
createApplication' x [y]
  = (Typ (HsTyFun x (Typ (HsTyVar (nameToTypePNT y)))))
createApplication' x (y:ys)
  = (createApplication' (Typ (HsTyFun x (Typ (HsTyVar (nameToTypePNT y))))) ys)
       
findType pnt t
  = applyTU (stop_tdTU (failTU `adhocTU` inSig)) t
      where
        inSig (dec@(Dec (HsTypeSig _ _ _ _))::HsDeclP)
          = do
               let res = definesTypeSig (pNTtoPN pnt) dec
               if res == True
                  then return [True]
                  else fail ""
          
        inSig _ = fail ""
              

       
       
       


