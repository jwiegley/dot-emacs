module RefacDebug where

import RefacTypeSyn
import RefacLocUtils
import GHC (Session)
import Data.Char
import GHC.Unicode
import AbstractIO
import Data.Maybe
import Data.List
import RefacUtils


refacDebug args
  = do let 
           fileName    = args!!0
           row         = read (args!!1)::Int
           col         = read (args!!2)::Int
               
       AbstractIO.putStrLn "refacDebug"
    
       modInfo@(inscps, exps, mod, tokList) <- parseSourceFile fileName
       
       case checkCursor fileName row col mod of
         Left errMsg -> do error errMsg
         Right decl ->
           do
             let name = (locToPN fileName (row, col) mod)
             result <- applyRefac (addDebug decl name) (Just modInfo) fileName
             writeRefactoredFiles False [result]
             AbstractIO.putStrLn "Done."
             
addDebug decl name (_,_,mod)
 = do
        -- create new declaration
        newDec <- createNewDec decl name
        -- newDec' <- renamePN name Nothing newName False newDec
        mod' <- update decl newDec mod
        return mod' 
          where
          
             -- oldPN = nameToPN name
             newName = (pNtoName name) ++ "'"
        
        
createNewDec d@(Dec (HsPatBind loc p (HsBody e) ds)) name
 = do   newDS <- renamePN name Nothing newName False d
        return (Dec (HsPatBind loc p (HsBody (createNewExp newName 0)) [newDS]))
    where newName =  (pNtoName (patToPN p)) ++ "'"
 
createNewDec (d@(Dec (HsFunBind loc (m@(HsMatch l i1 ps (HsBody e) ds1):ms)))) name
 = do  newDS <- renamePN name Nothing newName False d
 
       return (Dec (HsFunBind loc [HsMatch l i1 createPat (HsBody (createNewExp newName (length ps)))  [newDS]]))
    where newName = (pNTtoName i1) ++ "'"
          createPat = (map nameToPat (map (\a -> [a]) (take (length ps) ['a'..'z'])))
 

createNewExp name 0
 = Exp ((HsApp (nameToExp "seq")) (Exp (HsApp (Exp (HsParen (Exp (HsApp (nameToExp "unsafePerformIO") (Exp (HsParen (Exp (HsApp (nameToExp "print") (Exp (HsParen (nameToExp name) )))))))))) (nameToExp name)  )) )
createNewExp name l
 = Exp ((HsApp (nameToExp "seq")) (Exp (HsApp (Exp (HsParen (Exp (HsApp (nameToExp "unsafePerformIO") (Exp (HsParen (Exp (HsApp (nameToExp "print") (Exp (HsParen (createApp name l) )))))))))) (createApp name l))))

createApp :: String -> Int -> HsExpP
createApp n l
 = createFunc (nameToPNT n) (take l ['a'..'z'] )
    where 
    createFunc :: PNT -> [Char] -> HsExpP
    createFunc pat [exp]
      = (Exp (HsApp (Exp (HsId (HsVar pat))) (nameToExp [exp])))
    createFunc pat (exp:exps)
      = createFunc' (Exp (HsId (HsVar (pat)))) (exp:exps)

    -- | createFunc' is used by createFunc to build up a function application
    createFunc' :: HsExpP -> [Char] -> HsExpP
    createFunc' exp [x]
      = (Exp (HsApp exp (nameToExp [x])))
    createFunc' exp (x:xs)
      = (createFunc' (Exp (HsApp exp (nameToExp [x]))) xs)

 
 
 
renameName (d@(Dec (HsFunBind loc (m@(HsMatch l i1 ps (HsBody e) ds1):ms))))   
 = Dec (HsFunBind loc (map renameName' (m:ms)) )
renameName d@(Dec (HsPatBind loc2 p2 (HsBody e) ds))
 = Dec (HsPatBind loc2 newName (HsBody e) ds)
     where
      newName = (pNtoPat (nameToPN ((pNtoName (patToPN p2)) ++ "'")))

renameName' (HsMatch l i1 ps (HsBody e) ds)
 = HsMatch l newName ps (HsBody e) ds    
    where
        newName = nameToPNT ((pNTtoName i1) ++ "'")
           
--check whether the cursor points to the beginning of the datatype declaration
--taken from RefacADT.hs
checkCursor :: String -> Int -> Int -> HsModuleP -> Either String HsDeclP
checkCursor fileName row col mod
 = case locToTypeDecl of
     Nothing -> Left ("Invalid cursor position. Please place cursor at the beginning of the definiton!")
     Just decl -> Right decl
   where
    locToTypeDecl = find (definesPNT (locToPNT fileName (row, col) mod)) (hsModDecls mod)
    
    definesPNT pnt d@(Dec (HsPatBind loc p e ds))
      = findPNT pnt d
    definesPNT pnt d@(Dec (HsFunBind loc ms)) = findPNT pnt d
    definesPNT pnt _ = False
    



