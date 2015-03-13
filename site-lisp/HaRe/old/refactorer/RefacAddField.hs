-----------------------------------------------------------------------------
-- |
-- Module      :  RefacAddField
-- Copyright   :  (c) Christopher Brown 2007
--
-- Maintainer  :  cmb21@kent.ac.uk
-- Stability   :  provisional
-- Portability :  portable
--
-- This module contains a transformation for HaRe.
-- Add a field to a constructor and resolve
-- pattern matching by placing references to said
-- field by calls to error; also resolves type signatures (by making them
-- more general if necessary).

-----------------------------------------------------------------------------

module RefacAddField where

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
import RefacUtils hiding (getParams)
import PFE0 (findFile)
import MUtils (( # ))
import RefacLocUtils
-- import System
import System.IO
import Data.Char

refacAddField args
  = do
       when (length args /= 5) (error "Please enter a field name ( _ to omit) and a field type!")
       let
           fileName    = args!!0
           fName       = args!!1
           fType       = args!!2
           row         = read (args!!3)::Int
           col         = read (args!!4)::Int

       AbstractIO.putStrLn "refacAddField"

       modInfo@(inscps, exps, mod, tokList) <- parseSourceFile (fileName)
       case checkCursor fileName row col mod of
         Left errMsg -> do error errMsg
         Right dat ->
            do
             let res = locToPNT fileName (row, col) mod
             let res2 = locToPN fileName (row, col) mod
             let decs = hsDecls mod

             let datDec = definingDecls [res2] decs False True

             let datName = (declToName (head datDec))

             let datPNT = (declToPNT (head datDec))

             -- if the field in question is a record we must get
             -- the name of the record...

             ((_,m), (newToks, newMod)) <- applyRefac (addField datPNT datName res fName fType tokList)
                                                     (Just (inscps, exps, mod, tokList)) fileName

             writeRefactoredFiles False [((fileName, m), (newToks, newMod))]

             AbstractIO.putStrLn "Completed.\n"

checkCursor :: String -> Int -> Int -> HsModuleP -> Either String HsDeclP
checkCursor fileName row col mod
 = case locToTypeDecl of
     Nothing -> Left ("Invalid cursor position. Please place cursor at the beginning of the constructor name!")
     Just decl@(Dec (HsDataDecl loc c tp xs _)) -> Right decl
   where
    locToTypeDecl = find (definesTypeCon (locToPNT fileName (row, col) mod)) (hsModDecls mod)

    -- definesTypeCon pnt (Dec (HsDataDecl loc c tp xs _))
    --  = isDataCon pnt && (findPNT pnt tp)

    definesTypeCon pnt (Dec (HsDataDecl _ _ _ i _))
      = isDataCon pnt && (findPNT pnt i)
    definesTypeCon pnt _ = False




getRecordName (Dec (HsDataDecl s c tp recs i)) pos
  = getRecordName' recs pos 1
      where
        getRecordName' :: [HsConDeclP] -> Int -> Int -> PNT
        getRecordName' ((HsRecDecl _ _ _ _ recs):cons) pos n
         = getRecordName'' recs pos n


        getRecordName'' :: [ ([PNT], HsBangType t)] -> Int -> Int -> PNT
        getRecordName'' [] _ _ = error "Not a valid field position!"
        getRecordName'' (([], _): types) pos n
          = getRecordName'' types pos n
        getRecordName'' ( ((l:ls), t) :types) pos n
         | pos == n   = error $ show l
         | otherwise  = getRecordName'' ((ls, t):types) pos (n+1)

addField datPNT datName pnt fName fType tok (_, _, t)
 = do
      newMod <- addingField pnt fName fType t
      newMod' <- addingFieldInPat datName pnt fType tok newMod
      newMod'' <- addTypeVar datPNT pnt fType tok newMod
      return newMod''

addTypeVar datName pnt fType toks t
 = applyTP (full_buTP (idTP `adhocTP` inDatDeclaration)) t
    where
      inDatDeclaration (dat@(Dec (HsDataDecl a b tp c d))::HsDeclP)
        | (defineLoc datName == (defineLoc.typToPNT.(ghead "inDatDeclaration").flatternTApp) tp) &&
            (fType `elem` (map (pNTtoName.typToPNT) (flatternTApp tp))) == False &&
            isLower (head fType)
          = update dat (Dec (HsDataDecl a b (createTypFunc ((typToPNT.(ghead "inDatDeclaration").flatternTApp) tp)
                                              ( ((nameToTyp fType) : (tail (flatternTApp tp))) )) c d)) dat

      inDatDeclaration (dat@(Dec (HsTypeSig s is c t))::HsDeclP)
       | (pNTtoName datName) `elem` (map (pNTtoName.typToPNT) (flatternTApp t) )
          = do
               let res = changeType t
               if res == t
                 then return dat
                 else update dat (Dec (HsTypeSig s is c res)) dat

      inDatDeclaration  t = return t

      changeType :: HsTypeP -> HsTypeP
      changeType t@(Typ (HsTyFun t1 t2))
            = (Typ (HsTyFun (changeType t1) (changeType t2)))

      changeType t@(Typ (HsTyApp (Typ (HsTyCon p)) t2))
        | (defineLoc datName) == (defineLoc p) &&
          (fType `elem` (map (pNTtoName.typToPNT) (flatternTApp t))) == False &&
            isLower (head fType)
            = (createTypFunc ((typToPNT.(ghead "inDatDeclaration").flatternTApp) t)
                                              ( ((nameToTyp fType) : (tail (flatternTApp t)))))
      changeType t = t

      flatternTApp :: HsTypeP -> [HsTypeP]
      flatternTApp (Typ (HsTyFun t1 t2)) = flatternTApp t1 ++ flatternTApp t2
      flatternTApp (Typ (HsTyApp t1 t2)) = flatternTApp t1 ++ flatternTApp t2
      flatternTApp x = [x]

addingField pnt fName fType t
 = applyTP (stop_tdTP (failTP `adhocTP` inDat)) t
    where
     inDat (dat@(HsConDecl s i c p types)::HsConDeclP)
       | p == pnt = do
                       r <- update dat (HsConDecl s i c p (newTypes types fType)) dat
                       return r
     inDat (dat@(HsRecDecl s i c p types)::HsConDeclP)
       | p == pnt = do
                      r <- update dat (HsRecDecl s i c p (newRecTypes types fName fType)) dat
                      return r
     inDat _ = fail ""


     -- newRecTypes must check that the name is not already declared as a field name
     -- within that constructor.
     newRecTypes xs n a
       | n `elem` (map pNTtoName (unFlattern xs)) = error "There is already a field declared with that name!"
       | otherwise =  ([nameToPNT n], (HsUnBangedType (Typ (HsTyCon (nameToPNT a))))) : xs

     unFlattern :: [([a],b)] -> [a]
     unFlattern [] = []
     unFlattern ((xs, y):xss) = xs ++ (unFlattern xss)


     newTypes xs a = HsUnBangedType (Typ (HsTyCon (nameToPNT a))) : xs

addingFieldInPat datName pnt fType tok t
 = applyTP (stop_tdTP (failTP `adhocTP` inPat)) t
      where
        inPat d@(Dec _::HsDeclP)
          = do
               d'  <- checkPat1 pnt pos d
               d'' <- checkCall pnt pos d'
               return d'
                 where
                    -- checkPat :: (Term t) => PNT -> String -> t -> HsPatP
                    checkPat1 pnt pos t
                      = applyTP (full_buTP (idTP `adhocTP` inP)) t
                    inP pat@(Pat (HsPApp i p))
                      | (defineLoc i) == (defineLoc pnt) =  update pat (Pat (HsPApp i ([nameToPat newName] ++ p))) pat
                      -- RefacUtils.delete (p !! ((read pos::Int)-1)) pat
                    inP x =  return x

                    newName = mkNewName (nameLowered (pNTtoName pnt)) (map pNtoName (definedPNs d)) 1

                    nameLowered (x:xs) = toLower x : xs

                    checkCall pnt pos t
                      = applyTP (stop_tdTP (failTP `adhocTP` conApp)) t
                    -- a constructor application...
                    conApp exp@(Exp (HsApp e1 e2))
                      | defineLoc pnt == (defineLoc.expToPNT.(ghead "inE").flatternApp) exp
                        = update exp (createFuncFromPat ((expToPNT.(ghead "inE").flatternApp) exp)
                                     ([nameToExp "undefined"] ++ ( (tail.flatternApp) exp) )) exp

                    conApp _ = mzero

                    flatternApp :: HsExpP -> [HsExpP]
                    flatternApp (Exp (HsApp e1 e2)) = flatternApp e1 ++ flatternApp e2
                    flatternApp x = [x]

                    (!-) :: Int -> Int -> [a] -> [a]
                    (!-) _ _ [] = []
                    (!-) n pos (x:xs)
                     | n == pos  = xs
                     | otherwise = x : (!-) n (pos + 1) xs

                    newPats :: [HsPatP] -> Int -> Int -> [HsPatP]
                    newPats (p:ps) pos n
                     | n == pos  = ps
                     | otherwise = p : (newPats ps pos (n+1))
        -- inPat x = fail ""

checkPat2 datName pnt pos t
 = applyTP (stop_tdTP (failTP `adhocTP` inPat)) t
      where
        inPat d@(Dec _::HsDeclP)
          = do
               d'' <- addCall (declToName d) pnt pos d
               return d''
        addCall funcName pnt pos t
          = applyTP (stop_tdTP (failTP `adhocTP` (inE funcName))) t

        -- a name associated to a pattern binding somewhere...
        inE funcName exp@(Exp (HsId (HsVar x)))
          | (findPatBind pnt x (read pos::Int) t)
              = update exp  (Exp (HsApp (Exp  (HsApp  (Exp (HsApp (nameToExp ("error" ++ datName))
                                                                  (nameToExp ("\"" ++ (pNTtoName x) ++ "\""))))
                                                      (nameToExp ("\"" ++ (pNTtoName pnt) ++ "\""))))
                                        (nameToExp ("\"" ++ funcName ++ "\"")))) exp
        inE _ x = mzero

findPatBind :: (Term t) => PNT -> PNT -> Int -> t -> Bool
findPatBind pnt x pos
   = (fromMaybe False).(applyTU (once_tdTU (failTU `adhocTU` inBind)))
        where
           inBind (dat@(Pat (HsPApp i types))::HsPatP)
              | pnt == i && checkInTypes x (types!!(pos-1)) = Just True
           inBind _ = Nothing
           checkInTypes x (Pat (HsPId (HsVar typePnt)))
            |  defineLoc x == defineLoc typePnt = True
           checkInTypes _ x = False

-- thePNT id = (PNT (PN (UnQual id) (G (PlainModule "unknown") id (N (Just loc0)))) (Type (TypeInfo (Just Primitive) [] []))  (N (Just loc0)))
