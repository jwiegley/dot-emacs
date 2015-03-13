-----------------------------------------------------------------------------
-- |
-- Module      :  RefacRemoveField
-- Copyright   :  (c) Christopher Brown 2007
--
-- Maintainer  :  cmb21@kent.ac.uk
-- Stability   :  provisional
-- Portability :  portable
--
-- This module contains a transformation for HaRe.
-- Remove a field from a constructor and resolve
-- pattern matching by placing references to said
-- field by calls to error.

-----------------------------------------------------------------------------

module RefacRemoveField where

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

refacRemoveField args
  = do
       let
           fileName    = args!!0
           pos         = args!!1
           row         = read (args!!2)::Int
           col         = read (args!!3)::Int

       AbstractIO.putStrLn "refacRemoveField"

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

                 ((_,m), (newToks, newMod)) <- applyRefac (removeField datName datPNT res pos tokList)
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


removeField datName datPNT pnt pos tok (_, _, t)
 = do
      let fType = getField pnt ((read pos)::Int) t
      let fName = typToPNT (convertBang fType)
      newMod <- removingField pnt pos t
      d <- checkPat2 datName pnt pos newMod
      newMod' <- removingFieldInPat datName pnt pos tok d
      if d /= newMod
        then do
              newD' <- addDecl newMod' Nothing ([errorDecl], Nothing) True
              dataType <- getDataType datPNT newD'
              newTypedMod <- cleanTypeSigs fType fName datPNT datName pnt dataType newD'
              return newTypedMod
        else do
              dataType <- getDataType datPNT newMod'
              newTypedMod <- cleanTypeSigs fType fName datPNT datName pnt dataType newMod'
              return newTypedMod
      where
       errorDecl = (Dec (HsFunBind loc0
                                   [HsMatch loc0 (nameToPNT "errorData")
                                                 listOfPats
                                                 (HsBody (createFunc (nameToPNT ("error" ++ datName)) listOfExps)) []]))

       listOfPats = nameToPat "field" : (nameToPat "dat" : [nameToPat "function"])
       listOfExps = [Exp (HsId (HsVar (nameToPNT "(\"the binding for \" ++ field ++ \" in a pattern binding involving \" ++ dat ++ \" has been removed in function \" ++ function)"
                      )))]

convertBang (HsUnBangedType t) = t
convertBang (HsBangedType t) = t

getField pnt pos
 = (fromMaybe (error "not a valid field to remove!")).(applyTU (once_tdTU (failTU `adhocTU` inDatDeclaration)))
     where
       inDatDeclaration (dat@(HsConDecl _ _ _ i ts)::HsConDeclP)
        | pnt ==  i
          = Just (ts !! (pos-1))

       inDatDeclaration x = Nothing

       flatternTApp :: HsTypeP -> [HsTypeP]
       flatternTApp (Typ (HsTyFun t1 t2)) = flatternTApp t1 ++ flatternTApp t2
       flatternTApp (Typ (HsTyApp t1 t2)) = flatternTApp t1 ++ flatternTApp t2
       flatternTApp x = [x]

getDataType datPNT t
 = applyTU (once_tdTU (failTU `adhocTU` inDatDeclaration)) t
     where
        inDatDeclaration (dat@(Dec (HsDataDecl a b tp c d))::HsDeclP)
         | (defineLoc datPNT == (defineLoc.typToPNT.(ghead "inDatDeclaration").flatternTApp) tp)
            = return dat
        inDatDeclaration d = fail ""

        flatternTApp :: HsTypeP -> [HsTypeP]
        flatternTApp (Typ (HsTyFun t1 t2)) = flatternTApp t1 ++ flatternTApp t2
        flatternTApp (Typ (HsTyApp t1 t2)) = flatternTApp t1 ++ flatternTApp t2
        flatternTApp x = [x]

cleanTypeSigs fType fName datPNT datName pnt dataType t
 = applyTP (full_buTP (idTP `adhocTP` inDatDeclaration)) t
     where
       inDatDeclaration (dat@(Dec (HsDataDecl a b tp c d))::HsDeclP)
        | (defineLoc datPNT == (defineLoc.typToPNT.(ghead "inDatDeclaration").flatternTApp) tp) &&
           (redunParam (tail (flatternTApp tp)) c)
             =
             -- update the data declaration with the type removed!
                update dat (Dec (HsDataDecl a b (createDataFunc ((typToPNT.(ghead "inDatDeclaration").flatternTApp) tp)
                                                  ( (tail (flatternTApp tp)) <-> (convertBang fType))) c d)) dat
       inDatDeclaration (dat@(Dec (HsTypeSig s is c t))::HsDeclP)
        | datName `elem` (map (pNTtoName.typToPNT) (flatternTApp t) )
           = do
               let res = changeType t dataType
               if res == t
                 then return dat
                 else update dat (Dec (HsTypeSig s is c res)) dat
       inDatDeclaration t =return t



       changeType :: HsTypeP -> HsDeclP -> HsTypeP
       changeType t@(Typ (HsTyFun t1 t2)) x
         = (Typ (HsTyFun (changeType t1 x) (changeType t2 x)))

       changeType t@(Typ (HsTyApp t1 t2)) (Dec (HsDataDecl a b tp c d))
        | (defineLoc datPNT) == (defineLoc (convertToCon t1))     &&
          ((pNTtoName fName) `elem` (map (pNTtoName.typToPNT) (flatternTApp t))) &&
          isLower (head (pNTtoName fName)) &&
          (redunParam (tail (flatternTApp tp)) c)
            = (createDataFunc ((typToPNT.(ghead "inDatDeclaration").flatternTApp) t)
                                              ( ( (tail (flatternTApp t)) <-> (convertBang fType))))
       changeType t _ = t

       convertToCon :: HsTypeP -> PNT
       convertToCon (Typ (HsTyFun t1 t2)) = convertToCon t1
       convertToCon (Typ (HsTyApp t1 t2)) = convertToCon t1
       convertToCon (Typ (HsTyCon t1))  = t1
       convertToCon t = defaultPNT

       -- (<->) :: Term t => [a] -> a -> [a]
       (<->) [] _ = []
       (<->) (x:xs) y
          | (pNTtoName (typToPNT x)) == (pNTtoName (typToPNT y))   = (xs <-> y)
          | otherwise =  x : (xs <-> y)


       -- convertBangs :: [HsBangType t] -> [HsTypeP]


       redunParam [] _ = False
       redunParam xs (cs)
        = length (filter id (map (inT cs) (map (pNTtoName.typToPNT) xs))) == 1

       inT2 [] _ = [False]
       inT2 ((HsConDecl s i c p types) :cs) x
            = ((x `elem` (map (pNTtoName.typToPNT) (map convertBang types))) : (cs `inT2` x))

       inT x y = (not.or) (x `inT2` y)

       flatternTApp :: HsTypeP -> [HsTypeP]
       flatternTApp (Typ (HsTyFun t1 t2)) = flatternTApp t1 ++ flatternTApp t2
       flatternTApp (Typ (HsTyApp t1 t2)) = flatternTApp t1 ++ flatternTApp t2
       flatternTApp x = [x]

removingField pnt pos t
 = applyTP (stop_tdTP (failTP `adhocTP` inDat)) t
    where
     inDat (dat@(HsConDecl s i c p types)::HsConDeclP)
       | p == pnt = do
                      r <- update dat (HsConDecl s i c p (newTypes types (read pos::Int))) dat
                      return r
     inDat (dat@(HsRecDecl s i c p types)::HsConDeclP)
       | p == pnt = do
                      r <- update dat (HsRecDecl s i c p (newRecTypes types (read pos::Int))) dat
                      return r
     inDat _ = fail ""

     newRecTypes :: (Eq a) => [([a], b)] -> Int -> [([a], b)]
     newRecTypes xs i = newRecTypes' xs i 1
       where
         newRecTypes' :: (Eq a) => [([a], b)] -> Int -> Int -> [([a], b)]
         newRecTypes' [] i n = error "Please select a valid field position for this constructor!"
         newRecTypes' ((x,y):xs) i n
          | i >= n && i < (n+(length x)) = case newTypes' x i n of
                                                  [] -> xs
                                                  x  -> (x,y) : xs
          | otherwise = (x,y) : (newRecTypes' xs i (n+(length x)))

     newTypes :: [a] -> Int -> [a] -- -> [HsBangType HsTypeP]
     newTypes xs i = newTypes' xs i 1

     newTypes' :: [a] -> Int -> Int -> [a]
     newTypes' [] _ _ = error "Please select a valid field position for this constructor!"
     newTypes' (x:xs) i n
         | n == i    = xs
         | otherwise = x : (newTypes' xs i (n+1))

removingFieldInPat datName pnt pos tok t
 = applyTP (stop_tdTP (failTP `adhocTP` inPat)) t
      where
        inPat d@(Dec _::HsDeclP)
          = do
               d'  <- checkPat1 pnt pos d
               d'' <- checkCall pnt pos d'
               return d''
                 where
                    -- checkPat :: (Term t) => PNT -> String -> t -> HsPatP
                    checkPat1 pnt pos t
                      = applyTP (full_tdTP (idTP `adhocTP` inP)) t
                    inP pat@(Pat (HsPApp i p))
                      | (defineLoc i) == (defineLoc pnt) = RefacUtils.delete (p !! ((read pos::Int)-1)) pat
                    inP x =  return x

                    checkCall pnt pos t
                      = applyTP (stop_tdTP (failTP `adhocTP` conApp)) t
                    -- a constructor application...
                    conApp exp@(Exp (HsApp e1 e2))
                      | defineLoc pnt == (defineLoc.expToPNT.(ghead "inE").flatternApp) exp
                        = RefacUtils.delete ((tail (flatternApp exp)) !! ((read pos::Int)-1)) exp
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
