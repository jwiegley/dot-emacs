------- Maps for the E functor.

module HsExpMaps where

import HsExpStruct
import HsIdent
import HsGuardsMaps(mapAlt, accAlt, seqAlt)
import HsFieldsMaps
import AccList(accList)
import MUtils

mapEI idf = mapEI2 idf idf

mapEI2 :: (i1 -> i2) -> 
          (i1 -> i2) -> 
          (e1 -> e2) ->
          (p1 -> p2) ->
          (d1 -> d2) ->
          (t1 -> t2) ->
          (c1 -> c2) ->
          EI i1 e1 p1 d1 t1 c1 ->
          EI i2 e2 p2 d2 t2 c2
mapEI2 vf cf ef pf df tf ctxf exp =
  case exp of
    HsId n                 -> HsId (mapHsIdent2 vf cf n)
    HsLit s l              -> HsLit s l
    HsInfixApp x op z      -> HsInfixApp (ef x) (mapHsIdent2 vf cf op) (ef z)
    HsApp x y              -> HsApp (ef x) (ef y)
    HsNegApp s x           -> HsNegApp s (ef x)  
    HsLambda ps e          -> HsLambda (map pf ps) (ef e)
    HsLet ds e             -> HsLet (df ds) (ef e)
    HsIf x y z             -> HsIf (ef x) (ef y) (ef z) 
    HsCase e alts          -> HsCase (ef e) (map (mapAlt ef pf df) alts) 
    HsDo stmts             -> HsDo (mStmt stmts)
    HsTuple xs             -> HsTuple (map ef xs)
    HsList xs              -> HsList (map ef xs)
    HsParen x              -> HsParen (ef x) 
    HsLeftSection x op     -> HsLeftSection (ef x) (mapHsIdent2 vf cf op)
    HsRightSection op y    -> HsRightSection (mapHsIdent2 vf cf op) (ef y) 
    HsRecConstr s n upds   -> HsRecConstr s (cf n) (mapFieldsI vf ef upds)
    HsRecUpdate s e upds   -> HsRecUpdate s (ef e) (mapFieldsI vf ef upds)
    HsEnumFrom x           -> HsEnumFrom (ef x) 
    HsEnumFromTo x y       -> HsEnumFromTo (ef x) (ef y) 
    HsEnumFromThen x y     -> HsEnumFromThen (ef x) (ef y) 
    HsEnumFromThenTo x y z -> HsEnumFromThenTo (ef x) (ef y) (ef z)
    HsListComp stmts       -> HsListComp (mStmt stmts)
    HsExpTypeSig s e c t   -> HsExpTypeSig s (ef e) (ctxf c) (tf t)
    HsAsPat n e            -> HsAsPat (vf n) (ef e)  -- pattern only
    HsWildCard             -> HsWildCard        -- ditto
    HsIrrPat e             -> HsIrrPat (ef e)   -- ditto
  where
    mStmt = mapStmt ef pf df

mapStmt ef pf df stmt =
  case stmt of
    HsGenerator loc p e s -> HsGenerator loc (pf p) (ef e) (m s)
    HsQualifier e s       -> HsQualifier (ef e) (m s)
    HsLetStmt ds s        -> HsLetStmt (df ds) (m s)
    HsLast e              -> HsLast (ef e)
  where
    m = mapStmt ef pf df

-- Accumulator for the E functor.

accEI ::(i -> b -> b) ->
        (e -> b -> b) ->
        (p -> b -> b) ->
        (d -> b -> b) ->
        (t -> b -> b) ->
        (c -> b -> b) ->
        EI i e p d t c ->
        b ->
        b
accEI idf ef pf df tf cf exp =
    case exp of
    HsId n                 -> accHsIdent idf n 
    HsLit s l              -> id
    HsInfixApp x op z      -> ef x . accHsIdent idf op . ef z 
    HsApp x y              -> ef x . ef y 
    HsNegApp s x           -> ef x  
    HsLambda ps e          -> ef e . accList pf ps 
    HsLet ds e             -> ef e . df ds 
    HsIf x y z             -> ef x . ef y . ef z 
    HsCase e alts          -> ef e . accList (accAlt ef pf df) alts 
    HsDo stmts             -> accStmt df ef pf stmts 
    HsTuple xs             -> accList ef xs 
    HsList xs              -> accList ef xs 
    HsParen x              -> ef x  
    HsLeftSection x op     -> ef x . accHsIdent idf op  
    HsRightSection op y    -> accHsIdent idf op . ef y 
    HsRecConstr s n upds   -> idf n . accFieldsI idf ef upds 
    HsRecUpdate s e upds   -> ef e .  accFieldsI idf ef upds   
    HsEnumFrom x           -> ef x 
    HsEnumFromTo x y       -> ef x . ef y  
    HsEnumFromThen x y     -> ef x . ef y  
    HsEnumFromThenTo x y z -> ef x . ef y . ef z 
    HsListComp stmts       -> accStmt df ef pf stmts 
    HsExpTypeSig s e c t   -> ef e . cf c . tf t 

    HsAsPat n e            -> idf n . ef e  -- pattern only
    HsWildCard             -> id            -- ditto
    HsIrrPat e             -> ef e          -- ditto

accStmt df ef pf (HsGenerator _ p e s)    = pf p . ef e . accStmt df ef pf s
accStmt df ef pf (HsQualifier e s)      = ef e . accStmt df ef pf s
accStmt df ef pf (HsLetStmt ds s)       = df ds . accStmt df ef pf s
accStmt df ef pf (HsLast e)             = ef e 

---------


seqEI :: (Monad m,Functor m) =>
        EI (m i) (m e) (m p) (m ds) (m t) (m c) ->
        m (EI i e p ds t c)
seqEI exp =
    case exp of
    HsId n                 -> HsId # seqHsIdent n
    HsLit s l              -> return $ HsLit s l
    HsInfixApp x op z      -> HsInfixApp # x <# seqHsIdent op <# z
    HsApp x y              -> HsApp # x <# y
    HsNegApp s x           -> HsNegApp s # x
    HsLambda ps e          -> HsLambda # sequence ps <# e
    HsLet ds e             -> HsLet # ds <# e
    HsIf x y z             -> HsIf # x <# y <# z
    HsCase e alts          -> HsCase # e <# mapM seqAlt alts
    HsDo stmts             -> HsDo # seqStmt stmts 
    HsTuple xs             -> HsTuple # sequence xs
    HsList xs              -> HsList # sequence xs
    HsParen x              -> HsParen # x
    HsLeftSection x op     -> HsLeftSection # x <# seqHsIdent op 
    HsRightSection op y    -> HsRightSection # seqHsIdent op <# y
    HsRecConstr s n upds   -> HsRecConstr s # n <# seqFieldsI upds
    HsRecUpdate s e upds   -> HsRecUpdate s # e <# seqFieldsI upds
    HsEnumFrom x           -> HsEnumFrom # x
    HsEnumFromTo x y       -> HsEnumFromTo # x <# y
    HsEnumFromThen x y     -> HsEnumFromThen # x <# y
    HsEnumFromThenTo x y z -> HsEnumFromThenTo # x <# y <# z
    HsListComp stmts       -> HsListComp # seqStmt stmts
    HsExpTypeSig s e c t   -> HsExpTypeSig s # e <# c <# t

    HsAsPat n e            -> HsAsPat # n <# e    -- pattern only
    HsWildCard             -> return HsWildCard   -- ditto
    HsIrrPat e             -> HsIrrPat # e        -- ditto


seqStmt (HsGenerator loc p e s) = HsGenerator loc # p <# e <# seqStmt s
seqStmt (HsQualifier e s)   = HsQualifier # e <# seqStmt s
seqStmt (HsLetStmt ds s)    = HsLetStmt # ds <# seqStmt s
seqStmt (HsLast e)          = HsLast # e
