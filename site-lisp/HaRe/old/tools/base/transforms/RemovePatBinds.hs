module RemovePatBinds where

--import SrcLoc
import HasBaseStruct
import HsDeclStruct
import HsPatStruct
import HsPatUtil(isPVar)
import HsExpStruct
import HsGuardsStruct
import HsLiteral 
--import HsModule
import HsModuleMaps(mapDecls)
import DefinedNames
import MapDeclM
import HsIdent
import TiNames(ValueId,localVal)

import Data.Maybe(isNothing)
import Control.Monad(liftM)
import StateM
import PrettyPrint(pp,(<>))

-- should add a class here...

remPats pErr = remPatBinds' pErr names
  where names = [ localVal ("patbind__" ++ show n) | n <- [0..] ]

remPatBinds' pErr names = {-mapDecls-} (removePatBinds pErr names)

-- a perhaps more convinient version...
removePatBinds pErr names = withSt names . removePatBinds' err
  where
    -- the error we give if a pattern binding fails
    err pos =
      hsApp (hsId pErr) 
            (hsLit pos $ HsString $ pp $ pos<>": pattern binding failed")

-- removes all pattern bindings from a list of declarations (recursively)
{-
removePatBinds' :: 
    ( GetBaseStruct d (DI i e p [d] t c tp)
    , GetBaseStruct p (PI i p)
    , HasBaseStruct d (DI i e p [d] t c tp)
    , HasBaseStruct p (PI i p)
    , HasBaseStruct e (EI i e p [d] t c)
    , DefinedNames i p
    , ValueId i
    , MapDeclM d [d] )
    => [d] -> StateM [i] [d]
-}
removePatBinds' err ds = liftM concat $ mapM remPB ds
    where
    remPB d = do
        d' <- mapDeclM (removePatBinds' err) d
        case basestruct d' of
            Just d''@(HsPatBind _ pat _ _) 
                | isNothing (isPVar pat) -> do
                    n:_ <- updSt tail
                    return (remPatBind err n d'')
            _ -> return [d']

-- remove pattern bindings in a single declaration, non-recursive 
{-
remPatBind :: 
    ( HasBaseStruct d (DI i e p [d] t c tp)
    , HasBaseStruct p (PI i p)
    , HasBaseStruct e (EI i e p [d] t c)
    , ValueId i
    , DefinedNames i p
    )
    => i -> DI i e p [d] t c tp -> [d]
-}
remPatBind err n (HsPatBind pos pat rhs ds) 
    | nVars == 1 = [hsPatBind pos (hsPId (head vars)) tple ds]
    | otherwise = hsPatBind pos (hsPVar n) tple ds
                    : zipWith (mkDecl pos n nVars) [1..] vars
    where 
    vars    = definedVars pat 
    nVars   = length vars
    caseBody
        | nVars == 1    = hsId (head vars)
        | otherwise     = hsTuple (map hsId vars)

    toCase e = hsCase e 
        [ HsAlt pos pat (HsBody caseBody) ds
        , HsAlt pos hsPWildCard (HsBody (err pos)) []
        ]

    mkDecl pos n nVars x v = hsPatBind pos (hsPId v) (HsBody body) []
        where
        body = hsCase (hsEVar n) [ HsAlt pos pat (HsBody (hsEVar i)) [] ]
        i    = localVal "x"
        wcs  = repeat hsPWildCard 
        pat  = hsPTuple pos $ take (x - 1) wcs ++ [hsPVar i] ++ take (nVars - x) wcs


    tple = HsBody $ case rhs of
        HsBody e -> toCase e
        HsGuard gs -> foldr (\(_,g,e) -> hsIf g (toCase e)) (err pos) gs
