module RemoveIrrefPatsBaseStruct where

import RemoveIrrefPats 

import HasBaseStruct
import TiClasses(HasDef(..))
import HsPat
import HsExp
import HsDecl
import HsGuards
import HsModule
import HsIdent
import SrcLoc

import MUtils
import Control.Monad(liftM)


-- replaces listOutput, to handle generic lists of declarations
getDecls o = foldOutput noDef (`consDef` noDef) appendDef o
getDDecls o = foldOutput noDef id appendDef o

procDs :: (RemIrrefPats ds (OM i ds), HasDef ds d) => ds -> M i ds
procDs ds = uncurry appendDef # getDDecls (remIrrefPats ds)

-- we translate the patterns, and output pattern bindings,
-- which essentially delay the matching

instance ( GetBaseStruct p (PI i p)
         , HasBaseStruct d (DI i e p ds t c tp) 
         , HasBaseStruct e (EI i e p ds t c)
         , HasDef ds d 
         , RemIrrefPats p (OEM i d)

        ) => RemIrrefPats (PI i p) (OEM i d) where

    remIrrefPats p = do
        p1 <- seqPI (mapPI return remIrrefPats p)
        case p1 of
            HsPIrrPat p2 -> case basestruct p2 of
                Just p3 -> case p3 of
                    HsPWildCard     -> return p3
                    HsPId (HsVar _) -> return p3
                    HsPAsPat i p    -> decl i
                    _               -> decl . head =<< updSt tail 
                    where
                    decl x = do
                        s <- getEnv
                        output $ hsPatBind s p2 (HsBody (hsEVar x)) noDef
                        return (HsPId (HsVar x))
                Nothing -> return p1

            _ -> return p1


-- PRE: e & ds have been processed
instance (RemIrrefPats p (OEM i d), HasDef ds d)
    => RemIrrefPats (HsAlt e p ds) (M i) where

    remIrrefPats (HsAlt s p rhs ds) = do
        (p',ds')   <- withEnv s $ getDecls $ remIrrefPats p
        return (HsAlt s p' rhs (ds `appendDef` ds'))


-- PRE: e & ds have been processed
instance (RemIrrefPats p (OEM i d), HasDef ds d) 
    => RemIrrefPats (HsStmt e p ds) (EM i) where

    remIrrefPats = atoms2Stmt @@ liftM concat . mapM rem  . getStmtList 
        where
        rem (HsGeneratorAtom s p e) = do
            (p',ds) <- getDecls (remIrrefPats p)
            return [HsGeneratorAtom s p' e, HsLetStmtAtom ds]
        rem x = return [x]


-- PRE: e & ds have been processed
instance (RemIrrefPats p (OEM i d), HasDef ds d)
    => RemIrrefPats (HsMatchI i e p ds) (M i) where

    remIrrefPats (HsMatch s i ps rhs ds) = do
        (ps',ds')  <- withEnv s $ getDecls $ remIrrefPats ps
        return (HsMatch s i ps' rhs (ds `appendDef` ds'))
 

-- Expressions
instance ( RemIrrefPats e (EM i)
         , RemIrrefPats p (OEM i d)
         , RemIrrefPats ds (OM i ds)
         , HasBaseStruct e (EI i e p ds t c)
         , HasDef ds d
         )

    => RemIrrefPats (EI i e p ds t c) (EM i) where
    remIrrefPats e = do
        e1 <- seqEI (mapEI return remIrrefPats return (lift . procDs) 
                                                            return return e)

        case e1 of
            HsLambda ps e   -> do
                (ps',ds) <- getDecls (remIrrefPats ps)
                return (HsLambda ps' (hsLet ds e))  -- check null ds?
            HsCase e alts   -> HsCase e # lift (remIrrefPats alts)
            HsDo stms       -> HsDo # remIrrefPats stms 
            HsListComp stms -> HsListComp # remIrrefPats stms
            _               -> return e1




-- Declarations
instance ( RemIrrefPats e (EM i)
         , RemIrrefPats p (OEM i d)
         , RemIrrefPats ds (OM i ds)
         , HasDef ds d
         ) => RemIrrefPats (DI i e p ds t c tp) (OM i ds) where

    remIrrefPats d = do
        d1 <- lift $ seqDI (mapDI return (withEnv (srcLoc d) . remIrrefPats)
                           return procDs return return return d)
        case d1 of
            HsFunBind s ms      -> lift $ HsFunBind s # remIrrefPats ms
            HsPatBind s p r ds  -> do
                (p',ds1) <- lift $ withEnv s $ getDecls $ remIrrefPats p
                output ds1
                return (HsPatBind s p' r ds) 

            _   -> return d1

  
-- Modules

-- Note the i and j !!!  It looks like some mappings over identifiers,
-- do not quite change all identifiers

instance (RemIrrefPats ds (OM j ds), HasDef ds d) 
    => RemIrrefPats (HsModuleI i ds) (M j) where
    remIrrefPats (HsModule s n es is ds) 
        = HsModule s n es is # procDs ds

