{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

--------------------------------------------------------------------------------
-- Module      : TypeUtils

-- Maintainer  : refactor-fp\@kent.ac.uk
-- |
--
-- This module contains a collection of program analysis and
-- transformation functions (the API) that work over the Type
-- Decorated AST. Most of the functions defined in the module are
-- taken directly from the API, but in some cases are modified to work
-- with the type decorated AST.
--
-- In particular some new functions have been added to make type
-- decorated AST traversals easier.
--
-- In HaRe, in order to preserve the comments and layout of refactored
-- programs, a refactoring modifies not only the AST but also the
-- token stream, and the program source after the refactoring is
-- extracted from the token stream rather than the AST, for the
-- comments and layout information is kept in the token steam instead
-- of the AST. As a consequence, a program transformation function
-- from this API modifies both the AST and the token stream (unless
-- explicitly stated). So when you build your own program
-- transformations, try to use the API to do the transformation, as
-- this can liberate you from caring about the token stream.
--
-- This type decorated API is still in development. Any suggestions
-- and comments are very much welcome.


--------------------------------------------------------------------------------
module Language.Haskell.Refact.Utils.Binds
   (
     hsBinds
   , replaceBinds
   , getValBindSigs
   , emptyValBinds
   -- , unionBinds
   , HsValBinds(..)
 ) where

-- import Control.Monad.IO.Class ()
import Language.Haskell.Refact.Utils.GhcVersionSpecific
import Language.Haskell.TokenUtils.Utils

-- Modules from GHC
import qualified Bag           as GHC
import qualified BasicTypes    as GHC
import qualified GHC           as GHC

import qualified Data.Generics as SYB

-- ---------------------------------------------------------------------

getValBindSigs :: GHC.HsValBinds GHC.Name -> [GHC.LSig GHC.Name]
getValBindSigs binds = case binds of
    GHC.ValBindsIn  _ sigs -> sigs
    GHC.ValBindsOut _ sigs -> sigs

emptyValBinds :: GHC.HsValBinds GHC.Name
emptyValBinds = GHC.ValBindsIn (GHC.listToBag []) []

unionBinds :: [GHC.HsValBinds GHC.Name] ->  GHC.HsValBinds GHC.Name
unionBinds [] = emptyValBinds
unionBinds [x] = x
unionBinds (x1:x2:xs) = unionBinds ((mergeBinds x1 x2):xs)
  where
    mergeBinds :: GHC.HsValBinds GHC.Name -> GHC.HsValBinds GHC.Name -> GHC.HsValBinds GHC.Name
    mergeBinds (GHC.ValBindsIn b1 s1) (GHC.ValBindsIn b2 s2) = (GHC.ValBindsIn (GHC.unionBags b1 b2) (s1++s2))
    mergeBinds (GHC.ValBindsOut b1 s1) (GHC.ValBindsOut b2 s2) = (GHC.ValBindsOut (b1++b2) (s1++s2))
    mergeBinds y1@(GHC.ValBindsIn _ _) y2@(GHC.ValBindsOut _  _) = mergeBinds y2 y1
    mergeBinds    (GHC.ValBindsOut b1 s1) (GHC.ValBindsIn b2 s2) = (GHC.ValBindsOut (b1++[(GHC.NonRecursive,b2)]) (s1++s2))

-- NOTE: ValBindsIn are found before the Renamer, ValBindsOut after

hsBinds :: (HsValBinds t) => t -> [GHC.LHsBind GHC.Name]
hsBinds t = case hsValBinds t of
  GHC.ValBindsIn binds _sigs -> GHC.bagToList binds
  GHC.ValBindsOut bs _sigs -> concatMap (\(_,b) -> GHC.bagToList b) bs

replaceBinds :: (HsValBinds t) => t -> [GHC.LHsBind GHC.Name] -> t
-- replaceBinds t bs = replaceValBinds t (GHC.ValBindsIn (GHC.listToBag bs) [])
replaceBinds t bs = replaceValBinds t (GHC.ValBindsIn (GHC.listToBag bs) sigs)
  where
    sigs = case hsValBinds t of
      GHC.ValBindsIn  _ s -> s
      GHC.ValBindsOut _ s -> s

-- This class replaces the HsDecls one
class (SYB.Data t) => HsValBinds t where

    -- | Return the binds that are directly enclosed in the
    -- given syntax phrase.
    -- hsValBinds :: t -> [GHC.LHsBind GHC.Name]
    hsValBinds :: t -> GHC.HsValBinds GHC.Name

    -- | Replace the directly enclosed bind list by the given
    --  bind list. Note: This function does not modify the
    --  token stream.
    -- replaceBinds :: t -> [GHC.LHsBind GHC.Name] -> t
    replaceValBinds :: t -> GHC.HsValBinds GHC.Name -> t

    -- | Return True if the specified identifier is declared in the
    -- given syntax phrase.
    -- isDeclaredIn :: GHC.Name -> t -> Bool

    -- | Return the type class definitions that are directly enclosed
    -- in the given syntax phrase. Note: only makes sense for
    -- GHC.RenamedSource
    hsTyDecls :: t -> [[GHC.LTyClDecl GHC.Name]]


instance HsValBinds (GHC.RenamedSource) where
  hsValBinds (grp,_,_,_) = (GHC.hs_valds grp)

  replaceValBinds (grp,imps,exps,docs) binds = (grp',imps,exps,docs)
    where
      grp' = grp {GHC.hs_valds = binds}

  hsTyDecls (grp,_,_,_) = (GHC.hs_tyclds grp)


instance HsValBinds (GHC.HsValBinds GHC.Name) where
  hsValBinds vb = vb
  replaceValBinds _old new = new
  hsTyDecls _ = []

instance HsValBinds (GHC.HsGroup GHC.Name) where
  hsValBinds grp = (GHC.hs_valds grp)

  replaceValBinds (GHC.HsGroup b t i d f de fo w a r v doc) binds
    = (GHC.HsGroup b' t i d f de fo w a r v doc)
       where b' = replaceValBinds b binds

  hsTyDecls _ = []

instance HsValBinds (GHC.HsLocalBinds GHC.Name) where
  hsValBinds lb = case lb of
    GHC.HsValBinds b    -> b
    GHC.HsIPBinds _     -> emptyValBinds
    GHC.EmptyLocalBinds -> emptyValBinds

  replaceValBinds (GHC.HsValBinds _b) new    = (GHC.HsValBinds new)
  replaceValBinds (GHC.HsIPBinds _b) _new    = error "undefined replaceValBinds HsIPBinds"
  replaceValBinds (GHC.EmptyLocalBinds) new  = (GHC.HsValBinds new)

  hsTyDecls _ = []

instance HsValBinds (GHC.GRHSs GHC.Name) where
  hsValBinds (GHC.GRHSs _ lb) = hsValBinds lb

  replaceValBinds (GHC.GRHSs rhss b) new = (GHC.GRHSs rhss (replaceValBinds b new))

  hsTyDecls _ = []

-- ---------------------------------------------------------------------

instance HsValBinds (GHC.MatchGroup GHC.Name) where
  hsValBinds (GHC.MatchGroup matches _) = hsValBinds matches

  replaceValBinds (GHC.MatchGroup matches a) newBinds
               = (GHC.MatchGroup (replaceValBinds matches newBinds) a)

  hsTyDecls _ = []

-- ---------------------------------------------------------------------

instance HsValBinds [GHC.LMatch GHC.Name] where
  hsValBinds ms = unionBinds $ map (\m -> hsValBinds $ GHC.unLoc m) ms

  replaceValBinds [] _        = error "empty match list in replaceValBinds [GHC.LMatch GHC.Name]"
  replaceValBinds ms newBinds = (replaceValBinds (ghead "replaceValBinds" ms) newBinds):(tail ms)

  hsTyDecls _ = []

-- ---------------------------------------------------------------------

instance HsValBinds (GHC.LMatch GHC.Name) where
  hsValBinds m = hsValBinds $ GHC.unLoc m

  replaceValBinds (GHC.L l m) newBinds = (GHC.L l (replaceValBinds m newBinds))

  hsTyDecls _ = []

-- ---------------------------------------------------------------------


instance HsValBinds (GHC.Match GHC.Name) where
  hsValBinds (GHC.Match _ _ grhs) = hsValBinds grhs

  replaceValBinds (GHC.Match p t (GHC.GRHSs rhs _binds)) newBinds
    = (GHC.Match p t (GHC.GRHSs rhs binds'))
      where
        binds' = (GHC.HsValBinds newBinds)

  hsTyDecls _ = []

instance HsValBinds (GHC.HsBind GHC.Name) where
  hsValBinds (GHC.PatBind _p rhs _typ _fvs _) = hsValBinds rhs

  -- TODO: ++AZ++ added for compatibility with hsDecls.
  hsValBinds (GHC.FunBind _ _ matches _ _ _) = hsValBinds matches
  hsValBinds other = error $ "hsValBinds (GHC.HsBind GHC.Name) undefined for:" ++ (showGhc other)

  replaceValBinds (GHC.PatBind p (GHC.GRHSs rhs _binds) typ fvs pt) newBinds
    = (GHC.PatBind p (GHC.GRHSs rhs binds') typ fvs pt)
      where
        binds' = (GHC.HsValBinds newBinds)
  replaceValBinds x _newBinds
      = error $ "replaceValBinds (GHC.HsBind GHC.Name) undefined for:" ++ (showGhc x)

  hsTyDecls _ = []

instance HsValBinds (GHC.HsExpr GHC.Name) where
  hsValBinds (GHC.HsLet ds _) = hsValBinds ds
  hsValBinds x = error $ "TypeUtils.hsValBinds undefined for:" ++ showGhc x

  replaceValBinds (GHC.HsLet binds ex) new = (GHC.HsLet (replaceValBinds binds new) ex)
  replaceValBinds old _new = error $ "undefined replaceValBinds (GHC.HsExpr GHC.Name) for:" ++ (showGhc old)

  hsTyDecls _ = []

instance HsValBinds (GHC.Stmt GHC.Name) where
  hsValBinds (GHC.LetStmt ds) = hsValBinds ds
  hsValBinds other = error $ "hsValBinds (GHC.Stmt GHC.Name) undefined for:" ++ (showGhc other)
  replaceValBinds (GHC.LetStmt ds) new = (GHC.LetStmt (replaceValBinds ds new))
  replaceValBinds old _new = error $ "replaceValBinds (GHC.Stmt GHC.Name) undefined for:" ++ (showGhc old)

  hsTyDecls _ = []

-- ---------------------------------------------------------------------

instance HsValBinds (GHC.LHsBinds GHC.Name) where
  hsValBinds binds = hsValBinds $ GHC.bagToList binds
  replaceValBinds old _new = error $ "replaceValBinds (GHC.LHsBinds GHC.Name) undefined for:" ++ (showGhc old)
  hsTyDecls _ = []

-- ---------------------------------------------------------------------

instance HsValBinds (GHC.LHsBind GHC.Name) where
  hsValBinds (GHC.L _ (GHC.FunBind _ _ matches _ _ _)) = hsValBinds matches
  hsValBinds (GHC.L _ (GHC.PatBind _ rhs _ _ _))       = hsValBinds rhs
  hsValBinds (GHC.L _ (GHC.VarBind _ rhs _))           = hsValBinds rhs
  hsValBinds (GHC.L _ (GHC.AbsBinds _ _ _ _ binds))    = hsValBinds binds


  replaceValBinds (GHC.L l (GHC.FunBind a b matches c d e)) newBinds
               = (GHC.L l (GHC.FunBind a b (replaceValBinds matches newBinds) c d e))
  replaceValBinds (GHC.L l (GHC.PatBind a rhs b c d)) newBinds
               = (GHC.L l (GHC.PatBind a (replaceValBinds rhs newBinds) b c d))
  replaceValBinds (GHC.L l (GHC.VarBind a rhs b)) newBinds
               = (GHC.L l (GHC.VarBind a (replaceValBinds rhs newBinds) b))
  replaceValBinds (GHC.L l (GHC.AbsBinds a b c d binds)) newBinds
               = (GHC.L l (GHC.AbsBinds a b c d (replaceValBinds binds newBinds)))

  hsTyDecls _ = []

-- ---------------------------------------------------------------------

instance HsValBinds ([GHC.LHsBind GHC.Name]) where
  -- hsValBinds xs = concatMap hsValBinds xs -- As in original
  hsValBinds xs = GHC.ValBindsIn (GHC.listToBag xs) []

  replaceValBinds _old (GHC.ValBindsIn b _sigs) = GHC.bagToList b
  replaceValBinds _old (GHC.ValBindsOut rbinds _sigs) = GHC.bagToList $ GHC.unionManyBags $ map (\(_,b) -> b) rbinds

  -- replaceValBinds old new = error ("replaceValBinds (old,new)=" ++ (showGhc (old,new)))

  hsTyDecls _ = []

instance HsValBinds (GHC.LHsExpr GHC.Name) where
  hsValBinds (GHC.L _ (GHC.HsLet binds _ex)) = hsValBinds binds
  hsValBinds _                               = emptyValBinds

  replaceValBinds (GHC.L l (GHC.HsLet binds ex)) newBinds
     = (GHC.L l (GHC.HsLet (replaceValBinds binds newBinds) ex))
  replaceValBinds old _new = error $ "replaceValBinds (GHC.LHsExpr GHC.Name) undefined for:" ++ (showGhc old)

  hsTyDecls _ = []

-- ---------------------------------------------------------------------

instance HsValBinds [GHC.LGRHS GHC.Name] where
  hsValBinds xs = unionBinds $ map hsValBinds xs
  replaceValBinds _old _new = error $ "replaceValBinds [GHC.LGRHS GHC.Name] undefined for:" -- ++ (showGhc old)
  hsTyDecls _ = []

-- ---------------------------------------------------------------------

instance HsValBinds (GHC.LGRHS GHC.Name) where
  hsValBinds (GHC.L _ (GHC.GRHS stmts _expr)) = hsValBinds stmts
  replaceValBinds _old _new = error $ "replaceValBinds (GHC.LHGRHS GHC.Name) undefined for:" -- ++ (showGhc _old)
  hsTyDecls _ = []

-- ---------------------------------------------------------------------

instance HsValBinds [GHC.LStmt GHC.Name] where
  hsValBinds xs = unionBinds $ map hsValBinds xs
  replaceValBinds old _new = error $ "replaceValBinds [GHC.LStmt GHC.Name] undefined for:" ++ (showGhc old)
  hsTyDecls _ = []

-- ---------------------------------------------------------------------

instance HsValBinds (GHC.LStmt GHC.Name) where
  hsValBinds (GHC.L _ (GHC.LetStmt binds)) = hsValBinds binds
  hsValBinds _                             = emptyValBinds
  replaceValBinds old _new = error $ "replaceValBinds (GHC.LStmt GHC.Name) undefined for:" ++ (showGhc old)
  hsTyDecls _ = []

-- ---------------------------------------------------------------------

instance HsValBinds [GHC.LPat GHC.Name] where
  hsValBinds _ = emptyValBinds
  replaceValBinds old _new = error $ "replaceValBinds (GHC.LPat GHC.Name) undefined for:" ++ (showGhc old)
  hsTyDecls _ = []

-- ---------------------------------------------------------------------

instance HsValBinds (GHC.LPat GHC.Name) where
  hsValBinds _ = emptyValBinds
  replaceValBinds old _new = error $ "replaceValBinds (GHC.LPat GHC.Name) undefined for:" ++ (showGhc old)
  hsTyDecls _ = []

-- ---------------------------------------------------------------------

instance HsValBinds (GHC.Name) where
  hsValBinds _ = emptyValBinds
  replaceValBinds old _new = error $ "replaceValBinds (GHC.Name) undefined for:" ++ (showGhc old)
  hsTyDecls _ = []

-- ---------------------------------------------------------------------

instance HsValBinds [GHC.SyntaxExpr GHC.Name] where
  hsValBinds _ = emptyValBinds
  replaceValBinds old _new = error $ "replaceValBinds (GHC.SyntaxExpr GHC.Name) undefined for:" ++ (showGhc old)
  hsTyDecls _ = []

-- ---------------------------------------------------------------------

instance HsValBinds [[GHC.LTyClDecl GHC.Name]] where
  hsValBinds _ = emptyValBinds
  replaceValBinds old _new = error $ "replaceValBinds [[GHC.LTyClDecl GHC.Name]] undefined for:" ++ (showGhc old)
  hsTyDecls _ = []

-- ---------------------------------------------------------------------

instance HsValBinds [GHC.LTyClDecl GHC.Name] where
  hsValBinds _ = emptyValBinds
  replaceValBinds old _new = error $ "replaceValBinds [GHC.LTyClDecl GHC.Name] undefined for:" ++ (showGhc old)
  hsTyDecls _ = []

-- ---------------------------------------------------------------------

instance HsValBinds (GHC.LTyClDecl GHC.Name) where
  hsValBinds _ = error $ "hsValBinds (GHC.LTyClDecl GHC.Name) must pull out tcdMeths"
  replaceValBinds old _new = error $ "replaceValBinds (GHC.LTyClDecl GHC.Name) undefined for:" ++ (showGhc old)
  hsTyDecls _ = []

-- ---------------------------------------------------------------------

instance HsValBinds [GHC.LInstDecl GHC.Name] where
  hsValBinds _ = emptyValBinds
  replaceValBinds old _new = error $ "replaceValBinds [GHC.LInstDecl GHC.Name] undefined for:" ++ (showGhc old)
  hsTyDecls _ = []

-- ---------------------------------------------------------------------

instance HsValBinds (GHC.LInstDecl GHC.Name) where
  hsValBinds _ = emptyValBinds
  replaceValBinds old _new = error $ "replaceValBinds (GHC.LInstDecl GHC.Name) undefined for:" ++ (showGhc old)
  hsTyDecls _ = []

-- ---------------------------------------------------------------------

instance HsValBinds (GHC.LHsType GHC.Name) where
  hsValBinds _ = emptyValBinds
  replaceValBinds old _new = error $ "replaceValBinds (GHC.LHsType GHC.Name) undefined for:" ++ (showGhc old)
  hsTyDecls _ = []

-- ---------------------------------------------------------------------

instance HsValBinds [GHC.LSig GHC.Name] where
  hsValBinds _ = emptyValBinds
  replaceValBinds old _new = error $ "replaceValBinds [GHC.LSig GHC.Name] undefined for:" ++ (showGhc old)
  hsTyDecls _ = []

-- ---------------------------------------------------------------------

instance HsValBinds (GHC.LSig GHC.Name) where
  hsValBinds _ = emptyValBinds
  replaceValBinds old _new = error $ "replaceValBinds (GHC.LSig GHC.Name) undefined for:" ++ (showGhc old)
  hsTyDecls _ = []

-- ---------------------------------------------------------------------

#if __GLASGOW_HASKELL__ > 704
instance HsValBinds [GHC.LFamInstDecl GHC.Name] where
  hsValBinds _ = emptyValBinds
  replaceValBinds old _new = error $ "replaceValBinds [GHC.LFamInstDecl GHC.Name] undefined for:" ++ (showGhc old)
  hsTyDecls _ = []
#endif

-- ---------------------------------------------------------------------

#if __GLASGOW_HASKELL__ > 704
instance HsValBinds (GHC.LFamInstDecl GHC.Name) where
  hsValBinds _ = emptyValBinds
  replaceValBinds old _new = error $ "replaceValBinds (GHC.LFamInstDecl GHC.Name) undefined for:" ++ (showGhc old)
  hsTyDecls _ = []
#endif

-- ---------------------------------------------------------------------

instance HsValBinds (GHC.HsIPBinds GHC.Name) where
  hsValBinds _ = emptyValBinds
  replaceValBinds old _new = error $ "replaceValBinds (GHC.HsIPBinds GHC.Name) undefined for:" ++ (showGhc old)
  hsTyDecls _ = []

-- ---------------------------------------------------------------------
