module HsModuleMaps where
import HsModule
import MUtils
import HsIdent(seqHsIdent)

instance Functor (HsImportDeclI m) where
  fmap f (HsImportDecl s m q as optspec) =
    HsImportDecl s m q as (fmap (apSnd (map (fmap f))) optspec)

instance Functor (HsExportSpecI m) where
  fmap f e =
    case e of
      EntE espec -> EntE (fmap f espec)
      ModuleE mn -> ModuleE mn

instance Functor EntSpec where
  fmap f e =
    case e of
      Var i -> Var (f i)
      Abs i -> Abs (f i)
      AllSubs i -> AllSubs (f i)
      ListSubs i is -> ListSubs (f i) (map (fmap f) is)

--------------------------------------------------------------------------------

mapDecls f (HsModule loc name exps imps ds) = HsModule loc name exps imps (f ds)
seqDecls (HsModule loc name exps imps ds)   = HsModule loc name exps imps # ds

seqImportDecl (HsImportDecl s m q as optspec) =
  HsImportDecl s m q as # seqMaybe (fmap (apSndM (mapM seqEntSpec)) optspec)

seqExportSpec e =
  case e of
    EntE espec -> EntE # seqEntSpec espec
    ModuleE mn -> return (ModuleE mn)

seqEntSpec e =
  case e of
    Var i -> Var # i
    Abs i -> Abs # i
    AllSubs i -> AllSubs # i
    ListSubs i is -> ListSubs # i <# mapM seqHsIdent is

--------------------------------------------------------------------------------

mapModMN f (HsModule loc name exps imps ds) =
  HsModule loc (f name) (mapExpsMN f exps) (mapImpsMN f imps) ds

mapExpsMN f = fmap . map . mapExpMN $ f
mapExpMN f (EntE e) = EntE e
mapExpMN f (ModuleE m) = ModuleE (f m)

mapImpsMN f = map . mapImpMN $ f

mapImpMN f (HsImportDecl loc m q as spec) =
  HsImportDecl loc (f m) q (fmap f as) spec
