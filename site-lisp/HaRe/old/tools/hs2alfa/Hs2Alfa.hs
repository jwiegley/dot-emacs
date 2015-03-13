module Hs2Alfa(transModule,modPath) where
import BaseStruct2Alfa
import TiDecorate(TiDecls(..),TiDecl(..),TiExp(..))
import HsIdent
import HsModule
import qualified UAbstract as U

import MUtils

--default(Int)

transModule = trans :: HsModuleI i (TiDecls NName) -> Env -> U.Module

instance Trans (TiDecls NName) [U.Def] where
  trans (Decs ds env) = concat # extend env (ltrans ds)

instance Trans (TiDecl NName) [U.Def] where
  trans (Dec d) = trans d

instance Trans (TiExp NName) U.Exp where
  trans (Exp e) = trans e
  trans (TiSpec c@(HsCon _) sc ts) = transECon c sc ts
  --trans (TiSpec x _ []) = transEVar x
  trans s@(TiSpec x _ ts) = U.app # inst x <# ltrans ts
  trans (TiTyped e t) = transTyped (Just t) e

  transTyped t (Exp e) = transTyped t e
  transTyped _ e = trans e
