module ConvRefsTypes where
import RefsTypes
import SrcLoc1
import NameMaps
import TypedIds
import UniqueNames
import HsName
import HsIdent(getHSName)
import PrettyPrint
import MUtils(apFst)
--import NoEq

simplifyRefsTypes mrs = [(pp m,simplifyRefsTypes' rs)|(m,rs)<-mrs]

simplifyRefsTypes' refs = simprefs refs
  where
    simprefs rs = [(simpp p,(pp n,simpr dctx,simpsp sp,map (simpos.apFst getHSName) os))|
                    ((dctx,sp),i,os)<-rs,
		    let PN n p=getHSName i]::Refs

    simpr (Def TopLevel) = DT
    simpr (Def Local) = DL
    simpr (Def (ClassDef ())) = DC
    simpr (Def (Instance ())) = DI
    simpr (Def Pattern) = DP
    simpr (Sig _) = U -- hmm
    simpr Use = U
    simpr Logic = U
    simpr FieldLabel = U
    simpr (ExpEnt _) = Ex
    simpr (ImpEnt _ _) = Im

    simpsp ValueNames = V
    simpsp ClassOrTypeNames = T

    simpp (S s) = simpSrcLoc s
    simpes s = (simpf (srcPath s),simpSrcLoc s)

    simpf ('.':'/':s) = s
    simpf s = s

    simpos (PN n o,t) = (simpt t,simpo o)

    --simpo (G (Module m) n (N (Just s))) | s/=loc0 = Right (simpes s) -- Use m and n?
    simpo (G m n ({-N-} _)) = Left (m,n)
    simpo (S s) = Right (simpes s)

    simpt Value = V
    simpt Assertion = V -- !!
    simpt Property = V -- !!
    simpt (Type {}) = T
    simpt (Class {}) = Cl
    simpt (ConstrOf (PN n p) _)  = Co n -- (simpo p)
    simpt (FieldOf (PN n p) _) = Fi n --(simpo p)
    simpt (MethodOf (PN n p) _ _) = Me n --(simpo p)

simpSrcLoc (SrcLoc f n r c) = Pos n r c
