module PfeBrowserColors(Color,TokenTag(..),loadColorsF,defaultColor) where
import Array
import Fudgets
import Char(toLower)
import TokenTags

type Color = TokenTag
{-
data Color
  = Comment | Reserved | Var | Con | TCon | VarOp | ConOp | Lit
  deriving (Eq,Ord,Ix,Bounded,Show)
-}

--loadColorsF :: (PfeColor -> F a b) -> F a b   
loadColorsF gctx fud =
    conts mkColor colorList $ \colors->
    let a = listArray colorBounds colors
    in fud (a!)
  where
    mkColor colorname =
      wCreateGCtx gctx (gcFgA [colorname,fgColor])

colorBounds = (minBound,maxBound) :: (Color,Color)

colorList =
  [argKey (flagname c) (defaultColor c)|c<-range colorBounds]

flagname c = map toLower (show c)++"color"

defaultColor c =
  case c of
    Comment -> "#00A0A0"
    Reserved -> "brown"
    Con -> "#F08000"
    TCon -> "blue3"
    VarOp -> "red"
    ConOp -> "#F08000"
    Lit -> "purple"
    ModName -> "brown"
    _ -> fgColor
