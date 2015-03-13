module Statistics where
import Data.List(sortBy)
import OpTypes(cmpBy)
import Data.Char(toUpper)
import PrettyPrint
import Data.Array

ppStatistics descv descu [] = empty
ppStatistics descv descu xs =
       cap descu<+>"count:"<+> n
    $$ "Total"<+>descv<>":" <+> s
    $$ "Average"<+>descv<+>"per"<+>descu<>":"<+> (s `div` n)
    $$ "Median "<+>descv<+>"per"<+>descu<>":"<+> median n (map snd sxs)
    $$ topbottom
    $$ "Histogram:"<+> ppHistogram (map snd xs)
  where
    n = length xs
    s = sum (map snd xs)
    sxs = sortBy (cmpBy snd) xs

    ppObs (n,x) = n<>":"<+>x

    top = 10
    topbottom =
      if n <= 2*top+5
      then "All      :"<+> vcat (map ppObs sxs)
      else "Top    10:"<+> vcat (map ppObs . take top . reverse $ sxs)
        $$ "Bottom 10:"<+> vcat (map ppObs . take top $ sxs)

cap (c:cs) = toUpper c:cs
cap [] = []

-- pre: n == length xs
median n xs =
  if odd n
  then xs!!(n `div` 2)
  else let x1:x2:_ = drop (n `div` 2 - 1) xs
       in (x1+x2) `div` 2

ppHistogram xs = vcat (map bar h)
  where
    bar x = "|"<>replicate (x*scale `div` m) '*'<+> (100*x `div` s)<>"%"
    h = histogram n xs
    m = maximum h
    scale = min m 50
    s = sum h
    n = min 10 (maximum xs) -- number of bars

histogram n xs = elems $ accumArray (+) 0 (0,n-1) [(x*n `div` (m+1),1)|x<-xs]
  where
    m = maximum xs
