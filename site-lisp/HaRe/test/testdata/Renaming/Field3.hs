module Field3 where

{-Rename 'absPoint' to 'abs'. The use of 'abs' in 
  the 'main' function should become qualified. -}


data Point = Pt {pointx, pointy :: Float}

absPoint :: Point -> Float
absPoint p = sqrt (pointx p * pointx p +
                  pointy p * pointy p)

main = absPoint (Pt 1 2)
