module Field3 where

{-Rename 'absPoint' to 'abs'. The use of 'abs' in 
  the 'main' function should become qualified. -}


data Point = Pt {pointx, pointy :: Float}

abs :: Point -> Float
abs p = sqrt (pointx p * pointx p +
                  pointy p * pointy p)

main = Field3.abs (Pt 1 2)
