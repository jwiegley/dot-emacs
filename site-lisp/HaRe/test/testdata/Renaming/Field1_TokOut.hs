module Field1 where

--Rename field name 'pointx' to 'pointx1'

data Point = Pt {pointx1, pointy :: Float}

absPoint :: Point -> Float
absPoint p = sqrt (pointx1 p * pointx1 p +
                  pointy p * pointy p)

