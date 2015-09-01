module Field2 where

--Rename field name 'pointx' to 'absPoint' should fail because of name clash.

data Point = Pt {pointx, pointy :: Float}

absPoint :: Point -> Float
absPoint p = sqrt (pointx p * pointx p +
                  pointy p * pointy p)

