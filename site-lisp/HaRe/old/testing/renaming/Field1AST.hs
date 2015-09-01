module Field1 where
data Point = Pt {pointx1, pointy :: Float}
 
absPoint :: Point -> Float
 
absPoint p
    =   sqrt
            (((pointx1 p) * (pointx1 p)) +
                 ((pointy p) * (pointy p)))
 