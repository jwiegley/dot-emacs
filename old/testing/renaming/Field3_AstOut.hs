module Field3 where
data Point = Pt {pointx, pointy :: Float}
 
abs :: Point -> Float
 
abs p
    =   sqrt
	    (((pointx p) * (pointx p)) +
		 ((pointy p) * (pointy p)))
 
main = Field3.abs (Pt 1 2)
 