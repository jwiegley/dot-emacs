module A2 where
 
import C2 

import D2 hiding (anotherFun)

main xs = sumSquares xs + anotherFun xs  
        
