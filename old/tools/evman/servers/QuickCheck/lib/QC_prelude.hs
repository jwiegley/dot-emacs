module QC_prelude where

import qualified QC_combinators as QC 

pred_True True  = QC.true
pred_True _     = QC.false

pred_False False = QC.true
pred_False _     = QC.false

pred_Tuple0 _    = QC.true
pred_Tuple2 p q (x,y) = p x QC./\ q y
pred_Tuple3 p q r (x,y,z) = p x QC./\ q y QC./\ r z
pred_Tuple4 p q r s (x,y,z,w) = p x QC./\ q y QC./\ r z QC./\ s w

(p %: q) (x:xs) = p x QC./\ q xs
(p %: q) _      = QC.false

nil []          = QC.true
nil _           = QC.false

pred_Just p (Just x)  = p x
pred_Just p _         = QC.false

pred_Nothing Nothing = QC.true
pred_Nothing _       = QC.false

pred_Left p (Left x) = p x
pred_Left _ _        = QC.false

pred_Right p (Right x) = p x
pred_Right _ _         = QC.false

assert_Triv   = QC.true
assert_Absurd = QC.false

