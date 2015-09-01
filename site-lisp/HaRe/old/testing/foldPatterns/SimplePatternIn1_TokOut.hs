module SimplePatternIn1 where

-- try to fold against 'a' in Left a
-- gives an error as you cannot fold against a 
-- pattern binding (changes definition).


(Left a) = head f

f :: (Num a, Num b) =>[Either a b]
f = [Left 1, Right 2]