module ListCompIn2 where

--A definition can be removed if it is not used by other declarations.
--Where a definition is removed, it's type signature should also be removed.

--In this Example: remove the defintion 'ys'. it looks a little bit ugly when removing
--the first or last declaration in the 'let' clause.

main = sum [x + 4 | let ys=['h' ..'o'],
                        (x,y,z) <- zipthree [1,3..] ['h'..'o'] [False ..], x > 0] 

zipthree :: [a] -> [b] -> [c] -> [(a,b,c)]
zipthree = \xs ys zs -> case (xs, ys, zs) of
                             ([], _, _) -> [] 
                             (_, [], _) -> [] 
                             (_, _, []) -> [] 
                             (a:as, b:bs, c:cs) -> (a,b,c) : zipthree as bs cs

