module ListCompIn2 where
main
    =   sum [x + 4 | (x, y, z) <- zipthree [1, 3 ..]
                                      ['h' .. 'o']
                                      [False ..],
                     x > 0]
 
zipthree :: [a] -> [b] -> [c] -> [(a, b, c)]
 
zipthree
    =   \ xs ys zs ->
            case (xs, ys, zs) of
                ([], _, _) -> []
                (_, [], _) -> []
                (_, _, []) -> []
                ((a : as), (b : bs), (c : cs))
                    -> (a, b, c) : (zipthree as bs cs)
 