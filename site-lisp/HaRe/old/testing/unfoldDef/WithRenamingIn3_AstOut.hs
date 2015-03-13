module WithRenamingIn3 where
partialSquare pow = (\ pow_1 -> pow ^ pow_1)
 
sq x pow = x ^ pow
 