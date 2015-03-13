data Parser 
  = Parser { name :: String
           , exts :: [String]
           , tree :: String -> Tree String}
