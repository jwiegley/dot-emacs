haskell :: Parser
haskell =  Parser "Haskell" [".hs"] buildTreeHaskell

buildTreeHaskell :: String -> Tree String
buildTreeHaskell s = case parseHaskell s of
     Right ast -> flat $ data2tree (ast::HsModule)
     Left ParseError -> Node "ParseError" []

parseHaskell :: (Data a) => String -> Either ParseError a
parseHaskell s = case parseModule s of
  ParseOk p -> unsafeCoerce $ Right p
  _         -> Left ParseError
