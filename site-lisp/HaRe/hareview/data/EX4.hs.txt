user@host:path$ cd ~/.cabal/share/astview-0.2/data
user@host:~/.cabal/share/astview-0.2/data$ ghci Parsers.hs

-- ghci package-messages stripped

*Parsers> :info Parser
data Parser
  = Parser {name :: !String,
            exts :: [String],
            tree :: String -> Tree String}

-- show all registered parsers
*Parsers> map name parsers                                            
["Haskell","CSV","Expr","Java","IsoPascal","C","Glade","List"]

-- get haskell parser
*Parsers> let haskell = head parsers                                 

-- build a sample tree of strings
*Parsers> let sample = tree haskell "main = putStrLn \"Hello World\""

-- draw the tree
*Parsers> putStrLn $ Data.Tree.drawTree sample

-- lengthy output follows
