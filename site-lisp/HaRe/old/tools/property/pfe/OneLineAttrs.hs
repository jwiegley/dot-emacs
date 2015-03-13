module OneLineAttrs(parseOneLineAttrs) where
import Monad
import Maybe
import Char
--import Attrs

{-+
A parser for attribute descriptions like these two:

  name=hyp, type=string, label="Depends on", optional

  name=conc, type=string/assertion, label="Conclusion", required
-}

--type Attr  = (String, String) -- tag, value
--type Attrs = [Attr]

--parseOneLineAttrs :: String -> Maybe Attrs
parseOneLineAttrs = complete parseOneLineAttrs'

parseOneLineAttrs' = manySep comma parseOneLineAttr
comma s = [((),r)|(",",r)<-lex s]

parseOneLineAttr s =
  [((name,value),r)|(name,r1)<-lex s,
		    (value,r)<-parseValue r1]

parseValue s =
  [(value,r)|("=" ,r1)<-lex s,
	     (value,r)<-lexval r1]
  `orelse`
  [("",s)]

lexval s =
  case s' of
    [] -> []
    '"':_ -> reads s' -- string literal
    _ -> [span isAttr s']
  where
    s'=dropWhile isSpace s
    isAttr c = c/=',' && isPrint c

-- Parsing combinators for the ReadS type:

xs `orelse` ys = take 1 (xs++ys)

many p s = some p s `orelse` empty s
some p s = [(x:xs,r)|(x,r1)<-p s,(xs,r)<-many p r1]
empty s = [([],s)]

prefix p1 p2 s = [xr|(_,r1)<-p1 s,xr<-p2 r1]

someSep sep p s = [(x:xs,r)|(x,r1)<-p s,
                            (xs,r)<-many (prefix sep p) r1]

manySep sep p s = someSep sep p s `orelse` [([],s)]

complete p s = listToMaybe [x|(x,r)<-p s,("","")<-lex r]
