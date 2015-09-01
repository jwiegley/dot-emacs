
import Text.PrettyPrint

main = putStrLn foo


{-
          "["++
          "PprText [((((1,1),(1,61)),ITlineComment \"-- A simple let expression, to ensure the layout is detected\"),\"-- A simple let expression, to ensure the layout is detected\")],"++
          "PprText [((((3,1),(3,7)),ITmodule),\"module\"),((((3,8),(3,22)),ITqconid (\"Layout\",\"LetExpr\")),\"Layout.LetExpr\"),((((3,23),(3,28)),ITwhere),\"where\")],"++
          "PprText [((((5,1),(5,1)),ITvocurly),\"\"),((((5,1),(5,4)),ITvarid \"foo\"),\"foo\"),((((5,5),(5,6)),ITequal),\"=\"),((((5,7),(5,10)),ITlet),\"let\")],"++
          "PprOffset 0 4 "++
           "[PprAbove "++
             "[PprText [((((5,11),(5,11)),ITvocurly),\"\"),((((5,11),(5,12)),ITvarid \"x\"),\"x\"),((((5,13),(5,14)),ITequal),\"=\"),((((5,15),(5,16)),ITinteger 1),\"1\")],"++
              "PprText [((((6,11),(6,11)),ITsemi),\"\"),((((6,11),(6,12)),ITvarid \"y\"),\"y\"),((((6,13),(6,14)),ITequal),\"=\"),((((6,15),(6,16)),ITinteger 2),\"2\")]]],"++
          "PprText [((((7,7),(7,7)),ITvccurly),\"\"),((((7,7),(7,9)),ITin),\"in\"),((((7,10),(7,11)),ITvarid \"x\"),\"x\"),((((7,12),(7,13)),ITvarsym \"+\"),\"+\"),((((7,14),(7,15)),ITvarid \"y\"),\"y\")],"++
          "PprText [((((9,1),(9,1)),ITsemi),\"\")]]"
-}


foo' = render ff
  where
   ff = vcat
    [
     text "-- A simple let expression, to ensure the layout is detected"
    , text ""
    , text "module Layout.LetExpr where"
    , text ""
    , text "foo = let x = 1"
    , text "          y = 2"
    , text "      in x + y"
    ]


foo = render ff
  where
   ff = vcat
    [
     text "-- A simple let expression, to ensure the layout is detected"
    , text ""
    , text "module Layout.LetExpr where"
    , text ""
    , (text "foobarbaz = let") <> ((vcat []) <> text " ") <> (vcat [ text "x = 1"
                                   , text "y = 2"])
    , text "      in x + y"
    ]

foo''' = render ff
  where
   ff = vcat
    [
     text "-- A simple let expression, to ensure the layout is detected"
    , text ""
    , text "module Layout.LetExpr where"
    , text ""
    , (text "foobarbaz = let") <> text " " <> (vcat [ text "x = 1"
                                   , text "y = 2"])
    , text "      in x + y"
    ]

foo'' = render ff
  where
    ff = vcat 
      [
        text "a"
      , text ""
      , nest 3 (text "b") 
      ]
