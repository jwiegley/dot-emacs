module LocUtilsSpec (main, spec) where

import           Test.Hspec

import           TestUtils

import qualified FastString as GHC
import qualified GHC        as GHC
-- import qualified GhcMonad   as GHC
import qualified Lexer      as GHC
import qualified SrcLoc     as GHC

-- import Control.Monad.State
import Data.Maybe
import Language.Haskell.Refact.Utils.Binds
import Language.Haskell.Refact.Utils.GhcVersionSpecific
import Language.Haskell.Refact.Utils.LocUtils
import Language.Haskell.Refact.Utils.Monad
import Language.Haskell.Refact.Utils.TokenUtils
import Language.Haskell.Refact.Utils.TypeSyn
import Language.Haskell.Refact.Utils.TypeUtils

import Language.Haskell.TokenUtils.Types
import Language.Haskell.TokenUtils.TokenUtils
import Language.Haskell.TokenUtils.Utils
import Language.Haskell.TokenUtils.GHC.Layout

-- ---------------------------------------------------------------------

main :: IO ()
main = do
  -- setLogger
  hspec spec

spec :: Spec
spec = do

  describe "startEndLocIncComments" $ do
    it "gets start&end loc, including leading and trailing comments" $ do
      (t, toks) <- parsedFileDeclareGhc
      let renamed = fromJust $ GHC.tm_renamed_source t

      let declsr = hsBinds renamed

      let decls = filter isFunOrPatBindR declsr
      let decl = head $ drop 4 decls
      let (startPos,endPos) = startEndLocIncComments toks decl

      (showGhc decl) `shouldBe` "FreeAndDeclared.Declare.unD (FreeAndDeclared.Declare.B y) = y"

      (showToks $ getToks ((18,1),(25,1)) toks) `shouldBe`
             {-
             ("[(((18,1),(18,1)),ITsemi,\"\")," ++
             "(((18,1),(18,5)),ITdata,\"data\")," ++
             "(((18,6),(18,7)),ITconid \"D\",\"D\")," ++
             "(((18,8),(18,9)),ITequal,\"=\")," ++
             "(((18,10),(18,11)),ITconid \"A\",\"A\")," ++
             "(((18,12),(18,13)),ITvbar,\"|\")," ++
             "(((18,14),(18,15)),ITconid \"B\",\"B\")," ++
             "(((18,16),(18,22)),ITconid \"String\",\"String\")," ++
             "(((18,23),(18,24)),ITvbar,\"|\")," ++
             "(((18,25),(18,26)),ITconid \"C\",\"C\")," ++
             "(((20,1),(20,32)),ITlineComment \"-- Retrieve the String from a B\",\"-- Retrieve the String from a B\")," ++
             "(((21,1),(21,1)),ITsemi,\"\")," ++
             "(((21,1),(21,4)),ITvarid \"unD\",\"unD\")," ++
             "(((21,5),(21,6)),IToparen,\"(\")," ++
             "(((21,6),(21,7)),ITconid \"B\",\"B\")," ++
             "(((21,8),(21,9)),ITvarid \"y\",\"y\")," ++
             "(((21,9),(21,10)),ITcparen,\")\")," ++
             "(((21,11),(21,12)),ITequal,\"=\")," ++
             "(((21,13),(21,14)),ITvarid \"y\",\"y\")," ++
             "(((22,1),(22,18)),ITlineComment \"-- But no others.\",\"-- But no others.\")," ++
             "(((24,1),(24,73)),ITlineComment \"-- Infix data constructor, see http://stackoverflow.com/a/6420943/595714\"," ++
                                             "\"-- Infix data constructor, see http://stackoverflow.com/a/6420943/595714\")," ++
             "(((25,1),(25,1)),ITsemi,\"\")," ++
             "(((25,1),(25,5)),ITdata,\"data\")]")
             -}
           "[((18,1),(18,1),\"\"),((18,1),(18,5),\"data\"),((18,6),(18,7),\"D\"),((18,8),(18,9),\"=\"),((18,10),(18,11),\"A\"),((18,12),(18,13),\"|\"),((18,14),(18,15),\"B\"),((18,16),(18,22),\"String\"),((18,23),(18,24),\"|\"),((18,25),(18,26),\"C\"),((20,1),(20,32),\"-- Retrieve the String from a B\"),((21,1),(21,1),\"\"),((21,1),(21,4),\"unD\"),((21,5),(21,6),\"(\"),((21,6),(21,7),\"B\"),((21,8),(21,9),\"y\"),((21,9),(21,10),\")\"),((21,11),(21,12),\"=\"),((21,13),(21,14),\"y\"),((22,1),(22,18),\"-- But no others.\"),((24,1),(24,73),\"-- Infix data constructor, see http://stackoverflow.com/a/6420943/595714\"),((25,1),(25,1),\"\"),((25,1),(25,5),\"data\")]"


      (show $ getStartEndLoc decl) `shouldBe` "((21,1),(21,14))"
      (show   (startPos,endPos)) `shouldBe` "((20,1),(22,18))"

    -- -----------------------------------------------------------------

    it "gets start&end loc, including leading comments which belong" $ do
      (t, toks) <- parsedFileWhereIn3Ghc
      let renamed = fromJust $ GHC.tm_renamed_source t

      -- let declsr = hsBinds renamed

      let Just (GHC.L _ sq) = locToName (14, 1) renamed
      let (Just sqSig, _sigToks) =
            case (getSigAndToks sq renamed toks) of
              Just (sig, sigToks) -> (Just sig, sigToks)
              Nothing -> (Nothing,[])


      -- let decls = filter isFunOrPatBindR declsr

      -- let decl = head $ drop 1 decls
      let (startPos,endPos) = startEndLocIncComments toks sqSig

      -- (showGhc decls) `shouldBe` ""
      (showGhc sqSig) `shouldBe` "Demote.WhereIn3.sq ::\n  GHC.Types.Int -> GHC.Types.Int -> GHC.Types.Int"

      (showToks $ getToks ((11,1),(15,1)) toks) `shouldBe`
             {-
             ("[(((11,10),(11,15)),ITwhere,\"where\"),"++
             "(((11,16),(11,16)),ITvocurly,\"\"),"++
             "(((11,16),(11,17)),ITvarid \"p\",\"p\"),"++
             "(((11,17),(11,18)),ITequal,\"=\"),"++
             "(((11,18),(11,19)),ITinteger 2,\"2\"),"++
             "(((11,21),(11,43)),ITblockComment \"There is a comment\",\"{-There is a comment-}\"),"++
             "(((13,1),(13,1)),ITvccurly,\"\"),"++
             "(((13,1),(13,1)),ITsemi,\"\"),"++
             "(((13,1),(13,3)),ITvarid \"sq\",\"sq\"),"++
             "(((13,4),(13,6)),ITdcolon,\"::\"),"++
             "(((13,7),(13,10)),ITconid \"Int\",\"Int\"),"++
             "(((13,11),(13,13)),ITrarrow,\"->\"),"++
             "(((13,14),(13,17)),ITconid \"Int\",\"Int\"),"++
             "(((13,18),(13,20)),ITrarrow,\"->\"),"++
             "(((13,21),(13,24)),ITconid \"Int\",\"Int\"),"++
             "(((14,1),(14,1)),ITsemi,\"\"),"++
             "(((14,1),(14,3)),ITvarid \"sq\",\"sq\"),"++
             "(((14,4),(14,7)),ITvarid \"pow\",\"pow\"),"++
             "(((14,8),(14,9)),ITinteger 0,\"0\"),"++
             "(((14,10),(14,11)),ITequal,\"=\"),"++
             "(((14,12),(14,13)),ITinteger 0,\"0\"),"++
             "(((15,1),(15,1)),ITsemi,\"\"),"++
             "(((15,1),(15,3)),ITvarid \"sq\",\"sq\")]")
             -}
        "[((11,10),(11,15),\"where\"),((11,16),(11,16),\"\"),((11,16),(11,17),\"p\"),((11,17),(11,18),\"=\"),((11,18),(11,19),\"2\"),((11,21),(11,43),\"{-There is a comment-}\"),((13,1),(13,1),\"\"),((13,1),(13,1),\"\"),((13,1),(13,3),\"sq\"),((13,4),(13,6),\"::\"),((13,7),(13,10),\"Int\"),((13,11),(13,13),\"->\"),((13,14),(13,17),\"Int\"),((13,18),(13,20),\"->\"),((13,21),(13,24),\"Int\"),((14,1),(14,1),\"\"),((14,1),(14,3),\"sq\"),((14,4),(14,7),\"pow\"),((14,8),(14,9),\"0\"),((14,10),(14,11),\"=\"),((14,12),(14,13),\"0\"),((15,1),(15,1),\"\"),((15,1),(15,3),\"sq\")]"

      (show $ getStartEndLoc sqSig) `shouldBe` "((13,1),(13,24))"
      (show   (startPos,endPos)) `shouldBe` "((13,1),(13,24))"

    -- -----------------------------------------------------------------

    it "gets start&end loc, including leading comments which belong 2" $ do
      (t, toks) <- parsedFileTokenTestGhc
      let renamed = fromJust $ GHC.tm_renamed_source t

      let declsr = hsBinds renamed

      let Just (GHC.L _ _sq) = locToName (19, 1) renamed

      let decls = filter isFunOrPatBindR declsr

      let decl = head decls
      let (startPos,endPos) = startEndLocIncComments toks decl

      -- (showGhc decls) `shouldBe` ""
      (showGhc decl) `shouldBe` "TokenTest.foo x y\n  = do { c <- System.IO.getChar;\n         GHC.Base.return c }"

      (showToks $ getToks ((14,1),(26,1)) toks) `shouldBe`
             {-
             ("[(((14,3),(14,6)),ITlet,\"let\"),"++
             "(((14,7),(14,7)),ITvocurly,\"\"),"++
             "(((14,7),(14,10)),ITvarid \"bar\",\"bar\"),"++
             "(((14,11),(14,12)),ITequal,\"=\"),"++
             "(((14,13),(14,14)),ITinteger 3,\"3\"),"++
             "(((15,3),(15,3)),ITvccurly,\"\"),"++
             "(((15,3),(15,5)),ITin,\"in\"),"++
             "(((15,10),(15,11)),ITvarid \"b\",\"b\"),"++
             "(((15,12),(15,13)),ITvarsym \"+\",\"+\"),"++
             "(((15,14),(15,17)),ITvarid \"bar\",\"bar\"),"++
             "(((15,18),(15,38)),ITlineComment \"-- ^trailing comment\",\"-- ^trailing comment\"),"++
             "(((18,1),(18,19)),ITlineComment \"-- leading comment\",\"-- leading comment\"),"++
             "(((19,1),(19,1)),ITsemi,\"\"),"++
             "(((19,1),(19,4)),ITvarid \"foo\",\"foo\"),"++
             "(((19,5),(19,6)),ITvarid \"x\",\"x\"),"++
             "(((19,7),(19,8)),ITvarid \"y\",\"y\"),"++
             "(((19,9),(19,10)),ITequal,\"=\"),"++
             "(((20,3),(20,5)),ITdo,\"do\"),"++
             "(((20,6),(20,6)),ITvocurly,\"\"),"++
             "(((20,6),(20,7)),ITvarid \"c\",\"c\"),"++
             "(((20,8),(20,10)),ITlarrow,\"<-\"),"++
             "(((20,11),(20,18)),ITvarid \"getChar\",\"getChar\"),"++
             "(((21,6),(21,6)),ITsemi,\"\"),"++
             "(((21,6),(21,12)),ITvarid \"return\",\"return\"),"++
             "(((21,13),(21,14)),ITvarid \"c\",\"c\"),"++
             "(((26,1),(26,1)),ITvccurly,\"\"),"++
             "(((26,1),(26,1)),ITsemi,\"\")]")
             -}
          "[((14,3),(14,6),\"let\"),((14,7),(14,7),\"\"),((14,7),(14,10),\"bar\"),((14,11),(14,12),\"=\"),((14,13),(14,14),\"3\"),((15,3),(15,3),\"\"),((15,3),(15,5),\"in\"),((15,10),(15,11),\"b\"),((15,12),(15,13),\"+\"),((15,14),(15,17),\"bar\"),((15,18),(15,38),\"-- ^trailing comment\"),((18,1),(18,19),\"-- leading comment\"),((19,1),(19,1),\"\"),((19,1),(19,4),\"foo\"),((19,5),(19,6),\"x\"),((19,7),(19,8),\"y\"),((19,9),(19,10),\"=\"),((20,3),(20,5),\"do\"),((20,6),(20,6),\"\"),((20,6),(20,7),\"c\"),((20,8),(20,10),\"<-\"),((20,11),(20,18),\"getChar\"),((21,6),(21,6),\"\"),((21,6),(21,12),\"return\"),((21,13),(21,14),\"c\"),((26,1),(26,1),\"\"),((26,1),(26,1),\"\")]"

      (show $ getStartEndLoc decl) `shouldBe` "((19,1),(21,14))"
      (show   (startPos,endPos)) `shouldBe` "((18,1),(21,14))"

    -- -----------------------------------------------------------------

    it "get start&end loc, including leading comments which belong 3" $ do
      (t, toks) <- parsedFileTokenTestGhc
      let renamed = fromJust $ GHC.tm_renamed_source t

      let Just expr = locToExp (15,8) (15,18) renamed :: Maybe (GHC.Located (GHC.HsExpr GHC.Name))

      let (startPos,endPos) = startEndLocIncComments toks expr

      (showGhc expr) `shouldBe` "b GHC.Num.+ bar"

      (showToks $ getToks ((14,1),(26,1)) toks) `shouldBe`
             {-
             ("[(((14,3),(14,6)),ITlet,\"let\"),"++
             "(((14,7),(14,7)),ITvocurly,\"\"),"++
             "(((14,7),(14,10)),ITvarid \"bar\",\"bar\"),"++
             "(((14,11),(14,12)),ITequal,\"=\"),"++
             "(((14,13),(14,14)),ITinteger 3,\"3\"),"++
             "(((15,3),(15,3)),ITvccurly,\"\"),"++
             "(((15,3),(15,5)),ITin,\"in\"),"++
             "(((15,10),(15,11)),ITvarid \"b\",\"b\"),"++
             "(((15,12),(15,13)),ITvarsym \"+\",\"+\"),"++
             "(((15,14),(15,17)),ITvarid \"bar\",\"bar\"),"++
             "(((15,18),(15,38)),ITlineComment \"-- ^trailing comment\",\"-- ^trailing comment\"),"++
             "(((18,1),(18,19)),ITlineComment \"-- leading comment\",\"-- leading comment\"),"++
             "(((19,1),(19,1)),ITsemi,\"\"),"++
             "(((19,1),(19,4)),ITvarid \"foo\",\"foo\"),"++
             "(((19,5),(19,6)),ITvarid \"x\",\"x\"),"++
             "(((19,7),(19,8)),ITvarid \"y\",\"y\"),"++
             "(((19,9),(19,10)),ITequal,\"=\"),"++
             "(((20,3),(20,5)),ITdo,\"do\"),"++
             "(((20,6),(20,6)),ITvocurly,\"\"),"++
             "(((20,6),(20,7)),ITvarid \"c\",\"c\"),"++
             "(((20,8),(20,10)),ITlarrow,\"<-\"),"++
             "(((20,11),(20,18)),ITvarid \"getChar\",\"getChar\"),"++
             "(((21,6),(21,6)),ITsemi,\"\"),"++
             "(((21,6),(21,12)),ITvarid \"return\",\"return\"),"++
             "(((21,13),(21,14)),ITvarid \"c\",\"c\"),"++
             "(((26,1),(26,1)),ITvccurly,\"\"),"++
             "(((26,1),(26,1)),ITsemi,\"\")]")
             -}
         "[((14,3),(14,6),\"let\"),((14,7),(14,7),\"\"),((14,7),(14,10),\"bar\"),((14,11),(14,12),\"=\"),((14,13),(14,14),\"3\"),((15,3),(15,3),\"\"),((15,3),(15,5),\"in\"),((15,10),(15,11),\"b\"),((15,12),(15,13),\"+\"),((15,14),(15,17),\"bar\"),((15,18),(15,38),\"-- ^trailing comment\"),((18,1),(18,19),\"-- leading comment\"),((19,1),(19,1),\"\"),((19,1),(19,4),\"foo\"),((19,5),(19,6),\"x\"),((19,7),(19,8),\"y\"),((19,9),(19,10),\"=\"),((20,3),(20,5),\"do\"),((20,6),(20,6),\"\"),((20,6),(20,7),\"c\"),((20,8),(20,10),\"<-\"),((20,11),(20,18),\"getChar\"),((21,6),(21,6),\"\"),((21,6),(21,12),\"return\"),((21,13),(21,14),\"c\"),((26,1),(26,1),\"\"),((26,1),(26,1),\"\")]"

      (show $ getStartEndLoc expr) `shouldBe` "((15,10),(15,17))"
      (show   (startPos,endPos)) `shouldBe` "((15,3),(15,38))"

    -- ---------------------------------

    it "ignores trailing empty tokens" $ do
      (t, toks) <- parsedFileWhereIn6Ghc
      let renamed = fromJust $ GHC.tm_renamed_source t

      let declsr = hsBinds renamed
      let decls = filter isFunOrPatBindR declsr
      let decl = head $ decls
      (show $ getStartEndLoc decl) `shouldBe` "((13,1),(13,21))"
      let (startPos,endPos) = startEndLocIncComments toks decl

      (showGhc decl) `shouldBe` "Demote.WhereIn6.addthree a b c = a GHC.Num.+ b GHC.Num.+ c"
      -- (SYB.showData SYB.Renamer 0 decl) `shouldBe` "Demote.WhereIn6.addthree a b c = a GHC.Num.+ b GHC.Num.+ c"
      (showToks $ getToks ((13,1),(22,1)) toks) `shouldBe`
             {-
             ("[(((13,1),(13,1)),ITvccurly,\"\"),"++
              "(((13,1),(13,1)),ITsemi,\"\"),"++
              "(((13,1),(13,9)),ITvarid \"addthree\",\"addthree\"),"++
              "(((13,10),(13,11)),ITvarid \"a\",\"a\"),"++
              "(((13,12),(13,13)),ITvarid \"b\",\"b\"),"++
              "(((13,14),(13,15)),ITvarid \"c\",\"c\"),"++
              "(((13,15),(13,16)),ITequal,\"=\"),"++
              "(((13,16),(13,17)),ITvarid \"a\",\"a\"),"++
              "(((13,17),(13,18)),ITvarsym \"+\",\"+\"),"++
              "(((13,18),(13,19)),ITvarid \"b\",\"b\"),"++
              "(((13,19),(13,20)),ITvarsym \"+\",\"+\"),"++
              "(((13,20),(13,21)),ITvarid \"c\",\"c\"),"++
              "(((16,1),(16,1)),ITsemi,\"\")]")
              -}
          "[((13,1),(13,1),\"\"),((13,1),(13,1),\"\"),((13,1),(13,9),\"addthree\"),((13,10),(13,11),\"a\"),((13,12),(13,13),\"b\"),((13,14),(13,15),\"c\"),((13,15),(13,16),\"=\"),((13,16),(13,17),\"a\"),((13,17),(13,18),\"+\"),((13,18),(13,19),\"b\"),((13,19),(13,20),\"+\"),((13,20),(13,21),\"c\"),((16,1),(16,1),\"\")]"

      (show $ getStartEndLoc decl) `shouldBe` "((13,1),(13,21))"
      (show   (startPos,endPos)) `shouldBe` "((13,1),(13,21))"

  -- -------------------------------------------------------------------

  describe "startEndLocIncFowComment" $ do
    it "gets start&end loc, including trailing comments" $ do
      (t, toks) <- parsedFileDeclareGhc
      let renamed = fromJust $ GHC.tm_renamed_source t

      let declsr = hsBinds renamed

      let decls = filter isFunOrPatBindR declsr

      let decl = head $ drop 4 decls
      let (startPos,endPos) = startEndLocIncFowComment toks decl

      (showGhc decl) `shouldBe` "FreeAndDeclared.Declare.unD (FreeAndDeclared.Declare.B y) = y"

      (showToks $ getToks ((18,1),(25,1)) toks) `shouldBe`
             {-
             ("[(((18,1),(18,1)),ITsemi,\"\")," ++
             "(((18,1),(18,5)),ITdata,\"data\")," ++
             "(((18,6),(18,7)),ITconid \"D\",\"D\")," ++
             "(((18,8),(18,9)),ITequal,\"=\")," ++
             "(((18,10),(18,11)),ITconid \"A\",\"A\")," ++
             "(((18,12),(18,13)),ITvbar,\"|\")," ++
             "(((18,14),(18,15)),ITconid \"B\",\"B\")," ++
             "(((18,16),(18,22)),ITconid \"String\",\"String\")," ++
             "(((18,23),(18,24)),ITvbar,\"|\")," ++
             "(((18,25),(18,26)),ITconid \"C\",\"C\")," ++
             "(((20,1),(20,32)),ITlineComment \"-- Retrieve the String from a B\",\"-- Retrieve the String from a B\")," ++
             "(((21,1),(21,1)),ITsemi,\"\")," ++
             "(((21,1),(21,4)),ITvarid \"unD\",\"unD\")," ++
             "(((21,5),(21,6)),IToparen,\"(\")," ++
             "(((21,6),(21,7)),ITconid \"B\",\"B\")," ++
             "(((21,8),(21,9)),ITvarid \"y\",\"y\")," ++
             "(((21,9),(21,10)),ITcparen,\")\")," ++
             "(((21,11),(21,12)),ITequal,\"=\")," ++
             "(((21,13),(21,14)),ITvarid \"y\",\"y\")," ++
             "(((22,1),(22,18)),ITlineComment \"-- But no others.\",\"-- But no others.\")," ++
             "(((24,1),(24,73)),ITlineComment \"-- Infix data constructor, see http://stackoverflow.com/a/6420943/595714\"," ++
                                             "\"-- Infix data constructor, see http://stackoverflow.com/a/6420943/595714\")," ++
             "(((25,1),(25,1)),ITsemi,\"\")," ++
             "(((25,1),(25,5)),ITdata,\"data\")]")
             -}
          "[((18,1),(18,1),\"\"),((18,1),(18,5),\"data\"),((18,6),(18,7),\"D\"),((18,8),(18,9),\"=\"),((18,10),(18,11),\"A\"),((18,12),(18,13),\"|\"),((18,14),(18,15),\"B\"),((18,16),(18,22),\"String\"),((18,23),(18,24),\"|\"),((18,25),(18,26),\"C\"),((20,1),(20,32),\"-- Retrieve the String from a B\"),((21,1),(21,1),\"\"),((21,1),(21,4),\"unD\"),((21,5),(21,6),\"(\"),((21,6),(21,7),\"B\"),((21,8),(21,9),\"y\"),((21,9),(21,10),\")\"),((21,11),(21,12),\"=\"),((21,13),(21,14),\"y\"),((22,1),(22,18),\"-- But no others.\"),((24,1),(24,73),\"-- Infix data constructor, see http://stackoverflow.com/a/6420943/595714\"),((25,1),(25,1),\"\"),((25,1),(25,5),\"data\")]"

      (show $ getStartEndLoc decl) `shouldBe` "((21,1),(21,14))"
      (show   (startPos,endPos)) `shouldBe` "((21,1),(22,18))"

    -- -----------------------------------------------------------------

    it "gets start&end loc, including trailing comments, but not next from next decl 1" $ do
      (t, toks) <- parsedFileDemoteGhc
      let renamed = fromJust $ GHC.tm_renamed_source t

      let declsr = hsBinds renamed

      let decls = filter isFunOrPatBindR declsr

      let decl = head $ drop 2 decls
      let (startPos,endPos) = startEndLocIncFowComment toks decl

      (showGhc decls) `shouldBe` "[MoveDef.Demote.d = 9, MoveDef.Demote.c = 7,\n MoveDef.Demote.toplevel x = MoveDef.Demote.c GHC.Num.* x]"
      (showGhc decl) `shouldBe` "MoveDef.Demote.toplevel x = MoveDef.Demote.c GHC.Num.* x"

      (showToks $ getToks ((4,1),(8,1)) toks) `shouldBe`
             {-
             ("[(((4,1),(4,1)),ITsemi,\"\"),"++
             "(((4,1),(4,9)),ITvarid \"toplevel\",\"toplevel\"),"++
             "(((4,10),(4,11)),ITvarid \"x\",\"x\"),"++
             "(((4,12),(4,13)),ITequal,\"=\"),"++
             "(((4,14),(4,15)),ITvarid \"c\",\"c\"),"++
             "(((4,16),(4,17)),ITstar,\"*\"),"++
             "(((4,18),(4,19)),ITvarid \"x\",\"x\"),"++
             "(((6,1),(6,18)),ITlineComment \"-- c,d :: Integer\",\"-- c,d :: Integer\"),"++
             "(((7,1),(7,1)),ITsemi,\"\"),"++
             "(((7,1),(7,2)),ITvarid \"c\",\"c\"),"++
             "(((7,3),(7,4)),ITequal,\"=\"),"++
             "(((7,5),(7,6)),ITinteger 7,\"7\"),"++
             "(((8,1),(8,1)),ITsemi,\"\"),"++
             "(((8,1),(8,2)),ITvarid \"d\",\"d\")]")
             -}
          "[((4,1),(4,1),\"\"),((4,1),(4,9),\"toplevel\"),((4,10),(4,11),\"x\"),((4,12),(4,13),\"=\"),((4,14),(4,15),\"c\"),((4,16),(4,17),\"*\"),((4,18),(4,19),\"x\"),((6,1),(6,18),\"-- c,d :: Integer\"),((7,1),(7,1),\"\"),((7,1),(7,2),\"c\"),((7,3),(7,4),\"=\"),((7,5),(7,6),\"7\"),((8,1),(8,1),\"\"),((8,1),(8,2),\"d\")]"

      (show $ getStartEndLoc decl) `shouldBe` "((4,1),(4,19))"
      (show   (startPos,endPos)) `shouldBe` "((4,1),(4,19))"

    -- -----------------------------------------------------------------

    it "get start&end loc, including trailing comments, but not next from next decl 2" $ do
      (t, toks) <- parsedFileTokenTestGhc

      let renamed = fromJust $ GHC.tm_renamed_source t
      let decls = hsBinds renamed
      let decl@(GHC.L l _) = head $ tail decls
      (showGhc l) `shouldBe` "test/testdata/TokenTest.hs:(13,1)-(15,16)"
      (showSrcSpan l) `shouldBe` "((13,1),(15,17))"

      let (startPos,endPos) = startEndLocIncFowComment toks decl

      (showGhc decls) `shouldBe` "[TokenTest.foo x y\n   = do { c <- System.IO.getChar;\n          GHC.Base.return c },\n TokenTest.bab a b = let bar = 3 in b GHC.Num.+ bar,\n TokenTest.bib a b\n   = x\n   where\n       x = 3,\n TokenTest.bob a b\n   = x\n   where\n       x = 3]"
      (showGhc decl) `shouldBe` "TokenTest.bab a b = let bar = 3 in b GHC.Num.+ bar"

      (showToks $ getToks ((13,1),(19,1)) toks) `shouldBe`
             {-
             ("[(((13,1),(13,1)),ITvccurly,\"\"),"++
              "(((13,1),(13,1)),ITsemi,\"\"),"++
              "(((13,1),(13,4)),ITvarid \"bab\",\"bab\"),"++
              "(((13,5),(13,6)),ITvarid \"a\",\"a\"),"++
              "(((13,7),(13,8)),ITvarid \"b\",\"b\"),"++
              "(((13,9),(13,10)),ITequal,\"=\"),"++
              "(((14,3),(14,6)),ITlet,\"let\"),"++
              "(((14,7),(14,7)),ITvocurly,\"\"),"++
              "(((14,7),(14,10)),ITvarid \"bar\",\"bar\"),"++
              "(((14,11),(14,12)),ITequal,\"=\"),"++
              "(((14,13),(14,14)),ITinteger 3,\"3\"),"++
              "(((15,3),(15,3)),ITvccurly,\"\"),"++
              "(((15,3),(15,5)),ITin,\"in\"),"++
              "(((15,10),(15,11)),ITvarid \"b\",\"b\"),"++
              "(((15,12),(15,13)),ITvarsym \"+\",\"+\"),"++
              "(((15,14),(15,17)),ITvarid \"bar\",\"bar\"),"++
              "(((15,18),(15,38)),ITlineComment \"-- ^trailing comment\",\"-- ^trailing comment\"),"++
              "(((18,1),(18,19)),ITlineComment \"-- leading comment\",\"-- leading comment\"),"++
              "(((19,1),(19,1)),ITsemi,\"\"),(((19,1),(19,4)),ITvarid \"foo\",\"foo\")]")
              -}
          "[((13,1),(13,1),\"\"),((13,1),(13,1),\"\"),((13,1),(13,4),\"bab\"),((13,5),(13,6),\"a\"),((13,7),(13,8),\"b\"),((13,9),(13,10),\"=\"),((14,3),(14,6),\"let\"),((14,7),(14,7),\"\"),((14,7),(14,10),\"bar\"),((14,11),(14,12),\"=\"),((14,13),(14,14),\"3\"),((15,3),(15,3),\"\"),((15,3),(15,5),\"in\"),((15,10),(15,11),\"b\"),((15,12),(15,13),\"+\"),((15,14),(15,17),\"bar\"),((15,18),(15,38),\"-- ^trailing comment\"),((18,1),(18,19),\"-- leading comment\"),((19,1),(19,1),\"\"),((19,1),(19,4),\"foo\")]"

      (show $ getStartEndLoc decl) `shouldBe` "((13,1),(15,17))"
      (show   (startPos,endPos)) `shouldBe` "((13,1),(15,38))"

  -- -------------------------------------------------------------------

  describe "divideComments" $ do
    it "divides tokens falling between two declarations" $ do
      (_t, toks) <- parsedFileTokenTestGhc

      let commentToks = getToks ((15,18),(18,19)) toks
      let (first,second) = divideComments 15 19 commentToks

      (showToks $ getToks ((15,14),(19,1)) toks) `shouldBe`
            {-
             ("[(((15,14),(15,17)),ITvarid \"bar\",\"bar\"),"++
              "(((15,18),(15,38)),ITlineComment \"-- ^trailing comment\",\"-- ^trailing comment\"),"++
              "(((18,1),(18,19)),ITlineComment \"-- leading comment\",\"-- leading comment\"),"++
              "(((19,1),(19,1)),ITsemi,\"\"),(((19,1),(19,4)),ITvarid \"foo\",\"foo\")]")
            -}
          "[((15,14),(15,17),\"bar\"),((15,18),(15,38),\"-- ^trailing comment\"),((18,1),(18,19),\"-- leading comment\"),((19,1),(19,1),\"\"),((19,1),(19,4),\"foo\")]"

      (showToks first) `shouldBe` "[((15,18),(15,38),\"-- ^trailing comment\")]"
      (showToks second) `shouldBe` "[((18,1),(18,19),\"-- leading comment\")]"

  -- -------------------------------------------------------------------

  describe "tokenise" $ do
    it "converts a string to Haskell tokens" $ do
      -- let startLoc = (GHC.mkRealSrcLoc (GHC.mkFastString "foo") 3 4)
      let startLoc = ((3,4),(3,4))
      let toks = tokenise startLoc 0 False "x y\n  z" :: [GhcPosToken]
      (showToks toks) `shouldBe` {- ("[(((3,4),(3,5)),ITvarid \"x\",\"x\")," ++
                                   "(((3,6),(3,7)),ITvarid \"y\",\"y\")," ++
                                   "(((4,3),(4,4)),ITvarid \"z\",\"z\")]")
                                 -}
         "[((3,4),(3,5),\"x\"),((3,6),(3,7),\"y\"),((4,3),(4,4),\"z\")]"

    it "indents the string of tokens if required" $ do
      -- let startLoc = (GHC.mkRealSrcLoc (GHC.mkFastString "foo") 3 4)
      let startLoc = ((3,4),(3,4))
      let toks = tokenise startLoc 5 True "x y\n  z" :: [GhcPosToken]
      (showToks toks) `shouldBe` {- ("[(((3,9),(3,10)),ITvarid \"x\",\"x\")," ++
                                   "(((3,11),(3,12)),ITvarid \"y\",\"y\")," ++
                                   "(((4,8),(4,9)),ITvarid \"z\",\"z\")]")
                                 -}
                  "[((3,9),(3,10),\"x\"),((3,11),(3,12),\"y\"),((4,8),(4,9),\"z\")]"

  -- -------------------------------------------------------------------
{- moved to haskell-token-utils
  describe "lexStringToRichTokens" $ do
    it "parses a string to Haskell tokens" $ do
      let startLoc = (GHC.mkRealSrcLoc (GHC.mkFastString "foo") 3 4)
      toks <- lexStringToRichTokens startLoc "toplevel x y z"
      (showToks toks) `shouldBe` {- ("[(((3,4),(3,12)),ITvarid \"toplevel\",\"toplevel\")," ++ 
                                   "(((3,13),(3,14)),ITvarid \"x\",\"x\")," ++
                                   "(((3,15),(3,16)),ITvarid \"y\",\"y\")," ++
                                   "(((3,17),(3,18)),ITvarid \"z\",\"z\")]")
                                  -}
         "[((3,4),(3,12),((((3,4),(3,12)),ITvarid \"toplevel\"),\"toplevel\")),((3,13),(3,14),((((3,13),(3,14)),ITvarid \"x\"),\"x\")),((3,15),(3,16),((((3,15),(3,16)),ITvarid \"y\"),\"y\")),((3,17),(3,18),((((3,17),(3,18)),ITvarid \"z\"),\"z\"))]"
-}

  -- -------------------------------------------------------------------

  describe "updateToks" $ do
    it "needs a test or two" $ do
      pending -- "write this test"

  -- -------------------------------------------------------------------

  describe "splitToks" $ do
    it "splits the tokens into a front, middle and end" $ do
      (_t,toks) <- parsedFileCaseBGhc
      let -- renamed = fromJust $ GHC.tm_renamed_source t
          (_front,middle,_back) = splitToks ((4,9),(4,42)) toks
      (showToks middle) `shouldBe`
               {-
               "[(((4,9),(4,11)),ITif,\"if\")," ++
               "(((4,12),(4,13)),IToparen,\"(\")," ++
               "(((4,13),(4,16)),ITvarid \"odd\",\"odd\")," ++
               "(((4,17),(4,18)),ITvarid \"x\",\"x\")," ++
               "(((4,18),(4,19)),ITcparen,\")\")," ++
               "(((4,20),(4,24)),ITthen,\"then\")," ++
               "(((4,25),(4,30)),ITstring \"Odd\",\"\\\"Odd\\\"\")," ++
               "(((4,31),(4,35)),ITelse,\"else\")," ++
               "(((4,36),(4,42)),ITstring \"Even\",\"\\\"Even\\\"\")]"
               -}
               "[((4,9),(4,11),\"if\"),((4,12),(4,13),\"(\"),((4,13),(4,16),\"odd\"),((4,17),(4,18),\"x\"),((4,18),(4,19),\")\"),((4,20),(4,24),\"then\"),((4,25),(4,30),\"\\\"Odd\\\"\"),((4,31),(4,35),\"else\"),((4,36),(4,42),\"\\\"Even\\\"\")]"
      (GHC.showRichTokenStream middle) `shouldBe` "\n\n\n         if (odd x) then \"Odd\" else \"Even\""

    -- ---------------------------------------------

    it "splits the tokens into a front, middle and end 2" $ do
      (_t,toks) <- parsedFileWhereIn6Ghc

      let (_front,middle,_back) = splitToks ((13,10),(13,15)) toks
      (showToks middle) `shouldBe`
              {-
              "[(((13,10),(13,11)),ITvarid \"a\",\"a\"),"
              ++"(((13,12),(13,13)),ITvarid \"b\",\"b\"),"
              ++"(((13,14),(13,15)),ITvarid \"c\",\"c\")]"
              -}
              "[((13,10),(13,11),\"a\"),((13,12),(13,13),\"b\"),((13,14),(13,15),\"c\")]"

      (GHC.showRichTokenStream middle) `shouldBe` "\n\n\n\n\n\n\n\n\n\n\n\n          a b c"

    -- ---------------------------------------------

    it "splits the tokens into a front, middle and end, for a single token" $ do
      (_t,toks) <- parsedFileWhereIn6Ghc

      let (_front,middle,_back) = splitToks ((13,10),(13,11)) toks
      (showToks middle) `shouldBe` "[((13,10),(13,11),\"a\")]"

  -- -------------------------------------------------------------------

{-
  describe "replaceToks" $ do
    it "Replaces a set of tokens in a token stream" $ do
      (t,toks) <- parsedFileCaseBGhc
      let -- renamed = fromJust $ GHC.tm_renamed_source t
          (front,middle,_back) = splitToks ((4,9),(4,42)) toks
      (showToks middle) `shouldBe`
               "[(((4,9),(4,11)),ITif,\"if\")," ++
               "(((4,12),(4,13)),IToparen,\"(\")," ++
               "(((4,13),(4,16)),ITvarid \"odd\",\"odd\")," ++
               "(((4,17),(4,18)),ITvarid \"x\",\"x\")," ++
               "(((4,18),(4,19)),ITcparen,\")\")," ++
               "(((4,20),(4,24)),ITthen,\"then\")," ++
               "(((4,25),(4,30)),ITstring \"Odd\",\"\\\"Odd\\\"\")," ++
               "(((4,31),(4,35)),ITelse,\"else\")," ++
               "(((4,36),(4,42)),ITstring \"Even\",\"\\\"Even\\\"\")]"
      (GHC.showRichTokenStream middle) `shouldBe` "\n\n\n         if (odd x) then \"Odd\" else \"Even\""
      (showToks [(head front)]) `shouldBe` "[(((1,1),(1,7)),ITmodule,\"module\")]"

      let newToks = replaceToks middle (4,17) (4,18) [(head front)]
      (showToks newToks) `shouldBe`
               "[(((4,9),(4,11)),ITif,\"if\")," ++
               "(((4,12),(4,13)),IToparen,\"(\")," ++
               "(((4,13),(4,16)),ITvarid \"odd\",\"odd\")," ++
               -- "(((4,17),(4,18)),ITvarid \"x\",\"x\")," ++
               "(((1,1),(1,7)),ITmodule,\"module\")," ++
               "(((4,18),(4,19)),ITcparen,\")\")," ++
               "(((4,20),(4,24)),ITthen,\"then\")," ++
               "(((4,25),(4,30)),ITstring \"Odd\",\"\\\"Odd\\\"\")," ++
               "(((4,31),(4,35)),ITelse,\"else\")," ++
               "(((4,36),(4,42)),ITstring \"Even\",\"\\\"Even\\\"\")]"
-}
  -- -------------------------------------------------------------------
{-
  describe "replaceTok" $ do
    it "Replaces a single tokens in a token stream" $ do
      (_t,toks) <- parsedFileCaseBGhc

      let -- Just expr = locToExp (4,7) (4,43) renamed :: Maybe (GHC.Located (GHC.HsExpr GHC.Name))
          (_front,middle,_back) = splitToks ((4,1),(4,24)) toks
      (showToks middle) `shouldBe`
               "[(((4,1),(4,1)),ITvocurly,\"\"),"++
               "(((4,1),(4,4)),ITvarid \"foo\",\"foo\"),"++
               "(((4,5),(4,6)),ITvarid \"x\",\"x\"),"++
               "(((4,7),(4,8)),ITequal,\"=\"),"++
               "(((4,9),(4,11)),ITif,\"if\")," ++
               "(((4,12),(4,13)),IToparen,\"(\")," ++
               "(((4,13),(4,16)),ITvarid \"odd\",\"odd\")," ++
               "(((4,17),(4,18)),ITvarid \"x\",\"x\")," ++
               "(((4,18),(4,19)),ITcparen,\")\")," ++
               "(((4,20),(4,24)),ITthen,\"then\")]"

      (GHC.showRichTokenStream middle) `shouldBe` "\n\n\n foo x = if (odd x) then"

      let (GHC.L l t1,_n) = head $ tail middle

      let newTok = (GHC.L l t1,"marimba")
      (showToks [newTok]) `shouldBe` "[(((4,1),(4,4)),ITvarid \"foo\",\"marimba\")]"

      let newToks = replaceTok middle (4,1) newTok
      (showToks newToks) `shouldBe`
               "[(((4,1),(4,1)),ITvocurly,\"\"),"++

               -- "(((4,1),(4,4)),ITvarid \"foo\",\"foo\"),"++
               "(((4,1),(4,4)),ITvarid \"foo\",\"marimba\"),"++ -- the new tok

               "(((4,5),(4,6)),ITvarid \"x\",\"x\"),"++
               "(((4,7),(4,8)),ITequal,\"=\"),"++
               "(((4,9),(4,11)),ITif,\"if\")," ++
               "(((4,12),(4,13)),IToparen,\"(\")," ++
               "(((4,13),(4,16)),ITvarid \"odd\",\"odd\")," ++
               "(((4,17),(4,18)),ITvarid \"x\",\"x\")," ++
               "(((4,18),(4,19)),ITcparen,\")\")," ++
               "(((4,20),(4,24)),ITthen,\"then\")]"

      -- Check for token marker
      let (GHC.L l1 _,_) = head $ tail newToks
      (showGhc l1) `shouldBe` "HaRe:4:1-3"

-}
  -- -------------------------------------------------------------------

  describe "deleteToks" $ do
    it "deletes a set of tokens from a token stream" $ do
      (_t,toks) <- parsedFileCaseBGhc
      let toks' = take 25 toks
      (showToks toks') `shouldBe`
               {-
               "[(((1,1),(1,7)),ITmodule,\"module\")," ++
                "(((1,8),(1,9)),ITconid \"B\",\"B\")," ++
                "(((1,10),(1,15)),ITwhere,\"where\")," ++
                "(((2,1),(2,35)),ITlineComment \"-- Test for refactor of if to case\",\"-- Test for refactor of if to case\")," ++
                "(((4,1),(4,1)),ITvocurly,\"\")," ++
                "(((4,1),(4,4)),ITvarid \"foo\",\"foo\")," ++
                "(((4,5),(4,6)),ITvarid \"x\",\"x\")," ++
                "(((4,7),(4,8)),ITequal,\"=\")," ++
                "(((4,9),(4,11)),ITif,\"if\")," ++
                "(((4,12),(4,13)),IToparen,\"(\")," ++
                "(((4,13),(4,16)),ITvarid \"odd\",\"odd\")," ++
                "(((4,17),(4,18)),ITvarid \"x\",\"x\")," ++
                "(((4,18),(4,19)),ITcparen,\")\")," ++
                "(((4,20),(4,24)),ITthen,\"then\")," ++
                "(((4,25),(4,30)),ITstring \"Odd\",\"\\\"Odd\\\"\")," ++
                "(((4,31),(4,35)),ITelse,\"else\")," ++
                "(((4,36),(4,42)),ITstring \"Even\",\"\\\"Even\\\"\")," ++
                "(((6,1),(6,1)),ITsemi,\"\")," ++
                "(((6,1),(6,4)),ITvarid \"bob\",\"bob\")," ++
                "(((6,5),(6,6)),ITvarid \"x\",\"x\")," ++
                "(((6,7),(6,8)),ITvarid \"y\",\"y\")," ++
                "(((6,9),(6,10)),ITequal,\"=\")," ++
                "(((6,11),(6,12)),ITvarid \"x\",\"x\")," ++
                "(((6,13),(6,14)),ITvarsym \"+\",\"+\")," ++
                "(((6,15),(6,16)),ITvarid \"y\",\"y\")]"
                -}
                "[((1,1),(1,7),\"module\"),((1,8),(1,9),\"B\"),((1,10),(1,15),\"where\"),((2,1),(2,35),\"-- Test for refactor of if to case\"),((4,1),(4,1),\"\"),((4,1),(4,4),\"foo\"),((4,5),(4,6),\"x\"),((4,7),(4,8),\"=\"),((4,9),(4,11),\"if\"),((4,12),(4,13),\"(\"),((4,13),(4,16),\"odd\"),((4,17),(4,18),\"x\"),((4,18),(4,19),\")\"),((4,20),(4,24),\"then\"),((4,25),(4,30),\"\\\"Odd\\\"\"),((4,31),(4,35),\"else\"),((4,36),(4,42),\"\\\"Even\\\"\"),((6,1),(6,1),\"\"),((6,1),(6,4),\"bob\"),((6,5),(6,6),\"x\"),((6,7),(6,8),\"y\"),((6,9),(6,10),\"=\"),((6,11),(6,12),\"x\"),((6,13),(6,14),\"+\"),((6,15),(6,16),\"y\")]"
      (GHC.showRichTokenStream toks') `shouldBe` "module B where\n -- Test for refactor of if to case\n\n foo x = if (odd x) then \"Odd\" else \"Even\"\n\n bob x y = x + y"

      -- ---------------------------------------------------------------

      let newToks = deleteToks toks' (4,9) (4,42)
      (showToks newToks) `shouldBe`
               {-
               "[(((1,1),(1,7)),ITmodule,\"module\")," ++
                "(((1,8),(1,9)),ITconid \"B\",\"B\")," ++
                "(((1,10),(1,15)),ITwhere,\"where\")," ++
                "(((2,1),(2,35)),ITlineComment \"-- Test for refactor of if to case\",\"-- Test for refactor of if to case\")," ++
                "(((4,1),(4,1)),ITvocurly,\"\")," ++
                "(((4,1),(4,4)),ITvarid \"foo\",\"foo\")," ++
                "(((4,5),(4,6)),ITvarid \"x\",\"x\")," ++
                "(((4,7),(4,8)),ITequal,\"=\")," ++
                -- "(((4,9),(4,11)),ITif,\"if\")," ++
                -- "(((4,12),(4,13)),IToparen,\"(\")," ++
                -- "(((4,13),(4,16)),ITvarid \"odd\",\"odd\")," ++
                -- "(((4,17),(4,18)),ITvarid \"x\",\"x\")," ++
                -- "(((4,18),(4,19)),ITcparen,\")\")," ++
                -- "(((4,20),(4,24)),ITthen,\"then\")," ++
                -- "(((4,25),(4,30)),ITstring \"Odd\",\"\\\"Odd\\\"\")," ++
                -- "(((4,31),(4,35)),ITelse,\"else\")," ++
                -- "(((4,36),(4,42)),ITstring \"Even\",\"\\\"Even\\\"\")," ++
                "(((6,1),(6,1)),ITsemi,\"\")," ++
                "(((6,1),(6,4)),ITvarid \"bob\",\"bob\")," ++
                "(((6,5),(6,6)),ITvarid \"x\",\"x\")," ++
                "(((6,7),(6,8)),ITvarid \"y\",\"y\")," ++
                "(((6,9),(6,10)),ITequal,\"=\")," ++
                "(((6,11),(6,12)),ITvarid \"x\",\"x\")," ++
                "(((6,13),(6,14)),ITvarsym \"+\",\"+\")," ++
                "(((6,15),(6,16)),ITvarid \"y\",\"y\")]"
                -}
                "[((1,1),(1,7),\"module\"),((1,8),(1,9),\"B\"),((1,10),(1,15),\"where\"),((2,1),(2,35),\"-- Test for refactor of if to case\"),((4,1),(4,1),\"\"),((4,1),(4,4),\"foo\"),((4,5),(4,6),\"x\"),((4,7),(4,8),\"=\"),((6,1),(6,1),\"\"),((6,1),(6,4),\"bob\"),((6,5),(6,6),\"x\"),((6,7),(6,8),\"y\"),((6,9),(6,10),\"=\"),((6,11),(6,12),\"x\"),((6,13),(6,14),\"+\"),((6,15),(6,16),\"y\")]"

    -- ---------------------------------------------------------------

    it "deletes a set of tokens from a token stream2" $ do
      (_t,_toks) <- parsedFileWhereIn3Ghc
      -- let toks' = take 30 $ drop 25 toks
      let toks' =
           [
           mkMySrcSpan (((11,10),(11,15)),(GHC.ITwhere),"where"),
           mkMySrcSpan (((11,16),(11,16)),(GHC.ITvocurly),""),
           mkMySrcSpan (((11,16),(11,17)),(GHC.ITvarid (GHC.mkFastString "p")),"p"),
           mkMySrcSpan (((11,17),(11,18)),(GHC.ITequal),"="),
           mkMySrcSpan (((11,18),(11,19)),(GHC.ITinteger 2),"2"),
           mkMySrcSpan (((11,21),(11,43)),(GHC.ITblockComment ("There is a comment")),"{-There is a comment-}"),
           mkMySrcSpan (((13,1),(13,1)),(GHC.ITvccurly),""),
           mkMySrcSpan (((13,1),(13,1)),(GHC.ITsemi),""),
           mkMySrcSpan (((13,1),(13,3)),(GHC.ITvarid (GHC.mkFastString "sq")),"sq"),
           mkMySrcSpan (((13,4),(13,6)),(GHC.ITdcolon),"::"),
           mkMySrcSpan (((13,7),(13,10)),(GHC.ITconid (GHC.mkFastString "Int")),"Int"),
           mkMySrcSpan (((13,11),(13,13)),(GHC.ITrarrow),"->"),
           mkMySrcSpan (((13,14),(13,17)),(GHC.ITconid (GHC.mkFastString "Int")),"Int"),
           mkMySrcSpan (((13,18),(13,20)),(GHC.ITrarrow),"->"),
           mkMySrcSpan (((13,21),(13,24)),(GHC.ITconid (GHC.mkFastString "Int")),"Int"),
           mkMySrcSpan (((17,1),(17,11)),(GHC.ITvarid (GHC.mkFastString "anotherFun")),"anotherFun"),
           mkMySrcSpan (((17,12),(17,13)),(GHC.ITinteger 0),"0"),
           mkMySrcSpan (((17,14),(17,15)),(GHC.ITvarid (GHC.mkFastString "y")),"y"),
           mkMySrcSpan (((17,16),(17,17)),(GHC.ITequal),"="),
           mkMySrcSpan (((17,18),(17,20)),(GHC.ITvarid (GHC.mkFastString "sq")),"sq"),
           mkMySrcSpan (((17,21),(17,22)),(GHC.ITvarid (GHC.mkFastString "y")),"y"),
           mkMySrcSpan (((18,6),(18,11)),(GHC.ITwhere),"where")
           ]
      -- (showToks toks') `shouldBe` ""

      let newToks = deleteToks toks' (13,1) (13,24)
      (showToks newToks) `shouldBe`
            {-
            ("[(((11,10),(11,15)),ITwhere,\"where\"),"++
            "(((11,16),(11,16)),ITvocurly,\"\"),"++
            "(((11,16),(11,17)),ITvarid \"p\",\"p\"),"++
            "(((11,17),(11,18)),ITequal,\"=\"),"++
            "(((11,18),(11,19)),ITinteger 2,\"2\"),"++
            "(((11,21),(11,43)),ITblockComment \"There is a comment\",\"{-There is a comment-}\"),"++
            -- "(((13,1),(13,1)),ITvccurly,\"\"),"++
            -- "(((13,1),(13,1)),ITsemi,\"\"),"++
            -- "(((13,1),(13,3)),ITvarid \"sq\",\"sq\"),"++
            -- "(((13,4),(13,6)),ITdcolon,\"::\"),"++
            -- "(((13,7),(13,10)),ITconid \"Int\",\"Int\"),"++
            -- "(((13,11),(13,13)),ITrarrow,\"->\"),"++
            -- "(((13,14),(13,17)),ITconid \"Int\",\"Int\"),"++
            -- "(((13,18),(13,20)),ITrarrow,\"->\"),"++
            -- "(((13,21),(13,24)),ITconid \"Int\",\"Int\"),"++
            "(((17,1),(17,11)),ITvarid \"anotherFun\",\"anotherFun\"),"++
            "(((17,12),(17,13)),ITinteger 0,\"0\"),"++
            "(((17,14),(17,15)),ITvarid \"y\",\"y\"),"++
            "(((17,16),(17,17)),ITequal,\"=\"),"++
            "(((17,18),(17,20)),ITvarid \"sq\",\"sq\"),"++
            "(((17,21),(17,22)),ITvarid \"y\",\"y\"),"++
            "(((18,6),(18,11)),ITwhere,\"where\")]")
            -}
            "[((11,10),(11,15),\"where\"),((11,16),(11,16),\"\"),((11,16),(11,17),\"p\"),((11,17),(11,18),\"=\"),((11,18),(11,19),\"2\"),((11,21),(11,43),\"{-There is a comment-}\"),((17,1),(17,11),\"anotherFun\"),((17,12),(17,13),\"0\"),((17,14),(17,15),\"y\"),((17,16),(17,17),\"=\"),((17,18),(17,20),\"sq\"),((17,21),(17,22),\"y\"),((18,6),(18,11),\"where\")]"


  -- -------------------------------------------------------------------

  describe "groupTokensByLine" $ do
    it "groups a list of tokens by line" $ do
      (_t,toks) <- parsedFileCaseBGhc
      let toks' = take 25 toks
      (showToks toks') `shouldBe`
               {-
               "[(((1,1),(1,7)),ITmodule,\"module\")," ++
                "(((1,8),(1,9)),ITconid \"B\",\"B\")," ++
                "(((1,10),(1,15)),ITwhere,\"where\")," ++
                "(((2,1),(2,35)),ITlineComment \"-- Test for refactor of if to case\",\"-- Test for refactor of if to case\")," ++
                "(((4,1),(4,1)),ITvocurly,\"\")," ++
                "(((4,1),(4,4)),ITvarid \"foo\",\"foo\")," ++
                "(((4,5),(4,6)),ITvarid \"x\",\"x\")," ++
                "(((4,7),(4,8)),ITequal,\"=\")," ++
                "(((4,9),(4,11)),ITif,\"if\")," ++
                "(((4,12),(4,13)),IToparen,\"(\")," ++
                "(((4,13),(4,16)),ITvarid \"odd\",\"odd\")," ++
                "(((4,17),(4,18)),ITvarid \"x\",\"x\")," ++
                "(((4,18),(4,19)),ITcparen,\")\")," ++
                "(((4,20),(4,24)),ITthen,\"then\")," ++
                "(((4,25),(4,30)),ITstring \"Odd\",\"\\\"Odd\\\"\")," ++
                "(((4,31),(4,35)),ITelse,\"else\")," ++
                "(((4,36),(4,42)),ITstring \"Even\",\"\\\"Even\\\"\")," ++
                "(((6,1),(6,1)),ITsemi,\"\")," ++
                "(((6,1),(6,4)),ITvarid \"bob\",\"bob\")," ++
                "(((6,5),(6,6)),ITvarid \"x\",\"x\")," ++
                "(((6,7),(6,8)),ITvarid \"y\",\"y\")," ++
                "(((6,9),(6,10)),ITequal,\"=\")," ++
                "(((6,11),(6,12)),ITvarid \"x\",\"x\")," ++
                "(((6,13),(6,14)),ITvarsym \"+\",\"+\")," ++
                "(((6,15),(6,16)),ITvarid \"y\",\"y\")]"
                -}
                "[((1,1),(1,7),\"module\"),((1,8),(1,9),\"B\"),((1,10),(1,15),\"where\"),((2,1),(2,35),\"-- Test for refactor of if to case\"),((4,1),(4,1),\"\"),((4,1),(4,4),\"foo\"),((4,5),(4,6),\"x\"),((4,7),(4,8),\"=\"),((4,9),(4,11),\"if\"),((4,12),(4,13),\"(\"),((4,13),(4,16),\"odd\"),((4,17),(4,18),\"x\"),((4,18),(4,19),\")\"),((4,20),(4,24),\"then\"),((4,25),(4,30),\"\\\"Odd\\\"\"),((4,31),(4,35),\"else\"),((4,36),(4,42),\"\\\"Even\\\"\"),((6,1),(6,1),\"\"),((6,1),(6,4),\"bob\"),((6,5),(6,6),\"x\"),((6,7),(6,8),\"y\"),((6,9),(6,10),\"=\"),((6,11),(6,12),\"x\"),((6,13),(6,14),\"+\"),((6,15),(6,16),\"y\")]"

      let grouped = groupTokensByLine toks'
      (map showToks grouped) `shouldBe`
         {-
         ["[(((1,1),(1,7)),ITmodule,\"module\"),(((1,8),(1,9)),ITconid \"B\",\"B\"),(((1,10),(1,15)),ITwhere,\"where\")]",
          "[(((2,1),(2,35)),ITlineComment \"-- Test for refactor of if to case\",\"-- Test for refactor of if to case\")]",
          "[(((4,1),(4,1)),ITvocurly,\"\"),(((4,1),(4,4)),ITvarid \"foo\",\"foo\"),(((4,5),(4,6)),ITvarid \"x\",\"x\"),(((4,7),(4,8)),ITequal,\"=\"),(((4,9),(4,11)),ITif,\"if\"),(((4,12),(4,13)),IToparen,\"(\"),(((4,13),(4,16)),ITvarid \"odd\",\"odd\"),(((4,17),(4,18)),ITvarid \"x\",\"x\"),(((4,18),(4,19)),ITcparen,\")\"),(((4,20),(4,24)),ITthen,\"then\"),(((4,25),(4,30)),ITstring \"Odd\",\"\\\"Odd\\\"\"),(((4,31),(4,35)),ITelse,\"else\"),(((4,36),(4,42)),ITstring \"Even\",\"\\\"Even\\\"\")]",
          "[(((6,1),(6,1)),ITsemi,\"\"),(((6,1),(6,4)),ITvarid \"bob\",\"bob\"),(((6,5),(6,6)),ITvarid \"x\",\"x\"),(((6,7),(6,8)),ITvarid \"y\",\"y\"),(((6,9),(6,10)),ITequal,\"=\"),(((6,11),(6,12)),ITvarid \"x\",\"x\"),(((6,13),(6,14)),ITvarsym \"+\",\"+\"),(((6,15),(6,16)),ITvarid \"y\",\"y\")]"
         ]
         -}
         ["[((1,1),(1,7),\"module\"),((1,8),(1,9),\"B\"),((1,10),(1,15),\"where\")]",
          "[((2,1),(2,35),\"-- Test for refactor of if to case\")]",
          "[((4,1),(4,1),\"\"),((4,1),(4,4),\"foo\"),((4,5),(4,6),\"x\"),((4,7),(4,8),\"=\"),((4,9),(4,11),\"if\"),((4,12),(4,13),\"(\"),((4,13),(4,16),\"odd\"),((4,17),(4,18),\"x\"),((4,18),(4,19),\")\"),((4,20),(4,24),\"then\"),((4,25),(4,30),\"\\\"Odd\\\"\"),((4,31),(4,35),\"else\"),((4,36),(4,42),\"\\\"Even\\\"\")]",
          "[((6,1),(6,1),\"\"),((6,1),(6,4),\"bob\"),((6,5),(6,6),\"x\"),((6,7),(6,8),\"y\"),((6,9),(6,10),\"=\"),((6,11),(6,12),\"x\"),((6,13),(6,14),\"+\"),((6,15),(6,16),\"y\")]"
         ]

  -- -------------------------------------------------------------------

  describe "getSrcSpan" $ do
    it "Finds the top SrcSpan" $ do
      (t, _toks) <- parsedFileDd1Ghc
      let renamed = fromJust $ GHC.tm_renamed_source t
      let declsr = hsBinds renamed
          ss = getSrcSpan declsr
      (showGhc declsr) `shouldBe` "[DupDef.Dd1.dd q\n   = do { let ss = 5;\n          GHC.Base.return (ss GHC.Num.+ q) },\n DupDef.Dd1.l z = let ll = 34 in ll GHC.Num.+ z,\n DupDef.Dd1.ff y\n   = y GHC.Num.+ zz\n   where\n       zz = 1,\n DupDef.Dd1.tup@(DupDef.Dd1.h, DupDef.Dd1.t)\n   = GHC.List.head GHC.Base.$ GHC.List.zip [1 .. 10] [3 .. ff]\n   where\n       ff :: GHC.Types.Int\n       ff = 15,\n DupDef.Dd1.d = 9, DupDef.Dd1.c = 7,\n DupDef.Dd1.toplevel x = DupDef.Dd1.c GHC.Num.* x]"
      (showGhc ss) `shouldBe` "Just test/testdata/DupDef/Dd1.hs:(30,1)-(32,17)"

    -- -------------------------------
    it "Finds the SrcSpan for a top level decl" $ do
      (t, _toks) <- parsedFileDemoteGhc
      let renamed = fromJust $ GHC.tm_renamed_source t
      let declsr = hsBinds renamed
          decl = head $ drop 2 declsr
          ss = getSrcSpan decl
      (showGhc decl) `shouldBe` "MoveDef.Demote.toplevel x = MoveDef.Demote.c GHC.Num.* x"
      (showGhc ss) `shouldBe` "Just test/testdata/MoveDef/Demote.hs:4:1-18"

  -- -------------------------------------------------------------------

  describe "getAllSrcLocs" $ do
    it "gets all the srclocs in a syntax phrase" $ do
      (t, toks) <- parsedFileDeclareGhc
      let renamed = fromJust $ GHC.tm_renamed_source t

      let declsr = hsBinds renamed

      let decls = filter isFunOrPatBindR declsr

      let decl = head $ drop 4 decls
      let (_startPos,_endPos) = startEndLocIncComments toks decl

      (showGhc decl) `shouldBe` "FreeAndDeclared.Declare.unD (FreeAndDeclared.Declare.B y) = y"

      (showToks $ getToks ((18,1),(25,1)) toks) `shouldBe`
             {-
             ("[(((18,1),(18,1)),ITsemi,\"\")," ++
             "(((18,1),(18,5)),ITdata,\"data\")," ++
             "(((18,6),(18,7)),ITconid \"D\",\"D\")," ++
             "(((18,8),(18,9)),ITequal,\"=\")," ++
             "(((18,10),(18,11)),ITconid \"A\",\"A\")," ++
             "(((18,12),(18,13)),ITvbar,\"|\")," ++
             "(((18,14),(18,15)),ITconid \"B\",\"B\")," ++
             "(((18,16),(18,22)),ITconid \"String\",\"String\")," ++
             "(((18,23),(18,24)),ITvbar,\"|\")," ++
             "(((18,25),(18,26)),ITconid \"C\",\"C\")," ++
             "(((20,1),(20,32)),ITlineComment \"-- Retrieve the String from a B\",\"-- Retrieve the String from a B\")," ++
             "(((21,1),(21,1)),ITsemi,\"\")," ++
             "(((21,1),(21,4)),ITvarid \"unD\",\"unD\")," ++
             "(((21,5),(21,6)),IToparen,\"(\")," ++
             "(((21,6),(21,7)),ITconid \"B\",\"B\")," ++
             "(((21,8),(21,9)),ITvarid \"y\",\"y\")," ++
             "(((21,9),(21,10)),ITcparen,\")\")," ++
             "(((21,11),(21,12)),ITequal,\"=\")," ++
             "(((21,13),(21,14)),ITvarid \"y\",\"y\")," ++
             "(((22,1),(22,18)),ITlineComment \"-- But no others.\",\"-- But no others.\")," ++
             "(((24,1),(24,73)),ITlineComment \"-- Infix data constructor, see http://stackoverflow.com/a/6420943/595714\"," ++
                                             "\"-- Infix data constructor, see http://stackoverflow.com/a/6420943/595714\")," ++
             "(((25,1),(25,1)),ITsemi,\"\")," ++
             "(((25,1),(25,5)),ITdata,\"data\")]")
             -}
             "[((18,1),(18,1),\"\"),((18,1),(18,5),\"data\"),((18,6),(18,7),\"D\"),((18,8),(18,9),\"=\"),((18,10),(18,11),\"A\"),((18,12),(18,13),\"|\"),((18,14),(18,15),\"B\"),((18,16),(18,22),\"String\"),((18,23),(18,24),\"|\"),((18,25),(18,26),\"C\"),((20,1),(20,32),\"-- Retrieve the String from a B\"),((21,1),(21,1),\"\"),((21,1),(21,4),\"unD\"),((21,5),(21,6),\"(\"),((21,6),(21,7),\"B\"),((21,8),(21,9),\"y\"),((21,9),(21,10),\")\"),((21,11),(21,12),\"=\"),((21,13),(21,14),\"y\"),((22,1),(22,18),\"-- But no others.\"),((24,1),(24,73),\"-- Infix data constructor, see http://stackoverflow.com/a/6420943/595714\"),((25,1),(25,1),\"\"),((25,1),(25,5),\"data\")]"

      (show $ getAllSrcLocs decl) `shouldBe` "[((21,1),(21,14)),((21,1),(21,4)),((21,5),(21,10)),((21,6),(21,9)),((21,6),(21,7)),((21,8),(21,9)),((21,13),(21,14))]"


  -- -------------------------------------------------------------------

  describe "getBiggestStartEndLoc" $ do
    it "gets the smallest startpos and largest endpos in a syntax phrase" $ do
      (t, toks) <- parsedFileWhereIn6Ghc
      let renamed = fromJust $ GHC.tm_renamed_source t

      let declsr = hsBinds renamed

      let decls = filter isFunOrPatBindR declsr

      let decl = head $ decls
      let (startPos,endPos) = startEndLocIncComments toks decl

      (showGhc decl) `shouldBe` "Demote.WhereIn6.addthree a b c = a GHC.Num.+ b GHC.Num.+ c"
      -- (SYB.showData SYB.Renamer 0 decl) `shouldBe` "Demote.WhereIn6.addthree a b c = a GHC.Num.+ b GHC.Num.+ c"
      (show   (startPos,endPos)) `shouldBe` "((13,1),(13,21))"

      let (GHC.L _ (GHC.FunBind _ _ (GHC.MatchGroup matches _)  _ _ _)) = decl
      -- (SYB.showData SYB.Renamer 0 matches) `shouldBe` "Demote.WhereIn6.addthree a b c = a GHC.Num.+ b GHC.Num.+ c"

      (showToks $ getToks ((12,1),(25,1)) toks) `shouldBe`
             {-
             ("[(((13,1),(13,1)),ITvccurly,\"\"),"
             ++"(((13,1),(13,1)),ITsemi,\"\"),"
             ++"(((13,1),(13,9)),ITvarid \"addthree\",\"addthree\"),"
             ++"(((13,10),(13,11)),ITvarid \"a\",\"a\"),"
             ++"(((13,12),(13,13)),ITvarid \"b\",\"b\"),"
             ++"(((13,14),(13,15)),ITvarid \"c\",\"c\"),"
             ++"(((13,15),(13,16)),ITequal,\"=\"),"
             ++"(((13,16),(13,17)),ITvarid \"a\",\"a\"),"
             ++"(((13,17),(13,18)),ITvarsym \"+\",\"+\"),"
             ++"(((13,18),(13,19)),ITvarid \"b\",\"b\"),"
             ++"(((13,19),(13,20)),ITvarsym \"+\",\"+\"),"
             ++"(((13,20),(13,21)),ITvarid \"c\",\"c\"),"
             ++"(((16,1),(16,1)),ITsemi,\"\")]")
             -}
             "[((13,1),(13,1),\"\"),((13,1),(13,1),\"\"),((13,1),(13,9),\"addthree\"),((13,10),(13,11),\"a\"),((13,12),(13,13),\"b\"),((13,14),(13,15),\"c\"),((13,15),(13,16),\"=\"),((13,16),(13,17),\"a\"),((13,17),(13,18),\"+\"),((13,18),(13,19),\"b\"),((13,19),(13,20),\"+\"),((13,20),(13,21),\"c\"),((16,1),(16,1),\"\")]"

      (show $ getBiggestStartEndLoc matches) `shouldBe` "((13,10),(13,21))"
      (show   (startPos,endPos)) `shouldBe` "((13,1),(13,21))"


  -- -------------------------------------------------------------------

  describe "getToks" $ do
    it "gets a token stream from the middle of tokens" $ do
      (_t,toks) <- parsedFileCaseBGhc
      let
          middle = getToks ((4,9),(4,36)) toks
      (showToks middle) `shouldBe`
               {-
               "[(((4,9),(4,11)),ITif,\"if\")," ++
               "(((4,12),(4,13)),IToparen,\"(\")," ++
               "(((4,13),(4,16)),ITvarid \"odd\",\"odd\")," ++
               "(((4,17),(4,18)),ITvarid \"x\",\"x\")," ++
               "(((4,18),(4,19)),ITcparen,\")\")," ++
               "(((4,20),(4,24)),ITthen,\"then\")," ++
               "(((4,25),(4,30)),ITstring \"Odd\",\"\\\"Odd\\\"\")," ++
               "(((4,31),(4,35)),ITelse,\"else\")," ++
               "(((4,36),(4,42)),ITstring \"Even\",\"\\\"Even\\\"\")]"
               -}
               "[((4,9),(4,11),\"if\"),((4,12),(4,13),\"(\"),((4,13),(4,16),\"odd\"),((4,17),(4,18),\"x\"),((4,18),(4,19),\")\"),((4,20),(4,24),\"then\"),((4,25),(4,30),\"\\\"Odd\\\"\"),((4,31),(4,35),\"else\"),((4,36),(4,42),\"\\\"Even\\\"\")]"
      (GHC.showRichTokenStream middle) `shouldBe` "\n\n\n         if (odd x) then \"Odd\" else \"Even\""

    it "gets a token stream from the middle of tokens 2" $ do
      (_t,toks) <- parsedFileDd1Ghc
      let
          middle = getToks ((17,5),(17,23)) toks
      (showToks middle) `shouldBe`
               {-
               "[(((17,5),(17,5)),ITsemi,\"\")," ++
               "(((17,5),(17,7)),ITvarid \"ff\",\"ff\")," ++
               "(((17,8),(17,9)),ITequal,\"=\")," ++
               "(((17,10),(17,12)),ITinteger 15,\"15\")]"
               -}
               "[((17,5),(17,5),\"\"),((17,5),(17,7),\"ff\"),((17,8),(17,9),\"=\"),((17,10),(17,12),\"15\")]"
      (GHC.showRichTokenStream middle) `shouldBe` "\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n     ff = 15"

  -- -------------------------------------------------------------------
{-
  -- This has been moved into TypeUtils

  describe "addFormalParams" $ do
    it "adds new parameters to a token stream??" $ do
      let
        comp = do

         (t, toks) <- parseSourceFileTest "./test/testdata/DupDef/Dd1.hs"
         putParsedModule t toks
         parentr <- getRefactRenamed

         let mn = locToName (GHC.mkFastString "./test/testdata/DupDef/Dd1.hs") (4,1) parentr
         let (Just (ln@(GHC.L _ n))) = mn

         n1   <- mkNewGhcName "n1"
         n2   <- mkNewGhcName "n2"

         let declsr = hsBinds parentr
             tlDecls = definingDeclsNames [n] declsr True False
             pats = [GHC.noLoc (GHC.VarPat n1), GHC.noLoc (GHC.VarPat n2)]

         addFormalParams tlDecls pats

         forest <- getTokenTree
         return (tlDecls,ln,forest)
      ((d,l,f),s) <- runRefactGhcState comp
      (showGhc l) `shouldBe` "DupDef.Dd1.toplevel";
      (showGhc d) `shouldBe` "[DupDef.Dd1.toplevel x = DupDef.Dd1.c GHC.Num.* x]"
      -- (showToks $ take 20 $ toksFromState s) `shouldBe` ""
      (drawTreeEntry f) `shouldBe`
                "((1,1),(32,18))\n|\n"++
                "+- ((1,1),(3,31))\n|\n"++
                "+- ((4,1),(4,19))\n|\n"++
                "+- ((1000004,20),(1000004,25))\n|\n"++
                "`- ((6,1),(32,18))\n"
      -- (showTree f) `shouldBe` ""
      (GHC.showRichTokenStream $ toksFromState s) `shouldBe` "module DupDef.Dd1 where\n\n toplevel :: Integer -> Integer\n toplevel x = c * x n1 n2\n\n c,d :: Integer\n c = 7\n d = 9\n\n -- Pattern bind\n tup :: (Int, Int)\n h :: Int\n t :: Int\n tup@(h,t) = head $ zip [1..10] [3..ff]\n   where\n     ff :: Int\n     ff = 15\n\n data D = A | B String | C\n\n ff y = y + zz\n   where\n     zz = 1\n\n l z =\n   let\n     ll = 34\n   in ll + z\n\n dd q = do\n   let ss = 5\n   return (ss + q)\n\n "
-}

  -- -------------------------------------------------------------------

  describe "newLnToken" $ do
    it "bumps to next line" $ do
      (_t,toks) <- parsedFileCaseBGhc
      let
          middle = getToks ((4,9),(4,36)) toks
      (showToks middle) `shouldBe`
               {-
               "[(((4,9),(4,11)),ITif,\"if\")," ++
               "(((4,12),(4,13)),IToparen,\"(\")," ++
               "(((4,13),(4,16)),ITvarid \"odd\",\"odd\")," ++
               "(((4,17),(4,18)),ITvarid \"x\",\"x\")," ++
               "(((4,18),(4,19)),ITcparen,\")\")," ++
               "(((4,20),(4,24)),ITthen,\"then\")," ++
               "(((4,25),(4,30)),ITstring \"Odd\",\"\\\"Odd\\\"\")," ++
               "(((4,31),(4,35)),ITelse,\"else\")," ++
               "(((4,36),(4,42)),ITstring \"Even\",\"\\\"Even\\\"\")]"
               -}
               "[((4,9),(4,11),\"if\"),((4,12),(4,13),\"(\"),((4,13),(4,16),\"odd\"),((4,17),(4,18),\"x\"),((4,18),(4,19),\")\"),((4,20),(4,24),\"then\"),((4,25),(4,30),\"\\\"Odd\\\"\"),((4,31),(4,35),\"else\"),((4,36),(4,42),\"\\\"Even\\\"\")]"
      (showToks [newLnToken (head middle)]) `shouldBe` "[((5,1),(5,1),\"\")]"

  -- -------------------------------------------------------------------

  describe "lengthOfLastLine" $ do
    it "needs a test or two" $ do
      pending -- "write this test"

  -- -------------------------------------------------------------------

  describe "getLineOffset" $ do
    it "Get the start of the line prior to the current pos" $ do
      (_t,toks) <- parsedFileCaseBGhc
      getLineOffset toks (12,1) `shouldBe` 3

    it "Get the start of the line prior to the current pos2" $ do
      (_t,toks) <- parsedFileCaseBGhc
      getLineOffset toks (17,1) `shouldBe` 1

  -- -------------------------------------------------------------------

  describe "getIndentOffset" $ do
    it "gets the indent of the line prior to the current pos" $ do
      (_t,toks) <- parsedFileCaseBGhc
      getIndentOffset toks (12,1) `shouldBe` 2

    -- ---------------------------------

    it "gets the indent of the line prior to the current pos2" $ do
      (_t,toks) <- parsedFileCaseBGhc
      getIndentOffset toks (17,1) `shouldBe` 0

    -- ---------------------------------

    it "gets the indent after inline where clause" $ do
      (_t,toks) <- parsedFileOffsetGhc
      let middle = getToks ((6,1),(7,1)) toks
      (showToks middle) `shouldBe`
                "[((6,3),(6,8),\"where\"),((6,9),(6,9),\"\"),((6,9),(6,10),\"x\"),((6,11),(6,12),\"=\"),((6,13),(6,14),\"3\")]"
      getIndentOffset toks (7,1) `shouldBe` 8

    -- ---------------------------------

    it "gets the indent after where clause" $ do
      (_t,toks) <- parsedFileOffsetGhc
      getIndentOffset toks (11,1) `shouldBe` 4

    -- ---------------------------------

    it "gets the indent after inline let clause" $ do
      (_t,toks) <- parsedFileOffsetGhc
      getIndentOffset toks (15,1) `shouldBe` 6

    -- ---------------------------------

    it "gets the indent after embedded let clause" $ do
      (_t,toks) <- parsedFileOffsetGhc
      getIndentOffset toks (22,1) `shouldBe` 14

    -- ---------------------------------

    it "gets the indent after inline in clause" $ do
      (_t,toks) <- parsedFileOffsetGhc
      let middle = getToks ((15,1),(16,1)) toks
      (showToks middle) `shouldBe`
                "[((15,3),(15,3),\"\"),((15,3),(15,5),\"in\"),((15,10),(15,11),\"b\"),((15,12),(15,13),\"+\"),((15,14),(15,17),\"bar\")]"
      getIndentOffset toks (16,1) `shouldBe` 9

    -- ---------------------------------

    it "gets the indent after inline do clause" $ do
      (_t,toks) <- parsedFileOffsetGhc
      getIndentOffset toks (19,1) `shouldBe` 5

    -- ---------------------------------

    it "gets a sane indent for empty tokens" $ do
      (_t,_toks) <- parsedFileOffsetGhc
      getIndentOffset ([]::[PosToken]) (19,1) `shouldBe` 1

    -- ---------------------------------

    it "gets a sane indent for (0,0)" $ do
      (_t,toks) <- parsedFileOffsetGhc
      getIndentOffset toks (0,0) `shouldBe` 1

  -- -------------------------------------------------------------------

  describe "extendBackwards" $ do
    it "needs a test or two" $ do
      (_t, toks) <- parsedFileTypeSigs
      (show $ take 12 toks) `shouldBe`
               "[((((1,1),(1,7)),ITmodule),\"module\"),"++
               "((((1,8),(1,16)),ITconid \"TypeSigs\"),\"TypeSigs\"),"++
               "((((1,17),(1,22)),ITwhere),\"where\"),"++
               "((((3,1),(3,1)),ITvocurly),\"\"),"++
               "((((3,1),(3,3)),ITvarid \"sq\"),\"sq\"),"++
               "((((3,3),(3,4)),ITcomma),\",\"),"++
               "((((3,4),(3,14)),ITvarid \"anotherFun\"),\"anotherFun\"),"++
               "((((3,15),(3,17)),ITdcolon),\"::\"),"++
               "((((3,18),(3,21)),ITconid \"Int\"),\"Int\"),"++
               "((((3,22),(3,24)),ITrarrow),\"->\"),"++
               "((((3,25),(3,28)),ITconid \"Int\"),\"Int\"),"++
               "((((4,1),(4,1)),ITsemi),\"\")]"
      let (_,middle,_) = splitToks ((3,1),(3,28)) toks
      (show middle) `shouldBe`
               "[((((3,1),(3,1)),ITvocurly),\"\"),"++
               "((((3,1),(3,3)),ITvarid \"sq\"),\"sq\"),"++
               "((((3,3),(3,4)),ITcomma),\",\"),"++
               "((((3,4),(3,14)),ITvarid \"anotherFun\"),\"anotherFun\"),"++
               "((((3,15),(3,17)),ITdcolon),\"::\"),"++
               "((((3,18),(3,21)),ITconid \"Int\"),\"Int\"),"++
               "((((3,22),(3,24)),ITrarrow),\"->\"),"++
               "((((3,25),(3,28)),ITconid \"Int\"),\"Int\")]"

      -- (startPos1', endPos1'):((3,1),(3,3))
      -- (sspan):test/testdata/TypeUtils/TypeSigs.hs:3:1-27
      let t2 = extendBackwards middle ((3,4),(3,14)) isComma
      (show t2) `shouldBe` "((3,3),(3,14))"

  -- -------------------------------------------------------------------

  describe "extendForwards" $ do
    it "needs a test or two" $ do
      (_t, toks) <- parsedFileTypeSigs
      (show $ take 12 toks) `shouldBe` 
               "[((((1,1),(1,7)),ITmodule),\"module\"),"++
               "((((1,8),(1,16)),ITconid \"TypeSigs\"),\"TypeSigs\"),"++
               "((((1,17),(1,22)),ITwhere),\"where\"),"++
               "((((3,1),(3,1)),ITvocurly),\"\"),"++
               "((((3,1),(3,3)),ITvarid \"sq\"),\"sq\"),"++
               "((((3,3),(3,4)),ITcomma),\",\"),"++
               "((((3,4),(3,14)),ITvarid \"anotherFun\"),\"anotherFun\"),"++
               "((((3,15),(3,17)),ITdcolon),\"::\"),"++
               "((((3,18),(3,21)),ITconid \"Int\"),\"Int\"),"++
               "((((3,22),(3,24)),ITrarrow),\"->\"),"++
               "((((3,25),(3,28)),ITconid \"Int\"),\"Int\"),"++
               "((((4,1),(4,1)),ITsemi),\"\")]"
      let (_,middle,_) = splitToks ((3,1),(3,28)) toks
      (show middle) `shouldBe` 
               "[((((3,1),(3,1)),ITvocurly),\"\"),"++
               "((((3,1),(3,3)),ITvarid \"sq\"),\"sq\"),"++
               "((((3,3),(3,4)),ITcomma),\",\"),"++
               "((((3,4),(3,14)),ITvarid \"anotherFun\"),\"anotherFun\"),"++
               "((((3,15),(3,17)),ITdcolon),\"::\"),"++
               "((((3,18),(3,21)),ITconid \"Int\"),\"Int\"),"++
               "((((3,22),(3,24)),ITrarrow),\"->\"),"++
               "((((3,25),(3,28)),ITconid \"Int\"),\"Int\")]"

      -- (startPos1', endPos1'):((3,1),(3,3))`
      -- (sspan):test/testdata/TypeUtils/TypeSigs.hs:3:1-27
      let t2 = extendForwards middle ((3,1),(3,3)) isComma
      (show t2) `shouldBe` "((3,1),(3,4))"

  -- -------------------------------------------------------------------

  describe "foo" $ do
    it "needs a test or two" $ do
      pending -- "write this test"

-- ---------------------------------------------------------------------
-- Helper functions

mkMySrcSpan :: ((SimpPos,SimpPos),GHC.Token,String) -> PosToken
mkMySrcSpan (((r1,c1),(r2,c2)),tok,s) = (GHC.L sspan tok,s)
  where
    filename = whereIn3FileName
    sspan = GHC.mkSrcSpan (GHC.mkSrcLoc filename r1 c1) (GHC.mkSrcLoc filename r2 c2)


-- ---------------------------------------------------------------------

-- bFileName :: GHC.FastString
-- bFileName = GHC.mkFastString "./test/testdata/B.hs"

-- parsedFileBGhc :: IO (ParseResult,[PosToken])
-- parsedFileBGhc = parsedFileGhc "./test/testdata/B.hs"

-- offsetFileName :: GHC.FastString
-- offsetFileName = GHC.mkFastString "./test/testdata/Offset.hs"

parsedFileOffsetGhc :: IO (ParseResult,[PosToken])
parsedFileOffsetGhc = parsedFileGhc "./test/testdata/Offset.hs"

-- caseBFileName :: GHC.FastString
-- caseBFileName = GHC.mkFastString "./test/testdata/Case/B.hs"

parsedFileCaseBGhc :: IO (ParseResult,[PosToken])
parsedFileCaseBGhc = parsedFileGhc "./test/testdata/Case/B.hs"

-- parsedFileMGhc :: IO (ParseResult,[PosToken])
-- parsedFileMGhc = parsedFileGhc "./test/testdata/M.hs"

-- parseFileBGhc :: RefactGhc (ParseResult, [PosToken])
-- parseFileBGhc = parseSourceFileTest fileName
--   where
--     fileName = "./test/testdata/B.hs"

-- parseFileMGhc :: RefactGhc (ParseResult, [PosToken])
-- parseFileMGhc = parseSourceFileTest fileName
--   where
--     fileName = "./test/testdata/M.hs"

-- parsedFileNoMod = parsedFileGhc fileName
--   where
--     fileName = "./test/testdata/NoMod.hs"

parsedFileDd1Ghc :: IO (ParseResult,[PosToken])
parsedFileDd1Ghc = parsedFileGhc "./test/testdata/DupDef/Dd1.hs"

{-
comp :: RefactGhc String
comp = do
    s <- get
    modInfo@(t, toks) <- parseSourceFileTest "./test/testdata/B.hs"

    g <- GHC.getModuleGraph
    gs <- mapM GHC.showModule g
    GHC.liftIO (putStrLn $ "modulegraph=" ++ (show gs))

    let Just tm = rsModule s
    let tm' = tm {rsStreamModified = True}
    put (s {rsModule = Just tm'})

    return (show gs)
-}

-- ---------------------------------------------------------------------

parsedFileDeclareGhc :: IO (ParseResult,[PosToken])
parsedFileDeclareGhc = parsedFileGhc "./test/testdata/FreeAndDeclared/Declare.hs"

parsedFileWhereIn6Ghc :: IO (ParseResult,[PosToken])
parsedFileWhereIn6Ghc = parsedFileGhc "./test/testdata/Demote/WhereIn6.hs"

-- -----------

parsedFileDemoteGhc :: IO (ParseResult,[PosToken])
parsedFileDemoteGhc = parsedFileGhc "./test/testdata/MoveDef/Demote.hs"

-- demoteFileName :: GHC.FastString
-- demoteFileName = GHC.mkFastString "./test/testdata/MoveDef/Demote.hs"

-- -----------

parsedFileWhereIn3Ghc :: IO (ParseResult,[PosToken])
parsedFileWhereIn3Ghc = parsedFileGhc "./test/testdata/Demote/WhereIn3.hs"

whereIn3FileName :: GHC.FastString
whereIn3FileName = GHC.mkFastString "./test/testdata/Demote/WhereIn3.hs"

-- -----------

-- tokenTestFileName :: GHC.FastString
-- tokenTestFileName = GHC.mkFastString "./test/testdata/TokenTest.hs"

parsedFileTokenTestGhc :: IO (ParseResult,[PosToken])
parsedFileTokenTestGhc = parsedFileGhc "./test/testdata/TokenTest.hs"

-- ----------------------------------------------------

-- typeSigsFileName :: GHC.FastString
-- typeSigsFileName = GHC.mkFastString "./test/testdata/TypeUtils/TypeSigs.hs"

parsedFileTypeSigs :: IO (ParseResult, [PosToken])
parsedFileTypeSigs = parsedFileGhc "./test/testdata/TypeUtils/TypeSigs.hs"

-- -----------


-- EOF
