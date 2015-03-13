{-# LANGUAGE CPP #-}
module TypeUtilsSpec (main, spec) where

import           Test.Hspec

import           TestUtils

import qualified GHC.SYB.Utils         as SYB

-- import qualified FastString as GHC
import qualified GHC        as GHC
import qualified Name       as GHC
import qualified RdrName    as GHC
import qualified Module     as GHC

import Data.Maybe

import Language.Haskell.Refact.Utils.Binds
import Language.Haskell.Refact.Utils.GhcVersionSpecific
import Language.Haskell.Refact.Utils.LocUtils
import Language.Haskell.Refact.Utils.Monad
import Language.Haskell.Refact.Utils.MonadFunctions
import Language.Haskell.Refact.Utils.TokenUtils
import Language.Haskell.Refact.Utils.TypeSyn
import Language.Haskell.Refact.Utils.TypeUtils
import Language.Haskell.Refact.Utils.Utils

import Language.Haskell.TokenUtils.GHC.Layout
import Language.Haskell.TokenUtils.DualTree
import Language.Haskell.TokenUtils.Types
import Language.Haskell.TokenUtils.TokenUtils
import Language.Haskell.TokenUtils.Utils

import qualified Data.Tree.Zipper as Z

import qualified Data.Map as Map
import Data.List

main :: IO ()
main = do
  hspec spec

spec :: Spec
spec = do

  -- -------------------------------------------------------------------

  describe "findAllNameOccurences" $ do
   it "finds all occurrences of the given name in a syntax phrase" $ do
      (t, _toks) <- parsedFileSGhc
      let renamed = fromJust $ GHC.tm_renamed_source t

      let Just ((GHC.L _l n)) = locToName (4,5) renamed
      (showGhc n) `shouldBe` "x"

      let res = findAllNameOccurences n renamed
      (showGhc res) `shouldBe` "[x, x]"
      -- NOTE: does not get the x's in line 8
      (showGhc $ map startEndLocGhc res) `shouldBe` "[((4, 5), (4, 6)), ((4, 17), (4, 18))]"

  -- -------------------------------------------------------------------

  describe "locToName" $ do
    it "returns a GHC.Name for a given source location, if it falls anywhere in an identifier" $ do
      -- ((_,renamed,_), _toks) <- parsedFileBGhc
      (t, _toks) <- parsedFileBGhc
      let renamed = fromJust $ GHC.tm_renamed_source t

      let Just (res@(GHC.L l n)) = locToName (7,3) renamed
      showGhc l `shouldBe` "test/testdata/TypeUtils/B.hs:7:1-3"
      getLocatedStart res `shouldBe` (7,1)
      showGhc n `shouldBe` "TypeUtils.B.foo"

    -- ---------------------------------

    it "returns a GHC.Name for a given source location, if it falls anywhere in an identifier #2" $ do
      -- ((_, renamed,_),_toks) <- parsedFileBGhc
      (t, _toks) <- parsedFileBGhc
      let renamed = fromJust $ GHC.tm_renamed_source t

      let Just (res@(GHC.L l n)) = locToName (25,8) renamed
      showGhc n `shouldBe` "TypeUtils.B.bob"
      showGhc l `shouldBe` "test/testdata/TypeUtils/B.hs:25:7-9"
      getLocatedStart res `shouldBe` (25,7)

    -- ---------------------------------

    it "returns Nothing for a given source location, if it does not fall in an identifier" $ do
      (t, _toks) <- parsedFileBGhc
      let renamed = fromJust $ GHC.tm_renamed_source t

      let res = locToName (7,7) renamed
      (showGhc res) `shouldBe` "Nothing"

    -- ---------------------------------

    it "gets a short name too" $ do
      (t, _toks) <- parsedFileGhc "./test/testdata/Demote/WhereIn2.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t

      let Just (res@(GHC.L l n)) = locToName (14,1) renamed
      showGhc n `shouldBe` "Demote.WhereIn2.sq"
      -- Note: loc does not line up due to multiple matches in FunBind
      showGhc l `shouldBe` "test/testdata/Demote/WhereIn2.hs:13:1-2"
      getLocatedStart res `shouldBe` (13,1)

    -- ---------------------------------

    it "gets a type variable name" $ do
      (t, _toks) <- parsedFileGhc "./test/testdata/Renaming/ConstructorIn3.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t

      let Just (res@(GHC.L l n)) = locToName (9,12) renamed
      showGhc n `shouldBe` "a"
      -- Note: loc does not line up due to multiple matches in FunBind
      showGhc l `shouldBe` "test/testdata/Renaming/ConstructorIn3.hs:9:12"
      getLocatedStart res `shouldBe` (9,12)

    -- ---------------------------------

    it "gets an instance class name" $ do
      (t, _toks) <- parsedFileGhc "./test/testdata/Renaming/ClassIn3.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t
      -- (SYB.showData SYB.Renamer 0 renamed) `shouldBe` ""
      let Just (res@(GHC.L l n)) = locToName (16,10) renamed
      showGhc n `shouldBe` "GHC.Classes.Eq"
      showGhc l `shouldBe` "test/testdata/Renaming/ClassIn3.hs:16:10-11"
      getLocatedStart res `shouldBe` (16,10)

  -- -------------------------------------------------------------------

  describe "locToRdrName" $ do
    it "returns a GHC.RdrName for a given source location, if it falls anywhere in an identifier" $ do
      (t, _toks) <- parsedFileRenamingD5
      let parsed = GHC.pm_parsed_source $ GHC.tm_parsed_module t

      let Just (res@(GHC.L l n)) = locToRdrName (20,1) parsed
      showGhc l `shouldBe` "test/testdata/Renaming/D5.hs:20:1-10"
      getLocatedStart res `shouldBe` (20,1)
      showGhc n `shouldBe` "sumSquares"

    it "returns a GHC.RdrName for a source location, in a MatchGroup" $ do
      (t, _toks) <- parsedFileLocToName
      let parsed = GHC.pm_parsed_source $ GHC.tm_parsed_module t

      let Just (res@(GHC.L l n)) = locToRdrName (24,2) parsed
      showGhc n `shouldBe` "sumSquares"
      getLocatedStart res `shouldBe` (20,1) -- Because second match discards name
      showGhc l `shouldBe` "test/testdata/LocToName.hs:20:1-10"

  -- -------------------------------------------------------------------

  describe "allNames" $ do
    it "lists all Names" $ do
      (t, _toks) <- parsedFileSGhc
      let renamed = fromJust $ GHC.tm_renamed_source t
      let res = allNames renamed
      -- let res' = map (\(GHC.L l n) -> (showGhc $ GHC.nameUnique n,showGhc (l, n))) res
      let res' = map (\(GHC.L l n) -> (showGhc $ GHC.nameUnique n,showGhc (l, GHC.getSrcSpan n, n))) res

      -- Map.insertWith :: Ord k => (a -> a -> a) -> k -> a -> Map k a -> Map k a
      let res'' = foldl' (\m (k,a) -> Map.insertWith (++) k a m) Map.empty res'

      (sort $ Map.elems res'') `shouldBe`
                 ["(test/testdata/TypeUtils/S.hs:10:12,\n test/testdata/TypeUtils/S.hs:10:8,\n n)(test/testdata/TypeUtils/S.hs:10:8,\n test/testdata/TypeUtils/S.hs:10:8,\n n)"
                 ,"(test/testdata/TypeUtils/S.hs:10:14, <no location info>, GHC.Num.+)"
                 ,"(test/testdata/TypeUtils/S.hs:10:5-6,\n test/testdata/TypeUtils/S.hs:10:5-6,\n zz)(test/testdata/TypeUtils/S.hs:8:13-14,\n test/testdata/TypeUtils/S.hs:10:5-6,\n zz)"
                 ,"(test/testdata/TypeUtils/S.hs:4:1-3,\n test/testdata/TypeUtils/S.hs:4:1-3,\n TypeUtils.S.foo)"
                 ,"(test/testdata/TypeUtils/S.hs:4:13-15,\n <no location info>,\n GHC.Real.odd)"
                 ,"(test/testdata/TypeUtils/S.hs:4:17,\n test/testdata/TypeUtils/S.hs:4:5,\n x)(test/testdata/TypeUtils/S.hs:4:5,\n test/testdata/TypeUtils/S.hs:4:5,\n x)"
                 ,"(test/testdata/TypeUtils/S.hs:6:10,\n test/testdata/TypeUtils/S.hs:6:10,\n TypeUtils.S.A)"
                 ,"(test/testdata/TypeUtils/S.hs:6:14,\n test/testdata/TypeUtils/S.hs:6:14,\n TypeUtils.S.B)"
                 ,"(test/testdata/TypeUtils/S.hs:6:25,\n test/testdata/TypeUtils/S.hs:6:25,\n TypeUtils.S.C)"
                 ,"(test/testdata/TypeUtils/S.hs:6:6,\n test/testdata/TypeUtils/S.hs:6:6,\n TypeUtils.S.D)"
                 ,"(test/testdata/TypeUtils/S.hs:8:1-7,\n test/testdata/TypeUtils/S.hs:8:1-7,\n TypeUtils.S.subdecl)"
                 ,"(test/testdata/TypeUtils/S.hs:8:16,\n test/testdata/TypeUtils/S.hs:8:9,\n x)(test/testdata/TypeUtils/S.hs:8:9,\n test/testdata/TypeUtils/S.hs:8:9,\n x)"
                 ]


  -- -------------------------------------------------------------------

  describe "getName" $ do
    it "gets a qualified Name at the top level" $ do
      -- ((_, renamed,_), _toks) <- parsedFileBGhc
      (t, _toks) <- parsedFileBGhc
      let renamed = fromJust $ GHC.tm_renamed_source t
      let Just n = getName "TypeUtils.B.foo'" renamed
      (showGhc n) `shouldBe` "TypeUtils.B.foo'"
      (showGhc $ GHC.getSrcSpan n) `shouldBe` "test/testdata/TypeUtils/B.hs:14:1-4"

    it "gets any instance of an unqualified Name" $ do
      -- ((_, renamed,_), _toks) <- parsedFileBGhc
      (t, _toks) <- parsedFileBGhc
      let renamed = fromJust $ GHC.tm_renamed_source t
      let Just n = getName "foo" renamed
      (showGhc n) `shouldBe` "foo"
      (showGhc $ GHC.getSrcSpan n) `shouldBe` "test/testdata/TypeUtils/B.hs:9:15-17"

    it "returns Nothing if the Name is not found" $ do
      -- ((_, renamed,_), _toks) <- parsedFileBGhc
      (t, _toks) <- parsedFileBGhc
      let renamed = fromJust $ GHC.tm_renamed_source t
      let res = getName "baz" renamed
      (showGhc res) `shouldBe` "Nothing"


  -- -------------------------------------------------------------------
{-
  describe "definingDecls" $ do
    it "returns [] if not found" $ do
      (t, _toks) <- parsedFileDd1Ghc
      let (GHC.L _l (GHC.HsModule name exps imps ds _ _)) = GHC.pm_parsed_source $ GHC.tm_parsed_module t

      let res = definingDecls [(PN (mkRdrName "notdefine"))] ds True False
      showGhc res `shouldBe` "[]"


    it "finds declarations at the top level" $ do
      (t, _toks) <- parsedFileDd1Ghc
      let (GHC.L l (GHC.HsModule name exps imps ds _ _)) = GHC.pm_parsed_source $ GHC.tm_parsed_module t

      let res = definingDecls [(PN (mkRdrName "toplevel"))] ds False False
      showGhc res `shouldBe` "[toplevel x = c * x]"


    it "includes the typedef if requested" $ do
      (t, _toks) <- parsedFileDd1Ghc
      let (GHC.L l (GHC.HsModule name exps imps ds _ _)) = GHC.pm_parsed_source $ GHC.tm_parsed_module t

      let res = definingDecls [(PN (mkRdrName "toplevel"))] ds True False
      showGhc res `shouldBe` "[toplevel :: Integer -> Integer, toplevel x = c * x]"


    it "strips other names from typedef" $ do
      (t, _toks) <- parsedFileDd1Ghc
      let (GHC.L l (GHC.HsModule name exps imps ds _ _)) = GHC.pm_parsed_source $ GHC.tm_parsed_module t
      let res = definingDecls [(PN (mkRdrName "c"))] ds True False
      showGhc res `shouldBe` "[c :: Integer, c = 7]"


    it "finds in a patbind" $ do
      (t, _toks) <- parsedFileDd1Ghc
      let (GHC.L l (GHC.HsModule name exps imps ds _ _)) = GHC.pm_parsed_source $ GHC.tm_parsed_module t

      let res = definingDecls [(PN (mkRdrName "tup"))] ds False False
      showGhc res `shouldBe` "[tup@(h, t)\n   = head $ zip [1 .. 10] [3 .. ff]\n   where\n       ff :: Int\n       ff = 15]"


    it "finds in a patbind, with type signature" $ do
      (t, _toks) <- parsedFileDd1Ghc
      let (GHC.L l (GHC.HsModule name exps imps ds _ _)) = GHC.pm_parsed_source $ GHC.tm_parsed_module t

      let res = definingDecls [(PN (mkRdrName "tup"))] ds True False
      showGhc res `shouldBe` "[tup :: (Int, Int),\n tup@(h, t)\n   = head $ zip [1 .. 10] [3 .. ff]\n   where\n       ff :: Int\n       ff = 15]"


    it "finds in a data decl" $ do
      (t, _toks) <- parsedFileDd1Ghc
      let (GHC.L l (GHC.HsModule name exps imps ds _ _)) = GHC.pm_parsed_source $ GHC.tm_parsed_module t

      let res = definingDecls [(PN (GHC.mkRdrUnqual (GHC.mkDataOcc "A")))] ds True False
      showGhc res `shouldBe` "[data D = A | B String | C]"


    it "finds recursively in sub-binds" $ do
      {-
      modInfo@((_, _, mod@(GHC.L l (GHC.HsModule name exps imps ds _ _))), toks) <- parsedFileDd1Ghc
      let res = definingDecls [(PN (mkRdrName "zz"))] ds False True
      showGhc res `shouldBe` "[zz n = n + 1]" -- TODO: Currently fails, will come back to it
      -}
      pending -- "Currently fails, will come back to it"

    it "only finds recursively in sub-binds if asked" $ do
      -- modInfo@((_, _, mod@(GHC.L l (GHC.HsModule name exps imps ds _ _))), toks) <- parsedFileDd1Ghc
      (t, _toks) <- parsedFileDd1Ghc
      let (GHC.L l (GHC.HsModule name exps imps ds _ _)) = GHC.pm_parsed_source $ GHC.tm_parsed_module t

      let res = definingDecls [(PN (mkRdrName "zz"))] ds False False
      showGhc res `shouldBe` "[]"
-}
  -- -------------------------------------------------------------------

  describe "definingDeclsNames" $ do
    it "returns [] if not found" $ do
      -- ((_,Just renamed,_), _toks) <- parsedFileDd1Ghc
      (t, _toks) <- parsedFileDd1Ghc
      let renamed = fromJust $ GHC.tm_renamed_source t

      let Just ((GHC.L _ n)) = locToName (16,6) renamed
      let res = definingDeclsNames [n] (hsBinds renamed) False False
      showGhc res `shouldBe` "[]"

    it "finds declarations at the top level" $ do
      -- ((_,Just renamed,_), _toks) <- parsedFileDd1Ghc
      (t, _toks) <- parsedFileDd1Ghc
      let renamed = fromJust $ GHC.tm_renamed_source t

      let Just (GHC.L _ n) = locToName (3,3) renamed
      let res = definingDeclsNames [n] (hsBinds renamed) False False
      showGhc res `shouldBe` "[DupDef.Dd1.toplevel x = DupDef.Dd1.c GHC.Num.* x]"

    {-
    it "includes the typedef if requested" $ do
      ((_,renamed,_), _toks) <- parsedFileDd1Ghc
      let Just (GHC.L _ n) = locToName dd1FileName (3,3) renamed
      let res = definingDeclsNames [n] renamed True False
      showGhc res `shouldBe` "[toplevel :: Integer -> Integer,DupDef.Dd1.toplevel x = DupDef.Dd1.c GHC.Num.* x]"
    -}

    {-
    it "strips other names from typedef" $ do
      {-
      modInfo@((_, _, mod@(GHC.L l (GHC.HsModule name exps imps ds _ _))), toks) <- parsedFileDd1Ghc
      let res = definingDecls [(PN (mkRdrName "c"))] ds True False
      showGhc res `shouldBe` "[c :: Integer, c = 7]"
      -}
      pending -- "Convert to definingDeclsNames"
    -}

    it "finds in a patbind" $ do
      -- ((_,Just renamed,_), _toks) <- parsedFileDd1Ghc
      (t, _toks) <- parsedFileDd1Ghc
      let renamed = fromJust $ GHC.tm_renamed_source t

      let Just (GHC.L _ n) = locToName (14,1) renamed
      let res = definingDeclsNames [n] (hsBinds renamed) False False
      showGhc res `shouldBe` "[DupDef.Dd1.tup@(DupDef.Dd1.h, DupDef.Dd1.t)\n   = GHC.List.head GHC.Base.$ GHC.List.zip [1 .. 10] [3 .. ff]\n   where\n       ff :: GHC.Types.Int\n       ff = 15]"


    {-
    it "finds in a patbind, with type signature" $ do
      {-
      modInfo@((_, _, mod@(GHC.L l (GHC.HsModule name exps imps ds _ _))), toks) <- parsedFileDd1Ghc
      let res = definingDecls [(PN (mkRdrName "tup"))] ds True False
      showGhc res `shouldBe` "[tup :: (Int, Int), tup@(h, t) = head $ zip [1 .. 10] [3 .. 15]]"
      -}
      pending -- "Convert to definingDeclsNames"
    -}

    {- ++AZ++ a data decl is not part of the binds
    it "finds in a data decl" $ do
      (t, _toks) <- parsedFileDd1Ghc
      let renamed = fromJust $ GHC.tm_renamed_source t

      let Just (GHC.L _ n) = locToName dd1FileName (16,6) renamed
      let res = definingDeclsNames [n] (hsBinds renamed) False False
      showGhc res `shouldBe` "[data D]"
      {-
      modInfo@((_, _, mod@(GHC.L l (GHC.HsModule name exps imps ds _ _))), toks) <- parsedFileDd1Ghc
      let res = definingDecls [(PN (GHC.mkRdrUnqual (GHC.mkDataOcc "A")))] ds True False
      showGhc res `shouldBe` "[data D = A | B String | C]"
      -}
    -}

    it "finds recursively in sub-binds" $ do
      {-
      modInfo@((_, _, mod@(GHC.L l (GHC.HsModule name exps imps ds _ _))), toks) <- parsedFileDd1Ghc
      let res = definingDecls [(PN (mkRdrName "zz"))] ds False True
      showGhc res `shouldBe` "[zz n = n + 1]" -- TODO: Currently fails, will come back to it
      -}
      pending -- "Currently fails, will come back to it"

    it "only finds recursively in sub-binds if asked" $ do
      {-
      modInfo@((_, _, mod@(GHC.L l (GHC.HsModule name exps imps ds _ _))), toks) <- parsedFileDd1Ghc
      let res = definingDecls [(PN (mkRdrName "zz"))] ds False False
      showGhc res `shouldBe` "[]"
      -}
      pending -- "Convert to definingDeclsNames"

  -- -------------------------------------------------------------------

  describe "definingSigsNames" $ do
    it "returns [] if not found" $ do
      (t, _toks) <- parsedFileDd1Ghc
      let renamed = fromJust $ GHC.tm_renamed_source t

      let Just ((GHC.L _ n)) = locToName (21,1) renamed
      showGhc n `shouldBe` "DupDef.Dd1.ff"
      let res = definingSigsNames [n] renamed
      showGhc res `shouldBe` "[]"

    it "finds signatures at the top level" $ do
      (t, _toks) <- parsedFileDd1Ghc
      let renamed = fromJust $ GHC.tm_renamed_source t

      let Just ((GHC.L _ n)) = locToName (4,1) renamed
      showGhc n `shouldBe` "DupDef.Dd1.toplevel"
      let res = definingSigsNames [n] renamed
      showGhc res `shouldBe` "[DupDef.Dd1.toplevel ::\n   GHC.Integer.Type.Integer -> GHC.Integer.Type.Integer]"

    it "returns only the single signature where there are others too" $ do
      (t, _toks) <- parsedFileDd1Ghc
      let renamed = fromJust $ GHC.tm_renamed_source t

      let Just ((GHC.L _ n)) = locToName (7,1) renamed
      showGhc n `shouldBe` "DupDef.Dd1.c"
      let res = definingSigsNames [n] renamed
      showGhc res `shouldBe`  "[DupDef.Dd1.c :: GHC.Integer.Type.Integer]"

    it "finds signatures at lower levels" $ do
      (t, _toks) <- parsedFileDd1Ghc
      let renamed = fromJust $ GHC.tm_renamed_source t

      let Just ((GHC.L _ n)) = locToName (16,5) renamed
      showGhc n `shouldBe` "ff"
      let res = definingSigsNames [n] renamed
      showGhc res `shouldBe` "[ff :: GHC.Types.Int]"

    it "finds multiple signatures" $ do
      (t, _toks) <- parsedFileDd1Ghc
      let renamed = fromJust $ GHC.tm_renamed_source t

      let Just ((GHC.L _ n1)) = locToName (21,1) renamed
      showGhc n1 `shouldBe` "DupDef.Dd1.ff"

      let Just ((GHC.L _ n2)) = locToName (16,5) renamed
      showGhc n2 `shouldBe` "ff"

      let Just ((GHC.L _ n3)) = locToName (4,1) renamed
      showGhc n3 `shouldBe` "DupDef.Dd1.toplevel"

      let res = definingSigsNames [n1,n2,n3] renamed
      showGhc res `shouldBe` "[ff :: GHC.Types.Int,\n DupDef.Dd1.toplevel ::\n   GHC.Integer.Type.Integer -> GHC.Integer.Type.Integer]"


  -- -------------------------------------------------------------------

  describe "definingTyClDeclsNames" $ do
    it "returns [] if not found" $ do
      (t, _toks) <- parsedFileGhc "./test/testdata/TypeUtils/TyClDecls.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t

      let Just ((GHC.L _ n)) = locToName (10,29) renamed
      let res = definingTyClDeclsNames [n] renamed
      showGhc res `shouldBe` "[]"

    -- ---------------------------------

    it "finds foreign type declarations" $ do
      pending

    -- ---------------------------------

    it "finds family declarations" $ do
      (t, _toks) <- parsedFileGhc "./test/testdata/TypeUtils/TyClDecls.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t
      -- (SYB.showData SYB.Renamer 0 renamed) `shouldBe` ""

      let Just (GHC.L _ n) = locToName (7,14) renamed
      let res = definingTyClDeclsNames [n] renamed
#if __GLASGOW_HASKELL__ > 704
      showGhc res `shouldBe` "[data family TypeUtils.TyClDEcls.XList a]"
#else
      showGhc res `shouldBe`
          "[data instance TypeUtils.TyClDEcls.XList GHC.Types.Char\n"++
          "     = TypeUtils.TyClDEcls.XCons !GHC.Types.Char !TypeUtils.TyClDEcls.XList GHC.Types.Char |\n"++
          "       TypeUtils.TyClDEcls.XNil,\n"++
          " data family TypeUtils.TyClDEcls.XList a]"
#endif

    -- ---------------------------------

    it "finds data declarations" $ do
      (t, _toks) <- parsedFileGhc "./test/testdata/TypeUtils/TyClDecls.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t

      let Just (GHC.L _ n) = locToName (12,6) renamed
      let res = definingTyClDeclsNames [n] renamed
      (unspace $ showGhc res) `shouldBe` "[data TypeUtils.TyClDEcls.Foo\n = TypeUtils.TyClDEcls.Foo GHC.Types.Int]"

    -- ---------------------------------

    it "finds type declarations" $ do
      (t, _toks) <- parsedFileGhc "./test/testdata/TypeUtils/TyClDecls.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t

      let Just (GHC.L _ n) = locToName (14,6) renamed
      let res = definingTyClDeclsNames [n] renamed
      showGhc res `shouldBe` "[type TypeUtils.TyClDEcls.Foo2 = GHC.Base.String]"

    -- ---------------------------------

    it "finds class declarations" $ do
      (t, _toks) <- parsedFileGhc "./test/testdata/TypeUtils/TyClDecls.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t

      let Just (GHC.L _ n) = locToName (16,7) renamed
      let res = definingTyClDeclsNames [n] renamed
      showGhc res `shouldBe` "[class TypeUtils.TyClDEcls.Bar a where\n   TypeUtils.TyClDEcls.bar :: a -> GHC.Types.Bool]"

    -- ---------------------------------

    it "finds multiple declarations" $ do
      (t, _toks) <- parsedFileGhc "./test/testdata/TypeUtils/TyClDecls.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t

      let Just (GHC.L _ n1) = locToName (14,6) renamed
      let Just (GHC.L _ n2) = locToName (16,7) renamed
      let res = definingTyClDeclsNames [n1,n2] renamed
      showGhc res `shouldBe`
            "[type TypeUtils.TyClDEcls.Foo2 = GHC.Base.String,\n"++
            " class TypeUtils.TyClDEcls.Bar a where\n"++
            "   TypeUtils.TyClDEcls.bar :: a -> GHC.Types.Bool]"


  -- -------------------------------------------------------------------

  describe "isFunBindR" $ do
    it "Returns False if not a function definition" $ do
      -- modInfo@((_,Just renamed, mod@(GHC.L l (GHC.HsModule name exps imps ds _ _))), toks) <- parsedFileDd1Ghc
      (t, _toks) <- parsedFileDd1Ghc
      -- let (GHC.L _l (GHC.HsModule _name _exps _imps _ds _ _)) = GHC.pm_parsed_source $ GHC.tm_parsed_module t
      let renamed = fromJust $ GHC.tm_renamed_source t

      -- let [decl] = definingDecls [(PN (mkRdrName "tup"))] ds False False
      let Just tup = getName "DupDef.Dd1.tup" renamed
      let [decl] = definingDeclsNames [tup] (hsBinds renamed) False False
      isFunBindR decl  `shouldBe` False

    it "Returns True if a function definition" $ do
      -- modInfo@((_,Just renamed, mod@(GHC.L l (GHC.HsModule name exps imps ds _ _))), toks) <- parsedFileDd1Ghc
      (t, _toks) <- parsedFileDd1Ghc
      let (GHC.L _l (GHC.HsModule _name _exps _imps _ds _ _)) = GHC.pm_parsed_source $ GHC.tm_parsed_module t
      let renamed = fromJust $ GHC.tm_renamed_source t

      let Just toplevel = getName "DupDef.Dd1.toplevel" renamed
      let [decl] = definingDeclsNames [toplevel] (hsBinds renamed) False False
      isFunBindR decl  `shouldBe` True

  -- -------------------------------------------------------------------

  describe "isFunOrPatName" $ do
    it "Return True if a PName is a function/pattern name defined in t" $ do
      (t, _toks) <- parsedFileDd1Ghc
      -- let (GHC.L _l (GHC.HsModule _name _exps _imps _ds _ _)) = GHC.pm_parsed_source $ GHC.tm_parsed_module t
      let renamed = fromJust $ GHC.tm_renamed_source t

      let Just tup = getName "DupDef.Dd1.tup" renamed
      isFunOrPatName tup renamed  `shouldBe` True

    it "Return False if a PName is a function/pattern name defined in t" $ do
      (t, _toks)   <- parsedFileDd1Ghc
      (t2, _toks2) <- parsedFileDd2Ghc
      -- let mod@(GHC.L l (GHC.HsModule name exps imps ds _ _)) = GHC.pm_parsed_source $ GHC.tm_parsed_module t
      let renamed  = fromJust $ GHC.tm_renamed_source t
      let renamed2 = fromJust $ GHC.tm_renamed_source t2

      let Just tup = getName "DupDef.Dd1.tup" renamed
      isFunOrPatName tup renamed2  `shouldBe` False


  -- -------------------------------------------------------------------

{- ++AZ++
  describe "isSimplePatBind" $ do
    it "returns False if not a simple pat bind" $ do
      modInfo@((_, _, mod@(GHC.L l (GHC.HsModule name exps imps ds _ _))), toks) <- parsedFileDd1Ghc
      let [decl] = definingDecls [(PN (mkRdrName "toplevel"))] ds False False
      isSimplePatBind decl  `shouldBe` False

    it "returns True if a simple pat bind" $ do
      modInfo@((_, _, mod@(GHC.L l (GHC.HsModule name exps imps ds _ _))), toks) <- parsedFileDd1Ghc
      let [decl] = definingDecls [(PN (mkRdrName "tup"))] ds False False
      isSimplePatBind decl  `shouldBe` True
-}

  -- ---------------------------------------------------------------------
{-
  describe "showGhc" $ do
    it "Constructs custom GHC.DynFlags" $ do
      (t, toks) <- parsedFileDeclareGhc
      let renamed = fromJust $ GHC.tm_renamed_source t

      let
        comp = do
          return (prettyprint df df)
      -- ((res),_s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      ((res),_s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }

      (show res) `shouldBe` ""
-}
  -- ---------------------------------------------------------------------

  describe "hsFreeAndDeclaredPNs" $ do

    it "finds declared in type class definitions" $ do
      (t, toks) <- parsedFileGhc "./test/testdata/FreeAndDeclared/DeclareTypes.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t
      -- (SYB.showData SYB.Renamer 0 renamed) `shouldBe` ""
      -- (SYB.showData SYB.Renamer 0 $ hsTyDecls renamed) `shouldBe` ""

      let
        comp = do
          let tds = nub $ concatMap getDeclaredTypes $ concat $ hsTyDecls renamed
          return (tds)
      ((res),_s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- ((res),_s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }

      (showGhc $ map (\n -> (n, getGhcLoc $ GHC.nameSrcSpan n)) (res)) `shouldBe` 
          "[(FreeAndDeclared.DeclareTypes.XList, (8, 13)),\n"++
#if __GLASGOW_HASKELL__ > 704
#else
          " (FreeAndDeclared.DeclareTypes.XListUnit, (14, 26)),\n"++
          " (FreeAndDeclared.DeclareTypes.XCons, (11, 28)),\n"++
          " (FreeAndDeclared.DeclareTypes.XNil, (11, 56)),\n"++
#endif
          " (FreeAndDeclared.DeclareTypes.Foo, (21, 6)),\n"++
          " (FreeAndDeclared.DeclareTypes.X, (19, 6)),\n"++
          " (FreeAndDeclared.DeclareTypes.Y, (19, 10)),\n"++
          " (FreeAndDeclared.DeclareTypes.Z, (19, 22)),\n"++
          " (FreeAndDeclared.DeclareTypes.W, (19, 26)),\n"++
          " (FreeAndDeclared.DeclareTypes.Bar, (23, 7)),\n"++
          " (FreeAndDeclared.DeclareTypes.doBar, (27, 3)),\n"++
          " (FreeAndDeclared.DeclareTypes.BarVar, (24, 8)),\n"++
          " (FreeAndDeclared.DeclareTypes.BarData, (25, 8))]"

    -- ---------------------------------

    it "finds declared HsVar" $ do
      (t, toks) <- parsedFileGhc "./test/testdata/FreeAndDeclared/Declare.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t
      -- (SYB.showData SYB.Renamer 0 renamed) `shouldBe` ""

      let
        comp = do
          let r = hsFreeAndDeclaredPNsOld renamed
          rg <- hsFreeAndDeclaredPNs renamed
          let ff = map (\b -> getFreeVars [b]) $ hsBinds renamed
          return (r,rg,ff)
      ((res,resg,_fff),_s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- ((res,resg,_fff),_s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }

      -- (showGhc _fff) `shouldBe` ""

      -- Free Vars
      (showGhc $ map (\n -> (n, getGhcLoc $ GHC.nameSrcSpan n)) (fst res)) `shouldBe` 
                   "[(Data.Generics.Text.gshow, (-1, -1)),\n "++
                   "(System.IO.getChar, (-1, -1)), "++
                   "(System.IO.putStrLn, (-1, -1)),\n "++
                   "(GHC.Base.return, (-1, -1)), "++
                   "(GHC.Base.$, (-1, -1)),\n "++
                   "(GHC.List.head, (-1, -1)), "++
                   "(GHC.List.zip, (-1, -1)),\n "++
                   "(GHC.Num.fromInteger, (-1, -1)), "++
                   "(GHC.Num.*, (-1, -1))]"

      -- Declared Vars
      (showGhc $ map (\n -> (n, getGhcLoc $ GHC.nameSrcSpan n)) (snd res)) `shouldBe` 
                   "[(FreeAndDeclared.Declare.ff, (36, 1)),\n "++
                   "(FreeAndDeclared.Declare.mkT, (34, 1)),\n "++
                   "(FreeAndDeclared.Declare.main, (30, 1)),\n "++
                   "(FreeAndDeclared.Declare.unF, (27, 1)),\n "++
                   "(FreeAndDeclared.Declare.unD, (21, 1)),\n "++
                   "(FreeAndDeclared.Declare.h, (16, 6)),\n "++
                   "(FreeAndDeclared.Declare.t, (16, 8)),\n "++
                   "(FreeAndDeclared.Declare.d, (10, 1)),\n "++
                   "(FreeAndDeclared.Declare.c, (9, 1)),\n "++
                   "(FreeAndDeclared.Declare.toplevel, (6, 1))]"

      -- GHC version
      -- Free Vars
      (showGhc $ map (\n -> (n, getGhcLoc $ GHC.nameSrcSpan n)) (fst resg)) `shouldBe` 
                   "[(Data.Generics.Text.gshow, (-1, -1)),\n "++
                   "(System.IO.getChar, (-1, -1)), "++
                   "(System.IO.putStrLn, (-1, -1)),\n "++
                   "(GHC.List.head, (-1, -1)), "++
                   "(GHC.Base.$, (-1, -1)),\n "++
                   "(GHC.List.zip, (-1, -1)), "++
                   "(GHC.Num.*, (-1, -1))]"

      -- Declared Vars
      (showGhc $ map (\n -> (n, getGhcLoc $ GHC.nameSrcSpan n)) (snd resg)) `shouldBe` 
                   "[(FreeAndDeclared.Declare.ff, (36, 1)),\n "++
                   "(FreeAndDeclared.Declare.mkT, (34, 1)),\n "++
                   "(FreeAndDeclared.Declare.main, (30, 1)),\n "++
                   "(FreeAndDeclared.Declare.unF, (27, 1)),\n "++
                   "(FreeAndDeclared.Declare.unD, (21, 1)),\n "++
                   "(FreeAndDeclared.Declare.tup, (16, 1)),\n "++ -- ++AZ++ not found by old
                   "(FreeAndDeclared.Declare.h, (16, 6)),\n "++
                   "(FreeAndDeclared.Declare.t, (16, 8)),\n "++
                   "(FreeAndDeclared.Declare.d, (10, 1)),\n "++
                   "(FreeAndDeclared.Declare.c, (9, 1)),\n "++
                   "(FreeAndDeclared.Declare.toplevel, (6, 1)),\n "++
                   "(GHC.Types.Int, (-1, -1)), (GHC.Integer.Type.Integer, (-1, -1)),\n "++
                   "(FreeAndDeclared.Declare.D, (18, 6)),\n "++
                   "(FreeAndDeclared.Declare.A, (18, 10)),\n "++
                   "(FreeAndDeclared.Declare.B, (18, 14)),\n "++
                   "(FreeAndDeclared.Declare.C, (18, 25)),\n "++
                   "(FreeAndDeclared.Declare.F, (25, 6)),\n "++
                   "(FreeAndDeclared.Declare.G, (25, 10)),\n "++
                   "(FreeAndDeclared.Declare.:|, (25, 14))]"

    -- ---------------------------------

    it "finds free and declared in a single bind PrefixCon" $ do
      (t, toks) <- parsedFileGhc "./test/testdata/FreeAndDeclared/Declare.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t
      -- (SYB.showData SYB.Renamer 0 renamed) `shouldBe` ""

      let
        comp = do
          let b = head $ drop 4 $ hsBinds renamed
          rg <- hsFreeAndDeclaredPNs [b]
          return (b,rg)
      ((bb,resg),_s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- ((bb,resg),_s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }

      (showGhc bb) `shouldBe` "FreeAndDeclared.Declare.unD (FreeAndDeclared.Declare.B y) = y"
      -- (SYB.showData SYB.Renamer 0 bb) `shouldBe` ""

      -- GHC version
      -- Free Vars
      (showGhc $ map (\n -> (n, getGhcLoc $ GHC.nameSrcSpan n)) (fst resg)) `shouldBe` 
                   "[(FreeAndDeclared.Declare.B, (18, 14))]"

      -- Declared Vars
      (showGhc $ map (\n -> (n, getGhcLoc $ GHC.nameSrcSpan n)) (snd resg)) `shouldBe` 
                   "[(FreeAndDeclared.Declare.unD, (21, 1))]"

    -- ---------------------------------

    it "finds free and declared in a single bind InfixCon" $ do
      (t, toks) <- parsedFileGhc "./test/testdata/FreeAndDeclared/Declare.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t
      -- (SYB.showData SYB.Renamer 0 renamed) `shouldBe` ""

      let
        comp = do
          let b = head $ drop 3 $ hsBinds renamed
          rg <- hsFreeAndDeclaredPNs [b]
          return (b,rg)
      ((bb,resg),_s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- ((bb,resg),_s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }

      (showGhc bb) `shouldBe` "FreeAndDeclared.Declare.unF (a FreeAndDeclared.Declare.:| b)\n  = (a, b)"
      -- (SYB.showData SYB.Renamer 0 bb) `shouldBe` ""

      -- GHC version
      -- Free Vars
      (showGhc $ map (\n -> (n, getGhcLoc $ GHC.nameSrcSpan n)) (fst resg)) `shouldBe` 
                   "[(FreeAndDeclared.Declare.:|, (25, 14))]"

      -- Declared Vars
      (showGhc $ map (\n -> (n, getGhcLoc $ GHC.nameSrcSpan n)) (snd resg)) `shouldBe` 
                   "[(FreeAndDeclared.Declare.unF, (27, 1))]"

    -- ---------------------------------

    it "finds free and declared in a single bind RecCon" $ do
      (t, toks) <- parsedFileGhc "./test/testdata/FreeAndDeclared/DeclareRec.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t
      -- (SYB.showData SYB.Renamer 0 renamed) `shouldBe` ""

      let
        comp = do
          let b = head $ drop 0 $ hsBinds renamed
          rg <- hsFreeAndDeclaredPNs [b]
          return (b,rg)
      ((bb,resg),_s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- ((bb,resg),_s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }

      (showGhc bb) `shouldBe` "FreeAndDeclared.DeclareRec.unR2\n  (FreeAndDeclared.DeclareRec.RCon {FreeAndDeclared.DeclareRec.r1 = a})\n  = a"
      -- (SYB.showData SYB.Renamer 0 bb) `shouldBe` ""

      -- GHC version
      -- Free Vars
      (showGhc $ map (\n -> (n, getGhcLoc $ GHC.nameSrcSpan n)) (fst resg)) `shouldBe` 
                   "[(FreeAndDeclared.DeclareRec.RCon, (3, 10))]"

      -- Declared Vars
      (showGhc $ map (\n -> (n, getGhcLoc $ GHC.nameSrcSpan n)) (snd resg)) `shouldBe` 
                   "[(FreeAndDeclared.DeclareRec.unR2, (7, 1))]"

    -- -----------------------------------------------------------------

    it "hsFreeAndDeclaredPNs simplest" $ do
      (t, toks) <- parsedFileDeclareSGhc
      let renamed = fromJust $ GHC.tm_renamed_source t
      -- (SYB.showData SYB.Renamer 0 renamed) `shouldBe` ""
      let
        comp = do
          r <- hsFreeAndDeclaredPNs renamed
          return r
      ((res),_s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- ((res),_s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }

      -- Free Vars
      (showGhc $ map (\n -> (n, getGhcLoc $ GHC.nameSrcSpan n)) (fst res)) `shouldBe` "[]"

      -- Declared Vars
      (showGhc $ map (\n -> (n, getGhcLoc $ GHC.nameSrcSpan n)) (snd res)) `shouldBe` "[(FreeAndDeclared.DeclareS.c, (6, 1))]"

    -- -----------------------------------------------------------------

    it "finds free and declared in a single bind #2" $ do
      (t, toks) <- parsedFileGhc "./test/testdata/DupDef/Dd1.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t

      let Just tup = getName "DupDef.Dd1.ff" renamed
      let [decl] = definingDeclsNames [tup] (hsBinds renamed) False False

      let
        comp = do
          -- let r = hsFreeAndDeclaredPNs decl
          r <- hsFreeAndDeclaredPNs [decl]
          return (r,decl)
      ((res,d),_s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- ((res,d),_s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }

      (showGhc d) `shouldBe` "DupDef.Dd1.ff y\n  = y GHC.Num.+ zz\n  where\n      zz = 1"
      -- (SYB.showData SYB.Renamer 0 d) `shouldBe` ""

      -- Free Vars
      (showGhc $ map (\n -> (n, getGhcLoc $ GHC.nameSrcSpan n)) (fst res)) `shouldBe` 
                   "[(GHC.Num.+, (-1, -1))]"

      -- Declared Vars
      (showGhc $ map (\n -> (n, getGhcLoc $ GHC.nameSrcSpan n)) (snd res)) `shouldBe` 
                   "[(DupDef.Dd1.ff, (21, 1))]"

    -- -----------------------------------------------------------------

    it "finds free and declared at the top level 1" $ do
      (t, toks) <- parsedFileGhc "./test/testdata/LiftToToplevel/WhereIn1.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t

      let
        comp = do
          -- r <- hsFreeAndDeclaredPNs renamed
          r <- hsFreeAndDeclaredPNs $ hsBinds renamed
          return r
      ((res),_s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }

      -- Declared Vars
      (showGhc $ map (\n -> (n, getGhcLoc $ GHC.nameSrcSpan n)) (snd res)) `shouldBe` 
                   "[(LiftToToplevel.WhereIn1.anotherFun, (15, 1)),\n "++
                   "(LiftToToplevel.WhereIn1.sumSquares, (9, 1))]"

      -- Free Vars
      (showGhc $ map (\n -> (n, getGhcLoc $ GHC.nameSrcSpan n)) (fst res)) `shouldBe` 
                   "[(GHC.Real.^, (-1, -1)), (GHC.Num.+, (-1, -1))]"

    -- -----------------------------------------------------------------

    it "finds free and declared at the top level 2" $ do
      (t, toks) <- parsedFileGhc "./test/testdata/Renaming/IdIn3.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t

      let
        comp = do
          r <- hsFreeAndDeclaredPNs renamed
          -- r <- hsFreeAndDeclaredPNs $ hsBinds renamed
          return r
      ((res),_s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- ((res),_s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }

      -- Declared Vars
      (showGhc $ map (\n -> (n, getGhcLoc $ GHC.nameSrcSpan n)) (snd res)) `shouldBe` 
                   "[(IdIn3.bar, (14, 1))"++
                  ", (IdIn3.x, (10, 1))"++
                  ", (IdIn3.foo, (12, 1)),\n "++
                    "(IdIn3.main, (18, 1))]"


      -- Free Vars
      (showGhc $ map (\n -> (n, getGhcLoc $ GHC.nameSrcSpan n)) (fst res)) `shouldBe` 
                   "[(GHC.Num.+, (-1, -1))]"

    -- -----------------------------------------------------------------

    it "finds free and declared in a GRHSs" $ do
      (t, toks) <- parsedFileGhc "./test/testdata/LiftOneLevel/LetIn2.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t

      let Just tup = getName "LiftOneLevel.LetIn2.sumSquares" renamed
      let [decl] = definingDeclsNames [tup] (hsBinds renamed) False False

      let (GHC.L _ (GHC.FunBind _ _ (GHC.MatchGroup [match] _) _ _ _)) = decl
      let (GHC.L _ (GHC.Match _pat _ grhss)) = match
      -- (SYB.showData SYB.Renamer 0 grhss) `shouldBe` ""

      let
        comp = do
          r <- hsFreeAndDeclaredPNs grhss
          -- r <- hsFreeAndDeclaredPNs $ hsBinds renamed
          return r
      ((res),_s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- ((res),_s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }

      -- Declared Vars
      (showGhc $ map (\n -> (n, getGhcLoc $ GHC.nameSrcSpan n)) (snd res)) `shouldBe` 
                   "[]"

      -- Free Vars
      (showGhc $ map (\n -> (n, getGhcLoc $ GHC.nameSrcSpan n)) (fst res)) `shouldBe` 
                   "[(GHC.Real.^, (-1, -1)), (x, (10, 12)), (GHC.Num.+, (-1, -1)),\n (y, (10, 14))]"

    -- -----------------------------------------------------------------

    it "finds free and declared in a single bind" $ do
      pending -- "fix the prior test"

    -- -----------------------------------------------------------------
{-
    it "It does stop_tdTU" $ do
      -- Top-down type-unifying traversal that is cut of below nodes
      -- where the argument strategy succeeds.
      -- http://hackage.haskell.org/packages/archive/StrategyLib/4.0.0.0/doc/html/Data-Generics-Strafunski-StrategyLib-TraversalTheme.html#v%3Astop_tdTU

      (t, _toks) <- parsedFileLiftD1Ghc
      let renamed = fromJust $ GHC.tm_renamed_source t

      let res = hsFreeAndDeclaredPNs $ hsBinds renamed

      -- (showGhc $ hsBinds renamed) `shouldBe` ""

      let ff = getFvs $ hsBinds renamed
      (showGhc ff) `shouldBe` ""

      -- Free Vars
      {-
      (showGhc $ map (\n -> (n, getGhcLoc $ GHC.nameSrcSpan n)) (fst res)) `shouldBe` 
                   "[(GHC.Num.+, (-1, -1)), "++
                    "(sq, (8, 6)), "++
                    "(x, (6, 13)),\n "++
                    "(LiftToToplevel.D1.sumSquares, (6, 1)), "++
                    "(xs, (6, 15)),\n "++
                    "(GHC.Num.fromInteger, (-1, -1)), "++
                    "(GHC.Real.^, (-1, -1)),\n "++
                    "(x, (8, 9)), (pow, (9, 6))]"
      -}

      -- Declared Vars
      (showGhc $ map (\n -> (n, getGhcLoc $ GHC.nameSrcSpan n)) (snd res)) `shouldBe` 
                   "[(LiftToToplevel.D1.sumSquares, (6, 1)), "++
                    "(x, (6, 13)),\n "++
                    "(xs, (6, 15)), "++
                    "(LiftToToplevel.D1.main, (13, 1))]"
-}

  -- ---------------------------------------------------------------------

  describe "hsFDsFromInside" $ do
    it "does something useful" $ do
      pending -- "Complete this"

  describe "hsFDNamesFromInside" $ do
    it "does something useful" $ do
      pending -- "Complete this"

  -- ---------------------------------------------------------------------

  describe "hsVisibleNames" $ do
    it "does something useful" $ do
      pending -- "Complete this"

  -- ---------------------------------------------------------------------

  describe "hsVisiblePNs" $ do

    -- ---------------------------------

    it "returns [] if e does not occur in t" $ do
      (t,toks) <- parsedFileGhc "./test/testdata/DupDef/Dd1.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t

      let Just tl1  = locToExp (4,13) (4,40) renamed :: (Maybe (GHC.Located (GHC.HsExpr GHC.Name)))
      let Just tup = getName "DupDef.Dd1.tup" renamed
      -- let [decl] = definingDeclsNames [tup] (hsBinds renamed) False False
      let
        comp = do
          r <- hsVisiblePNs tup tl1
          return r
      ((res),_s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- ((res),_s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }

      (showGhc $ res) `shouldBe` "[]"

    -- -----------------------------------------------------------------

    it "returns visible vars if e does occur in t #1" $ do
      (t,toks) <- parsedFileGhc "./test/testdata/DupDef/Dd1.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t
      -- (SYB.showData SYB.Renamer 0 renamed) `shouldBe` ""

      let Just tl1  = locToExp (28,4) (28,12) renamed :: (Maybe (GHC.Located (GHC.HsExpr GHC.Name)))
      (showGhc tl1) `shouldBe` "ll GHC.Num.+ z"
      -- (SYB.showData SYB.Renamer 0 tl1) `shouldBe` ""

      let Just tup = getName "DupDef.Dd1.l" renamed
      let [decl] = definingDeclsNames [tup] (hsBinds renamed) False False
      (showGhc decl) `shouldBe` "DupDef.Dd1.l z = let ll = 34 in ll GHC.Num.+ z"
      -- (SYB.showData SYB.Renamer 0 decl) `shouldBe` ""

      let
        comp = do
         r <- hsVisiblePNs tl1 decl
         -- let r2 = hsVisiblePNsOld tl1 decl
         return (r)
      ((res),_s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- ((res,res2),_s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }

      (showGhc res ) `shouldBe` "[z, ll]"
      -- (showGhc res2 ) `shouldBe` "[z, ll]"

    -- -----------------------------------------------------------------

    it "returns visible vars if e does occur in t #2" $ do
      (t,toks) <- parsedFileDd1Ghc
      let renamed = fromJust $ GHC.tm_renamed_source t

      let Just tl1  = locToExp (28,4) (28,12) renamed :: (Maybe (GHC.Located (GHC.HsExpr GHC.Name)))
      (showGhc tl1) `shouldBe` "ll GHC.Num.+ z"

      let Just rhs  = locToExp (26,1) (28,12) renamed :: (Maybe (GHC.Located (GHC.HsExpr GHC.Name)))
      (showGhc rhs) `shouldBe` "let ll = 34 in ll GHC.Num.+ z"

      let
        comp = do
          r <- hsVisiblePNs tl1 rhs
          return r
      ((res),_s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }

      (showGhc res) `shouldBe` "[ll]"

    -- -----------------------------------------------------------------

{-
    it "returns visible vars if e does occur in t #3" $ do
      (t,toks) <- parsedFileGhc "./test/testdata/TypeUtils/VisiblePNs.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t
      (SYB.showData SYB.Renamer 0 renamed) `shouldBe` ""

      let
        comp = do
          renamed <- getRefactRenamed
          let Just tl1  = locToName (41,11) renamed  --  :: (Maybe (GHC.Located (GHC.HsExpr GHC.Name)))
          r <- hsVisiblePNs tl1 renamed
          -- let r = hsVisiblePNsGhc tl1 renamed
          let fvs = map (\b -> (showGhc b,getFreeVars [b])) (hsBinds renamed)
          let dvs = getDeclaredVars $ hsBinds renamed
          return (tl1,r,fvs,dvs)
      -- ((tl,res,_f,d),_s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      ((tl,res,_f,d),_s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }

      (showGhc tl) `shouldBe` "modu"
      -- (showGhc f) `shouldBe` ""
      (showGhc d) `shouldBe`
           "[TypeUtils.VisiblePNs.parsedFileGhc,\n"++
           " TypeUtils.VisiblePNs.parsedFileBGhc,\n"++
           " TypeUtils.VisiblePNs.runRefactGhcState,"++
           " TypeUtils.VisiblePNs.zz,\n"++
           " TypeUtils.VisiblePNs.yy,"++
           " TypeUtils.VisiblePNs.xx,\n"++
           " TypeUtils.VisiblePNs.ww,"++
           " TypeUtils.VisiblePNs.spec,\n"++
           " TypeUtils.VisiblePNs.main]"
      (showGhc res) `shouldBe`
           "[TypeUtils.VisiblePNs.parsedFileGhc,\n"++
           " TypeUtils.VisiblePNs.parsedFileBGhc,\n"++
           " TypeUtils.VisiblePNs.runRefactGhcState,"++
           " TypeUtils.VisiblePNs.zz,\n"++
           " TypeUtils.VisiblePNs.yy,"++
           " TypeUtils.VisiblePNs.xx,\n"++
           " TypeUtils.VisiblePNs.ww,"++
           " TypeUtils.VisiblePNs.spec,\n"++
           " TypeUtils.VisiblePNs.main,"++
           " modu,"++
           " t,"++
           " _toks,"++
           " expr]"
-}

  -- ---------------------------------------------------------------------

  describe "hsVisibleDs" $ do
    it "finds function arguments visible in RHS 1" $ do
      (t,toks) <- parsedFileGhc "./test/testdata/Visible/Simple.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t
      -- (SYB.showData SYB.Renamer 0 renamed) `shouldBe` ""

      let Just e  = locToExp (5,11) (5,19) renamed :: (Maybe (GHC.Located (GHC.HsExpr GHC.Name)))
      (showGhc e) `shouldBe` "a GHC.Num.+ b"

      let Just n = getName "Visible.Simple.params" renamed
      let [decl] = definingDeclsNames [n] (hsBinds renamed) False False

      let binds = hsValBinds [decl]

      -- (SYB.showData SYB.Renamer 0 $ head $ hsBinds binds) `shouldBe` ""

      let
        comp = do
          fds' <- hsVisibleDs e $  head $ hsBinds binds
          -- let fds'o = hsVisiblePNsOld e $  head $ hsBinds binds
          return (fds')
      ((fds),_s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- ((fds),_s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }

      (show fds) `shouldBe` "DN [a, b, GHC.Num.+]"

    -- -----------------------------------

    it "finds function arguments visible in RHS 2" $ do
      (t,toks) <- parsedFileGhc "./test/testdata/Visible/Simple.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t
      -- (SYB.showData SYB.Renamer 0 renamed) `shouldBe` ""

      let Just e  = locToExp (9,15) (9,17) renamed :: (Maybe (GHC.LHsExpr GHC.Name))
      (showGhc e) `shouldBe` "x"

      let Just n = getName "Visible.Simple.param2" renamed
      let [decl] = definingDeclsNames [n] (hsBinds renamed) False False

      let binds = hsValBinds [decl]

      let
        comp = do
          fds' <- hsVisibleDs e $  head $ hsBinds binds
          return (fds')
      ((fds),_s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- ((fds),_s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }

      (show fds) `shouldBe` "DN [x]"


    -- -----------------------------------

    it "finds visible vars inside a function" $ do
      (t,toks) <- parsedFileGhc "./test/testdata/Renaming/IdIn5.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t
      -- (SYB.showData SYB.Renamer 0 renamed) `shouldBe` ""

      let Just rhs  = locToExp (14,6) (15,14) renamed :: (Maybe (GHC.LHsExpr GHC.Name))
      (showGhc rhs) `shouldBe` "IdIn5.x GHC.Num.+ y GHC.Num.+ z"
      -- (SYB.showData SYB.Renamer 0 rhs) `shouldBe` ""

      let Just e = getName "IdIn5.x" renamed

      let
        comp = do
          fds' <- hsVisibleDs e rhs
          ffds <- hsFreeAndDeclaredGhc rhs
          return (fds',ffds)
      ((fds,_fds),_s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- ((fds,_fds),_s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }

      (show _fds) `shouldBe` "(FN [IdIn5.x, GHC.Num.+, y, z],DN [])"
      (show fds) `shouldBe` "DN [GHC.Num.+, y, z]"


  -- ---------------------------------------------------------------------

  describe "hsFreeAndDeclaredGhc" $ do
    it "finds function arguments visible in RHS fd" $ do
      (t,toks) <- parsedFileGhc "./test/testdata/Visible/Simple.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t
      -- (SYB.showData SYB.Renamer 0 renamed) `shouldBe` ""

      let Just e  = locToExp (5,11) (5,19) renamed :: (Maybe (GHC.Located (GHC.HsExpr GHC.Name)))
      (showGhc e) `shouldBe` "a GHC.Num.+ b"

      let Just n = getName "Visible.Simple.params" renamed
      let [decl] = definingDeclsNames [n] (hsBinds renamed) False False

      let binds = hsValBinds [decl]

      let
        comp = do
          fds' <- hsFreeAndDeclaredGhc $  head $ hsBinds binds
          return (fds')
      ((fds),_s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- ((fds),_s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }

      (show fds) `shouldBe` "(FN [GHC.Num.+],DN [Visible.Simple.params])"

    -- -----------------------------------

    it "finds function arguments and free vars visible in RHS" $ do
      (t,toks) <- parsedFileGhc "./test/testdata/Visible/Simple.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t
      -- (SYB.showData SYB.Renamer 0 renamed) `shouldBe` ""

      let Just e  = locToExp (9,15) (9,17) renamed :: (Maybe (GHC.LHsExpr GHC.Name))
      (showGhc e) `shouldBe` "x"

      let Just n = getName "Visible.Simple.param2" renamed
      let [decl] = definingDeclsNames [n] (hsBinds renamed) False False

      let binds = hsValBinds [decl]
      let (GHC.L _ (GHC.FunBind _ _ (GHC.MatchGroup matches _) _ _ _)) = head $ hsBinds binds
      let [(GHC.L _ (GHC.Match pats _ _))] = matches
      let lpat = head pats

      let
        comp = do
          fds' <- hsFreeAndDeclaredGhc $ lpat
          return (fds')
      ((fds),_s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- ((fds),_s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }

      (show fds) `shouldBe` "(FN [Visible.Simple.B],DN [x])"

    -- -----------------------------------

    it "finds imported functions used in the rhs" $ do
      (t,toks) <- parsedFileGhc "./test/testdata/FreeAndDeclared/Declare.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t
      -- (SYB.showData SYB.Renamer 0 renamed) `shouldBe` ""

      let Just n = getName "FreeAndDeclared.Declare.tup" renamed
      let decls = definingDeclsNames [n] (hsBinds renamed) False False
      -- (SYB.showData SYB.Renamer 0 decls) `shouldBe` ""

      let
        comp = do
          fds' <- hsFreeAndDeclaredGhc $ decls
          return (fds')
      ((fds),_s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- ((fds),_s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }

      (show fds) `shouldBe`
            "(FN [GHC.List.head, GHC.Base.$, GHC.List.zip],"++
            "DN [FreeAndDeclared.Declare.tup, FreeAndDeclared.Declare.h,\n "++
                "FreeAndDeclared.Declare.t])"

    -- -----------------------------------

    it "finds free vars in HsWithBndrs" $ do
      (t,toks) <- parsedFileGhc "./test/testdata/FreeAndDeclared/Binders.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t
      -- (SYB.showData SYB.Renamer 0 renamed) `shouldBe` ""

      let Just n = getName "FreeAndDeclared.Binders.findNewPName" renamed
      let [decl] = definingDeclsNames [n] (hsBinds renamed) False False
      let (GHC.L _ (GHC.FunBind _ _ (GHC.MatchGroup [match] _) _ _ _)) = decl
      let (GHC.L _ (GHC.Match _pats _rhs binds)) = match
      -- (SYB.showData SYB.Renamer 0 binds) `shouldBe` ""
      -- (showGhc binds) `shouldBe` ""

      let
        comp = do
          fds' <- hsFreeAndDeclaredGhc $ binds
          return (fds')
      ((fds),_s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- ((fds),_s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }

      (show fds) `shouldBe`
            "(FN [FreeAndDeclared.Binders.gfromJust,"++
            " FreeAndDeclared.Binders.Name,\n"++
            " FreeAndDeclared.Binders.occNameString,"++
            " GHC.Base.$,\n"++
            " FreeAndDeclared.Binders.getOccName,"++
            " GHC.Classes.==,"++
            " name,\n"++
            " Data.Maybe.Just,"++
            " Data.Maybe.Nothing,\n"++
            " FreeAndDeclared.Binders.somethingStaged,\n"++
            " FreeAndDeclared.Binders.Renamer, renamed],"++
            "DN [worker, res])"

    -- -----------------------------------

    it "finds free vars in TH files" $ do
      (t,toks) <- parsedFileGhc "./test/testdata/TH/Main.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t
      -- (SYB.showData SYB.Renamer 0 renamed) `shouldBe` ""

      -- (SYB.showData SYB.Renamer 0 binds) `shouldBe` ""
      -- (showGhc binds) `shouldBe` ""

      let
        comp = do
          fds' <- hsFreeAndDeclaredGhc renamed
          return (fds')
      ((fds),_s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- ((fds),_s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }

      (show fds) `shouldBe`
            "(FN [System.IO.putStrLn, TH.Printf.pr],"++
             "DN [TH.Main.baz, TH.Main.sillyString, TH.Main.main])"

  -- ---------------------------------------------

  describe "getParsedForRenamedLPat" $ do
    it "gets the ParsedSource version of a RenamedSource LPat" $ do
      (t,_toks) <- parsedFileGhc "./test/testdata/Visible/Simple.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t
      -- (SYB.showData SYB.Renamer 0 renamed) `shouldBe` ""
      let parsed = GHC.pm_parsed_source $ GHC.tm_parsed_module t

      let Just e  = locToExp (9,15) (9,17) renamed :: (Maybe (GHC.LHsExpr GHC.Name))
      (showGhc e) `shouldBe` "x"

      let Just n = getName "Visible.Simple.param2" renamed
      let [decl] = definingDeclsNames [n] (hsBinds renamed) False False

      let binds = hsValBinds [decl]
      let (GHC.L _ (GHC.FunBind _ _ (GHC.MatchGroup matches _) _ _ _)) = head $ hsBinds binds
      let [(GHC.L _ (GHC.Match pats _ _))] = matches
      let pat@(GHC.L lp _) = head pats

      let pat' = getParsedForRenamedLPat parsed pat

      let (GHC.L lp' _) = pat'
      lp `shouldBe` lp'

      (SYB.showData SYB.Renamer 0 pat') `shouldBe`
           "\n"++
           "(L {test/testdata/Visible/Simple.hs:9:8-12} \n"++
           " (ParPat \n"++
           "  (L {test/testdata/Visible/Simple.hs:9:9-11} \n"++
           "   (ConPatIn \n"++
           "    (L {test/testdata/Visible/Simple.hs:9:9} \n"++
           "     (Unqual {OccName: B})) \n"++
           "    (PrefixCon \n"++
           "     [\n"++
           "      (L {test/testdata/Visible/Simple.hs:9:11} \n"++
           "       (VarPat \n"++
           "        (Unqual {OccName: x})))])))))"

      (SYB.showData SYB.Renamer 0 pat) `shouldBe`
           "\n"++
           "(L {test/testdata/Visible/Simple.hs:9:8-12} \n"++
           " (ParPat \n"++
           "  (L {test/testdata/Visible/Simple.hs:9:9-11} \n"++
           "   (ConPatIn \n"++
           "    (L {test/testdata/Visible/Simple.hs:9:9} {Name: Visible.Simple.B}) \n"++
           "    (PrefixCon \n"++
           "     [\n"++
           "      (L {test/testdata/Visible/Simple.hs:9:11} \n"++
           "       (VarPat {Name: x}))])))))"


  -- ---------------------------------------------

  describe "isLocalPN" $ do
    it "returns True if the name is local to the module" $ do
      (t, _toks) <- parsedFileDd1Ghc
      let renamed = fromJust $ GHC.tm_renamed_source t
      let Just (GHC.L _ n) = locToName (17, 5) renamed
      (showGhc n) `shouldBe` "ff"
      isLocalPN n `shouldBe` True

    it "returns False if the name is not local to the module" $ do
      (t, _toks) <- parsedFileDd1Ghc
      let renamed = fromJust $ GHC.tm_renamed_source t
      let Just (GHC.L _ n) = locToName (21, 1) renamed
      (showGhc n) `shouldBe` "DupDef.Dd1.ff"
      isLocalPN n `shouldBe` False

  -- ---------------------------------------------

  describe "isTopLevelPN" $ do
    it "returns False if the name is not defined at the top level of the module" $ do
      (t, toks) <- parsedFileDd1Ghc
      let
        comp = do
          renamed <- getRefactRenamed
          let Just (GHC.L _ n) = locToName (17, 5) renamed
          topLevel <- isTopLevelPN n
          return (n,topLevel)
      ((nf,tl),_s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      (showGhc nf) `shouldBe` "ff"
      tl `shouldBe` False

    it "returns True if the name is defined at the top level of the module" $ do
      (t, toks) <- parsedFileDd1Ghc
      let
        comp = do
          renamed <- getRefactRenamed
          let Just (GHC.L _ n) = locToName (21, 1) renamed
          topLevel <- isTopLevelPN n
          return (n,topLevel)

      ((nf,tl),_s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      (showGhc nf) `shouldBe` "DupDef.Dd1.ff"
      tl `shouldBe` True

  -- ---------------------------------------------

  describe "definedPNs" $ do
    it "gets the PNs defined in a declaration" $ do
      (t, _toks) <- parsedFileDd1Ghc
      let renamed = fromJust $ GHC.tm_renamed_source t

      let Just (GHC.L _ pn) = locToName (3, 1) renamed
      (showGhc pn) `shouldBe` "DupDef.Dd1.toplevel"

      let origDecls = hsBinds renamed
      let demotedDecls'= definingDeclsNames [pn] origDecls True False
      let declaredPns = nub $ concatMap definedPNs demotedDecls'

      (showGhc declaredPns) `shouldBe` "[DupDef.Dd1.toplevel]"

    -- ---------------------------------

    it "gets the PNs defined in an as-match" $ do
      (t, _toks) <- parsedFileDd1Ghc
      let renamed = fromJust $ GHC.tm_renamed_source t

      let Just (GHC.L _ pn) = locToName (14, 1) renamed
      (showGhc pn) `shouldBe` "DupDef.Dd1.tup"

      let origDecls = hsBinds renamed
      let demotedDecls'= definingDeclsNames [pn] origDecls True False
      let declaredPns = nub $ concatMap definedPNs demotedDecls'

      (showGhc declaredPns) `shouldBe` "[DupDef.Dd1.tup, DupDef.Dd1.h, DupDef.Dd1.t]"


  -- ---------------------------------------------

  describe "inScopeInfo" $ do
    it "returns 4 element tuples for in scope names" $ do
      pending -- "is this still needed?"
      {-
      ((inscopes, _renamed, _parsed), _toks) <- parsedFileDd1Ghc
      let info = inScopeInfo inscopes
      (show $ head info) `shouldBe` "foo"
      -- (show $ info) `shouldBe` "foo"
      -}

  -- ---------------------------------------------

  describe "isInScopeAndUnqualified" $ do
    it "True if the identifier is in scope and unqualified" $ do
      pending -- "needed?"
      {-
      ((inscopes, _renamed, _parsed), _toks) <- parsedFileDd1Ghc
      let info = inScopeInfo inscopes
      (show $ head info) `shouldBe` "foo"
      -}
-- inScopeInfo for c is
-- (\"DupDef.Dd1.c\",VarName,DupDef.Dd1,Nothing)

  -- ---------------------------------------------

  describe "isInScopeAndUnqualifiedGhc" $ do
    it "True if the identifier is in scope and unqualified" $ do
      let
        comp = do
         (_p,_toks) <- parseSourceFileTest "./test/testdata/DupDef/Dd1.hs"
         ctx <- GHC.getContext
         res1 <- isInScopeAndUnqualifiedGhc "c" Nothing
         res2 <- isInScopeAndUnqualifiedGhc "DupDef.Dd1.c" Nothing
         res3 <- isInScopeAndUnqualifiedGhc "nonexistent" Nothing
         return (res1,res2,res3,ctx)
      ((r1,r2,r3,_c),_s) <- runRefactGhcState comp
      -- (showGhc c) `shouldBe` "[*DupDef.Dd1]"
      r1 `shouldBe` True
      r2 `shouldBe` True
      r3 `shouldBe` False

    it "Requires qualification on name clash with an import" $ do
      let
        comp = do
         (t,toks) <- parseSourceFileTest  "./test/testdata/ScopeAndQual.hs"
         putParsedModule t toks
         renamed <- getRefactRenamed

         logm $ "renamed=" ++ (SYB.showData SYB.Renamer 0 renamed) -- ++AZ++

         ctx <- GHC.getContext

         let Just sumSquares = locToName (13,15) renamed
         ssUnqual <- isQualifiedPN $ GHC.unLoc sumSquares
         names <- GHC.parseName "sum"
         names2 <- GHC.parseName "mySumSq"
         res1 <- isInScopeAndUnqualifiedGhc "sum" Nothing
         res2 <- isInScopeAndUnqualifiedGhc "L.sum" Nothing
         return (res1,res2,names,names2,sumSquares,ssUnqual,ctx)
      -- ((r1,r2,ns,ns2,ss,ssu,c),_s) <- runRefactGhcStateLog comp True
      ((r1,r2,ns,ns2,ss,ssu,_c),_s) <- runRefactGhcState comp

      -- (showGhc c) `shouldBe` "[*ScopeAndQual]"
      (prettyprint ss) `shouldBe` "sumSquares"
      (showGhc ss) `shouldBe` "ScopeAndQual.sumSquares"
      (show $ ssu) `shouldBe` "False"
      (showGhc ns) `shouldBe` "[ScopeAndQual.sum]"
      (showGhc ns2) `shouldBe` "[ScopeAndQual.mySumSq]"
      "1" ++ (show r1) `shouldBe` "1True"
      "2" ++ (show r2) `shouldBe` "2True"

  -- ---------------------------------------------

  describe "mkNewGhcName" $ do
    it "Creates a new GHC.Name" $ do
      let modu = GHC.mkModule (GHC.stringToPackageId "mypackage-1.0") (GHC.mkModuleName "F1")
      let
        comp = do
         name1 <- mkNewGhcName Nothing "foo"
         name2 <- mkNewGhcName Nothing "bar"
         name3 <- mkNewGhcName (Just modu) "baz"
         return (name1,name2,name3)
      ((n1,n2,n3),_s) <- runRefactGhcState comp
      GHC.getOccString n1 `shouldBe` "foo"
      showGhc n1 `shouldBe` "foo"
      GHC.getOccString n2 `shouldBe` "bar"
      showGhc n2 `shouldBe` "bar"
      (showGhc $ GHC.nameModule n3) `shouldBe` "mypackage-1.0:F1"
      (SYB.showData SYB.Renamer 0 n3) `shouldBe` "{Name: F1.baz}"
      GHC.getOccString n3 `shouldBe` "baz"
      showGhc n3 `shouldBe` "F1.baz"
      (showGhc $ GHC.nameUnique n1) `shouldBe` "H2"
      (showGhc $ GHC.nameUnique n2) `shouldBe` "H3"
      (showGhc $ GHC.nameUnique n3) `shouldBe` "H4"

  -- ---------------------------------------------

  describe "newNameTok" $ do
    it "Creates a new token from a GHC.Name" $ do
      (_t, toks) <-parsedFileDd1Ghc
      let modu = GHC.mkModule (GHC.stringToPackageId "mypackage-1.0") (GHC.mkModuleName "F1")
      let
        comp = do
         name1 <- mkNewGhcName Nothing "foo"
         name2 <- mkNewGhcName (Just modu) "baz"
         return (name1,name2)
      ((n1,n2),_s) <- runRefactGhcState comp
      let sspan = posToSrcSpanTok (head toks) ((10,1),(10,15))
      (show $ newNameTok False sspan n1) `shouldBe` "((((10,1),(10,4)),ITvarid \"foo\"),\"foo\")"
      (show $ newNameTok True sspan n1) `shouldBe` "((((10,1),(10,4)),ITvarid \"foo\"),\"foo\")"

      (show $ newNameTok False sspan n2) `shouldBe` "((((10,1),(10,4)),ITvarid \"baz\"),\"baz\")"
      (show $ newNameTok True sspan n2) `shouldBe` "((((10,1),(10,7)),ITvarid \"F1.baz\"),\"F1.baz\")"

  -- ---------------------------------------------

  describe "prettyprint" $ do
    it "Prints a GHC.Name ready for parsing into tokens" $ do
      let
        comp = do
         name1 <- mkNewGhcName Nothing "foo"
         name2 <- mkNewGhcName Nothing "bar"
         return (name1,name2)
      ((n1,n2),_s) <- runRefactGhcState comp
      GHC.getOccString n1 `shouldBe` "foo"
      showGhc n1 `shouldBe` "foo"
      GHC.getOccString n2 `shouldBe` "bar"
      showGhc n2 `shouldBe` "bar"
      -- prettyprint n1 `shouldBe` "foo"
      showGhc n1 `shouldBe` "foo"

  -- ---------------------------------------------

  describe "duplicateDecl" $ do
    it "duplicates a RenamedSource bind, and updates the token stream" $ do
      (t, toks) <- parsedFileGhc "./test/testdata/DupDef/Dd1.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t

      let declsr = hsBinds renamed
      let Just (GHC.L _ n) = locToName (3, 1) renamed
      let
        comp = do
         _newName <- mkNewGhcName Nothing "bar"
         newName2 <- mkNewGhcName Nothing "bar2"
         newBinding <- duplicateDecl declsr renamed n newName2

         return newBinding
      (nb,s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- (nb,s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }
      (showGhc n) `shouldBe` "DupDef.Dd1.toplevel"
      (GHC.showRichTokenStream $ toks) `shouldBe` "module DupDef.Dd1 where\n\n toplevel :: Integer -> Integer\n toplevel x = c * x\n\n c,d :: Integer\n c = 7\n d = 9\n\n -- Pattern bind\n tup :: (Int, Int)\n h :: Int\n t :: Int\n tup@(h,t) = head $ zip [1..10] [3..ff]\n   where\n     ff :: Int\n     ff = 15\n\n data D = A | B String | C\n\n ff y = y + zz\n   where\n     zz = 1\n\n l z =\n   let\n     ll = 34\n   in ll + z\n\n dd q = do\n   let ss = 5\n   return (ss + q)\n\n "
      -- (show $ toksFromState s) `shouldBe` ""
      (renderLines $ linesFromState s) `shouldBe` "module DupDef.Dd1 where\n\ntoplevel :: Integer -> Integer\ntoplevel x = c * x\n\nbar2 :: Integer -> Integer\nbar2 x = c * x\n\nc,d :: Integer\nc = 7\nd = 9\n\n-- Pattern bind\ntup :: (Int, Int)\nh :: Int\nt :: Int\ntup@(h,t) = head $ zip [1..10] [3..ff]\n  where\n    ff :: Int\n    ff = 15\n\ndata D = A | B String | C\n\nff y = y + zz\n  where\n    zz = 1\n\nl z =\n  let\n    ll = 34\n  in ll + z\n\ndd q = do\n  let ss = 5\n  return (ss + q)\n\n"
      (showGhc nb) `shouldBe` "[bar2 x = DupDef.Dd1.c GHC.Num.* x]"

  -- ---------------------------------------------

    it "duplicates a bind with a signature, and an offset" $ do
      (t, toks) <- parsedFileDd1Ghc
      let renamed = fromJust $ GHC.tm_renamed_source t

      let declsr = hsBinds renamed
      let Just (GHC.L _l n) = locToName (17, 6) renamed
      (showGhc n) `shouldBe` "ff"
      let
        comp = do
         newName2 <- mkNewGhcName Nothing "gg"

         let
           declsToDup = definingDeclsNames [n] declsr True True
           funBinding = filter isFunOrPatBindR declsToDup     --get the fun binding.

         newBinding <- duplicateDecl declsToDup renamed n newName2

         -- return newBinding
         return (funBinding,declsToDup,newBinding)
      ((fb,dd,newb),s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- ((fb,dd,newb),s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }

      (showGhc n) `shouldBe` "ff"
      (showGhc dd) `shouldBe` "[ff = 15]"
      (showGhc fb) `shouldBe` "[ff = 15]"
      (show $ getStartEndLoc fb) `shouldBe` "((17,5),(17,12))"
      (GHC.showRichTokenStream $ toks) `shouldBe` "module DupDef.Dd1 where\n\n toplevel :: Integer -> Integer\n toplevel x = c * x\n\n c,d :: Integer\n c = 7\n d = 9\n\n -- Pattern bind\n tup :: (Int, Int)\n h :: Int\n t :: Int\n tup@(h,t) = head $ zip [1..10] [3..ff]\n   where\n     ff :: Int\n     ff = 15\n\n data D = A | B String | C\n\n ff y = y + zz\n   where\n     zz = 1\n\n l z =\n   let\n     ll = 34\n   in ll + z\n\n dd q = do\n   let ss = 5\n   return (ss + q)\n\n "
      (renderLines $ linesFromState s) `shouldBe` "module DupDef.Dd1 where\n\ntoplevel :: Integer -> Integer\ntoplevel x = c * x\n\nc,d :: Integer\nc = 7\nd = 9\n\n-- Pattern bind\ntup :: (Int, Int)\nh :: Int\nt :: Int\ntup@(h,t) = head $ zip [1..10] [3..ff]\n  where\n    ff :: Int\n    ff = 15\n\n    gg :: Int\n    gg = 15\n\ndata D = A | B String | C\n\nff y = y + zz\n  where\n    zz = 1\n\nl z =\n  let\n    ll = 34\n  in ll + z\n\ndd q = do\n  let ss = 5\n  return (ss + q)\n\n"
      (showGhc newb) `shouldBe` "[gg = 15]"
      (showGhc fb) `shouldBe` "[ff = 15]"


  -- ---------------------------------------------

  describe "addParamsToDecl" $ do
    it "adds parameters to a declaration, and updates the token stream" $ do
      (t, toks) <- parsedFileGhc "./test/testdata/MoveDef/Md1.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t

      let declsr = hsBinds renamed
      let Just (GHC.L _ n) = locToName (3, 1) renamed
      let
        comp = do
         _newName <- mkNewGhcName Nothing "bar"
         newName2 <- mkNewGhcName Nothing "bar2"
         newBinding <- addParamsToDecls declsr n [newName2] True

         return newBinding
      (nb,s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- (nb,s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }
      (showGhc n) `shouldBe` "MoveDef.Md1.toplevel"
      (GHC.showRichTokenStream $ toks) `shouldBe` "module MoveDef.Md1 where\n\n toplevel :: Integer -> Integer\n toplevel x = c * x\n\n c,d :: Integer\n c = 7\n d = 9\n\n -- Pattern bind\n tup :: (Int, Int)\n h :: Int\n t :: Int\n tup@(h,t) = head $ zip [1..10] [3..ff]\n   where\n     ff :: Int\n     ff = 15\n\n data D = A | B String | C\n\n ff :: Int -> Int\n ff y = y + zz\n   where\n     zz = 1\n\n l z =\n   let\n     ll = 34\n   in ll + z\n\n dd q = do\n   let ss = 5\n   return (ss + q)\n\n zz1 a = 1 + toplevel a\n\n -- General Comment\n -- |haddock comment\n tlFunc :: Integer -> Integer\n tlFunc x = c * x\n -- Comment at end\n\n\n "
      -- (showToks $ take 20 $ toksFromState s) `shouldBe` ""
      (renderLines $ linesFromState s) `shouldBe` "module MoveDef.Md1 where\n\ntoplevel :: Integer -> Integer\ntoplevel bar2 x= c * x\n\nc,d :: Integer\nc = 7\nd = 9\n\n-- Pattern bind\ntup :: (Int, Int)\nh :: Int\nt :: Int\ntup@(h,t) = head $ zip [1..10] [3..ff]\n  where\n    ff :: Int\n    ff = 15\n\ndata D = A | B String | C\n\nff :: Int -> Int\nff y = y + zz\n  where\n    zz = 1\n\nl z =\n  let\n    ll = 34\n  in ll + z\n\ndd q = do\n  let ss = 5\n  return (ss + q)\n\nzz1 a = 1 + toplevel a\n\n-- General Comment\n-- |haddock comment\ntlFunc :: Integer -> Integer\ntlFunc x = c * x\n-- Comment at end\n\n\n"
      (showGhc $ last $ init nb) `shouldBe` "MoveDef.Md1.toplevel bar2 x = MoveDef.Md1.c GHC.Num.* x"

    -- ---------------------------------

    it "adds parameters to a declaration with multiple matches" $ do
      (t, toks) <- parsedFileGhc "./test/testdata/AddParams1.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t

      let declsr = hsBinds renamed
      let Just (GHC.L _ n) = locToName (3, 1) renamed
      let
        comp = do
         newName <- mkNewGhcName Nothing "pow"
         newBinding <- addParamsToDecls declsr n [newName] True

         return newBinding
      (_nb,s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- (_nb,s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }
      (showGhc n) `shouldBe` "AddParams1.sq"
      (GHC.showRichTokenStream $ toks) `shouldBe` "module AddParams1 where\n\n sq  0 = 0\n sq  z = z^2\n\n foo = 3\n\n "
      -- (showToks $ take 20 $ toksFromState s) `shouldBe` ""
      (renderLines $ linesFromState s) `shouldBe` "module AddParams1 where\n\nsq  pow 0= 0\nsq  pow z= z^2\n\nfoo = 3\n\n"
      -- (showGhc $ last $ init nb) `shouldBe` ""

    -- ---------------------------------

    it "adds parameters to a declaration with no existing ones" $ do
      (t, toks) <- parsedFileAddParams1
      let renamed = fromJust $ GHC.tm_renamed_source t
      -- (SYB.showData SYB.Renamer 0 renamed) `shouldBe` ""

      let declsr = hsBinds renamed
      let Just (GHC.L _ n) = locToName (6, 1) renamed
      let
        comp = do
         newName1 <- mkNewGhcName Nothing "baz"
         newName2 <- mkNewGhcName Nothing "bar"
         newBinding <- addParamsToDecls declsr n [newName1,newName2] True

         return newBinding
      (_nb,s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- (nb,s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }
      (showGhc n) `shouldBe` "AddParams1.foo"
      (GHC.showRichTokenStream $ toks) `shouldBe` "module AddParams1 where\n\n sq  0 = 0\n sq  z = z^2\n\n foo = 3\n\n "
      -- (showToks $ take 20 $ toksFromState s) `shouldBe` ""
      (renderLines $ linesFromState s) `shouldBe` "module AddParams1 where\n\nsq  0 = 0\nsq  z = z^2\n\nfoo baz bar= 3\n\n"
      -- (showGhc $ last $ init nb) `shouldBe` ""

  -- ---------------------------------------------

  describe "addActualParamsToRhs" $ do
    it "adds a parameter to the rhs of a declaration, and updates the token stream" $ do
      (t, toks) <- parsedFileLiftD1Ghc
      let renamed = fromJust $ GHC.tm_renamed_source t

      let declsr = hsBinds renamed
      -- let decl@(GHC.L _ (GHC.FunBind _ _ (GHC.MatchGroup [GHC.L _ (GHC.Match _ _ rhs) ] _) _ _ _)) = head declsr
      let decl = head declsr
      (showGhc decl) `shouldBe` "LiftToToplevel.D1.sumSquares (x : xs)\n  = sq x GHC.Num.+ LiftToToplevel.D1.sumSquares xs\n  where\n      sq x = x GHC.Real.^ pow\n      pow = 2\nLiftToToplevel.D1.sumSquares [] = 0"
      -- (SYB.showData SYB.Renamer 0 rhs) `shouldBe` ""
      let Just (GHC.L _ n) = locToName (6, 21) renamed
      let
        comp = do
         _newName <- mkNewGhcName Nothing "bar"
         newName2 <- mkNewGhcName Nothing "bar2"
         newBinding <- addActualParamsToRhs True n [newName2] decl

         return newBinding
      (nb,s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- (nb,s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }
      (showGhc n) `shouldBe` "sq"
      -- (showToks $ take 20 $ toksFromState s) `shouldBe` ""
      (showGhc nb) `shouldBe` "LiftToToplevel.D1.sumSquares (x : xs)\n  = (sq bar2) x GHC.Num.+ LiftToToplevel.D1.sumSquares xs\n  where\n      sq x = x GHC.Real.^ pow\n      pow = 2\nLiftToToplevel.D1.sumSquares [] = 0"

      (renderLines $ linesFromState s) `shouldBe` "module LiftToToplevel.D1 where\n\n{-lift 'sq' to top level. This refactoring\n  affects module 'D1' and 'C1' -}\n\nsumSquares (x:xs) = (sq bar2)x + sumSquares xs\n  where\n     sq x = x ^ pow\n     pow =2\n\nsumSquares [] = 0\n\nmain = sumSquares [1..4]\n\n\n"

    -- --------------------

    it "adds parameters to a complex rhs of a declaration, and updates the token stream" $ do
      (t, toks) <- parsedFileLiftWhereIn7Ghc
      let renamed = fromJust $ GHC.tm_renamed_source t

      let declsr = hsBinds renamed
      -- let decl@(GHC.L _ (GHC.FunBind _ _ (GHC.MatchGroup [GHC.L _ (GHC.Match _ _ rhs) ] _) _ _ _)) = head declsr
      let decl = head declsr
      (showGhc decl) `shouldBe` "LiftToToplevel.WhereIn7.fun x y z\n  = inc addthree\n  where\n      inc a = a GHC.Num.+ 1\n      addthree = x GHC.Num.+ y GHC.Num.+ z"
      -- (SYB.showData SYB.Renamer 0 rhs) `shouldBe` ""
      let Just (GHC.L _ n) = locToName (10, 17) renamed
      let
        comp = do
         newName1 <- mkNewGhcName Nothing "x1"
         newName2 <- mkNewGhcName Nothing "y1"
         newName3 <- mkNewGhcName Nothing "z1"
         newBinding <- addActualParamsToRhs True n [newName1,newName2,newName3] decl

         return newBinding
      (nb,s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- (nb,s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }
      (showGhc n) `shouldBe` "addthree"
      -- (showToks $ take 20 $ toksFromState s) `shouldBe` ""
      (renderLines $ linesFromState s) `shouldBe` "module LiftToToplevel.WhereIn7 where\n\n--A definition can be lifted from a where or let to the top level binding group.\n--Lifting a definition widens the scope of the definition.\n\n--In this example, lift 'addthree' defined in 'fun'.\n--This example aims to test adding parenthese.\n\n\nfun x y z =inc (addthree x1 y1 z1)\n       where inc a =a +1\n             addthree=x+y+z\n"
      (showGhc nb) `shouldBe` "LiftToToplevel.WhereIn7.fun x y z\n  = inc (addthree x1 y1 z1)\n  where\n      inc a = a GHC.Num.+ 1\n      addthree = x GHC.Num.+ y GHC.Num.+ z"


  -- ---------------------------------------------

  describe "rmDecl" $ do
    it "removes a top level declaration, leaving type signature" $ do
      (t, toks) <- parsedFileMd1Ghc
      let renamed = fromJust $ GHC.tm_renamed_source t

      let declsr = hsBinds renamed
      let Just (GHC.L _ n) = locToName (22, 1) renamed
      let
        comp = do
         (newDecls,_removedDecl,_removedSig) <- rmDecl n False declsr

         return newDecls
      (nb,s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- (nb,s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }
      (showGhc n) `shouldBe` "MoveDef.Md1.ff"
      (GHC.showRichTokenStream $ toks) `shouldBe` "module MoveDef.Md1 where\n\n toplevel :: Integer -> Integer\n toplevel x = c * x\n\n c,d :: Integer\n c = 7\n d = 9\n\n -- Pattern bind\n tup :: (Int, Int)\n h :: Int\n t :: Int\n tup@(h,t) = head $ zip [1..10] [3..ff]\n   where\n     ff :: Int\n     ff = 15\n\n data D = A | B String | C\n\n ff :: Int -> Int\n ff y = y + zz\n   where\n     zz = 1\n\n l z =\n   let\n     ll = 34\n   in ll + z\n\n dd q = do\n   let ss = 5\n   return (ss + q)\n\n zz1 a = 1 + toplevel a\n\n -- General Comment\n -- |haddock comment\n tlFunc :: Integer -> Integer\n tlFunc x = c * x\n -- Comment at end\n\n\n "
      -- (drawTreeCompact ((tkCache $ rsTokenCache $ fromJust $ rsModule s) Map.! mainTid)) `shouldBe` ""
      -- (drawTreeCompact $ adjustLinesForDeleted ((tkCache $ rsTokenCache $ fromJust $ rsModule s) Map.! mainTid)) `shouldBe` ""
      -- (showGhc $ retrieveTokensPpr ((tkCache $ rsTokenCache $ fromJust $ rsModule s) Map.! mainTid)) `shouldBe` ""
      -- (renderPpr $ retrieveTokensPpr $ adjustLinesForDeleted ((tkCache $ rsTokenCache $ fromJust $ rsModule s) Map.! mainTid)) `shouldBe` ""
      -- (showGhc $ pprFromState s) `shouldBe` ""
      (renderLines $ linesFromState s) `shouldBe` "module MoveDef.Md1 where\n\ntoplevel :: Integer -> Integer\ntoplevel x = c * x\n\nc,d :: Integer\nc = 7\nd = 9\n\n-- Pattern bind\ntup :: (Int, Int)\nh :: Int\nt :: Int\ntup@(h,t) = head $ zip [1..10] [3..ff]\n  where\n    ff :: Int\n    ff = 15\n\ndata D = A | B String | C\n\nff :: Int -> Int\n\nl z =\n  let\n    ll = 34\n  in ll + z\n\ndd q = do\n  let ss = 5\n  return (ss + q)\n\nzz1 a = 1 + toplevel a\n\n-- General Comment\n-- |haddock comment\ntlFunc :: Integer -> Integer\ntlFunc x = c * x\n-- Comment at end\n\n\n"
      (showGhc nb) `shouldBe` "[MoveDef.Md1.dd q\n   = do { let ss = 5;\n          GHC.Base.return (ss GHC.Num.+ q) },\n MoveDef.Md1.l z = let ll = 34 in ll GHC.Num.+ z,\n MoveDef.Md1.tup@(MoveDef.Md1.h, MoveDef.Md1.t)\n   = GHC.List.head GHC.Base.$ GHC.List.zip [1 .. 10] [3 .. ff]\n   where\n       ff :: GHC.Types.Int\n       ff = 15,\n MoveDef.Md1.d = 9, MoveDef.Md1.c = 7,\n MoveDef.Md1.tlFunc x = MoveDef.Md1.c GHC.Num.* x,\n MoveDef.Md1.toplevel x = MoveDef.Md1.c GHC.Num.* x,\n MoveDef.Md1.zz1 a = 1 GHC.Num.+ MoveDef.Md1.toplevel a]"

    -- ---------------------------------

    it "removes a top level declaration, and type signature" $ do
      (t, toks) <- parsedFileGhc "./test/testdata/MoveDef/Md1.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t

      -- let declsr = hsBinds renamed
      let Just (GHC.L _ n) = locToName (22, 1) renamed
      let
        comp = do
         (newDecls,_removedDecl,_removedSig) <- rmDecl n True renamed
         return newDecls
      (nb,s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- (nb,s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }
      (showGhc n) `shouldBe` "MoveDef.Md1.ff"
      (GHC.showRichTokenStream $ toks) `shouldBe` "module MoveDef.Md1 where\n\n toplevel :: Integer -> Integer\n toplevel x = c * x\n\n c,d :: Integer\n c = 7\n d = 9\n\n -- Pattern bind\n tup :: (Int, Int)\n h :: Int\n t :: Int\n tup@(h,t) = head $ zip [1..10] [3..ff]\n   where\n     ff :: Int\n     ff = 15\n\n data D = A | B String | C\n\n ff :: Int -> Int\n ff y = y + zz\n   where\n     zz = 1\n\n l z =\n   let\n     ll = 34\n   in ll + z\n\n dd q = do\n   let ss = 5\n   return (ss + q)\n\n zz1 a = 1 + toplevel a\n\n -- General Comment\n -- |haddock comment\n tlFunc :: Integer -> Integer\n tlFunc x = c * x\n -- Comment at end\n\n\n "
      -- (showToks $ take 20 $ toksFromState s) `shouldBe` ""
      -- (show $ entriesFromState s) `shouldBe` "[]"
      (renderLines $ linesFromState s) `shouldBe` "module MoveDef.Md1 where\n\ntoplevel :: Integer -> Integer\ntoplevel x = c * x\n\nc,d :: Integer\nc = 7\nd = 9\n\n-- Pattern bind\ntup :: (Int, Int)\nh :: Int\nt :: Int\ntup@(h,t) = head $ zip [1..10] [3..ff]\n  where\n    ff :: Int\n    ff = 15\n\ndata D = A | B String | C\n\nl z =\n  let\n    ll = 34\n  in ll + z\n\ndd q = do\n  let ss = 5\n  return (ss + q)\n\nzz1 a = 1 + toplevel a\n\n-- General Comment\n-- |haddock comment\ntlFunc :: Integer -> Integer\ntlFunc x = c * x\n-- Comment at end\n\n\n"
      (unspace $ showGhc nb) `shouldBe` "(MoveDef.Md1.toplevel ::\n GHC.Integer.Type.Integer -> GHC.Integer.Type.Integer\n MoveDef.Md1.toplevel x = MoveDef.Md1.c GHC.Num.* x\n MoveDef.Md1.c, MoveDef.Md1.d :: GHC.Integer.Type.Integer\n MoveDef.Md1.c = 7\n MoveDef.Md1.d = 9\n MoveDef.Md1.tup :: (GHC.Types.Int, GHC.Types.Int)\n MoveDef.Md1.h :: GHC.Types.Int\n MoveDef.Md1.t :: GHC.Types.Int\n MoveDef.Md1.tup@(MoveDef.Md1.h, MoveDef.Md1.t)\n = GHC.List.head GHC.Base.$ GHC.List.zip [1 .. 10] [3 .. ff]\n where\n ff :: GHC.Types.Int\n ff = 15\n MoveDef.Md1.l z = let ll = 34 in ll GHC.Num.+ z\n MoveDef.Md1.dd q\n = do { let ss = 5;\n GHC.Base.return (ss GHC.Num.+ q) }\n MoveDef.Md1.zz1 a = 1 GHC.Num.+ MoveDef.Md1.toplevel a\n MoveDef.Md1.tlFunc ::\n GHC.Integer.Type.Integer -> GHC.Integer.Type.Integer\n MoveDef.Md1.tlFunc x = MoveDef.Md1.c GHC.Num.* x\n \n data MoveDef.Md1.D\n = MoveDef.Md1.A | MoveDef.Md1.B GHC.Base.String | MoveDef.Md1.C,\n [import (implicit) Prelude],\n Nothing,\n Nothing)"

    -- -----------------------------------

    it "removes the last local decl in a let/in clause" $ do
      (t, toks) <- parsedFileGhc "./test/testdata/LiftToToplevel/LetIn1.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t
      -- (SYB.showData SYB.Renamer 0 renamed) `shouldBe` ""

      let declsr = hsBinds renamed
      let Just (GHC.L _ n) = locToName (11, 22) renamed
      let
        comp = do
         (newDecls,_removedDecl,_removedSig) <- rmDecl n True declsr

         return newDecls
      (nb,s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- (nb,s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }
      (showGhc n) `shouldBe` "sq"
      (GHC.showRichTokenStream $ toks) `shouldBe` "module LiftToToplevel.LetIn1 where\n\n --A definition can be lifted from a where or let to the top level binding group.\n --Lifting a definition widens the scope of the definition.\n\n --In this example, lift 'sq' in 'sumSquares'\n --This example aims to test lifting a definition from a let clause to top level,\n --and the elimination of the keywords 'let' and 'in'\n\n sumSquares x y = let sq 0=0\n                      sq z=z^pow\n                   in sq x + sq y\n                        where pow=2\n\n anotherFun 0 y = sq y\n      where sq x = x^2\n "
      -- (showToks $ take 20 $ toksFromState s) `shouldBe` ""
      (renderLines $ linesFromState s) `shouldBe` "module LiftToToplevel.LetIn1 where\n\n--A definition can be lifted from a where or let to the top level binding group.\n--Lifting a definition widens the scope of the definition.\n\n--In this example, lift 'sq' in 'sumSquares'\n--This example aims to test lifting a definition from a let clause to top level,\n--and the elimination of the keywords 'let' and 'in'\n\nsumSquares x y = sq x + sq y\n\n\n                       where pow=2\n\nanotherFun 0 y = sq y\n     where sq x = x^2\n"
      (showGhc nb) `shouldBe` "[LiftToToplevel.LetIn1.anotherFun 0 y\n   = sq y\n   where\n       sq x = x GHC.Real.^ 2,\n LiftToToplevel.LetIn1.sumSquares x y\n   = sq x GHC.Num.+ sq y\n   where\n       pow = 2]"

    -- -----------------------------------

    it "removes the non last local decl in a let/in clause" $ do
      (t, toks) <- parsedFileGhc "./test/testdata/Demote/LetIn1.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t
      -- (SYB.showData SYB.Renamer 0 renamed) `shouldBe` ""

      let declsr = hsBinds renamed
      let Just (GHC.L _ n) = locToName (12, 22) renamed
      let
        comp = do
         (newDecls,_removedDecl,_removedSig) <- rmDecl n False declsr

         return newDecls
      (nb,s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- (nb,s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }
      (showGhc n) `shouldBe` "pow"
      (GHC.showRichTokenStream $ toks) `shouldBe` "module Demote.LetIn1 where\n\n --A definition can be demoted to the local 'where' binding of a friend declaration,\n --if it is only used by this friend declaration.\n\n --Demoting a definition narrows down the scope of the definition.\n --In this example, demote the local  'pow' to 'sq'\n --This example also aims to test the demoting a local declaration in 'let'.\n\n sumSquares x y = let sq 0=0\n                      sq z=z^pow\n                      pow=2\n                  in sq x + sq y\n\n\n anotherFun 0 y = sq y\n      where  sq x = x^2\n\n   "
      -- (showToks $ take 20 $ toksFromState s) `shouldBe` ""
      (renderLines $ linesFromState s) `shouldBe` "module Demote.LetIn1 where\n\n--A definition can be demoted to the local 'where' binding of a friend declaration,\n--if it is only used by this friend declaration.\n\n--Demoting a definition narrows down the scope of the definition.\n--In this example, demote the local  'pow' to 'sq'\n--This example also aims to test the demoting a local declaration in 'let'.\n\nsumSquares x y = let sq 0=0\n                     sq z=z^pow\n                 in sq x + sq y\n\n\nanotherFun 0 y = sq y\n     where  sq x = x^2\n\n  "
      (showGhc nb) `shouldBe` "[Demote.LetIn1.anotherFun 0 y\n   = sq y\n   where\n       sq x = x GHC.Real.^ 2,\n Demote.LetIn1.sumSquares x y\n   = let\n       sq 0 = 0\n       sq z = z GHC.Real.^ pow\n     in sq x GHC.Num.+ sq y]"

  -- ---------------------------------------------

  describe "rmTypeSig" $ do
    it "removes a type signature from the top level" $ do
      (t, toks) <- parsedFileMd1Ghc
      let renamed = fromJust $ GHC.tm_renamed_source t
      let Just (GHC.L _ n) = locToName (22, 1) renamed
      let
        comp = do
         (renamed',sigRemoved) <- rmTypeSig n renamed
         return (renamed',sigRemoved)
      ((nb,os),s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- ((nb,os),s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }
      (showGhc n) `shouldBe` "MoveDef.Md1.ff"
      (GHC.showRichTokenStream $ toks) `shouldBe` "module MoveDef.Md1 where\n\n toplevel :: Integer -> Integer\n toplevel x = c * x\n\n c,d :: Integer\n c = 7\n d = 9\n\n -- Pattern bind\n tup :: (Int, Int)\n h :: Int\n t :: Int\n tup@(h,t) = head $ zip [1..10] [3..ff]\n   where\n     ff :: Int\n     ff = 15\n\n data D = A | B String | C\n\n ff :: Int -> Int\n ff y = y + zz\n   where\n     zz = 1\n\n l z =\n   let\n     ll = 34\n   in ll + z\n\n dd q = do\n   let ss = 5\n   return (ss + q)\n\n zz1 a = 1 + toplevel a\n\n -- General Comment\n -- |haddock comment\n tlFunc :: Integer -> Integer\n tlFunc x = c * x\n -- Comment at end\n\n\n "
      -- (showToks $ take 20 $ toksFromState s) `shouldBe` ""
      (renderLines $ linesFromState s) `shouldBe` "module MoveDef.Md1 where\n\ntoplevel :: Integer -> Integer\ntoplevel x = c * x\n\nc,d :: Integer\nc = 7\nd = 9\n\n-- Pattern bind\ntup :: (Int, Int)\nh :: Int\nt :: Int\ntup@(h,t) = head $ zip [1..10] [3..ff]\n  where\n    ff :: Int\n    ff = 15\n\ndata D = A | B String | C\n\nff y = y + zz\n  where\n    zz = 1\n\nl z =\n  let\n    ll = 34\n  in ll + z\n\ndd q = do\n  let ss = 5\n  return (ss + q)\n\nzz1 a = 1 + toplevel a\n\n-- General Comment\n-- |haddock comment\ntlFunc :: Integer -> Integer\ntlFunc x = c * x\n-- Comment at end\n\n\n"
      (unspace $ showGhc nb) `shouldBe` "(MoveDef.Md1.toplevel ::\n GHC.Integer.Type.Integer -> GHC.Integer.Type.Integer\n MoveDef.Md1.toplevel x = MoveDef.Md1.c GHC.Num.* x\n MoveDef.Md1.c, MoveDef.Md1.d :: GHC.Integer.Type.Integer\n MoveDef.Md1.c = 7\n MoveDef.Md1.d = 9\n MoveDef.Md1.tup :: (GHC.Types.Int, GHC.Types.Int)\n MoveDef.Md1.h :: GHC.Types.Int\n MoveDef.Md1.t :: GHC.Types.Int\n MoveDef.Md1.tup@(MoveDef.Md1.h, MoveDef.Md1.t)\n = GHC.List.head GHC.Base.$ GHC.List.zip [1 .. 10] [3 .. ff]\n where\n ff :: GHC.Types.Int\n ff = 15\n MoveDef.Md1.ff y\n = y GHC.Num.+ zz\n where\n zz = 1\n MoveDef.Md1.l z = let ll = 34 in ll GHC.Num.+ z\n MoveDef.Md1.dd q\n = do { let ss = 5;\n GHC.Base.return (ss GHC.Num.+ q) }\n MoveDef.Md1.zz1 a = 1 GHC.Num.+ MoveDef.Md1.toplevel a\n MoveDef.Md1.tlFunc ::\n GHC.Integer.Type.Integer -> GHC.Integer.Type.Integer\n MoveDef.Md1.tlFunc x = MoveDef.Md1.c GHC.Num.* x\n \n data MoveDef.Md1.D\n = MoveDef.Md1.A | MoveDef.Md1.B GHC.Base.String | MoveDef.Md1.C,\n [import (implicit) Prelude],\n Nothing,\n Nothing)"
      (showGhc os) `shouldBe` "Just MoveDef.Md1.ff :: GHC.Types.Int -> GHC.Types.Int"

    -- -----------------------------------------------------------------

    it "removes a type signature from the top level, after decl removed" $ do
      (t, toks) <- parsedFileWhereIn3Ghc
      let renamed = fromJust $ GHC.tm_renamed_source t
      let Just (GHC.L _ n) = locToName (14, 1) renamed
      let
        comp = do
         (ds,_removedDecl,_removedSig1) <- rmDecl n True (hsBinds renamed)
         (renamed',_removedSig2) <- rmTypeSig n renamed
         drawTokenTree "after removing typesig"

         let renamed'' = (replaceBinds renamed' ds)
         return renamed''
      (nb,s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- (nb,s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }
      (showGhc n) `shouldBe` "Demote.WhereIn3.sq"
      (GHC.showRichTokenStream $ toks) `shouldBe` "module Demote.WhereIn3 where\n\n --A definition can be demoted to the local 'where' binding of a friend declaration,\n --if it is only used by this friend declaration.\n\n --Demoting a definition narrows down the scope of the definition.\n --In this example, demote the top level 'sq' to 'sumSquares'\n --In this case (there are multi matches), the parameters are not folded after demoting.\n\n sumSquares x y = sq p x + sq p y\n          where p=2  {-There is a comment-}\n\n sq :: Int -> Int -> Int\n sq pow 0 = 0\n sq pow z = z^pow  --there is a comment\n\n anotherFun 0 y = sq y\n      where  sq x = x^2\n\n "
      -- (showToks $ take 40 $ drop 15 $ toksFromState s) `shouldBe` ""
      -- (showGhc $ pprFromState s) `shouldBe` ""
      (renderLines $ linesFromState s) `shouldBe` "module Demote.WhereIn3 where\n\n--A definition can be demoted to the local 'where' binding of a friend declaration,\n--if it is only used by this friend declaration.\n\n--Demoting a definition narrows down the scope of the definition.\n--In this example, demote the top level 'sq' to 'sumSquares'\n--In this case (there are multi matches), the parameters are not folded after demoting.\n\nsumSquares x y = sq p x + sq p y\n         where p=2  {-There is a comment-}\n\nanotherFun 0 y = sq y\n     where  sq x = x^2\n\n"
      (showGhc nb) `shouldBe` "(Demote.WhereIn3.sumSquares x y\n   = Demote.WhereIn3.sq p x GHC.Num.+ Demote.WhereIn3.sq p y\n   where\n       p = 2\n Demote.WhereIn3.anotherFun 0 y\n   = sq y\n   where\n       sq x = x GHC.Real.^ 2,\n [import (implicit) Prelude],\n Nothing,\n Nothing)"
      -- (showGhc renamed) `shouldBe` ""


    -- -----------------------------------------------------------------

    it "removes a type signature from non-top level" $ do
      (t, toks) <- parsedFileGhc "./test/testdata/MoveDef/Md1.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t
      let Just (GHC.L _ n) = locToName (16, 5) renamed
      let
        comp = do
         (renamed',_removedSig) <- rmTypeSig n renamed
         return renamed'
      (nb,s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- (nb,s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }
      (showGhc n) `shouldBe` "ff"
      (GHC.showRichTokenStream $ toks) `shouldBe` "module MoveDef.Md1 where\n\n toplevel :: Integer -> Integer\n toplevel x = c * x\n\n c,d :: Integer\n c = 7\n d = 9\n\n -- Pattern bind\n tup :: (Int, Int)\n h :: Int\n t :: Int\n tup@(h,t) = head $ zip [1..10] [3..ff]\n   where\n     ff :: Int\n     ff = 15\n\n data D = A | B String | C\n\n ff :: Int -> Int\n ff y = y + zz\n   where\n     zz = 1\n\n l z =\n   let\n     ll = 34\n   in ll + z\n\n dd q = do\n   let ss = 5\n   return (ss + q)\n\n zz1 a = 1 + toplevel a\n\n -- General Comment\n -- |haddock comment\n tlFunc :: Integer -> Integer\n tlFunc x = c * x\n -- Comment at end\n\n\n "
      -- (showToks $ take 20 $ toksFromState s) `shouldBe` ""
      (renderLines $ linesFromState s) `shouldBe` "module MoveDef.Md1 where\n\ntoplevel :: Integer -> Integer\ntoplevel x = c * x\n\nc,d :: Integer\nc = 7\nd = 9\n\n-- Pattern bind\ntup :: (Int, Int)\nh :: Int\nt :: Int\ntup@(h,t) = head $ zip [1..10] [3..ff]\n  where\n    ff = 15\n\ndata D = A | B String | C\n\nff :: Int -> Int\nff y = y + zz\n  where\n    zz = 1\n\nl z =\n  let\n    ll = 34\n  in ll + z\n\ndd q = do\n  let ss = 5\n  return (ss + q)\n\nzz1 a = 1 + toplevel a\n\n-- General Comment\n-- |haddock comment\ntlFunc :: Integer -> Integer\ntlFunc x = c * x\n-- Comment at end\n\n\n"
      (unspace $ showGhc nb) `shouldBe` unspace "(MoveDef.Md1.toplevel ::\n   GHC.Integer.Type.Integer -> GHC.Integer.Type.Integer\n MoveDef.Md1.toplevel x = MoveDef.Md1.c GHC.Num.* x\n MoveDef.Md1.c, MoveDef.Md1.d :: GHC.Integer.Type.Integer\n MoveDef.Md1.c = 7\n MoveDef.Md1.d = 9\n MoveDef.Md1.tup :: (GHC.Types.Int, GHC.Types.Int)\n MoveDef.Md1.h :: GHC.Types.Int\n MoveDef.Md1.t :: GHC.Types.Int\n MoveDef.Md1.tup@(MoveDef.Md1.h, MoveDef.Md1.t)\n   = GHC.List.head GHC.Base.$ GHC.List.zip [1 .. 10] [3 .. ff]\n   where\n       ff = 15\n MoveDef.Md1.ff :: GHC.Types.Int -> GHC.Types.Int\n MoveDef.Md1.ff y\n   = y GHC.Num.+ zz\n   where\n       zz = 1\n MoveDef.Md1.l z = let ll = 34 in ll GHC.Num.+ z\n MoveDef.Md1.dd q\n   = do { let ss = 5;\n          GHC.Base.return (ss GHC.Num.+ q) }\n MoveDef.Md1.zz1 a = 1 GHC.Num.+ MoveDef.Md1.toplevel a\n MoveDef.Md1.tlFunc ::\n   GHC.Integer.Type.Integer -> GHC.Integer.Type.Integer\n MoveDef.Md1.tlFunc x = MoveDef.Md1.c GHC.Num.* x\n \n data MoveDef.Md1.D\n   = MoveDef.Md1.A | MoveDef.Md1.B GHC.Base.String | MoveDef.Md1.C,\n [import (implicit) Prelude],\n Nothing,\n Nothing)"
      -- (showGhc renamed) `shouldBe` ""

    -- -----------------------------------------------------------------

    it "removes a type signature within multi signatures 1" $ do
      (t, toks) <- parsedFileTypeSigs
      let renamed = fromJust $ GHC.tm_renamed_source t
      let Just (GHC.L _ b) = locToName (12, 1) renamed
      let
        comp = do
         (renamed',_removedSig) <- rmTypeSig b renamed
         return renamed'
      (nb,s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      (showGhc b) `shouldBe` "TypeSigs.b"
      (GHC.showRichTokenStream $ toks) `shouldBe` "module TypeSigs where\n\n sq,anotherFun :: Int -> Int\n sq 0 = 0\n sq z = z^2\n\n anotherFun x = x^2\n\n a,b,c::Int->Integer->Char\n\n a x y = undefined\n b x y = undefined\n c x y = undefined\n\n "
      -- (showToks $ take 20 $ toksFromState s) `shouldBe` ""
      (renderLines $ linesFromState s) `shouldBe` "module TypeSigs where\n\nsq,anotherFun :: Int -> Int\nsq 0 = 0\nsq z = z^2\n\nanotherFun x = x^2\n\na  ,c::Int->Integer->Char\n\na x y = undefined\nb x y = undefined\nc x y = undefined\n\n"
      (showGhc nb) `shouldBe` "(TypeSigs.sq, TypeSigs.anotherFun :: GHC.Types.Int -> GHC.Types.Int\n TypeSigs.sq 0 = 0\n TypeSigs.sq z = z GHC.Real.^ 2\n TypeSigs.anotherFun x = x GHC.Real.^ 2\n TypeSigs.a, TypeSigs.c ::\n   GHC.Types.Int -> GHC.Integer.Type.Integer -> GHC.Types.Char\n TypeSigs.a x y = GHC.Err.undefined\n TypeSigs.b x y = GHC.Err.undefined\n TypeSigs.c x y = GHC.Err.undefined,\n [import (implicit) Prelude],\n Nothing,\n Nothing)"
      -- (showGhc renamed) `shouldBe` ""

    -- -----------------------------------------------------------------

    it "removes a type signature within multi signatures 2" $ do
      (t, toks) <- parsedFileTypeSigs
      let renamed = fromJust $ GHC.tm_renamed_source t
      let Just (GHC.L _ n) = locToName (4, 1) renamed
      let
        comp = do
         (renamed',removedSig) <- rmTypeSig n renamed
         let (Just (GHC.L ss _)) = removedSig
         oldSigToks <- getToksForSpan ss
         return (renamed',removedSig,oldSigToks)
      ((nb,os,ot),s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      (showGhc n) `shouldBe` "TypeSigs.sq"
      (GHC.showRichTokenStream $ toks) `shouldBe` "module TypeSigs where\n\n sq,anotherFun :: Int -> Int\n sq 0 = 0\n sq z = z^2\n\n anotherFun x = x^2\n\n a,b,c::Int->Integer->Char\n\n a x y = undefined\n b x y = undefined\n c x y = undefined\n\n "
      -- (showToks $ take 20 $ toksFromState s) `shouldBe` ""
      (renderLines $ linesFromState s) `shouldBe` "module TypeSigs where\n\nanotherFun :: Int -> Int\nsq 0 = 0\nsq z = z^2\n\nanotherFun x = x^2\n\na,b,c::Int->Integer->Char\n\na x y = undefined\nb x y = undefined\nc x y = undefined\n\n"
      (showGhc nb) `shouldBe` "(TypeSigs.anotherFun :: GHC.Types.Int -> GHC.Types.Int\n TypeSigs.sq 0 = 0\n TypeSigs.sq z = z GHC.Real.^ 2\n TypeSigs.anotherFun x = x GHC.Real.^ 2\n TypeSigs.a, TypeSigs.c, TypeSigs.b ::\n   GHC.Types.Int -> GHC.Integer.Type.Integer -> GHC.Types.Char\n TypeSigs.a x y = GHC.Err.undefined\n TypeSigs.b x y = GHC.Err.undefined\n TypeSigs.c x y = GHC.Err.undefined,\n [import (implicit) Prelude],\n Nothing,\n Nothing)"
      (showGhc os) `shouldBe` "Just TypeSigs.sq :: GHC.Types.Int -> GHC.Types.Int"
      (GHC.showRichTokenStream ot) `shouldBe` "\n\n sq            :: Int -> Int"

    -- -----------------------------------------------------------------
{-
    it "removes a type signature for a pattern in a bind" $ do
      (t, toks) <- parsedFileGhc "./test/testdata/LiftToToplevel/PatBindIn1.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t
      let Just (GHC.L _ n) = locToName (GHC.mkFastString "./test/testdata/LiftToToplevel/PatBindIn1.hs") (18, 7) renamed
      let
        comp = do
         (renamed',removedSig) <- rmTypeSig n renamed
         let (Just (GHC.L ss _)) = removedSig
         oldSigToks <- getToksForSpan ss
         return (renamed',removedSig,oldSigToks)
      -- ((nb,os,ot),s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      ((nb,os,ot),s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks } 
      (showGhc n) `shouldBe` "tup"
      (GHC.showRichTokenStream $ toks) `shouldBe` "module LiftToToplevel.PatBindIn1 where\n\n --A definition can be lifted from a where or let into the surrounding binding group.\n --Lifting a definition widens the scope of the definition.\n\n --In this example, lift 'tup' defined in 'foo'\n --This example aims to test renaming and the lifting of type signatures.\n\n main :: Int\n main = foo 3\n\n foo :: Int -> Int\n foo x = h + t + (snd tup)\n       where\n       h :: Int\n       t :: Int\n       tup :: (Int,Int)\n       tup@(h,t) = head $ zip [1..10] [3..15]\n "
      -- (showToks $ take 20 $ toksFromState s) `shouldBe` ""
      (renderLines $ linesFromState s) `shouldBe` "module LiftToToplevel.PatBindIn1 where\n\n --A definition can be lifted from a where or let into the surrounding binding group.\n --Lifting a definition widens the scope of the definition.\n\n --In this example, lift 'tup' defined in 'foo'\n --This example aims to test renaming and the lifting of type signatures.\n\n main :: Int\n main = foo 3\n\n foo :: Int -> Int\n foo x = h + t + (snd tup)\n       where\n       \n       \n\n       tup@(h,t) = head $ zip [1..10] [3..15]\n "
      (showGhc nb) `shouldBe` ""
      (showGhc os) `shouldBe` ""
      (GHC.showRichTokenStream ot) `shouldBe` ""
-}
  -- ---------------------------------------------

  describe "addDecl" $ do
    it "adds a top level declaration without a type signature, in default pos" $ do
      (t, toks) <- parsedFileMd1Ghc
      let
        comp = do
         renamed <- getRefactRenamed
         nn  <- mkNewGhcName Nothing "nn"
         nn2 <- mkNewGhcName Nothing "nn2"
         let newDecl = GHC.noLoc (GHC.VarBind nn (GHC.noLoc (GHC.HsVar nn2)) False)
         newDecls <- addDecl renamed Nothing (newDecl,[],Nothing) True

         return newDecls
      (nb,s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- (nb,s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }
      -- (showGhc n) `shouldBe` "MoveDef.Md1.ff"
      (GHC.showRichTokenStream $ toks) `shouldBe` "module MoveDef.Md1 where\n\n toplevel :: Integer -> Integer\n toplevel x = c * x\n\n c,d :: Integer\n c = 7\n d = 9\n\n -- Pattern bind\n tup :: (Int, Int)\n h :: Int\n t :: Int\n tup@(h,t) = head $ zip [1..10] [3..ff]\n   where\n     ff :: Int\n     ff = 15\n\n data D = A | B String | C\n\n ff :: Int -> Int\n ff y = y + zz\n   where\n     zz = 1\n\n l z =\n   let\n     ll = 34\n   in ll + z\n\n dd q = do\n   let ss = 5\n   return (ss + q)\n\n zz1 a = 1 + toplevel a\n\n -- General Comment\n -- |haddock comment\n tlFunc :: Integer -> Integer\n tlFunc x = c * x\n -- Comment at end\n\n\n "
      -- (pprFromState s) `shouldBe` []
      (renderLines $ linesFromState s) `shouldBe` "module MoveDef.Md1 where\n\ntoplevel :: Integer -> Integer\ntoplevel x = c * x\n\nc,d :: Integer\nc = 7\nd = 9\n\n-- Pattern bind\ntup :: (Int, Int)\nh :: Int\nt :: Int\ntup@(h,t) = head $ zip [1..10] [3..ff]\n  where\n    ff :: Int\n    ff = 15\n\ndata D = A | B String | C\n\nff :: Int -> Int\nff y = y + zz\n  where\n    zz = 1\n\nl z =\n  let\n    ll = 34\n  in ll + z\n\ndd q = do\n  let ss = 5\n  return (ss + q)\n\nnn = nn2\n\nzz1 a = 1 + toplevel a\n\n-- General Comment\n-- |haddock comment\ntlFunc :: Integer -> Integer\ntlFunc x = c * x\n-- Comment at end\n\n\n"
      (unspace $ showGhc nb) `shouldBe` unspace "(MoveDef.Md1.toplevel ::\n   GHC.Integer.Type.Integer -> GHC.Integer.Type.Integer\n MoveDef.Md1.toplevel x = MoveDef.Md1.c GHC.Num.* x\n MoveDef.Md1.c, MoveDef.Md1.d :: GHC.Integer.Type.Integer\n MoveDef.Md1.c = 7\n MoveDef.Md1.d = 9\n MoveDef.Md1.tup :: (GHC.Types.Int, GHC.Types.Int)\n MoveDef.Md1.h :: GHC.Types.Int\n MoveDef.Md1.t :: GHC.Types.Int\n MoveDef.Md1.tup@(MoveDef.Md1.h, MoveDef.Md1.t)\n   = GHC.List.head GHC.Base.$ GHC.List.zip [1 .. 10] [3 .. ff]\n   where\n       ff :: GHC.Types.Int\n       ff = 15\n MoveDef.Md1.ff :: GHC.Types.Int -> GHC.Types.Int\n MoveDef.Md1.ff y\n   = y GHC.Num.+ zz\n   where\n       zz = 1\n MoveDef.Md1.l z = let ll = 34 in ll GHC.Num.+ z\n MoveDef.Md1.dd q\n   = do { let ss = 5;\n          GHC.Base.return (ss GHC.Num.+ q) }\n MoveDef.Md1.zz1 a = 1 GHC.Num.+ MoveDef.Md1.toplevel a\n MoveDef.Md1.tlFunc ::\n   GHC.Integer.Type.Integer -> GHC.Integer.Type.Integer\n MoveDef.Md1.tlFunc x = MoveDef.Md1.c GHC.Num.* x\n nn = nn2\n \n data MoveDef.Md1.D\n   = MoveDef.Md1.A | MoveDef.Md1.B GHC.Base.String | MoveDef.Md1.C,\n [import (implicit) Prelude],\n Nothing,\n Nothing)"

    -- -------------------------------------------

    it "adds a top level declaration with a type signature" $ do
      (t, toks) <- parsedFileMd1Ghc
      let
        comp = do
         renamed <- getRefactRenamed
         nn  <- mkNewGhcName Nothing "nn"
         nn2 <- mkNewGhcName Nothing "nn2"
         let (GHC.ValBindsOut _ vb) = hsValBinds renamed
         let hSig = head $ drop 3 vb
         let (GHC.L _ (GHC.TypeSig _ (GHC.L _ (GHC.HsTyVar intName)))) = hSig
         let newDecl = GHC.noLoc (GHC.VarBind nn (GHC.noLoc (GHC.HsVar nn2)) False)
         let sig = GHC.noLoc (GHC.TypeSig [(GHC.noLoc nn)] (GHC.noLoc (GHC.HsTyVar intName)))
{-
(L {test/testdata/SwapArgs/B.hs:36:1-10}
      (TypeSig
       [
        (L {test/testdata/SwapArgs/B.hs:36:1-3} {Name: SwapArgs.B.baz})]
       (L {test/testdata/SwapArgs/B.hs:36:8-10}
        (HsTyVar {Name: GHC.Types.Int}))))
-}
         newDecls <- addDecl renamed Nothing (newDecl,[sig],Nothing) True
         -- newDecls <- addDecl renamed Nothing (newDecl,Nothing,Nothing) True

         return (hSig,intName,newDecls)
      ((_hs,iname,nb),s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- (showGhc n) `shouldBe` "MoveDef.Md1.ff"
      (showGhc iname) `shouldBe` "GHC.Types.Int"
      (GHC.showRichTokenStream $ toks) `shouldBe` "module MoveDef.Md1 where\n\n toplevel :: Integer -> Integer\n toplevel x = c * x\n\n c,d :: Integer\n c = 7\n d = 9\n\n -- Pattern bind\n tup :: (Int, Int)\n h :: Int\n t :: Int\n tup@(h,t) = head $ zip [1..10] [3..ff]\n   where\n     ff :: Int\n     ff = 15\n\n data D = A | B String | C\n\n ff :: Int -> Int\n ff y = y + zz\n   where\n     zz = 1\n\n l z =\n   let\n     ll = 34\n   in ll + z\n\n dd q = do\n   let ss = 5\n   return (ss + q)\n\n zz1 a = 1 + toplevel a\n\n -- General Comment\n -- |haddock comment\n tlFunc :: Integer -> Integer\n tlFunc x = c * x\n -- Comment at end\n\n\n "
      -- (showToks $ take 20 $ toksFromState s) `shouldBe` ""
      (renderLines $ linesFromState s) `shouldBe` "module MoveDef.Md1 where\n\ntoplevel :: Integer -> Integer\ntoplevel x = c * x\n\nc,d :: Integer\nc = 7\nd = 9\n\n-- Pattern bind\ntup :: (Int, Int)\nh :: Int\nt :: Int\ntup@(h,t) = head $ zip [1..10] [3..ff]\n  where\n    ff :: Int\n    ff = 15\n\ndata D = A | B String | C\n\nff :: Int -> Int\nff y = y + zz\n  where\n    zz = 1\n\nl z =\n  let\n    ll = 34\n  in ll + z\n\ndd q = do\n  let ss = 5\n  return (ss + q)\n\nnn :: Int\nnn = nn2\n\nzz1 a = 1 + toplevel a\n\n-- General Comment\n-- |haddock comment\ntlFunc :: Integer -> Integer\ntlFunc x = c * x\n-- Comment at end\n\n\n"
      (unspace $ showGhc nb) `shouldBe` unspace "(MoveDef.Md1.toplevel ::\n   GHC.Integer.Type.Integer -> GHC.Integer.Type.Integer\n MoveDef.Md1.toplevel x = MoveDef.Md1.c GHC.Num.* x\n MoveDef.Md1.c, MoveDef.Md1.d :: GHC.Integer.Type.Integer\n MoveDef.Md1.c = 7\n MoveDef.Md1.d = 9\n MoveDef.Md1.tup :: (GHC.Types.Int, GHC.Types.Int)\n MoveDef.Md1.h :: GHC.Types.Int\n MoveDef.Md1.t :: GHC.Types.Int\n MoveDef.Md1.tup@(MoveDef.Md1.h, MoveDef.Md1.t)\n   = GHC.List.head GHC.Base.$ GHC.List.zip [1 .. 10] [3 .. ff]\n   where\n       ff :: GHC.Types.Int\n       ff = 15\n MoveDef.Md1.ff :: GHC.Types.Int -> GHC.Types.Int\n MoveDef.Md1.ff y\n   = y GHC.Num.+ zz\n   where\n       zz = 1\n MoveDef.Md1.l z = let ll = 34 in ll GHC.Num.+ z\n MoveDef.Md1.dd q\n   = do { let ss = 5;\n          GHC.Base.return (ss GHC.Num.+ q) }\n MoveDef.Md1.zz1 a = 1 GHC.Num.+ MoveDef.Md1.toplevel a\n MoveDef.Md1.tlFunc ::\n   GHC.Integer.Type.Integer -> GHC.Integer.Type.Integer\n MoveDef.Md1.tlFunc x = MoveDef.Md1.c GHC.Num.* x\n nn = nn2\n nn :: GHC.Types.Int\n \n data MoveDef.Md1.D\n   = MoveDef.Md1.A | MoveDef.Md1.B GHC.Base.String | MoveDef.Md1.C,\n [import (implicit) Prelude],\n Nothing,\n Nothing)"

    -- -------------------------------------------

    it "adds a top level declaration after a specified one" $ do
      (t, toks) <- parsedFileMd1Ghc
      let
        comp = do
         renamed <- getRefactRenamed
         let Just (GHC.L _l n) = locToName (21, 1) renamed
         nn  <- mkNewGhcName Nothing "nn"
         nn2 <- mkNewGhcName Nothing "nn2"
         let newDecl = GHC.noLoc (GHC.VarBind nn (GHC.noLoc (GHC.HsVar nn2)) False)
         newDecls <- addDecl renamed (Just n) (newDecl,[],Nothing) True

         return (n,newDecls)
      ((n,nb),s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      (showGhc n) `shouldBe` "MoveDef.Md1.ff"
      (GHC.showRichTokenStream $ toks) `shouldBe` "module MoveDef.Md1 where\n\n toplevel :: Integer -> Integer\n toplevel x = c * x\n\n c,d :: Integer\n c = 7\n d = 9\n\n -- Pattern bind\n tup :: (Int, Int)\n h :: Int\n t :: Int\n tup@(h,t) = head $ zip [1..10] [3..ff]\n   where\n     ff :: Int\n     ff = 15\n\n data D = A | B String | C\n\n ff :: Int -> Int\n ff y = y + zz\n   where\n     zz = 1\n\n l z =\n   let\n     ll = 34\n   in ll + z\n\n dd q = do\n   let ss = 5\n   return (ss + q)\n\n zz1 a = 1 + toplevel a\n\n -- General Comment\n -- |haddock comment\n tlFunc :: Integer -> Integer\n tlFunc x = c * x\n -- Comment at end\n\n\n "
      -- (showToks $ take 20 $ toksFromState s) `shouldBe` ""
      (renderLines $ linesFromState s) `shouldBe` "module MoveDef.Md1 where\n\ntoplevel :: Integer -> Integer\ntoplevel x = c * x\n\nc,d :: Integer\nc = 7\nd = 9\n\n-- Pattern bind\ntup :: (Int, Int)\nh :: Int\nt :: Int\ntup@(h,t) = head $ zip [1..10] [3..ff]\n  where\n    ff :: Int\n    ff = 15\n\ndata D = A | B String | C\n\nff :: Int -> Int\nff y = y + zz\n  where\n    zz = 1\n\nnn = nn2\n\nl z =\n  let\n    ll = 34\n  in ll + z\n\ndd q = do\n  let ss = 5\n  return (ss + q)\n\nzz1 a = 1 + toplevel a\n\n-- General Comment\n-- |haddock comment\ntlFunc :: Integer -> Integer\ntlFunc x = c * x\n-- Comment at end\n\n\n"
      (unspace $ showGhc nb) `shouldBe` unspace "(MoveDef.Md1.toplevel ::\n   GHC.Integer.Type.Integer -> GHC.Integer.Type.Integer\n MoveDef.Md1.toplevel x = MoveDef.Md1.c GHC.Num.* x\n MoveDef.Md1.c, MoveDef.Md1.d :: GHC.Integer.Type.Integer\n MoveDef.Md1.c = 7\n MoveDef.Md1.d = 9\n MoveDef.Md1.tup :: (GHC.Types.Int, GHC.Types.Int)\n MoveDef.Md1.h :: GHC.Types.Int\n MoveDef.Md1.t :: GHC.Types.Int\n MoveDef.Md1.tup@(MoveDef.Md1.h, MoveDef.Md1.t)\n   = GHC.List.head GHC.Base.$ GHC.List.zip [1 .. 10] [3 .. ff]\n   where\n       ff :: GHC.Types.Int\n       ff = 15\n MoveDef.Md1.ff :: GHC.Types.Int -> GHC.Types.Int\n MoveDef.Md1.ff y\n   = y GHC.Num.+ zz\n   where\n       zz = 1\n MoveDef.Md1.l z = let ll = 34 in ll GHC.Num.+ z\n MoveDef.Md1.dd q\n   = do { let ss = 5;\n          GHC.Base.return (ss GHC.Num.+ q) }\n MoveDef.Md1.zz1 a = 1 GHC.Num.+ MoveDef.Md1.toplevel a\n MoveDef.Md1.tlFunc ::\n   GHC.Integer.Type.Integer -> GHC.Integer.Type.Integer\n MoveDef.Md1.tlFunc x = MoveDef.Md1.c GHC.Num.* x\n nn = nn2\n \n data MoveDef.Md1.D\n   = MoveDef.Md1.A | MoveDef.Md1.B GHC.Base.String | MoveDef.Md1.C,\n [import (implicit) Prelude],\n Nothing,\n Nothing)"


    -- -------------------------------------------

    it "adds a top level declaration with a type signature after a specified one" $ do
      (t, toks) <- parsedFileMd1Ghc
      let
        comp = do
         renamed <- getRefactRenamed
         let Just (GHC.L _l n) = locToName (21, 1) renamed
         nn  <- mkNewGhcName Nothing "nn"
         nn2 <- mkNewGhcName Nothing "nn2"
         let newDecl = GHC.noLoc (GHC.VarBind nn (GHC.noLoc (GHC.HsVar nn2)) False)

         let (GHC.ValBindsOut _ vb) = hsValBinds renamed
         let hSig = head $ drop 3 vb
         let (GHC.L _ (GHC.TypeSig _ (GHC.L _ (GHC.HsTyVar intName)))) = hSig
         let sig = GHC.noLoc (GHC.TypeSig [(GHC.noLoc nn)] (GHC.noLoc (GHC.HsTyVar intName)))

         newDecls <- addDecl renamed (Just n) (newDecl,[sig],Nothing) True

         return (n,newDecls)
      ((n,nb),s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      (showGhc n) `shouldBe` "MoveDef.Md1.ff"
      (GHC.showRichTokenStream $ toks) `shouldBe` "module MoveDef.Md1 where\n\n toplevel :: Integer -> Integer\n toplevel x = c * x\n\n c,d :: Integer\n c = 7\n d = 9\n\n -- Pattern bind\n tup :: (Int, Int)\n h :: Int\n t :: Int\n tup@(h,t) = head $ zip [1..10] [3..ff]\n   where\n     ff :: Int\n     ff = 15\n\n data D = A | B String | C\n\n ff :: Int -> Int\n ff y = y + zz\n   where\n     zz = 1\n\n l z =\n   let\n     ll = 34\n   in ll + z\n\n dd q = do\n   let ss = 5\n   return (ss + q)\n\n zz1 a = 1 + toplevel a\n\n -- General Comment\n -- |haddock comment\n tlFunc :: Integer -> Integer\n tlFunc x = c * x\n -- Comment at end\n\n\n "
      -- (showToks $ take 20 $ toksFromState s) `shouldBe` ""
      (renderLines $ linesFromState s) `shouldBe`"module MoveDef.Md1 where\n\ntoplevel :: Integer -> Integer\ntoplevel x = c * x\n\nc,d :: Integer\nc = 7\nd = 9\n\n-- Pattern bind\ntup :: (Int, Int)\nh :: Int\nt :: Int\ntup@(h,t) = head $ zip [1..10] [3..ff]\n  where\n    ff :: Int\n    ff = 15\n\ndata D = A | B String | C\n\nff :: Int -> Int\nff y = y + zz\n  where\n    zz = 1\n\nnn :: Int\nnn = nn2\n\nl z =\n  let\n    ll = 34\n  in ll + z\n\ndd q = do\n  let ss = 5\n  return (ss + q)\n\nzz1 a = 1 + toplevel a\n\n-- General Comment\n-- |haddock comment\ntlFunc :: Integer -> Integer\ntlFunc x = c * x\n-- Comment at end\n\n\n"
      (unspace $ showGhc nb) `shouldBe` unspace "(MoveDef.Md1.toplevel ::\n   GHC.Integer.Type.Integer -> GHC.Integer.Type.Integer\n MoveDef.Md1.toplevel x = MoveDef.Md1.c GHC.Num.* x\n MoveDef.Md1.c, MoveDef.Md1.d :: GHC.Integer.Type.Integer\n MoveDef.Md1.c = 7\n MoveDef.Md1.d = 9\n MoveDef.Md1.tup :: (GHC.Types.Int, GHC.Types.Int)\n MoveDef.Md1.h :: GHC.Types.Int\n MoveDef.Md1.t :: GHC.Types.Int\n MoveDef.Md1.tup@(MoveDef.Md1.h, MoveDef.Md1.t)\n   = GHC.List.head GHC.Base.$ GHC.List.zip [1 .. 10] [3 .. ff]\n   where\n       ff :: GHC.Types.Int\n       ff = 15\n MoveDef.Md1.ff :: GHC.Types.Int -> GHC.Types.Int\n MoveDef.Md1.ff y\n   = y GHC.Num.+ zz\n   where\n       zz = 1\n MoveDef.Md1.l z = let ll = 34 in ll GHC.Num.+ z\n MoveDef.Md1.dd q\n   = do { let ss = 5;\n          GHC.Base.return (ss GHC.Num.+ q) }\n MoveDef.Md1.zz1 a = 1 GHC.Num.+ MoveDef.Md1.toplevel a\n MoveDef.Md1.tlFunc ::\n   GHC.Integer.Type.Integer -> GHC.Integer.Type.Integer\n MoveDef.Md1.tlFunc x = MoveDef.Md1.c GHC.Num.* x\n nn = nn2\n nn :: GHC.Types.Int\n \n data MoveDef.Md1.D\n   = MoveDef.Md1.A | MoveDef.Md1.B GHC.Base.String | MoveDef.Md1.C,\n [import (implicit) Prelude],\n Nothing,\n Nothing)"


    -- -------------------------------------------

    it "adds a local declaration without a type signature 1" $ do
      (t, toks) <- parsedFileMd1Ghc
      let
        comp = do

         renamed <- getRefactRenamed

         let Just (GHC.L _ tl) = locToName (4, 1) renamed
         let declsr = hsBinds renamed
             [tlDecls] = definingDeclsNames [tl] declsr True False

         nn  <- mkNewGhcName Nothing "nn"
         nn2 <- mkNewGhcName Nothing "nn2"
         let newDecl = GHC.noLoc (GHC.VarBind nn (GHC.noLoc (GHC.HsVar nn2)) False)
         newDecls <- addDecl tlDecls Nothing (newDecl,[],Nothing) False

         return (tlDecls,newDecls)
      ((tl,nb),s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      (showGhc tl) `shouldBe` "MoveDef.Md1.toplevel x = MoveDef.Md1.c GHC.Num.* x"
      -- (showToks $ take 30 $ toksFromState s) `shouldBe` ""
      (GHC.showRichTokenStream $ toks) `shouldBe` "module MoveDef.Md1 where\n\n toplevel :: Integer -> Integer\n toplevel x = c * x\n\n c,d :: Integer\n c = 7\n d = 9\n\n -- Pattern bind\n tup :: (Int, Int)\n h :: Int\n t :: Int\n tup@(h,t) = head $ zip [1..10] [3..ff]\n   where\n     ff :: Int\n     ff = 15\n\n data D = A | B String | C\n\n ff :: Int -> Int\n ff y = y + zz\n   where\n     zz = 1\n\n l z =\n   let\n     ll = 34\n   in ll + z\n\n dd q = do\n   let ss = 5\n   return (ss + q)\n\n zz1 a = 1 + toplevel a\n\n -- General Comment\n -- |haddock comment\n tlFunc :: Integer -> Integer\n tlFunc x = c * x\n -- Comment at end\n\n\n "
      (renderLines $ linesFromState s) `shouldBe` "module MoveDef.Md1 where\n\ntoplevel :: Integer -> Integer\ntoplevel x = c * x\n    where\n       nn = nn2\n    \n\nc,d :: Integer\nc = 7\nd = 9\n\n-- Pattern bind\ntup :: (Int, Int)\nh :: Int\nt :: Int\ntup@(h,t) = head $ zip [1..10] [3..ff]\n  where\n    ff :: Int\n    ff = 15\n\ndata D = A | B String | C\n\nff :: Int -> Int\nff y = y + zz\n  where\n    zz = 1\n\nl z =\n  let\n    ll = 34\n  in ll + z\n\ndd q = do\n  let ss = 5\n  return (ss + q)\n\nzz1 a = 1 + toplevel a\n\n-- General Comment\n-- |haddock comment\ntlFunc :: Integer -> Integer\ntlFunc x = c * x\n-- Comment at end\n\n\n"
      (showGhc nb) `shouldBe` "MoveDef.Md1.toplevel x\n  = MoveDef.Md1.c GHC.Num.* x\n  where\n      nn = nn2"


    -- -------------------------------------------

    it "adds a local declaration with a type signature" $ do
      (t, toks) <- parsedFileMd1Ghc
      let
        comp = do

         renamed <- getRefactRenamed

         let Just (GHC.L _ tl) = locToName (4, 1) renamed
         let declsr = hsBinds renamed
             [tlDecls] = definingDeclsNames [tl] declsr True False

         nn  <- mkNewGhcName Nothing "nn"
         nn2 <- mkNewGhcName Nothing "nn2"
         let newDecl = GHC.noLoc (GHC.VarBind nn (GHC.noLoc (GHC.HsVar nn2)) False)

         let (GHC.ValBindsOut _ vb) = hsValBinds renamed
         let hSig = head $ drop 3 vb
         let (GHC.L _ (GHC.TypeSig _ (GHC.L _ (GHC.HsTyVar intName)))) = hSig
         let sig = GHC.noLoc (GHC.TypeSig [(GHC.noLoc nn)] (GHC.noLoc (GHC.HsTyVar intName)))

         newDecls <- addDecl tlDecls Nothing (newDecl,[sig],Nothing) False

         return (tlDecls,newDecls)
      ((tl,nb),s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      (showGhc tl) `shouldBe` "MoveDef.Md1.toplevel x = MoveDef.Md1.c GHC.Num.* x"
      -- (showToks $ take 30 $ toksFromState s) `shouldBe` ""
      (GHC.showRichTokenStream $ toks) `shouldBe` "module MoveDef.Md1 where\n\n toplevel :: Integer -> Integer\n toplevel x = c * x\n\n c,d :: Integer\n c = 7\n d = 9\n\n -- Pattern bind\n tup :: (Int, Int)\n h :: Int\n t :: Int\n tup@(h,t) = head $ zip [1..10] [3..ff]\n   where\n     ff :: Int\n     ff = 15\n\n data D = A | B String | C\n\n ff :: Int -> Int\n ff y = y + zz\n   where\n     zz = 1\n\n l z =\n   let\n     ll = 34\n   in ll + z\n\n dd q = do\n   let ss = 5\n   return (ss + q)\n\n zz1 a = 1 + toplevel a\n\n -- General Comment\n -- |haddock comment\n tlFunc :: Integer -> Integer\n tlFunc x = c * x\n -- Comment at end\n\n\n "
      (renderLines $ linesFromState s) `shouldBe` "module MoveDef.Md1 where\n\ntoplevel :: Integer -> Integer\ntoplevel x = c * x\n    where\n       nn :: Int\n       nn = nn2\n    \n\nc,d :: Integer\nc = 7\nd = 9\n\n-- Pattern bind\ntup :: (Int, Int)\nh :: Int\nt :: Int\ntup@(h,t) = head $ zip [1..10] [3..ff]\n  where\n    ff :: Int\n    ff = 15\n\ndata D = A | B String | C\n\nff :: Int -> Int\nff y = y + zz\n  where\n    zz = 1\n\nl z =\n  let\n    ll = 34\n  in ll + z\n\ndd q = do\n  let ss = 5\n  return (ss + q)\n\nzz1 a = 1 + toplevel a\n\n-- General Comment\n-- |haddock comment\ntlFunc :: Integer -> Integer\ntlFunc x = c * x\n-- Comment at end\n\n\n"
      (showGhc nb) `shouldBe` "MoveDef.Md1.toplevel x\n  = MoveDef.Md1.c GHC.Num.* x\n  where\n      nn :: GHC.Types.Int\n      nn = nn2"


    -- -------------------------------------------

    it "adds a local declaration with a where clause" $ do
      (t, toks) <- parsedFileDemoteGhc
      let
        comp = do

         renamed <- getRefactRenamed

         let Just (GHC.L _ tl) = locToName (4, 1) renamed
         let declsr = hsBinds renamed
             [tlDecls] = definingDeclsNames [tl] declsr True False

         nn  <- mkNewGhcName Nothing "nn"
         nn2 <- mkNewGhcName Nothing "nn2"
         let newDecl = GHC.noLoc (GHC.VarBind nn (GHC.noLoc (GHC.HsVar nn2)) False)
         newDecls <- addDecl tlDecls Nothing (newDecl,[],Nothing) False

         return (tlDecls,newDecls)
      ((tl,nb),s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      (showGhc tl) `shouldBe` "MoveDef.Demote.toplevel x = MoveDef.Demote.c GHC.Num.* x"
      -- (showToks $ take 30 $ toks) `shouldBe` ""
      -- (showToks $ take 30 $ toksFromState s) `shouldBe` ""
      (GHC.showRichTokenStream $ toks) `shouldBe` "module MoveDef.Demote where\n\n toplevel :: Integer -> Integer\n toplevel x = c * x\n\n -- c,d :: Integer\n c = 7\n d = 9\n\n\n "
      -- (drawTreeCompact $ fromJust $ layoutFromState s) `shouldBe` ""
      -- (showGhc $ pprFromState s) `shouldBe` ""
      (renderLines $ linesFromState s) `shouldBe` "module MoveDef.Demote where\n\ntoplevel :: Integer -> Integer\ntoplevel x = c * x\n    where\n       nn = nn2\n    \n\n-- c,d :: Integer\nc = 7\nd = 9\n\n\n"
      (showGhc nb) `shouldBe` "MoveDef.Demote.toplevel x\n  = MoveDef.Demote.c GHC.Num.* x\n  where\n      nn = nn2"

    -- -------------------------------------------

    it "adds a local declaration to an existing one" $ do
      (t, toks) <- parsedFileMd2Ghc
      let
        comp = do

         renamed <- getRefactRenamed

         let Just (GHC.L _ tl) = locToName (4, 1) renamed
         let declsr = hsBinds renamed
             [tlDecls] = definingDeclsNames [tl] declsr True False

         nn  <- mkNewGhcName Nothing "nn"
         nn2 <- mkNewGhcName Nothing "nn2"
         let newDecl = GHC.noLoc (GHC.VarBind nn (GHC.noLoc (GHC.HsVar nn2)) False)
         newDecls <- addDecl tlDecls Nothing (newDecl,[],Nothing) False

         return (tlDecls,newDecls)
      ((tl,nb),s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- ((tl,nb),s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }
      (showGhc tl) `shouldBe` "MoveDef.Md2.toplevel x\n  = MoveDef.Md2.c GHC.Num.* x GHC.Num.* b\n  where\n      b = 3"
      (GHC.showRichTokenStream $ toks) `shouldBe` "module MoveDef.Md2 where\n\n toplevel :: Integer -> Integer\n toplevel x = c * x * b\n   where\n     b = 3\n\n c,d :: Integer\n c = 7\n d = 9\n\n -- Pattern bind\n tup :: (Int, Int)\n h :: Int\n t :: Int\n tup@(h,t) = head $ zip [1..10] [3..ff]\n   where\n     ff :: Int\n     ff = 15\n\n data D = A | B String | C\n\n ff :: Int -> Int\n ff y = y + zz\n   where\n     zz = 1\n\n l z =\n   let\n     ll = 34\n   in ll + z\n\n dd q = do\n   let ss = 5\n   return (ss + q)\n\n zz1 a = 1 + toplevel a\n\n -- General Comment\n -- |haddock comment\n tlFunc :: Integer -> Integer\n tlFunc x = c * x\n -- Comment at end\n\n\n "
      -- (showToks $ take 30 $ toksFromState s) `shouldBe` ""
      (renderLines $ linesFromState s) `shouldBe` "module MoveDef.Md2 where\n\ntoplevel :: Integer -> Integer\ntoplevel x = c * x * b\n  where\n    b = 3\n\n    nn = nn2\n\nc,d :: Integer\nc = 7\nd = 9\n\n-- Pattern bind\ntup :: (Int, Int)\nh :: Int\nt :: Int\ntup@(h,t) = head $ zip [1..10] [3..ff]\n  where\n    ff :: Int\n    ff = 15\n\ndata D = A | B String | C\n\nff :: Int -> Int\nff y = y + zz\n  where\n    zz = 1\n\nl z =\n  let\n    ll = 34\n  in ll + z\n\ndd q = do\n  let ss = 5\n  return (ss + q)\n\nzz1 a = 1 + toplevel a\n\n-- General Comment\n-- |haddock comment\ntlFunc :: Integer -> Integer\ntlFunc x = c * x\n-- Comment at end\n\n\n"
      (showGhc nb) `shouldBe` "MoveDef.Md2.toplevel x\n  = MoveDef.Md2.c GHC.Num.* x GHC.Num.* b\n  where\n      b = 3\n      nn = nn2"

    -- -------------------------------------------

    it "adds a local declaration with a type signature to an existing one" $ do
      (t, toks) <- parsedFileMd2Ghc
      let
        comp = do

         renamed <- getRefactRenamed

         let Just (GHC.L _ tl) = locToName (4, 1) renamed
         let declsr = hsBinds renamed
             [tlDecls] = definingDeclsNames [tl] declsr True False

         nn  <- mkNewGhcName Nothing "nn"
         nn2 <- mkNewGhcName Nothing "nn2"
         let newDecl = GHC.noLoc (GHC.VarBind nn (GHC.noLoc (GHC.HsVar nn2)) False)

         let (GHC.ValBindsOut _ vb) = hsValBinds renamed
         let hSig = head $ drop 3 vb
         let (GHC.L _ (GHC.TypeSig _ (GHC.L _ (GHC.HsTyVar intName)))) = hSig
         let sig = GHC.noLoc (GHC.TypeSig [(GHC.noLoc nn)] (GHC.noLoc (GHC.HsTyVar intName)))

         -- newDecls <- addDecl tlDecls Nothing (newDecl,Nothing,Nothing) False
         newDecls <- addDecl tlDecls Nothing (newDecl,[sig],Nothing) False

         return (tlDecls,newDecls)
      ((tl,nb),s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- ((tl,nb),s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }
      (showGhc tl) `shouldBe` "MoveDef.Md2.toplevel x\n  = MoveDef.Md2.c GHC.Num.* x GHC.Num.* b\n  where\n      b = 3"
      (GHC.showRichTokenStream $ toks) `shouldBe` "module MoveDef.Md2 where\n\n toplevel :: Integer -> Integer\n toplevel x = c * x * b\n   where\n     b = 3\n\n c,d :: Integer\n c = 7\n d = 9\n\n -- Pattern bind\n tup :: (Int, Int)\n h :: Int\n t :: Int\n tup@(h,t) = head $ zip [1..10] [3..ff]\n   where\n     ff :: Int\n     ff = 15\n\n data D = A | B String | C\n\n ff :: Int -> Int\n ff y = y + zz\n   where\n     zz = 1\n\n l z =\n   let\n     ll = 34\n   in ll + z\n\n dd q = do\n   let ss = 5\n   return (ss + q)\n\n zz1 a = 1 + toplevel a\n\n -- General Comment\n -- |haddock comment\n tlFunc :: Integer -> Integer\n tlFunc x = c * x\n -- Comment at end\n\n\n "
      -- (showToks $ take 30 $ toksFromState s) `shouldBe` ""
      (renderLines $ linesFromState s) `shouldBe` "module MoveDef.Md2 where\n\ntoplevel :: Integer -> Integer\ntoplevel x = c * x * b\n  where\n    b = 3\n\n    nn :: Int\n    nn = nn2\n\nc,d :: Integer\nc = 7\nd = 9\n\n-- Pattern bind\ntup :: (Int, Int)\nh :: Int\nt :: Int\ntup@(h,t) = head $ zip [1..10] [3..ff]\n  where\n    ff :: Int\n    ff = 15\n\ndata D = A | B String | C\n\nff :: Int -> Int\nff y = y + zz\n  where\n    zz = 1\n\nl z =\n  let\n    ll = 34\n  in ll + z\n\ndd q = do\n  let ss = 5\n  return (ss + q)\n\nzz1 a = 1 + toplevel a\n\n-- General Comment\n-- |haddock comment\ntlFunc :: Integer -> Integer\ntlFunc x = c * x\n-- Comment at end\n\n\n"
      (showGhc nb) `shouldBe` "MoveDef.Md2.toplevel x\n  = MoveDef.Md2.c GHC.Num.* x GHC.Num.* b\n  where\n      b = 3\n      nn :: GHC.Types.Int\n      nn = nn2"


    -- -------------------------------------------

    it "adds a local decl with type signature to an existing one, with a comment" $ do
      (t, toks) <- parsedFileWhereIn3Ghc
      let
        comp = do
         renamed <- getRefactRenamed

         let Just (GHC.L _ tl) = locToName (10, 1) renamed
         let declsr = hsBinds renamed
             [tlDecls] = definingDeclsNames [tl] declsr True False

         let Just (GHC.L _ sq) = locToName (14, 1) renamed

         let [sqDecl] = definingDeclsNames [sq] (hsBinds renamed) False False
             [sqSig]  = definingSigsNames  [sq] renamed


         -- newDecls <- addDecl tlDecls Nothing (newDecl,Nothing,Nothing) False
         newDecls <- addDecl tlDecls Nothing (sqDecl,[sqSig],Nothing) False

         return (sqSig,tlDecls,newDecls)
      ((sigs,tl,nb),s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      (showGhc sigs) `shouldBe` "Demote.WhereIn3.sq ::\n  GHC.Types.Int -> GHC.Types.Int -> GHC.Types.Int"
      (showGhc tl) `shouldBe` "Demote.WhereIn3.sumSquares x y\n  = Demote.WhereIn3.sq p x GHC.Num.+ Demote.WhereIn3.sq p y\n  where\n      p = 2"
      (GHC.showRichTokenStream $ toks) `shouldBe` "module Demote.WhereIn3 where\n\n --A definition can be demoted to the local 'where' binding of a friend declaration,\n --if it is only used by this friend declaration.\n\n --Demoting a definition narrows down the scope of the definition.\n --In this example, demote the top level 'sq' to 'sumSquares'\n --In this case (there are multi matches), the parameters are not folded after demoting.\n\n sumSquares x y = sq p x + sq p y\n          where p=2  {-There is a comment-}\n\n sq :: Int -> Int -> Int\n sq pow 0 = 0\n sq pow z = z^pow  --there is a comment\n\n anotherFun 0 y = sq y\n      where  sq x = x^2\n\n "
      -- (showToks $ take 30 $ toksFromState s) `shouldBe` ""
      (renderLines $ linesFromState s) `shouldBe` "module Demote.WhereIn3 where\n\n--A definition can be demoted to the local 'where' binding of a friend declaration,\n--if it is only used by this friend declaration.\n\n--Demoting a definition narrows down the scope of the definition.\n--In this example, demote the top level 'sq' to 'sumSquares'\n--In this case (there are multi matches), the parameters are not folded after demoting.\n\nsumSquares x y = sq p x + sq p y\n         where p=2  {-There is a comment-}\n\n               sq :: Int -> Int -> Int\n               sq pow 0 = 0\n               sq pow z = z ^ pow\n\nsq :: Int -> Int -> Int\nsq pow 0 = 0\nsq pow z = z^pow  --there is a comment\n\nanotherFun 0 y = sq y\n     where  sq x = x^2\n\n"
      (showGhc nb) `shouldBe` "Demote.WhereIn3.sumSquares x y\n  = Demote.WhereIn3.sq p x GHC.Num.+ Demote.WhereIn3.sq p y\n  where\n      p = 2\n      Demote.WhereIn3.sq ::\n        GHC.Types.Int -> GHC.Types.Int -> GHC.Types.Int\n      Demote.WhereIn3.sq pow 0 = 0\n      Demote.WhereIn3.sq pow z = z GHC.Real.^ pow"


    -- -------------------------------------------

    it "adds a local decl with type signature to an existing one with a comment using toks (original)" $ do
      (t, toks) <- parsedFileWhereIn3Ghc
      let
        comp = do

         renamed <- getRefactRenamed

         let Just (GHC.L _ tl) = locToName (10, 1) renamed
         let declsr = hsBinds renamed
             [tlDecls] = definingDeclsNames [tl] declsr True False

         let Just (GHC.L _ sq) = locToName (14, 1) renamed

         let ([sqDecl],declToks) = getDeclAndToks sq True toks renamed
         let (Just sqSig, sigToks) =
               case (getSigAndToks sq renamed toks) of
                 Just (sig, sigToks') -> (Just sig, sigToks')
                 Nothing -> (Nothing,[])
             toksToAdd = sigToks ++ declToks


         newDecls <- addDecl tlDecls Nothing (sqDecl,[sqSig],Just toksToAdd) False

         return (sqSig,tlDecls,newDecls,toksToAdd)
         -- return (sqSig,tlDecls,newDecls,sigToks')

      ((sigs,tl,nb,_tta),s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- ((sigs,tl,nb,_tta),s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }
      -- "" `shouldBe` "this test hangs on accessing sigToks. investigate"


      -- (showToks _tta) `shouldBe` ""
      (showGhc sigs) `shouldBe` "Demote.WhereIn3.sq ::\n  GHC.Types.Int -> GHC.Types.Int -> GHC.Types.Int"
      (showGhc tl) `shouldBe` "Demote.WhereIn3.sumSquares x y\n  = Demote.WhereIn3.sq p x GHC.Num.+ Demote.WhereIn3.sq p y\n  where\n      p = 2"
      (GHC.showRichTokenStream $ toks) `shouldBe` "module Demote.WhereIn3 where\n\n --A definition can be demoted to the local 'where' binding of a friend declaration,\n --if it is only used by this friend declaration.\n\n --Demoting a definition narrows down the scope of the definition.\n --In this example, demote the top level 'sq' to 'sumSquares'\n --In this case (there are multi matches), the parameters are not folded after demoting.\n\n sumSquares x y = sq p x + sq p y\n          where p=2  {-There is a comment-}\n\n sq :: Int -> Int -> Int\n sq pow 0 = 0\n sq pow z = z^pow  --there is a comment\n\n anotherFun 0 y = sq y\n      where  sq x = x^2\n\n "
      -- (showToks $ take 30 $ toksFromState s) `shouldBe` ""
      (renderLines $ linesFromState s) `shouldBe` "module Demote.WhereIn3 where\n\n--A definition can be demoted to the local 'where' binding of a friend declaration,\n--if it is only used by this friend declaration.\n\n--Demoting a definition narrows down the scope of the definition.\n--In this example, demote the top level 'sq' to 'sumSquares'\n--In this case (there are multi matches), the parameters are not folded after demoting.\n\nsumSquares x y = sq p x + sq p y\n         where p=2  {-There is a comment-}\n\n               sq :: Int -> Int -> Int\n               sq pow 0 = 0\n               sq pow z = z^pow  --there is a comment\n\nsq :: Int -> Int -> Int\nsq pow 0 = 0\nsq pow z = z^pow  --there is a comment\n\nanotherFun 0 y = sq y\n     where  sq x = x^2\n\n"
      (showGhc nb) `shouldBe` "Demote.WhereIn3.sumSquares x y\n  = Demote.WhereIn3.sq p x GHC.Num.+ Demote.WhereIn3.sq p y\n  where\n      p = 2\n      Demote.WhereIn3.sq ::\n        GHC.Types.Int -> GHC.Types.Int -> GHC.Types.Int\n      Demote.WhereIn3.sq pow 0 = 0\n      Demote.WhereIn3.sq pow z = z GHC.Real.^ pow"


  -- ---------------------------------------------

  describe "renamePN" $ do
    it "replaces a Name with another, updating tokens 1" $ do
      (t, toks) <- parsedFileDd1Ghc
      let renamed = fromJust $ GHC.tm_renamed_source t

      let declsr = hsBinds renamed
      -- (showGhc declsr) `shouldBe` ""
      let Just (GHC.L l n) = locToName (3, 1) renamed
      let
        comp = do
         newName <- mkNewGhcName Nothing "bar2"
         new <- renamePN n newName True False (last declsr)

         return (new,newName)
      let

      ((nb,nn),s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- ((nb,nn),s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }
      (showGhc n) `shouldBe` "DupDef.Dd1.toplevel"
      (showToks $ [newNameTok False l nn]) `shouldBe` "[((3,1),(3,5),\"bar2\")]"
      (GHC.showRichTokenStream $ toks) `shouldBe` "module DupDef.Dd1 where\n\n toplevel :: Integer -> Integer\n toplevel x = c * x\n\n c,d :: Integer\n c = 7\n d = 9\n\n -- Pattern bind\n tup :: (Int, Int)\n h :: Int\n t :: Int\n tup@(h,t) = head $ zip [1..10] [3..ff]\n   where\n     ff :: Int\n     ff = 15\n\n data D = A | B String | C\n\n ff y = y + zz\n   where\n     zz = 1\n\n l z =\n   let\n     ll = 34\n   in ll + z\n\n dd q = do\n   let ss = 5\n   return (ss + q)\n\n "
      (renderLines $ linesFromState s) `shouldBe` "module DupDef.Dd1 where\n\ntoplevel :: Integer -> Integer\nbar2 x = c * x\n\nc,d :: Integer\nc = 7\nd = 9\n\n-- Pattern bind\ntup :: (Int, Int)\nh :: Int\nt :: Int\ntup@(h,t) = head $ zip [1..10] [3..ff]\n  where\n    ff :: Int\n    ff = 15\n\ndata D = A | B String | C\n\nff y = y + zz\n  where\n    zz = 1\n\nl z =\n  let\n    ll = 34\n  in ll + z\n\ndd q = do\n  let ss = 5\n  return (ss + q)\n\n"
      (showGhc nb) `shouldBe` "bar2 x = DupDef.Dd1.c GHC.Num.* x"
      (showToks $ take 20 $ toks) `shouldBe` "[((1,1),(1,7),\"module\"),((1,8),(1,18),\"DupDef.Dd1\"),((1,19),(1,24),\"where\"),((3,1),(3,1),\"\"),((3,1),(3,9),\"toplevel\"),((3,10),(3,12),\"::\"),((3,13),(3,20),\"Integer\"),((3,21),(3,23),\"->\"),((3,24),(3,31),\"Integer\"),((4,1),(4,1),\"\"),((4,1),(4,9),\"toplevel\"),((4,10),(4,11),\"x\"),((4,12),(4,13),\"=\"),((4,14),(4,15),\"c\"),((4,16),(4,17),\"*\"),((4,18),(4,19),\"x\"),((6,1),(6,1),\"\"),((6,1),(6,2),\"c\"),((6,2),(6,3),\",\"),((6,3),(6,4),\"d\")]"
      -- (showToks $ take 20 $ toksFromState s) `shouldBe` ""

    -- -----------------------------------------------------------------

    it "replaces a Name with another, updating tokens 2" $ do
      (t, toks) <- parsedFileWhereIn4Ghc

      let renamed = fromJust $ GHC.tm_renamed_source t

      let declsr = hsBinds renamed
      let decl = head $ drop 2 declsr
      (showGhc decl) `shouldBe` "Demote.WhereIn4.sumSquares x y\n  = Demote.WhereIn4.sq p x GHC.Num.+ Demote.WhereIn4.sq p y\n  where\n      p = 2"

      let Just (GHC.L l n) = locToName (11, 21) renamed
      let
        comp = do
         newName <- mkNewGhcName Nothing "p_1"
         new <- renamePN n newName True False decl

         return (new,newName)
      let

      ((nb,nn),s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      (showGhc n) `shouldBe` "p"
      (showToks $ [newNameTok False l nn]) `shouldBe` "[((11,21),(11,24),\"p_1\")]"
      (GHC.showRichTokenStream $ toks) `shouldBe` "module Demote.WhereIn4 where\n\n --A definition can be demoted to the local 'where' binding of a friend declaration,\n --if it is only used by this friend declaration.\n\n --Demoting a definition narrows down the scope of the definition.\n --In this example, demote the top level 'sq' to 'sumSquares'\n --In this case (there is single matches), if possible,\n --the parameters will be folded after demoting and type sigature will be removed.\n\n sumSquares x y = sq p x + sq p y\n          where p=2  {-There is a comment-}\n\n sq::Int->Int->Int\n sq pow z = z^pow  --there is a comment\n\n anotherFun 0 y = sq y\n      where  sq x = x^2\n\n "
      (renderLines $ linesFromState s) `shouldBe` "module Demote.WhereIn4 where\n\n--A definition can be demoted to the local 'where' binding of a friend declaration,\n--if it is only used by this friend declaration.\n\n--Demoting a definition narrows down the scope of the definition.\n--In this example, demote the top level 'sq' to 'sumSquares'\n--In this case (there is single matches), if possible,\n--the parameters will be folded after demoting and type sigature will be removed.\n\nsumSquares x y = sq p_1 x + sq p_1 y\n         where p_1=2  {-There is a comment-}\n\nsq::Int->Int->Int\nsq pow z = z^pow  --there is a comment\n\nanotherFun 0 y = sq y\n     where  sq x = x^2\n\n"
      (showGhc nb) `shouldBe` "Demote.WhereIn4.sumSquares x y\n  = Demote.WhereIn4.sq p_1 x GHC.Num.+ Demote.WhereIn4.sq p_1 y\n  where\n      p_1 = 2"
      (showToks $ take 20 $ toks) `shouldBe` "[((1,1),(1,7),\"module\"),((1,8),(1,23),\"Demote.WhereIn4\"),((1,24),(1,29),\"where\"),((3,1),(3,84),\"--A definition can be demoted to the local 'where' binding of a friend declaration,\"),((4,1),(4,49),\"--if it is only used by this friend declaration.\"),((6,1),(6,66),\"--Demoting a definition narrows down the scope of the definition.\"),((7,1),(7,61),\"--In this example, demote the top level 'sq' to 'sumSquares'\"),((8,1),(8,55),\"--In this case (there is single matches), if possible,\"),((9,1),(9,82),\"--the parameters will be folded after demoting and type sigature will be removed.\"),((11,1),(11,1),\"\"),((11,1),(11,11),\"sumSquares\"),((11,12),(11,13),\"x\"),((11,14),(11,15),\"y\"),((11,16),(11,17),\"=\"),((11,18),(11,20),\"sq\"),((11,21),(11,22),\"p\"),((11,23),(11,24),\"x\"),((11,25),(11,26),\"+\"),((11,27),(11,29),\"sq\"),((11,30),(11,31),\"p\")]"
      -- (showToks $ take 20 $ toksFromState s) `shouldBe` ""

    -- ---------------------------------

    it "replaces a Name with another in limited scope, updating tokens 1" $ do
      (t,toks) <- parsedFileGhc "./test/testdata/TokenTest.hs"
      let parsed = GHC.pm_parsed_source $ GHC.tm_parsed_module t

      let forest = allocTokens parsed toks

      let renamed = fromJust $ GHC.tm_renamed_source t
      let decls = hsBinds renamed
      let (GHC.L l _) = head decls
      (showGhc l) `shouldBe` "test/testdata/TokenTest.hs:(19,1)-(21,13)"
      (showSrcSpan l) `shouldBe` "((19,1),(21,14))"
      let Just (GHC.L _ n) = locToName (19, 1) renamed
      (showGhc n) `shouldBe` "TokenTest.foo"

      let (forest',tree) = getSrcSpanFor forest (ghcSrcSpanToForestSpan l)

      let toks' = retrieveTokensInterim tree
      let (forest'',sspan) = addNewSrcSpanAndToksAfter forest' (gs2ss l) (gs2ss l) (PlaceOffset 2 0 2) toks'
      (invariant forest'') `shouldBe` []

      (showSrcSpanF $ ss2gs sspan) `shouldBe` "(((False,0,1,19),1),((False,0,1,21),14))"

      let pprFinal = retrieveLinesFromLayoutTree forest''
      (renderLines pprFinal) `shouldBe` "module TokenTest where\n\n-- Test new style token manager\n\nbob a b = x\n  where x = 3\n\nbib a b = x\n  where\n    x = 3\n\n\nbab a b =\n  let bar = 3\n  in     b + bar -- ^trailing comment\n\n\n-- leading comment\nfoo x y =\n  do c <- getChar\n     return c\n\n-- leading comment\nfoo x y =\n  do c <- getChar\n     return c\n\n"

      let
        comp = do
         newName <- mkNewGhcName Nothing "bar2"
         toksForOp <- getToksForSpan l
         new <- renamePN n newName True False (head decls)

         return (new,newName,toksForOp)
      let

      ((nb,nn,_tfo),s) <- runRefactGhc comp $ initialState { rsModule = Just (RefMod {rsTokenCache = mkTokenCache forest'', rsTypecheckedMod = t, rsOrigTokenStream = toks, rsStreamModified=True})}
      -- (show _tfo) `shouldBe` ""
      (showGhc n) `shouldBe` "TokenTest.foo"
      (showToks $ [newNameTok False l nn]) `shouldBe` "[((19,1),(19,5),\"bar2\")]"
      (GHC.showRichTokenStream $ toks) `shouldBe` "module TokenTest where\n\n -- Test new style token manager\n\n bob a b = x\n   where x = 3\n\n bib a b = x\n   where\n     x = 3\n\n\n bab a b =\n   let bar = 3\n   in     b + bar -- ^trailing comment\n\n\n -- leading comment\n foo x y =\n   do c <- getChar\n      return c\n\n\n\n\n "
      (renderLines $ linesFromState s) `shouldBe` "module TokenTest where\n\n-- Test new style token manager\n\nbob a b = x\n  where x = 3\n\nbib a b = x\n  where\n    x = 3\n\n\nbab a b =\n  let bar = 3\n  in     b + bar -- ^trailing comment\n\n\n-- leading comment\nbar2 x y =\n  do c <- getChar\n     return c\n\n-- leading comment\nfoo x y =\n  do c <- getChar\n     return c\n\n"
      (showGhc nb) `shouldBe` "bar2 x y\n  = do { c <- System.IO.getChar;\n         GHC.Base.return c }"
      -- (showToks $ take 20 $ toksFromState s) `shouldBe` ""

    -- ---------------------------------

    it "replace a Name with another in limited scope, updating tokens 2" $ do
      (t,toks) <- parsedFileTokenTestGhc
      let forest = mkTreeFromTokens toks

      let renamed = fromJust $ GHC.tm_renamed_source t
      let decls = hsBinds renamed
      let decl@(GHC.L l _) = head decls
      (showGhc l) `shouldBe` "test/testdata/TokenTest.hs:(19,1)-(21,13)"
      (showSrcSpan l) `shouldBe` "((19,1),(21,14))"
      let Just (GHC.L _ n) = locToName (19, 1) renamed
      (showGhc n) `shouldBe` "TokenTest.foo"

      let (forest',tree) = getSrcSpanFor forest (ghcSrcSpanToForestSpan l)

      let toks' = retrieveTokensInterim tree
      let (forest'',sspan) = addToksAfterSrcSpan forest' (gs2ss l) (PlaceOffset 2 0 2) toks'
      let decl' = syncAST decl (ss2f sspan)
          forest''' = forest''

      -- (showGhc $ getSrcSpan decl') `shouldBe` "Just test/testdata/TokenTest.hs:(1000024,1)-(1000026,13)"
      (showGhc $ getSrcSpan decl') `shouldBe` "Just foo:(1048600,1)-(1048602,13)"
      (showSrcSpanF $ fromJust $ getSrcSpan decl') `shouldBe` "(((False,0,1,24),1),((False,0,1,26),14))"

      (invariant forest''') `shouldBe` []
      (drawTreeEntry forest'') `shouldBe`
              "((1,1),(21,14))\n|\n"++
              "+- ((1,1),(15,17))\n|\n"++
              "+- ((19,1),(21,14))\n|\n"++
              "`- ((1000024,1),(1000026,14))\n"  -- our inserted span
      (showSrcSpanF $ ss2gs sspan) `shouldBe` "(((False,0,1,24),1),((False,0,1,26),14))"

      -- (show $ getTokensFor True forest''' sspan) `shouldBe` ""

      -- let toksFinal = retrieveTokensFinal forest'''
      (renderTree forest''') `shouldBe` "module TokenTest where\n\n-- Test new style token manager\n\nbob a b = x\n  where x = 3\n\nbib a b = x\n  where\n    x = 3\n\n\nbab a b =\n  let bar = 3\n  in     b + bar -- ^trailing comment\n\n\n-- leading comment\nfoo x y =\n  do c <- getChar\n     return c\n\n-- leading comment\nfoo x y =\n  do c <- getChar\n     return c\n"

      let
        comp = do
         newName <- mkNewGhcName Nothing "bar2"
         -- toksForOp <- getToksForSpan sspan -- The new span this time
         new <- renamePN n newName True False decl'

         return (new,newName)

      ((nb,nn),s) <- runRefactGhc comp $ initialState { rsModule = Just (RefMod {rsTokenCache = mkTokenCache forest''', rsTypecheckedMod = t, rsOrigTokenStream = toks, rsStreamModified=True})}
      -- ((nb,nn),s) <- runRefactGhc comp $ initialLogOnState { rsModule = Just (RefMod {rsTokenCache = mkTokenCache forest''', rsTypecheckedMod = t, rsOrigTokenStream = toks, rsStreamModified=True})}

      -- (show tfo) `shouldBe` ""
      (showGhc n) `shouldBe` "TokenTest.foo"
      (showToks $ [newNameTok False l nn]) `shouldBe` "[((19,1),(19,5),\"bar2\")]"
      (GHC.showRichTokenStream $ toks) `shouldBe` "module TokenTest where\n\n -- Test new style token manager\n\n bob a b = x\n   where x = 3\n\n bib a b = x\n   where\n     x = 3\n\n\n bab a b =\n   let bar = 3\n   in     b + bar -- ^trailing comment\n\n\n -- leading comment\n foo x y =\n   do c <- getChar\n      return c\n\n\n\n\n "
      (renderLines $ linesFromState s) `shouldBe` "module TokenTest where\n\n-- Test new style token manager\n\nbob a b = x\n  where x = 3\n\nbib a b = x\n  where\n    x = 3\n\n\nbab a b =\n  let bar = 3\n  in     b + bar -- ^trailing comment\n\n\n-- leading comment\nfoo x y =\n  do c <- getChar\n     return c\n\n-- leading comment\nbar2 x y =\n  do c <- getChar\n     return c\n"
      (showGhc nb) `shouldBe` "bar2 x y\n  = do { c <- System.IO.getChar;\n         GHC.Base.return c }"
      -- (showToks $ take 20 $ toksFromState s) `shouldBe` ""

    -- ---------------------------------

    it "replace a Name with another in limited scope, updating tokens 3" $ do
      (t,toks) <- parsedFileDd1Ghc
      let forest = mkTreeFromTokens toks

      let renamed = fromJust $ GHC.tm_renamed_source t
      let decls = hsBinds renamed
      let decl@(GHC.L l _) = head $ drop 6 decls
      (showGhc l) `shouldBe` "test/testdata/DupDef/Dd1.hs:4:1-18"
      (showSrcSpan l) `shouldBe` "((4,1),(4,19))"
      let Just (GHC.L _ n) = locToName (4, 1) renamed
      (showGhc n) `shouldBe` "DupDef.Dd1.toplevel"

      -- let (forest',tree) = getSrcSpanFor forest (ghcSrcSpanToForestSpan l)
      let (forest',toks') = getTokensFor True forest (gs2ss l)

      let typeSig = definingSigsNames [n] renamed
      (showGhc typeSig) `shouldBe` "[DupDef.Dd1.toplevel ::\n   GHC.Integer.Type.Integer -> GHC.Integer.Type.Integer]"

      let Just sspanSig = getSrcSpan typeSig
      (showGhc sspanSig) `shouldBe` "test/testdata/DupDef/Dd1.hs:3:1-30"

      let (forest'',toksSig) = getTokensFor True forest' (gs2ss sspanSig)
      (GHC.showRichTokenStream toksSig) `shouldBe` "\n\n toplevel :: Integer -> Integer"

--
      let (fwithspan,_tree) = getSrcSpanFor forest'' (ghcSrcSpanToForestSpan l)

      -- (show fwithspan) `shouldBe` ""

      -- toks'' = placeToksForSpan fwithspan oldSpan tree pos toks
      let z = openZipperToSpan (ghcSrcSpanToForestSpan l) $ Z.fromTree fwithspan
      let prevToks = retrievePrevLineToks z
      (show prevToks) `shouldBe` "RT [((((4,18),(4,19)),ITvarid \"x\"),\"x\"),((((4,16),(4,17)),ITstar),\"*\"),((((4,14),(4,15)),ITvarid \"c\"),\"c\"),((((4,12),(4,13)),ITequal),\"=\"),((((4,10),(4,11)),ITvarid \"x\"),\"x\"),((((4,1),(4,9)),ITvarid \"toplevel\"),\"toplevel\"),((((4,1),(4,1)),ITsemi),\"\"),((((3,24),(3,31)),ITconid \"Integer\"),\"Integer\"),((((3,21),(3,23)),ITrarrow),\"->\"),((((3,13),(3,20)),ITconid \"Integer\"),\"Integer\"),((((3,10),(3,12)),ITdcolon),\"::\"),((((3,1),(3,9)),ITvarid \"toplevel\"),\"toplevel\"),((((3,1),(3,1)),ITvocurly),\"\"),((((1,19),(1,24)),ITwhere),\"where\"),((((1,8),(1,18)),ITqconid (\"DupDef\",\"Dd1\")),\"DupDef.Dd1\"),((((1,1),(1,7)),ITmodule),\"module\")]"
      let prevToks' = limitPrevToks prevToks (gs2ss l)
      (show prevToks') `shouldBe` "RT [((((4,18),(4,19)),ITvarid \"x\"),\"x\"),((((4,16),(4,17)),ITstar),\"*\"),((((4,14),(4,15)),ITvarid \"c\"),\"c\"),((((4,12),(4,13)),ITequal),\"=\"),((((4,10),(4,11)),ITvarid \"x\"),\"x\"),((((4,1),(4,9)),ITvarid \"toplevel\"),\"toplevel\"),((((4,1),(4,1)),ITsemi),\"\")]"

      let toks'2 = reIndentToks (PlaceOffset 2 0 0) (unReverseToks prevToks') toksSig
      (show toks'2) `shouldBe` "[((((6,1),(6,1)),ITvocurly),\"\"),((((6,1),(6,9)),ITvarid \"toplevel\"),\"toplevel\"),((((6,10),(6,12)),ITdcolon),\"::\"),((((6,13),(6,20)),ITconid \"Integer\"),\"Integer\"),((((6,21),(6,23)),ITrarrow),\"->\"),((((6,24),(6,31)),ITconid \"Integer\"),\"Integer\")]"
--
      -- typeSig'  <- putDeclToksAfterSpan l (head typeSig) (PlaceOffset 2 0 0) toksSig
      let (forest''',newSpan,_typeSig') = addDeclToksAfterSrcSpan forest'' l (PlaceOffset 2 0 0) toksSig (head typeSig) 
      -- typeSig'' <- renamePN n "tl1" True typeSig'
      -- (show forest''') `shouldBe` "" -- ++AZ++ : as expected

      (invariant forest''') `shouldBe` []
      (drawTreeEntry forest''') `shouldBe`
              "((1,1),(32,18))\n|\n"++
              "+- ((1,1),(3,31))\n|  |\n"++
              "|  +- ((1,1),(1,24))\n|  |\n"++
              "|  `- ((3,1),(3,31))\n|\n"++
              "+- ((4,1),(4,19))\n|\n"++
              "+- ((1000006,1),(1000006,31))\n|\n"++
              "`- ((6,1),(32,18))\n"

      (showGhc newSpan) `shouldBe` "foo:1048582:1-30"
      (showSrcSpanF newSpan) `shouldBe` "(((False,0,1,6),1),((False,0,1,6),31))"

      -- let (_forest4',_tree4) = getSrcSpanFor forest''' (ghcSrcSpanToForestSpan newSpan)
      -- (show forest4') `shouldBe` "" -- Broken, tokens for 1000006,31
                                    -- end at 6,20
      -- (show tree4) `shouldBe` ""

      let _forest4'' = insertSrcSpan forest''' (ghcSrcSpanToForestSpan newSpan)
      -- (show forest4'') `shouldBe` "" -- Broken, tokens for 1000006,31

      -- TODO: It seems the openZipperToSpan is the actual failure point
      let z1 = openZipperToSpan (ghcSrcSpanToForestSpan newSpan) $ Z.fromTree forest'''
      let _ztoks = retrieveTokensInterim $ Z.toTree z1
      -- (show $ Z.tree z) `shouldBe` "" -- Looks good


      let (forest4,toksSig1) = getTokensFor True forest''' (gs2ss newSpan)
      (invariant forest4) `shouldBe` []
      (drawTreeEntry forest4) `shouldBe`
              "((1,1),(32,18))\n|\n"++
              "+- ((1,1),(3,31))\n|  |\n"++
              "|  +- ((1,1),(1,24))\n|  |\n"++
              "|  `- ((3,1),(3,31))\n|\n"++
              "+- ((4,1),(4,19))\n|\n"++
              "+- ((1000006,1),(1000006,31))\n|\n"++
              "`- ((6,1),(32,18))\n"

      (GHC.showRichTokenStream toksSig1) `shouldBe` "\n\n\n\n\n toplevel :: Integer -> Integer"

      --
      let (((ForestLine _chs _trs vs _),_),(ForestLine _che _tre ve _,_)) = ghcSrcSpanToForestSpan newSpan

      let fl = (ForestLine True 0 1 6)
      (ghcLineToForestLine $ forestLineToGhcLine fl) `shouldBe` fl
      (forestLineToGhcLine fl) `shouldBe` 1074790406
      (hex $ forestLineToGhcLine fl) `shouldBe` "0x40100006"

      let (startPos,endPos) = ((6,1),(6,31))
      let tSpan = insertLenChangedInSrcSpan True False
                $ insertVersionsInSrcSpan vs ve $ gs2ss $ posToSrcSpan forest (startPos,endPos) 
      (showSrcSpanF $ ss2gs $ insertVersionsInSrcSpan vs ve $ gs2ss $ posToSrcSpan forest (startPos,endPos))
                                  `shouldBe` "(((False,0,1,6),1),((False,0,1,6),31))"
      (showSrcSpanF newSpan)      `shouldBe` "(((False,0,1,6),1),((False,0,1,6),31))"
      (showSrcSpanF $ ss2gs tSpan) `shouldBe` "(((True,0,1,6),1),((False,0,1,6),31))"

      (show (vs,ve)) `shouldBe` "(1,1)"
      let ((s1,_),_) =  ghcSrcSpanToForestSpan newSpan
      (hex $ forestLineToGhcLine s1) `shouldBe` "0x100006"
      -- let ((s,_),_e) = srcSpanToForestSpan tSpan
      let ((s,_),_e) = ss2f tSpan
      (hex $ forestLineToGhcLine s) `shouldBe`  "0x40100006"

      --

      let (forest5,_newSpan2,_) = updateTokensForSrcSpan forest4 (gs2ss newSpan) toksSig1
      (invariant forest5) `shouldBe` []
      (drawTreeEntry forest5) `shouldBe`
              "((1,1),(32,18))\n|\n"++
              "+- ((1,1),(3,31))\n|  |\n"++
              "|  +- ((1,1),(1,24))\n|  |\n"++
              "|  `- ((3,1),(3,31))\n|\n"++
              "+- ((4,1),(4,19))\n|\n"++
              "+- ((10001000006,1),(10001000006,31))\n|\n"++
              "`- ((6,1),(32,18))\n"


      let (_forest3,sspan) = addToksAfterSrcSpan forest' (gs2ss l) (PlaceOffset 2 0 2) toks'
      let _decl' = syncAST decl (ss2f sspan)

      "a" `shouldBe` "a"

    ------------------------------------

    it "replaces a name in a data declaration too" $ do
      (t, toks) <- parsedFileRenamingField1
      let renamed = fromJust $ GHC.tm_renamed_source t

      let Just (GHC.L l n) = locToName (5, 19) renamed
      let
        comp = do
         newName <- mkNewGhcName Nothing "pointx1"
         new <- renamePN n newName True False renamed

         return (new,newName)
      let

      ((nb,nn),s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- ((nb,nn),s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }
      (showGhc n) `shouldBe` "Field1.pointx"
      (showToks $ [newNameTok False l nn]) `shouldBe` "[((5,18),(5,25),\"pointx1\")]"
      (GHC.showRichTokenStream $ toks) `shouldBe` "module Field1 where\n\n --Rename field name 'pointx' to 'pointx1'\n\n data Point = Pt {pointx, pointy :: Float}\n\n absPoint :: Point -> Float\n absPoint p = sqrt (pointx p * pointx p +\n                   pointy p * pointy p)\n\n "
      (renderLines $ linesFromState s) `shouldBe` "module Field1 where\n\n--Rename field name 'pointx' to 'pointx1'\n\ndata Point = Pt {pointx1, pointy :: Float}\n\nabsPoint :: Point -> Float\nabsPoint p = sqrt (pointx1 p * pointx1 p +\n                  pointy p * pointy p)\n\n"
      (unspace $ showGhc nb) `shouldBe` unspace "(Field1.absPoint :: Field1.Point -> GHC.Types.Float\n Field1.absPoint p\n   = GHC.Float.sqrt\n       (pointx1 p GHC.Num.* pointx1 p\n        GHC.Num.+ Field1.pointy p GHC.Num.* Field1.pointy p)\n \n data Field1.Point\n   = Field1.Pt {pointx1 :: GHC.Types.Float,\n                Field1.pointy :: GHC.Types.Float},\n [import (implicit) Prelude],\n Nothing,\n Nothing)"


    ------------------------------------

    it "replaces a name in a type signature too" $ do
      (t, toks) <- parsedFileRenamingField1
      let renamed = fromJust $ GHC.tm_renamed_source t

      let Just (GHC.L l n) = locToName (5, 6) renamed
      let
        comp = do
         newName <- mkNewGhcName Nothing "NewPoint"
         new <- renamePN n newName True False renamed

         return (new,newName)
      let

      ((nb,nn),s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      (showGhc n) `shouldBe` "Field1.Point"
      (showToks $ [newNameTok False l nn]) `shouldBe` "[((5,6),(5,14),\"NewPoint\")]"
      (GHC.showRichTokenStream $ toks) `shouldBe` "module Field1 where\n\n --Rename field name 'pointx' to 'pointx1'\n\n data Point = Pt {pointx, pointy :: Float}\n\n absPoint :: Point -> Float\n absPoint p = sqrt (pointx p * pointx p +\n                   pointy p * pointy p)\n\n "
      (renderLines $ linesFromState s) `shouldBe` "module Field1 where\n\n--Rename field name 'pointx' to 'pointx1'\n\ndata NewPoint = Pt {pointx, pointy :: Float}\n\nabsPoint :: NewPoint -> Float\nabsPoint p = sqrt (pointx p * pointx p +\n                  pointy p * pointy p)\n\n"
      (unspace $ showGhc nb) `shouldBe` unspace "(Field1.absPoint :: NewPoint -> GHC.Types.Float\n Field1.absPoint p\n   = GHC.Float.sqrt\n       (Field1.pointx p GHC.Num.* Field1.pointx p\n        GHC.Num.+ Field1.pointy p GHC.Num.* Field1.pointy p)\n \n data NewPoint\n   = Field1.Pt {Field1.pointx :: GHC.Types.Float,\n                Field1.pointy :: GHC.Types.Float},\n [import (implicit) Prelude],\n Nothing,\n Nothing)"

    ------------------------------------

    it "replace a name in a FunBind with multiple patterns" $ do
      (t, toks) <- parsedFileGhc "./test/testdata/LocToName.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t

      let Just (GHC.L l n) = locToName (20, 1) renamed
      let
        comp = do
         newName <- mkNewGhcName Nothing "newPoint"
         new <- renamePN n newName True False renamed

         return (new,newName)
      let

      ((nb,nn),s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- ((nb,nn),s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }
      (showGhc n) `shouldBe` "LocToName.sumSquares"
      (showToks $ [newNameTok False l nn]) `shouldBe` "[((20,1),(20,9),\"newPoint\")]"
      (GHC.showRichTokenStream $ toks) `shouldBe` "module LocToName where\n\n {-\n\n\n\n\n\n\n\n\n-}\n\n\n\n\n\n\n\n sumSquares (x:xs) = x ^2 + sumSquares xs\n     -- where sq x = x ^pow \n     --       pow = 2\n\n sumSquares [] = 0\n "
      (renderLines $ linesFromState s) `shouldBe` "module LocToName where\n\n{-\n\n\n\n\n\n\n\n\n-}\n\n\n\n\n\n\n\nnewPoint (x:xs) = x ^2 + newPoint xs\n    -- where sq x = x ^pow \n    --       pow = 2\n\nnewPoint [] = 0\n"
      (unspace $ showGhc nb) `shouldBe` unspace "(newPoint (x : xs) = x GHC.Real.^ 2 GHC.Num.+ newPoint xs\n newPoint [] = 0,\n [import (implicit) Prelude],\n Nothing,\n Nothing)"

    ------------------------------------

    it "replaces a qualified name in a FunBind with multiple patterns" $ do
      (t, toks) <- parsedFileLocToName
      let renamed = fromJust $ GHC.tm_renamed_source t
      let modu = GHC.mkModule (GHC.stringToPackageId "mypackage-1.0") (GHC.mkModuleName "LocToName")

      let Just (GHC.L l n) = locToName (20, 1) renamed
      let
        comp = do
         newName <- mkNewGhcName (Just modu) "newPoint"
         new <- renamePN n newName True True renamed

         return (new,newName)

      ((nb,nn),s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- ((nb,nn),s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }
      (showGhc n) `shouldBe` "LocToName.sumSquares"
      (showToks $ [newNameTok False l nn]) `shouldBe` "[((20,1),(20,9),\"newPoint\")]"
      (GHC.showRichTokenStream $ toks) `shouldBe` "module LocToName where\n\n {-\n\n\n\n\n\n\n\n\n-}\n\n\n\n\n\n\n\n sumSquares (x:xs) = x ^2 + sumSquares xs\n     -- where sq x = x ^pow \n     --       pow = 2\n\n sumSquares [] = 0\n "
      -- (show $ layoutFromState s) `shouldBe` ""
      -- (showGhc $ retrieveTokensPpr $ fromJust $ layoutFromState s) `shouldBe` ""
      (renderLines $ linesFromState s) `shouldBe` "module LocToName where\n\n{-\n\n\n\n\n\n\n\n\n-}\n\n\n\n\n\n\n\nnewPoint (x:xs) = x ^2 + LocToName.newPoint xs\n    -- where sq x = x ^pow \n    --       pow = 2\n\nnewPoint [] = 0\n"
      (unspace $ showGhc nb) `shouldBe` unspace "(LocToName.newPoint (x : xs)\n = x GHC.Real.^ 2 GHC.Num.+ LocToName.newPoint xs\n LocToName.newPoint [] = 0,\n [import (implicit) Prelude],\n Nothing,\n Nothing)"


    ------------------------------------

    it "replaces a parameter name in a FunBind" $ do
      (t, toks) <- parsedFileGhc "./test/testdata/Renaming/LayoutIn2.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t

      let Just (GHC.L l n) = locToName (8, 7) renamed
      let
        comp = do
         logm $ "renamed:" ++ (SYB.showData SYB.Renamer 0 renamed)

         newName <- mkNewGhcName Nothing "ls"
         new <- renamePN n newName True True renamed

         return (new,newName)

      ((nb,nn),s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- ((nb,nn),s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }
      -- (showGhc n) `shouldBe` "list"
      -- (showGhc $ retrieveTokensPpr $ fromJust $ layoutFromState s) `shouldBe` ""
      (showToks $ [newNameTok False l nn]) `shouldBe` "[((8,7),(8,9),\"ls\")]"
      (GHC.showRichTokenStream $ toks) `shouldBe` "module LayoutIn2 where\n\n --Layout rule applies after 'where','let','do' and 'of'\n\n --In this Example: rename 'list' to 'ls'.\n\n silly :: [Int] -> Int\n silly list = case list of  (1:xs) -> 1\n --There is a comment\n                            (2:xs)\n                              | x < 10    -> 4  where  x = last xs\n                            otherwise -> 12\n\n "
      -- (showGhc $ sourceTreeFromState s) `shouldBe` ""
      (renderLines $ linesFromState s) `shouldBe` "module LayoutIn2 where\n\n--Layout rule applies after 'where','let','do' and 'of'\n\n--In this Example: rename 'list' to 'ls'.\n\nsilly :: [Int] -> Int\nsilly ls = case ls of  (1:xs) -> 1\n--There is a comment\n                       (2:xs)\n                         | x < 10    -> 4  where  x = last xs\n                       otherwise -> 12\n\n"
      (unspace $ showGhc nb) `shouldBe` unspace "(LayoutIn2.silly :: [GHC.Types.Int] -> GHC.Types.Int\n LayoutIn2.silly ls\n = case ls of {\n (1 : xs) -> 1\n (2 : xs)\n | x GHC.Classes.< 10 -> 4\n where\n x = GHC.List.last xs\n otherwise -> 12 },\n [import (implicit) Prelude],\n Nothing,\n Nothing)"


    ------------------------------------

    it "does not qualify a name in an import hiding clause" $ do
      (t,toks) <- parsedFileScopeAndQual
      let renamed = fromJust $ GHC.tm_renamed_source t
      let modu = GHC.mkModule (GHC.stringToPackageId "mypackage-1.0") (GHC.mkModuleName "LocToName")

      let Just (GHC.L l n) = locToName (4, 24) renamed
      let
        comp = do
         newName <- mkNewGhcName (Just modu) "mySum"
         new <- renamePN n newName True True renamed

         return (new,newName)

      ((nb,nn),s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- ((nb,nn),s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }
      (showGhc n) `shouldBe` "Data.List.sum"
      (showToks $ [newNameTok False l nn]) `shouldBe` "[((4,24),(4,29),\"mySum\")]"
      (GHC.showRichTokenStream $ toks) `shouldBe` "module ScopeAndQual where\n\n import qualified Data.List as L\n import Prelude hiding (sum)\n\n main :: IO ()\n main = putStrLn (show $ L.sum [1,2,3])\n\n sum a b = a + b\n\n sumSquares xs = L.sum $ map (\\x -> x*x) xs\n\n mySumSq = sumSquares\n "
      (renderLines $ linesFromState s) `shouldBe` "module ScopeAndQual where\n\nimport qualified Data.List as L\nimport Prelude hiding (mySum)\n\nmain :: IO ()\nmain = putStrLn (show $ L.mySum [1,2,3])\n\nsum a b = a + b\n\nsumSquares xs = L.mySum $ map (\\x -> x*x) xs\n\nmySumSq = sumSquares\n"
      (unspace $ showGhc nb) `shouldBe` unspace "(ScopeAndQual.main :: GHC.Types.IO ()\n ScopeAndQual.main\n = System.IO.putStrLn\n (GHC.Show.show GHC.Base.$ LocToName.mySum [1, 2, 3])\n ScopeAndQual.sum a b = a GHC.Num.+ b\n ScopeAndQual.sumSquares xs\n = LocToName.mySum GHC.Base.$ GHC.Base.map (\\ x -> x GHC.Num.* x) xs\n ScopeAndQual.mySumSq = ScopeAndQual.sumSquares,\n [import qualified Data.List as L,\n import Prelude hiding ( LocToName.mySum )],\n Nothing,\n Nothing)"


    ------------------------------------

    it "does not qualify the subject of a type signature" $ do
      (t,toks) <- parsedFileRenamingC7
      let renamed = fromJust $ GHC.tm_renamed_source t
      let modu = GHC.mkModule (GHC.stringToPackageId "mypackage-1.0") (GHC.mkModuleName "LocToName")

      let Just (GHC.L l n) = locToName (5, 1) renamed
      let
        comp = do
         logm $ "renamed:" ++ (SYB.showData SYB.Renamer 0 renamed)
         newName <- mkNewGhcName (Just modu) "myNewFringe"
         new <- renamePN n newName True True renamed

         return (new,newName)

      ((nb,nn),s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- ((nb,nn),s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }
      (showGhc n) `shouldBe` "Renaming.C7.myFringe"
      (showToks $ [newNameTok False l nn]) `shouldBe` "[((5,1),(5,12),\"myNewFringe\")]"
      (GHC.showRichTokenStream $ toks) `shouldBe` "module Renaming.C7(myFringe)  where\n\n import Renaming.D7\n\n myFringe:: Tree a -> [a]\n myFringe (Leaf x ) = [x]\n myFringe (Branch left right) = myFringe left ++ fringe right\n\n\n\n\n "
      (renderLines $ linesFromState s) `shouldBe` "module Renaming.C7(LocToName.myNewFringe)  where\n\nimport Renaming.D7\n\nmyNewFringe:: Tree a -> [a]\nmyNewFringe (Leaf x ) = [x]\nmyNewFringe (Branch left right) = LocToName.myNewFringe left ++ fringe right\n\n\n\n\n"
      (unspace $ showGhc nb) `shouldBe` unspace "(LocToName.myNewFringe :: Renaming.D7.Tree a -> [a]\n LocToName.myNewFringe (Renaming.D7.Leaf x) = [x]\n LocToName.myNewFringe (Renaming.D7.Branch left right)\n = LocToName.myNewFringe left GHC.Base.++ Renaming.D7.fringe right,\n [import (implicit) Prelude, import Renaming.D7],\n Just [LocToName.myNewFringe],\n Nothing)"

    ------------------------------------

    it "realigns toks in a case for a shorter name" $ do
      (t, toks) <- parsedFileLayoutIn2
      let renamed = fromJust $ GHC.tm_renamed_source t

      let Just (GHC.L l n) = locToName (8, 7) renamed
      let
        comp = do
         logm $ "renamed:" ++ (SYB.showData SYB.Renamer 0 renamed)

         newName <- mkNewGhcName Nothing "ls"
         new <- renamePN n newName True True renamed

         return (new,newName)

      ((nb,nn),s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- ((nb,nn),s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }
      (showGhc n) `shouldBe` "list"
      (showToks $ [newNameTok False l nn]) `shouldBe` "[((8,7),(8,9),\"ls\")]"
      (GHC.showRichTokenStream $ toks) `shouldBe` "module LayoutIn2 where\n\n --Layout rule applies after 'where','let','do' and 'of'\n\n --In this Example: rename 'list' to 'ls'.\n\n silly :: [Int] -> Int\n silly list = case list of  (1:xs) -> 1\n --There is a comment\n                            (2:xs)\n                              | x < 10    -> 4  where  x = last xs\n                            otherwise -> 12\n\n "
      (renderLines $ linesFromState s) `shouldBe` "module LayoutIn2 where\n\n--Layout rule applies after 'where','let','do' and 'of'\n\n--In this Example: rename 'list' to 'ls'.\n\nsilly :: [Int] -> Int\nsilly ls = case ls of  (1:xs) -> 1\n--There is a comment\n                       (2:xs)\n                         | x < 10    -> 4  where  x = last xs\n                       otherwise -> 12\n\n"
      (unspace $ showGhc nb) `shouldBe` unspace "(LayoutIn2.silly :: [GHC.Types.Int] -> GHC.Types.Int\n LayoutIn2.silly ls\n = case ls of {\n (1 : xs) -> 1\n (2 : xs)\n | x GHC.Classes.< 10 -> 4\n where\n x = GHC.List.last xs\n otherwise -> 12 },\n [import (implicit) Prelude],\n Nothing,\n Nothing)"



    ------------------------------------

    it "realigns toks in a case for a longer name" $ do
      (t, toks) <- parsedFileGhc "./test/testdata/Renaming/LayoutIn2.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t

      let Just (GHC.L l n) = locToName (8, 7) renamed
      let
        comp = do
         logm $ "renamed:" ++ (SYB.showData SYB.Renamer 0 renamed)

         newName <- mkNewGhcName Nothing "listlonger"
         new <- renamePN n newName True True renamed

         return (new,newName)

      ((nb,nn),s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- ((nb,nn),s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }
      (showGhc n) `shouldBe` "list"
      (showToks $ [newNameTok False l nn]) `shouldBe` "[((8,7),(8,17),\"listlonger\")]"
      (GHC.showRichTokenStream $ toks) `shouldBe` "module LayoutIn2 where\n\n --Layout rule applies after 'where','let','do' and 'of'\n\n --In this Example: rename 'list' to 'ls'.\n\n silly :: [Int] -> Int\n silly list = case list of  (1:xs) -> 1\n --There is a comment\n                            (2:xs)\n                              | x < 10    -> 4  where  x = last xs\n                            otherwise -> 12\n\n "
      -- (showGhc $ linesFromState s) `shouldBe` ""
      -- (showGhc $ sourceTreeFromState s) `shouldBe` ""
      (renderLines $ linesFromState s) `shouldBe` "module LayoutIn2 where\n\n--Layout rule applies after 'where','let','do' and 'of'\n\n--In this Example: rename 'list' to 'ls'.\n\nsilly :: [Int] -> Int\nsilly listlonger = case listlonger of  (1:xs) -> 1\n            --There is a comment\n                                       (2:xs)\n                                         | x < 10    -> 4  where  x = last xs\n                                       otherwise -> 12\n\n"
      (unspace $ showGhc nb) `shouldBe` unspace "(LayoutIn2.silly :: [GHC.Types.Int] -> GHC.Types.Int\n LayoutIn2.silly listlonger\n = case listlonger of {\n (1 : xs) -> 1\n (2 : xs)\n | x GHC.Classes.< 10 -> 4\n where\n x = GHC.List.last xs\n otherwise -> 12 },\n [import (implicit) Prelude],\n Nothing,\n Nothing)"


    ------------------------------------

    it "realigns toks in a do for a shorter name" $ do
      (t, toks) <- parsedFileGhc "./test/testdata/Renaming/LayoutIn4.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t

      let Just (GHC.L l n) = locToName (7, 8) renamed
      let
        comp = do
         logm $ "renamed:" ++ (SYB.showData SYB.Renamer 0 renamed)

         newName <- mkNewGhcName Nothing "io"
         new <- renamePN n newName True True renamed

         -- drawTokenTree "after renaming"

         return (new,newName)

      ((nb,nn),s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- ((nb,nn),s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }
      (showGhc n) `shouldBe` "ioFun"
      (showToks $ [newNameTok False l nn]) `shouldBe` "[((7,8),(7,10),\"io\")]"
      (GHC.showRichTokenStream $ toks) `shouldBe` "module LayoutIn4 where\n\n --Layout rule applies after 'where','let','do' and 'of'\n\n --In this Example: rename 'ioFun' to  'io'\n\n main = ioFun \"hello\" where ioFun s= do  let  k = reverse s\n  --There is a comment\n                                         s <- getLine\n                                         let  q = (k ++ s)\n                                         putStr q\n                                         putStr \"foo\"\n\n "
      -- (pprFromState s) `shouldBe` []
      (renderLines $ linesFromState s) `shouldBe` "module LayoutIn4 where\n\n--Layout rule applies after 'where','let','do' and 'of'\n\n--In this Example: rename 'ioFun' to  'io'\n\nmain = io \"hello\" where io s= do  let  k = reverse s\n--There is a comment\n                                  s <- getLine\n                                  let  q = (k ++ s)\n                                  putStr q\n                                  putStr \"foo\"\n\n"
      (unspace $ showGhc nb) `shouldBe` unspace "(LayoutIn4.main\n = io \"hello\"\n where\n io s\n = do { let k = GHC.List.reverse s;\n s <- System.IO.getLine;\n let q = (k GHC.Base.++ s);\n System.IO.putStr q;\n System.IO.putStr \"foo\" },\n [import (implicit) Prelude],\n Nothing,\n Nothing)"


    ------------------------------------

    it "realigns toks in a do for a longer name" $ do
      (t, toks) <- parsedFileLayoutIn4
      let renamed = fromJust $ GHC.tm_renamed_source t

      let Just (GHC.L l n) = locToName (7, 8) renamed
      let
        comp = do
         logm $ "renamed:" ++ (SYB.showData SYB.Renamer 0 renamed)

         newName <- mkNewGhcName Nothing "ioFunLong"
         new <- renamePN n newName True True renamed

         return (new,newName)

      ((nb,nn),s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- ((nb,nn),s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }
      (showGhc n) `shouldBe` "ioFun"
      (showToks $ [newNameTok False l nn]) `shouldBe` "[((7,8),(7,17),\"ioFunLong\")]"
      (GHC.showRichTokenStream $ toks) `shouldBe` "module LayoutIn4 where\n\n --Layout rule applies after 'where','let','do' and 'of'\n\n --In this Example: rename 'ioFun' to  'io'\n\n main = ioFun \"hello\" where ioFun s= do  let  k = reverse s\n  --There is a comment\n                                         s <- getLine\n                                         let  q = (k ++ s)\n                                         putStr q\n                                         putStr \"foo\"\n\n "
      (renderLines $ linesFromState s) `shouldBe` "module LayoutIn4 where\n\n--Layout rule applies after 'where','let','do' and 'of'\n\n--In this Example: rename 'ioFun' to  'io'\n\nmain = ioFunLong \"hello\" where ioFunLong s= do  let  k = reverse s\n         --There is a comment\n                                                s <- getLine\n                                                let  q = (k ++ s)\n                                                putStr q\n                                                putStr \"foo\"\n\n"
      (unspace $ showGhc nb) `shouldBe` unspace "(LayoutIn4.main\n = ioFunLong \"hello\"\n where\n ioFunLong s\n = do { let k = GHC.List.reverse s;\n s <- System.IO.getLine;\n let q = (k GHC.Base.++ s);\n System.IO.putStr q;\n System.IO.putStr \"foo\" },\n [import (implicit) Prelude],\n Nothing,\n Nothing)"

    ------------------------------------

    it "realigns toks in a where for a shorter name" $ do
      (t, toks) <- parsedFileLayoutIn1
      let renamed = fromJust $ GHC.tm_renamed_source t

      let Just (GHC.L l n) = locToName (7, 17) renamed
      let
        comp = do
         logm $ "renamed:" ++ (SYB.showData SYB.Renamer 0 renamed)

         newName <- mkNewGhcName Nothing "q"
         new <- renamePN n newName True True renamed

         return (new,newName)

      ((nb,nn),s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- ((nb,nn),s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }
      (showGhc n) `shouldBe` "sq"
      (showToks $ [newNameTok False l nn]) `shouldBe` "[((7,17),(7,18),\"q\")]"
      (GHC.showRichTokenStream $ toks) `shouldBe` "module LayoutIn1 where\n\n --Layout rule applies after 'where','let','do' and 'of'\n\n --In this Example: rename 'sq' to 'square'.\n\n sumSquares x y= sq x + sq y where sq x= x^pow\n   --There is a comment.\n                                   pow=2\n "
      (renderLines $ linesFromState s) `shouldBe` "module LayoutIn1 where\n\n--Layout rule applies after 'where','let','do' and 'of'\n\n--In this Example: rename 'sq' to 'square'.\n\nsumSquares x y= q x + q y where q x= x^pow\n--There is a comment.\n                                pow=2\n"
      (unspace $ showGhc nb) `shouldBe` unspace "(LayoutIn1.sumSquares x y\n = q x GHC.Num.+ q y\n where\n q x = x GHC.Real.^ pow\n pow = 2,\n [import (implicit) Prelude],\n Nothing,\n Nothing)"


    ------------------------------------

    it "realigns toks in a where for a longer name" $ do
      (t, toks) <- parsedFileGhc "./test/testdata/Renaming/LayoutIn1.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t

      let Just (GHC.L l n) = locToName (7, 17) renamed
      let
        comp = do
         logm $ "renamed:" ++ (SYB.showData SYB.Renamer 0 renamed)

         newName <- mkNewGhcName Nothing "square"
         new <- renamePN n newName True True renamed

         return (new,newName)

      ((nb,nn),s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- ((nb,nn),s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }
      (showGhc n) `shouldBe` "sq"
      (showToks $ [newNameTok False l nn]) `shouldBe` "[((7,17),(7,23),\"square\")]"
      (GHC.showRichTokenStream $ toks) `shouldBe` "module LayoutIn1 where\n\n --Layout rule applies after 'where','let','do' and 'of'\n\n --In this Example: rename 'sq' to 'square'.\n\n sumSquares x y= sq x + sq y where sq x= x^pow\n   --There is a comment.\n                                   pow=2\n "
      -- (pprFromState s) `shouldBe` []
      (renderLines $ linesFromState s) `shouldBe` "module LayoutIn1 where\n\n--Layout rule applies after 'where','let','do' and 'of'\n\n--In this Example: rename 'sq' to 'square'.\n\nsumSquares x y= square x + square y where square x= x^pow\n          --There is a comment.\n                                          pow=2\n"
      (unspace $ showGhc nb) `shouldBe` unspace "(LayoutIn1.sumSquares x y\n = square x GHC.Num.+ square y\n where\n square x = x GHC.Real.^ pow\n pow = 2,\n [import (implicit) Prelude],\n Nothing,\n Nothing)"

    ------------------------------------

    it "realigns toks in a let/in for a shorter name" $ do
      (t, toks) <- parsedFileLayoutLet1
      let renamed = fromJust $ GHC.tm_renamed_source t

      let Just (GHC.L l n) = locToName (6, 6) renamed
      let
        comp = do
         logm $ "renamed:" ++ (SYB.showData SYB.Renamer 0 renamed)

         newName <- mkNewGhcName Nothing "x"
         new <- renamePN n newName True True renamed

         return (new,newName)

      ((nb,nn),s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- ((nb,nn),s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }
      (showGhc n) `shouldBe` "xxx"
      (showToks $ [newNameTok False l nn]) `shouldBe` "[((6,5),(6,6),\"x\")]"
      (GHC.showRichTokenStream $ toks) `shouldBe` "module LayoutLet1 where\n\n -- Simple let expression, rename xxx to something longer or shorter\n -- and the let/in layout should adjust accordingly\n\n foo xxx = let a = 1\n               b = 2\n           in xxx + a + b\n\n "
      (renderLines $ linesFromState s) `shouldBe` "module LayoutLet1 where\n\n-- Simple let expression, rename xxx to something longer or shorter\n-- and the let/in layout should adjust accordingly\n\nfoo x = let a = 1\n            b = 2\n          in x + a + b\n\n"
      (unspace $ showGhc nb) `shouldBe` unspace "(LayoutLet1.foo x\n = let\n a = 1\n b = 2\n in x GHC.Num.+ a GHC.Num.+ b,\n [import (implicit) Prelude],\n Nothing,\n Nothing)"

    ------------------------------------

    it "realigns toks in a let/in for a longer name 1" $ do
      (t, toks) <- parsedFileGhc "./test/testdata/TypeUtils/LayoutLet1.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t

      let Just (GHC.L l n) = locToName (6, 6) renamed
      let
        comp = do
         logm $ "renamed:" ++ (SYB.showData SYB.Renamer 0 renamed)

         newName <- mkNewGhcName Nothing "xxxlong"
         new <- renamePN n newName True True renamed

         return (new,newName)

      ((nb,nn),s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- ((nb,nn),s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }
      (showGhc n) `shouldBe` "xxx"
      (showToks $ [newNameTok False l nn]) `shouldBe` "[((6,5),(6,12),\"xxxlong\")]"
      (GHC.showRichTokenStream $ toks) `shouldBe` "module LayoutLet1 where\n\n -- Simple let expression, rename xxx to something longer or shorter\n -- and the let/in layout should adjust accordingly\n\n foo xxx = let a = 1\n               b = 2\n           in xxx + a + b\n\n "
      -- (pprFromState s) `shouldBe` []
      (renderLines $ linesFromState s) `shouldBe` "module LayoutLet1 where\n\n-- Simple let expression, rename xxx to something longer or shorter\n-- and the let/in layout should adjust accordingly\n\nfoo xxxlong = let a = 1\n                  b = 2\n          in xxxlong + a + b\n\n"
      (unspace $ showGhc nb) `shouldBe` unspace "(LayoutLet1.foo xxxlong\n = let\n a = 1\n b = 2\n in xxxlong GHC.Num.+ a GHC.Num.+ b,\n [import (implicit) Prelude],\n Nothing,\n Nothing)"


    ------------------------------------

    it "realigns toks in a let/in for a longer name 2" $ do
      (t, toks) <- parsedFileGhc "./test/testdata/TypeUtils/LayoutLet2.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t

      let Just (GHC.L l n) = locToName (7, 6) renamed
      let
        comp = do
         logm $ "renamed:" ++ (SYB.showData SYB.Renamer 0 renamed)

         newName <- mkNewGhcName Nothing "xxxlong"
         new <- renamePN n newName True True renamed

         return (new,newName)

      ((nb,nn),s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- ((nb,nn),s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }
      (showGhc n) `shouldBe` "xxx"
      (showToks $ [newNameTok False l nn]) `shouldBe` "[((7,5),(7,12),\"xxxlong\")]"
      (GHC.showRichTokenStream $ toks) `shouldBe` "module LayoutLet2 where\n\n -- Simple let expression, rename xxx to something longer or shorter\n -- and the let/in layout should adjust accordingly\n -- In this case the tokens for xxx + a + b should also shift out\n\n foo xxx = let a = 1\n               b = 2 in xxx + a + b\n\n "
      -- (pprFromState s) `shouldBe` []
      (renderLines $ linesFromState s) `shouldBe` "module LayoutLet2 where\n\n-- Simple let expression, rename xxx to something longer or shorter\n-- and the let/in layout should adjust accordingly\n-- In this case the tokens for xxx + a + b should also shift out\n\nfoo xxxlong = let a = 1\n                  b = 2 in xxxlong + a + b\n\n"
      (unspace $ showGhc nb) `shouldBe` unspace "(LayoutLet2.foo xxxlong\n = let\n a = 1\n b = 2\n in xxxlong GHC.Num.+ a GHC.Num.+ b,\n [import (implicit) Prelude],\n Nothing,\n Nothing)"


  -- ---------------------------------------------

  describe "qualifyToplevelName" $ do
    it "qualifies a name at the top level, updating tokens" $ do
      (t, toks) <- parsedFileGhc "./test/testdata/Renaming/C7.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t

      let Just (GHC.L _l n) = locToName (7, 1) renamed
      let
        comp = do
         _new <- qualifyToplevelName n

         return ()
      let

      (_,s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      -- (_,s) <- runRefactGhc comp $ initialLogOnState { rsModule = initRefactModule t toks }
      (showGhc n) `shouldBe` "Renaming.C7.myFringe"
      (GHC.showRichTokenStream $ toks) `shouldBe` "module Renaming.C7(myFringe)  where\n\n import Renaming.D7\n\n myFringe:: Tree a -> [a]\n myFringe (Leaf x ) = [x]\n myFringe (Branch left right) = myFringe left ++ fringe right\n\n\n\n\n "
      -- (showGhc $ sourceTreeFromState s) `shouldBe` ""
      (renderLines $ linesFromState s) `shouldBe` "module Renaming.C7(Renaming.C7.myFringe)  where\n\nimport Renaming.D7\n\nmyFringe:: Tree a -> [a]\nmyFringe (Leaf x ) = [x]\nmyFringe (Branch left right) = Renaming.C7.myFringe left ++ fringe right\n\n\n\n\n"



  -- ---------------------------------------------

  describe "findEntity" $ do
    it "returns true if a (Located) Name is part of a HsBind 1" $ do
      let
        comp = do
         (t, toks) <- parseSourceFileTest "./test/testdata/DupDef/Dd1.hs"
         putParsedModule t toks
         parentr <- getRefactRenamed

         let mn = locToName (4,1) parentr
         let (Just (ln@(GHC.L _ n))) = mn

         let declsr = hsBinds parentr
             duplicatedDecls = definingDeclsNames [n] declsr True False

             res  = findEntity ln duplicatedDecls
             res2 = findEntity n duplicatedDecls
             -- res = findEntity' ln duplicatedDecls

         return (res,res2,duplicatedDecls,ln)
      ((r,r2,d,_l),_s) <- runRefactGhcState comp
      (showGhc d) `shouldBe` "[DupDef.Dd1.toplevel x = DupDef.Dd1.c GHC.Num.* x]"
      (showGhc _l) `shouldBe` "DupDef.Dd1.toplevel"
      ("1" ++ show r) `shouldBe` "1True"
      ("2" ++ show r2) `shouldBe` "2True"

    -- ---------------------------------

    it "returns true if a (Located) Name is part of a HsBind 2" $ do
      let
        comp = do
         (t, toks) <- parseSourceFileTest "./test/testdata/DupDef/Dd1.hs"
         putParsedModule t toks
         parentr <- getRefactRenamed

         let mn = locToName (31,7) parentr
         let (Just (ln@(GHC.L _ n))) = mn

         let mnd = locToName (30,1) parentr
         let (Just ((GHC.L _ nd))) = mnd

         let declsr = hsBinds parentr
             duplicatedDecls = definingDeclsNames [nd] declsr True False

             res = findEntity ln duplicatedDecls
             res2 = findEntity  n duplicatedDecls
             -- res = findEntity' ln duplicatedDecls

         return (res,res2,duplicatedDecls,ln)
      ((r,r2,d,_l),_s) <- runRefactGhcState comp
      (showGhc d) `shouldBe` "[DupDef.Dd1.dd q\n   = do { let ss = 5;\n"++
                             "          GHC.Base.return (ss GHC.Num.+ q) }]"
      (showGhc _l) `shouldBe` "ss"
      ("1" ++ show r) `shouldBe` "1True"
      ("2" ++ show r2) `shouldBe` "2True"


    -- -----------------------------------------------------------------

    it "returns false if a syntax phrase is not part of another" $ do
      let
        comp = do
         (t, toks) <- parseSourceFileTest "./test/testdata/DupDef/Dd1.hs"
         putParsedModule t toks
         parentr <- getRefactRenamed

         let mn = locToName (4,1) parentr
         let (Just (ln@(GHC.L _ n))) = mn

         let mltup = locToName (11,1) parentr
         let (Just ((GHC.L _ tup))) = mltup

         let declsr = hsBinds parentr
             duplicatedDecls = definingDeclsNames [n] declsr True False

             res = findEntity tup duplicatedDecls
             -- res = findEntity' ln duplicatedDecls

         return (res,duplicatedDecls,ln)
      ((r,d,_l),_s) <- runRefactGhcState comp
      (showGhc d) `shouldBe` "[DupDef.Dd1.toplevel x = DupDef.Dd1.c GHC.Num.* x]"
      -- (show l) `shouldBe` "foo"
      -- (show r) `shouldBe` "foo"
      ("1" ++ show r) `shouldBe` "1False"
      -- ("2" ++ show r2) `shouldBe` "2False"

    -- -----------------------------------------------------------------

    it "Finds an entity in [HsBind Name]" $ do
      pending -- "write this test"

    -- -----------------------------------------------------------------

    it "Finds an entity in (MatchGroup matches _)" $ do
      pending -- "write this test"

    -- -----------------------------------------------------------------

    it "Finds an entity in (HsLet decls _)" $ do
      pending -- "write this test"

    -- -----------------------------------------------------------------

    it "Finds an entity in (HsLet _ e1)" $ do
      pending -- "write this test"

    -- -----------------------------------------------------------------

    it "Finds an entity in (HsLet decls _)" $ do
      pending -- "write this test"

    -- -----------------------------------------------------------------

    it "Finds an entity in (PatBind pat rhs _ _ _)" $ do
      pending -- "write this test"

    -- -----------------------------------------------------------------

    it "Finds an entity in (Match _ _ rhs)" $ do
      pending -- "write this test"

    -- -----------------------------------------------------------------

    it "Finds an entity in (LetStmt binds)" $ do
      pending -- "write this test"

    -- -----------------------------------------------------------------

    it "Finds an entity in (BindStmt _ rhs _ _)" $ do
      pending -- "write this test"


  -- ---------------------------------------------

  describe "modIsExported" $ do
    it "Returns True if the module is explicitly exported" $ do
      -- ((_,_renamed,parsed), _toks) <- parsedFileDeclareGhc
      (t, _toks) <- parsedFileDeclareGhc
      let parsed = GHC.pm_parsed_source $ GHC.tm_parsed_module t
      let renamed = fromJust $ GHC.tm_renamed_source t
      let (Just (modName,_)) = getModuleName parsed

      (modIsExported modName renamed) `shouldBe` True

    it "Returns True if the module is exported by default" $ do
      -- ((_,_renamed,parsed), _toks) <- parsedFileDeclare1Ghc
      (t, _toks) <- parsedFileDeclare1Ghc
      let parsed = GHC.pm_parsed_source $ GHC.tm_parsed_module t
      let renamed = fromJust $ GHC.tm_renamed_source t
      let (Just (modName,_)) = getModuleName parsed

      (modIsExported modName renamed) `shouldBe` True

    it "Returns False if the module is explicitly not exported" $ do
      -- ((_,_renamed,parsed), _toks) <- parsedFileDeclare2Ghc
      (t, _toks) <- parsedFileDeclare2Ghc
      let parsed = GHC.pm_parsed_source $ GHC.tm_parsed_module t
      let renamed = fromJust $ GHC.tm_renamed_source t
      let (Just (modName,_)) = getModuleName parsed

      (modIsExported modName renamed) `shouldBe` False

  -- ---------------------------------------------

  describe "isExported" $ do
    it "Returns True if a GHC.Name is exported" $ do
      (t, toks) <- parsedFileRenamingB1

      let
        comp = do
         renamed <- getRefactRenamed

         let mn1 = locToName (11,1) renamed
         let (Just (GHC.L _ myFringe)) = mn1

         let mn2 = locToName (15,1) renamed
         let (Just (GHC.L _ sumSquares)) = mn2

         exMyFring <- isExported myFringe
         exSumSquares <- isExported sumSquares

         return (myFringe,exMyFring,sumSquares,exSumSquares)
      ((mf,emf,ss,ess),_s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }

      (showGhc mf) `shouldBe` "Renaming.B1.myFringe"
      emf `shouldBe` True
      (showGhc ss) `shouldBe` "Renaming.B1.sumSquares"
      ess `shouldBe` False

  -- ---------------------------------------------

  describe "addHiding" $ do
    it "Add a hiding entry to the imports with no existing hiding" $ do
      let
        comp = do

         (t1,_toks1)  <- parseSourceFileTest "./test/testdata/DupDef/Dd1.hs"
         clearParsedModule
         (t2, toks2) <- parseSourceFileTest "./test/testdata/DupDef/Dd2.hs"
         -- clearParsedModule
         let renamed1 = fromJust $ GHC.tm_renamed_source t1
         let renamed2 = fromJust $ GHC.tm_renamed_source t2

         let parsed1 = GHC.pm_parsed_source $ GHC.tm_parsed_module t1
         -- let parsed2 = GHC.pm_parsed_source $ GHC.tm_parsed_module t2

         let mn = locToName (4,1) renamed1
         let (Just (GHC.L _ _n)) = mn

         let Just (modName,_) = getModuleName parsed1
         n1   <- mkNewGhcName Nothing "n1"
         n2   <- mkNewGhcName Nothing "n2"
         res  <- addHiding modName renamed2 [n1,n2]
         toks <- fetchToks

         return (res,toks,renamed2,toks2)
      ((_r,t,_r2,_tk2),_s) <- runRefactGhcState comp
      (GHC.showRichTokenStream t) `shouldBe` "module DupDef.Dd2 where\n\n import DupDef.Dd1 hiding (n1,n2)\n\n\n f2 x = ff (x+1)\n\n mm = 5\n\n\n "

    ------------------------------------

    it "Adds a hiding entry to the imports with an existing hiding" $ do
      let
        comp = do

         (t1,_toks1)  <- parseSourceFileTest "./test/testdata/DupDef/Dd1.hs"
         clearParsedModule
         (t2, toks2) <- parseSourceFileTest "./test/testdata/DupDef/Dd3.hs"
         -- clearParsedModule
         let renamed1 = fromJust $ GHC.tm_renamed_source t1
         let renamed2 = fromJust $ GHC.tm_renamed_source t2

         let parsed1 = GHC.pm_parsed_source $ GHC.tm_parsed_module t1
         -- let parsed2 = GHC.pm_parsed_source $ GHC.tm_parsed_module t2

         let mn = locToName (4,1) renamed1
         let (Just (GHC.L _ _n)) = mn

         let Just (modName,_) = getModuleName parsed1
         n1   <- mkNewGhcName Nothing "n1"
         n2   <- mkNewGhcName Nothing "n2"
         res  <- addHiding modName renamed2 [n1,n2]
         toks <- fetchToks

         return (res,toks,renamed2,toks2)
      ((_r,t,_r2,_tk2),_s) <- runRefactGhcState comp
      (GHC.showRichTokenStream t) `shouldBe` "module DupDef.Dd3 where\n\n import DupDef.Dd1 hiding (dd,n1,n2)\n\n\n f2 x = ff (x+1)\n\n mm = 5\n\n\n "

  -- ---------------------------------------------

  describe "usedWithoutQualR" $ do
    it "Returns True if the identifier is used unqualified" $ do
      let
        comp = do
          (t, toks) <- parseSourceFileTest "./test/testdata/DupDef/Dd1.hs"
          putParsedModule t toks
          renamed <- getRefactRenamed
          parsed <- getRefactParsed

          let Just n@(GHC.L _ name) = locToName (14,21) renamed
          let res = usedWithoutQualR name parsed
          return (res,n,name)

      -- ((r,n1,n2),s) <- runRefactGhc comp $ initialState { rsTokenStream = toks }
      ((r,n1,n2),_s) <- runRefactGhcState comp

      (GHC.getOccString n2) `shouldBe` "zip"
      (showGhc n1) `shouldBe` "GHC.List.zip"
      r `shouldBe` True

    it "Returns False if the identifier is used qualified" $ do
      let
        comp = do
          (t, toks) <- parseSourceFileTest "./test/testdata/FreeAndDeclared/Declare.hs"
          putParsedModule t toks
          renamed <- getRefactRenamed
          parsed <- getRefactParsed

          let Just n@(GHC.L _ name) = locToName (36,12) renamed
          -- let PNT np@(GHC.L _ namep) = locToPNT (GHC.mkFastString "./test/testdata/FreeAndDeclared/Declare.hs") (36,12) parsed
          let Just (GHC.L _ namep) = locToRdrName (36,12) parsed
          let res = usedWithoutQualR name parsed
          return (res,namep,name,n)
      -- ((r,np,n1,n2),s) <- runRefactGhc comp $ initialState { rsTokenStream = toks }
      ((r,np,n1,n2),_s) <- runRefactGhcState comp

      (myShow np) `shouldBe` "Qual:G:gshow"
      (myShow $ GHC.getRdrName n1) `shouldBe` "Exact:Data.Generics.Text.gshow"
      -- (GHC.showRdrName $ GHC.getRdrName n1) `shouldBe` "Data.Generics.Text.gshow"
      (showGhc $ GHC.getRdrName n1) `shouldBe` "Data.Generics.Text.gshow"
      -- (showGhc $ GHC.occNameFS $ GHC.getOccName name) `shouldBe` "G.gshow"
      -- (GHC.getOccString name) `shouldBe` "G.gshow"
      (showGhc n2) `shouldBe` "Data.Generics.Text.gshow"
      r `shouldBe` False

  -- ---------------------------------------------

  describe "isExplicitlyExported" $ do
    it "Returns True if the identifier is explicitly exported" $ do
      pending -- "write this "

    it "Returns False if the identifier is not explicitly exported" $ do
      pending -- "write this "

  -- ---------------------------------------------

  describe "causeNameClashInExports" $ do
    it "Returns True if there is a clash" $ do

      (t, _toks) <- parsedFileGhc "./test/testdata/Renaming/ConflictExport.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t
      let parsed  = GHC.pm_parsed_source $ GHC.tm_parsed_module t

      let modu = GHC.ms_mod $ GHC.pm_mod_summary $ GHC.tm_parsed_module t

      -- Is this the right module?
      let Just (modName,_) = getModuleName parsed

      let Just (GHC.L _ myFringe) = locToName (9,1) renamed
      (showGhc myFringe) `shouldBe` "Renaming.ConflictExport.myFringe"

      -- old name is myFringe
      -- new name is "Renaming.ConflictExport.fringe"
      let newName = mkTestGhcName 1 (Just modu) "fringe"

      (showGhc modu) `shouldBe` "main:Renaming.ConflictExport"
      (showGhc newName) `shouldBe` "Renaming.ConflictExport.fringe"

      (showGhc $ GHC.localiseName newName) `shouldBe` "fringe"

      let res = causeNameClashInExports myFringe newName modName renamed
      res `shouldBe` True

    it "Returns False if there is no clash" $ do
      (t, _toks) <- parsedFileGhc "./test/testdata/Renaming/ConflictExport.hs"
      let renamed = fromJust $ GHC.tm_renamed_source t
      let parsed  = GHC.pm_parsed_source $ GHC.tm_parsed_module t

      let modu = GHC.ms_mod $ GHC.pm_mod_summary $ GHC.tm_parsed_module t

      -- Is this the right module?
      let Just (modName,_) = getModuleName parsed

      let Just (GHC.L _ myFringe) = locToName (9,1) renamed
      (showGhc myFringe) `shouldBe` "Renaming.ConflictExport.myFringe"

      -- old name is myFringe
      -- new name is "Renaming.ConflictExport.fringe"
      let newName = mkTestGhcName 1 (Just modu) "fringeOk"

      (showGhc modu) `shouldBe` "main:Renaming.ConflictExport"
      (showGhc newName) `shouldBe` "Renaming.ConflictExport.fringeOk"

      (showGhc $ GHC.localiseName newName) `shouldBe` "fringeOk"

      let res = causeNameClashInExports myFringe newName modName renamed
      res `shouldBe` False

  -- --------------------------------------

  describe "getDeclAndToks" $ do
    it "returns a declaration and its associated tokens" $ do
      let
        comp = do
          (t, toks) <- parseSourceFileTest "./test/testdata/MoveDef/Md1.hs"
          putParsedModule t toks
          renamed <- getRefactRenamed

          let Just n@(GHC.L _ name) = locToName (40,4) renamed
          let res = getDeclAndToks name True toks renamed
          return (res,n,name)

      (((d,t),n1,_n2),_s) <- runRefactGhcState comp
      -- (((d,t),n1,n2),s) <- runRefactGhcStateLog comp Debug
      (showGhc n1) `shouldBe` "MoveDef.Md1.tlFunc"
      (showGhc d) `shouldBe` "[MoveDef.Md1.tlFunc x = MoveDef.Md1.c GHC.Num.* x]"
      (show $ getStartEndLoc d) `shouldBe` "((40,1),(40,17))"
      -- (show $ startEndLocIncComments (toksFromState s) d) `shouldBe` "((40,1),(41,18))"
      (showToks t) `shouldBe` "[((40,0),(40,0),\"\"),((40,0),(40,6),\"tlFunc\"),((40,7),(40,8),\"x\"),((40,9),(40,10),\"=\"),((40,11),(40,12),\"c\"),((40,13),(40,14),\"*\"),((40,15),(40,16),\"x\"),((41,0),(41,17),\"-- Comment at end\")]"


  -- --------------------------------------
{-
This function is not used and has been removed
  describe "getDeclToks" $ do
    it "Returns a the tokens associated with a declaration" $ do
      let
        comp = do
          (t, toks) <- parseSourceFileTest "./test/testdata/Demote/D1.hs"
          putParsedModule t toks
          renamed <- getRefactRenamed

          let Just n@(GHC.L _ name) = locToName (GHC.mkFastString "./test/testdata/Demote/D1.hs") (9,1) renamed
          let res = getDeclToks name False (hsBinds renamed) toks
          return (res,n,name)

      ((dt,n1,n2),s) <- runRefactGhcState comp
      (showGhc n1) `shouldBe` "Demote.D1.sq"
      (showToks dt) `shouldBe` "[(((9,1),(9,1)),ITsemi,\"\"),(((9,1),(9,3)),ITvarid \"sq\",\"sq\"),(((9,4),(9,5)),ITvarid \"x\",\"x\"),(((9,6),(9,7)),ITequal,\"=\"),(((9,8),(9,9)),ITvarid \"x\",\"x\"),(((9,10),(9,11)),ITvarsym \"^\",\"^\"),(((9,11),(9,14)),ITvarid \"pow\",\"pow\")]"
-}

  -- ---------------------------------------

  describe "rmQualifier" $ do
    it "Removes the qualifiers from a list of identifiers in a given syntax phrase" $ do
      (t, toks) <- parsedFileWhereIn3Ghc
      let
        comp = do
          renamed <- getRefactRenamed

          let Just (GHC.L _ sq) = locToName (14, 1) renamed

          let ([sqDecl],_declToks) = getDeclAndToks sq True toks renamed

          res <- rmQualifier [sq] sqDecl
          return (res,sqDecl,sq)

      ((r,d,n1),_s) <- runRefactGhc comp $ initialState { rsModule = initRefactModule t toks }
      (showGhc n1) `shouldBe` "Demote.WhereIn3.sq"
      (showGhc d) `shouldBe` "Demote.WhereIn3.sq pow 0 = 0\nDemote.WhereIn3.sq pow z = z GHC.Real.^ pow"
      (showGhc r) `shouldBe` "sq pow 0 = 0\nsq pow z = z GHC.Real.^ pow"

    it "Removes the qualifiers and updates the tokens" $ do
      pending -- "Is this needed?"

  -- ---------------------------------------

  describe "usedByRhs" $ do
    it "Returns True if a given identifier is used in the RHS of a syntax element" $ do
      let
        comp = do
          (t, toks) <- parseSourceFileTest "./test/testdata/MoveDef/Demote.hs"
          putParsedModule t toks
          renamed <- getRefactRenamed

          let Just (GHC.L _ tl)   = locToName (4,1) renamed
          let Just (GHC.L _ name) = locToName (7,1) renamed
          let decls = (definingDeclsNames [tl] (hsBinds renamed) False False)
          decls' <- rmQualifier [name] decls

          -- let res = usedByRhs decls [name]
          let res = usedByRhs decls' [name]

          return (res,decls,tl,name)

      ((r,d,n1,n2),_s) <- runRefactGhcState comp
      (showGhc n1) `shouldBe` "MoveDef.Demote.toplevel"
      (showGhc n2) `shouldBe` "MoveDef.Demote.c"
      (showGhc d) `shouldBe` "[MoveDef.Demote.toplevel x = MoveDef.Demote.c GHC.Num.* x]"
      r `shouldBe` True

  -- ---------------------------------------

  describe "autoRenameLocalVar" $ do
    it "renames an identifier if it is used, no token update" $ do
      let
        comp = do
          (t, toks) <- parseSourceFileTest "./test/testdata/Demote/WhereIn4.hs"
          putParsedModule t toks
          renamed <- getRefactRenamed

          let Just (GHC.L _ tl)   = locToName (11,1) renamed
          let Just (GHC.L _ name) = locToName (11,21) renamed
          let decls = (definingDeclsNames [tl] (hsBinds renamed) False False)
          decls' <- autoRenameLocalVar False name decls

          return (decls',decls,tl,name)

      ((r,d,n1,n2),s) <- runRefactGhcState comp
      (showGhc n1) `shouldBe` "Demote.WhereIn4.sumSquares"
      (showGhc n2) `shouldBe` "p"
      (showGhc d) `shouldBe` "[Demote.WhereIn4.sumSquares x y\n   = Demote.WhereIn4.sq p x GHC.Num.+ Demote.WhereIn4.sq p y\n   where\n       p = 2]"
      (showGhc r) `shouldBe` "[Demote.WhereIn4.sumSquares x y\n   = Demote.WhereIn4.sq p_1 x GHC.Num.+ Demote.WhereIn4.sq p_1 y\n   where\n       p_1 = 2]"
      (renderLines $ linesFromState s) `shouldBe` "module Demote.WhereIn4 where\n\n--A definition can be demoted to the local 'where' binding of a friend declaration,\n--if it is only used by this friend declaration.\n\n--Demoting a definition narrows down the scope of the definition.\n--In this example, demote the top level 'sq' to 'sumSquares'\n--In this case (there is single matches), if possible,\n--the parameters will be folded after demoting and type sigature will be removed.\n\nsumSquares x y = sq p x + sq p y\n         where p=2  {-There is a comment-}\n\nsq::Int->Int->Int\nsq pow z = z^pow  --there is a comment\n\nanotherFun 0 y = sq y\n     where  sq x = x^2\n\n"


    it "renames an identifier if it is used and updates tokens" $ do
      let
        comp = do
          (t, toks) <- parseSourceFileTest "./test/testdata/Demote/WhereIn4.hs"
          putParsedModule t toks
          renamed <- getRefactRenamed

          let Just (GHC.L _ tl)   = locToName (11,1) renamed
          let Just (GHC.L _ name) = locToName (11,21) renamed
          let decls = (definingDeclsNames [tl] (hsBinds renamed) False False)
          decls' <- autoRenameLocalVar True name decls

          return (decls',decls,tl,name)

      ((r,d,n1,n2),s) <- runRefactGhcState comp
      (showGhc n1) `shouldBe` "Demote.WhereIn4.sumSquares"
      (showGhc n2) `shouldBe` "p"
      (showGhc d) `shouldBe` "[Demote.WhereIn4.sumSquares x y\n   = Demote.WhereIn4.sq p x GHC.Num.+ Demote.WhereIn4.sq p y\n   where\n       p = 2]"
      (showGhc r) `shouldBe` "[Demote.WhereIn4.sumSquares x y\n   = Demote.WhereIn4.sq p_1 x GHC.Num.+ Demote.WhereIn4.sq p_1 y\n   where\n       p_1 = 2]"
      (renderLines $ linesFromState s) `shouldBe` "module Demote.WhereIn4 where\n\n--A definition can be demoted to the local 'where' binding of a friend declaration,\n--if it is only used by this friend declaration.\n\n--Demoting a definition narrows down the scope of the definition.\n--In this example, demote the top level 'sq' to 'sumSquares'\n--In this case (there is single matches), if possible,\n--the parameters will be folded after demoting and type sigature will be removed.\n\nsumSquares x y = sq p_1 x + sq p_1 y\n         where p_1=2  {-There is a comment-}\n\nsq::Int->Int->Int\nsq pow z = z^pow  --there is a comment\n\nanotherFun 0 y = sq y\n     where  sq x = x^2\n\n"

  -- ---------------------------------------

  describe "mkNewName" $ do
    it "Makes a new name that does not clash with existing ones" $ do
      (mkNewName "f" ["f"] 0) `shouldBe` "f_1"
      (mkNewName "f" ["g"] 0) `shouldBe` "f"
      (mkNewName "f" ["g","f_1","f"] 0) `shouldBe` "f_2"

  -- ---------------------------------------

  describe "addImportDecl" $ do
    it "Add an import entry to a module with already existing, non conflicting imports and other declarations." $ do
      let
        comp = do

         -- (_t1,_toks1)  <- parseSourceFileTest "./test/testdata/DupDef/Dd1.hs"
         clearParsedModule
         (t2, toks2) <- parseSourceFileTest "./test/testdata/DupDef/Dd2.hs"
         -- clearParsedModule
         -- let renamed1 = fromJust $ GHC.tm_renamed_source t1
         let renamed2 = fromJust $ GHC.tm_renamed_source t2

         -- let parsed1 = GHC.pm_parsed_source $ GHC.tm_parsed_module t1

         let listModName  = GHC.mkModuleName "Data.List"
         -- n1   <- mkNewGhcName Nothing "n1"
         -- n2   <- mkNewGhcName Nothing "n2"
         res  <- addImportDecl renamed2 listModName Nothing False False False Nothing False [] 
         toks <- fetchToks

         return (res,toks,renamed2,toks2)
      ((_r,t,_r2,_tk2),_s) <- runRefactGhcState comp
      (GHC.showRichTokenStream t) `shouldBe` "module DupDef.Dd2 where\n\n import DupDef.Dd1\n import Data.List\n\n f2 x = ff (x+1)\n\n mm = 5\n\n\n "

    -- ---------------------------------

    it "adds an import entry to a module with some declaration, but no explicit imports." $ do
      let
        comp = do

         (t1,_toks1)  <- parseSourceFileTest "./test/testdata/TypeUtils/Simplest.hs"
         -- clearParsedModule
         let renamed1 = fromJust $ GHC.tm_renamed_source t1

         let listModName  = GHC.mkModuleName "Data.List"
         res  <- addImportDecl renamed1 listModName Nothing False False False Nothing False [] 
         toks <- fetchToks

         return (res,toks,renamed1,_toks1)
      ((_r,t,_r2,_tk2),_s) <- runRefactGhcState comp
      (GHC.showRichTokenStream t) `shouldBe` "module Simplest where\n import Data.List\n\n simple x = x\n "

    -- ---------------------------------

    it "adds an import entry to a module with explicit imports, but no declarations." $ do
      let
        comp = do

         (t1,_toks1)  <- parseSourceFileTest "./test/testdata/TypeUtils/JustImports.hs"
         -- clearParsedModule
         let renamed1 = fromJust $ GHC.tm_renamed_source t1

         let listModName  = GHC.mkModuleName "Data.List"
         res  <- addImportDecl renamed1 listModName Nothing False False False Nothing False [] 
         toks <- fetchToks

         return (res,toks,renamed1,_toks1)
      ((_r,t,_r2,_tk2),_s) <- runRefactGhcState comp
      (GHC.showRichTokenStream t) `shouldBe` "module JustImports where\n\n import Data.Maybe\n import Data.List"

    -- ---------------------------------

    it "adds an import entry to a module with no declarations and no explicit imports" $ do
      let
        comp = do

         (t1,toks1)  <- parseSourceFileTest "./test/testdata/TypeUtils/Empty.hs"
         putParsedModule t1 toks1
         renamed1 <- getRefactRenamed

         -- let renamed1 = fromJust $ GHC.tm_renamed_source t1

         let listModName  = GHC.mkModuleName "Data.List"
         res  <- addImportDecl renamed1 listModName Nothing False False False Nothing False [] 

         return (res,renamed1,toks1)
      ((_r,_r2,_tk2),s) <- runRefactGhcState comp
      -- ((_r,_r2,_tk2),s) <- runRefactGhcStateLog comp Debug

      (renderLines $ linesFromState s) `shouldBe` "module Empty where\nimport Data.List"


  -- ---------------------------------------

  describe "addItemsToImport" $ do
    it "adds an item to an import entry with no items" $ do
      let
        comp = do
         (t1,_toks1)  <- parseSourceFileTest "./test/testdata/TypeUtils/JustImports.hs"
         -- clearParsedModule
         let renamed1 = fromJust $ GHC.tm_renamed_source t1

         let modName  = GHC.mkModuleName "Data.Maybe"
         itemName <- mkNewGhcName Nothing "fromJust"

         res  <- addItemsToImport modName renamed1 [itemName]
         toks <- fetchToks

         return (res,toks,renamed1,_toks1)
      ((_r,_t,_r2,_tk2),s) <- runRefactGhcState comp
      -- ((_r,t,r2,tk2),s) <- runRefactGhcStateLog comp Debug

      -- This is the correct behavior. If the import doesn't have an import list, creating 
      -- one for an item effectively reduces the imported interface.
      (renderLines $ linesFromState s) `shouldBe` "module JustImports where\n\nimport Data.Maybe\n"
      -- (GHC.showRichTokenStream t) `shouldBe` "module JustImports where\n\n import Data.Maybe\n "

-- Not sure if this should be a test
{-    it "Try adding more than one item to an existing import entry with no items, using separate calls." $ do
      let
        comp = do
         (t1,_toks1)  <- parseSourceFileTest "./test/testdata/TypeUtils/JustImports.hs"
         -- clearParsedModule
         let renamed1 = fromJust $ GHC.tm_renamed_source t1

         let modName  = GHC.mkModuleName "Data.Maybe"
         itemName <- mkNewGhcName Nothing "fromJust"

         res  <- addItemsToImport modName renamed1 [itemName] --listModName Nothing False False False Nothing False [] 

         itemName2 <- mkNewGhcName Nothing "isJust"

         res2 <- addItemsToImport modName res [itemName2]
         toks <- fetchToks

         return (res2,toks,renamed,_toks1)
      ((_r,t,r2,tk2),s) <- runRefactGhcState comp
      (GHC.showRichTokenStream t) `shouldBe` "module JustImports where\n\n import Data.Maybe (fromJust,isJust)\n "
-}

    it "Add an item to an import entry with existing items." $ do
      let
        comp = do
         (t1,_toks1)  <- parseSourceFileTest "./test/testdata/TypeUtils/SelectivelyImports.hs"
         -- clearParsedModule
         let renamed1 = fromJust $ GHC.tm_renamed_source t1

         let modName  = GHC.mkModuleName "Data.Maybe"
         itemName <- mkNewGhcName Nothing "isJust"

         res  <- addItemsToImport modName renamed1 [itemName]
         toks <- fetchToks

         return (res,toks,renamed1,_toks1)
      ((_r,t,_r2,_tk2),_s) <- runRefactGhcState comp
      (GHC.showRichTokenStream t) `shouldBe` "module SelectivelyImports where\n\n import Data.Maybe (fromJust,isJust)\n\n __ = id\n "

{- -- test after properly inserting conditional identifier
    it "Add an item to an import entry with existing items, passing existing conditional identifier." $ do
      let
        comp = do
         (t1,_toks1)  <- parseSourceFileTest "./test/testdata/TypeUtils/SelectivelyImports.hs"
         -- clearParsedModule
         let renamed1 = fromJust $ GHC.tm_renamed_source t1

         let modName  = GHC.mkModuleName "Data.Maybe"
         itemName <- mkNewGhcName Nothing "isJust"
         conditionalId <- mkNewGhcName Nothing "fromJust"

         res  <- addItemsToImport modName renamed1 [itemName] (Just conditionalId) 
         toks <- fetchToks

         return (res,toks,renamed1,_toks1)
      ((_r,t,r2,tk2),s) <- runRefactGhcState comp
      (GHC.showRichTokenStream t) `shouldBe` "module SelectivelyImports where\n\n import Data.Maybe (fromJust,isJust)\n\n __ = id\n "

    it "Add an item to an import entry with existing items, passing missing conditional identifier" $ do
      let
        comp = do
         (t1,_toks1)  <- parseSourceFileTest "./test/testdata/TypeUtils/SelectivelyImports.hs"
         -- clearParsedModule
         let renamed1 = fromJust $ GHC.tm_renamed_source t1

         let modName  = GHC.mkModuleName "Data.Maybe"
         itemName <- mkNewGhcName Nothing "isJust"

         res  <- addItemsToImport modName renamed1 [itemName] (Just itemName)
         toks <- fetchToks

         return (res,toks,renamed1,_toks1)
      ((_r,t,r2,tk2),s) <- runRefactGhcState comp
      (GHC.showRichTokenStream t) `shouldBe` "module SelectivelyImports where\n\n import Data.Maybe (fromJust)\n\n __ = id\n "
-}

  -- ---------------------------------------

  describe "hsValBinds" $ do
    it "returns ValBinds for RenamedSource" $ do
      (t,_toks) <- parsedFileLiftOneD1Ghc
      let renamed = fromJust $ GHC.tm_renamed_source t
      let vb = hsValBinds renamed
      (showGhc vb) `shouldBe` "LiftOneLevel.D1.sumSquares (x : xs)\n  = sq x GHC.Num.+ LiftOneLevel.D1.sumSquares xs\n  where\n      sq x = x GHC.Real.^ pow\n      pow = 2\nLiftOneLevel.D1.sumSquares [] = 0\nLiftOneLevel.D1.main = LiftOneLevel.D1.sumSquares [1 .. 4]"

    -- ---------------------------------

    it "returns ValBinds for (HsGroup Name)" $ do
      (t,_toks) <- parsedFileLiftOneD1Ghc
      let (g,_,_,_) = fromJust $ GHC.tm_renamed_source t
      let vb = hsValBinds g
      (showGhc vb) `shouldBe` "LiftOneLevel.D1.sumSquares (x : xs)\n  = sq x GHC.Num.+ LiftOneLevel.D1.sumSquares xs\n  where\n      sq x = x GHC.Real.^ pow\n      pow = 2\nLiftOneLevel.D1.sumSquares [] = 0\nLiftOneLevel.D1.main = LiftOneLevel.D1.sumSquares [1 .. 4]"

  -- ---------------------------------------

  describe "stripLeadingSpaces" $ do
    it "Strips the longest common space prefix from a list of Strings" $ do
      (stripLeadingSpaces []) `shouldBe` []
      (stripLeadingSpaces ["a"," b","  c"]) `shouldBe` ["a"," b","  c"]
      (stripLeadingSpaces [" a"," b","  c"]) `shouldBe` ["a","b"," c"]

  -- ---------------------------------------

  describe "unspace" $ do
    it "Reduces all sequences of more than one space to a single one" $ do
      (unspace []) `shouldBe` []
      (unspace "a") `shouldBe` "a"
      (unspace "a bc") `shouldBe` "a bc"
      (unspace "a  bc") `shouldBe` "a bc"
      (unspace "ab   c") `shouldBe` "ab c"
      (unspace "  ab   c") `shouldBe` " ab c"
      (unspace "abc    ") `shouldBe` "abc "

  -- ---------------------------------------

  describe "isFieldName" $ do
    it "returns True if a Name is a field name" $ do
      (t,_toks) <- parsedFileRenamingField3
      let renamed = fromJust $ GHC.tm_renamed_source t
      let Just (GHC.L _ nf) = locToName (10,21) renamed
      let Just (GHC.L _ n) = locToName (10,1) renamed

      (showGhc n) `shouldBe` "Field3.absPoint"
      (showGhc nf) `shouldBe` "Field3.pointx"

      -- (show $ isFieldName nf) `shouldBe` "True"
      -- (show $ isFieldName n) `shouldBe` "False"

  -- ---------------------------------------

  describe "name predicates" $ do
    it "classifies names" $ do
      (t,_toks) <- parsedFileCon
      let renamed = fromJust $ GHC.tm_renamed_source t
      let Just (GHC.L _ n1) = locToName (3,6) renamed
      let Just (GHC.L _ n2) = locToName (3,12) renamed
      let Just (GHC.L _ n3) = locToName (3,16) renamed
      let Just (GHC.L _ n4) = locToName (5,1) renamed
      let Just (GHC.L _ n5) = locToName (8,5) renamed

      (showGhc n1) `shouldBe` "Main.Foo"
      "11" ++ (show $ GHC.isTyVarName n1)   `shouldBe` "11False"
      "12" ++ (show $ GHC.isTyConName n1)   `shouldBe` "12True"
      "13" ++ (show $ GHC.isDataConName n1) `shouldBe` "13False"
      "14" ++ (show $ GHC.isValName n1)     `shouldBe` "14False"
      "15" ++ (show $ GHC.isVarName n1)     `shouldBe` "15False"

      (showGhc n2) `shouldBe` "Main.Ff"
      "21" ++ (show $ GHC.isTyVarName n2)   `shouldBe` "21False"
      "22" ++ (show $ GHC.isTyConName n2)   `shouldBe` "22False"
      "23" ++ (show $ GHC.isDataConName n2) `shouldBe` "23True"
      "24" ++ (show $ GHC.isValName n2)     `shouldBe` "24True"
      "25" ++ (show $ GHC.isVarName n2)     `shouldBe` "25False"

      (showGhc n3) `shouldBe` "Main.fooA" -- field name
      "31" ++ (show $ GHC.isTyVarName n3)   `shouldBe` "31False"
      "32" ++ (show $ GHC.isTyConName n3)   `shouldBe` "32False"
      "33" ++ (show $ GHC.isDataConName n3) `shouldBe` "33False"
      "34" ++ (show $ GHC.isValName n3)     `shouldBe` "34True"
      "35" ++ (show $ GHC.isVarName n3)     `shouldBe` "35True"

      (showGhc n4) `shouldBe` "Main.xx"
      "41" ++ (show $ GHC.isTyVarName n4)   `shouldBe` "41False"
      "42" ++ (show $ GHC.isTyConName n4)   `shouldBe` "42False"
      "43" ++ (show $ GHC.isDataConName n4) `shouldBe` "43False"
      "44" ++ (show $ GHC.isValName n4)     `shouldBe` "44True"
      "45" ++ (show $ GHC.isVarName n4)     `shouldBe` "45True"

      (showGhc n5) `shouldBe` "GHC.Classes.=="
      "51" ++ (show $ GHC.isTyVarName n5)   `shouldBe` "51False"
      "52" ++ (show $ GHC.isTyConName n5)   `shouldBe` "52False"
      "53" ++ (show $ GHC.isDataConName n5) `shouldBe` "53False"
      "54" ++ (show $ GHC.isValName n5)     `shouldBe` "54True"
      "55" ++ (show $ GHC.isVarName n5)     `shouldBe` "55True"

      -- (show $ isFieldName n3) `shouldBe` "True"
      -- (show $ isFieldName n2) `shouldBe` "False"

  -- ---------------------------------------


myShow :: GHC.RdrName -> String
myShow n = case n of
  GHC.Unqual on  -> ("Unqual:" ++ (showGhc on))
  GHC.Qual ms on -> ("Qual:" ++ (showGhc ms) ++ ":" ++ (showGhc on))
  GHC.Orig ms on -> ("Orig:" ++ (showGhc ms) ++ ":" ++ (showGhc on))
  GHC.Exact en   -> ("Exact:" ++ (showGhc en))



-- ---------------------------------------------------------------------
-- Helper functions

-- conFileName :: GHC.FastString
-- conFileName = GHC.mkFastString "./test/testdata/Con.hs"

parsedFileCon :: IO (ParseResult,[PosToken])
parsedFileCon = parsedFileGhc "./test/testdata/Con.hs"


-- renamingField3FileName :: GHC.FastString
-- renamingField3FileName = GHC.mkFastString "./test/testdata/Renaming/Field3.hs"

parsedFileRenamingField3 :: IO (ParseResult,[PosToken])
parsedFileRenamingField3 = parsedFileGhc "./test/testdata/Renaming/Field3.hs"


-- renamingD5FileName :: GHC.FastString
-- renamingD5FileName = GHC.mkFastString "./test/testdata/Renaming/D5.hs"

parsedFileRenamingD5 :: IO (ParseResult,[PosToken])
parsedFileRenamingD5 = parsedFileGhc "./test/testdata/Renaming/D5.hs"


-- renamingC7FileName :: GHC.FastString
-- renamingC7FileName = GHC.mkFastString "./test/testdata/Renaming/C7.hs"

parsedFileRenamingC7 :: IO (ParseResult,[PosToken])
parsedFileRenamingC7 = parsedFileGhc "./test/testdata/Renaming/C7.hs"


-- locToNameFileName :: GHC.FastString
-- locToNameFileName = GHC.mkFastString "./test/testdata/LocToName.hs"

parsedFileLocToName :: IO (ParseResult,[PosToken])
parsedFileLocToName = parsedFileGhc "./test/testdata/LocToName.hs"


-- bFileName :: GHC.FastString
-- bFileName = GHC.mkFastString "./test/testdata/TypeUtils/B.hs"

parsedFileBGhc :: IO (ParseResult,[PosToken])
parsedFileBGhc = parsedFileGhc "./test/testdata/TypeUtils/B.hs"

-- sFileName :: GHC.FastString
-- sFileName = GHC.mkFastString "./test/testdata/TypeUtils/S.hs"

parsedFileSGhc :: IO (ParseResult,[PosToken])
parsedFileSGhc = parsedFileGhc "./test/testdata/TypeUtils/S.hs"


-- dd1FileName :: GHC.FastString
-- dd1FileName = GHC.mkFastString "./test/testdata/DupDef/Dd1.hs"

parsedFileDd1Ghc :: IO (ParseResult,[PosToken])
parsedFileDd1Ghc = parsedFileGhc "./test/testdata/DupDef/Dd1.hs"

parsedFileDd2Ghc :: IO (ParseResult,[PosToken])
parsedFileDd2Ghc = parsedFileGhc "./test/testdata/DupDef/Dd2.hs"

parsedFileDeclareGhc :: IO (ParseResult,[PosToken])
parsedFileDeclareGhc = parsedFileGhc "./test/testdata/FreeAndDeclared/Declare.hs"

parsedFileDeclareSGhc :: IO (ParseResult,[PosToken])
parsedFileDeclareSGhc = parsedFileGhc "./test/testdata/FreeAndDeclared/DeclareS.hs"

parsedFileDeclare1Ghc :: IO (ParseResult,[PosToken])
parsedFileDeclare1Ghc = parsedFileGhc "./test/testdata/FreeAndDeclared/Declare1.hs"

parsedFileDeclare2Ghc :: IO (ParseResult,[PosToken])
parsedFileDeclare2Ghc = parsedFileGhc "./test/testdata/FreeAndDeclared/Declare2.hs"

parsedFileDemoteGhc :: IO (ParseResult,[PosToken])
parsedFileDemoteGhc = parsedFileGhc "./test/testdata/MoveDef/Demote.hs"

-- demoteFileName :: GHC.FastString
-- demoteFileName = GHC.mkFastString "./test/testdata/MoveDef/Demote.hs"

parsedFileMd1Ghc :: IO (ParseResult,[PosToken])
parsedFileMd1Ghc = parsedFileGhc "./test/testdata/MoveDef/Md1.hs"

-- md1FileName :: GHC.FastString
-- md1FileName = GHC.mkFastString "./test/testdata/MoveDef/Md1.hs"

parsedFileMd2Ghc :: IO (ParseResult,[PosToken])
parsedFileMd2Ghc = parsedFileGhc "./test/testdata/MoveDef/Md2.hs"

-- md2FileName :: GHC.FastString
-- md2FileName = GHC.mkFastString "./test/testdata/MoveDef/Md2.hs"

-- -----------

-- parsedFileD1Ghc :: IO (ParseResult,[PosToken])
-- parsedFileD1Ghc = parsedFileGhc "./test/testdata/Demote/D1.hs"

-- d1FileName :: GHC.FastString
-- d1FileName = GHC.mkFastString "./test/testdata/Demote/D1.hs"

-- -----------

-- liftD1FileName :: GHC.FastString
-- liftD1FileName = GHC.mkFastString "./test/testdata/LiftToToplevel/D1.hs"

parsedFileLiftD1Ghc :: IO (ParseResult,[PosToken])
parsedFileLiftD1Ghc = parsedFileGhc "./test/testdata/LiftToToplevel/D1.hs"

-- -----------

-- liftOneD1FileName :: GHC.FastString
-- liftOneD1FileName = GHC.mkFastString "./test/testdata/LiftOneLevel/D1.hs"

parsedFileLiftOneD1Ghc :: IO (ParseResult,[PosToken])
parsedFileLiftOneD1Ghc = parsedFileGhc "./test/testdata/LiftOneLevel/D1.hs"

-- -----------

-- liftWhereIn1FileName :: GHC.FastString
-- liftWhereIn1FileName = GHC.mkFastString "./test/testdata/LiftToToplevel/WhereIn1.hs"

-- parsedFileLiftWhereIn1Ghc :: IO (ParseResult,[PosToken])
-- parsedFileLiftWhereIn1Ghc = parsedFileGhc "./test/testdata/LiftToToplevel/WhereIn1.hs"

-- -----------

-- liftWhereIn7FileName :: GHC.FastString
-- liftWhereIn7FileName = GHC.mkFastString "./test/testdata/LiftToToplevel/WhereIn7.hs"

parsedFileLiftWhereIn7Ghc :: IO (ParseResult,[PosToken])
parsedFileLiftWhereIn7Ghc = parsedFileGhc "./test/testdata/LiftToToplevel/WhereIn7.hs"

-- -----------

parsedFileWhereIn3Ghc :: IO (ParseResult,[PosToken])
parsedFileWhereIn3Ghc = parsedFileGhc "./test/testdata/Demote/WhereIn3.hs"

-- ----------------------------------------------------

parsedFileWhereIn4Ghc :: IO (ParseResult,[PosToken])
parsedFileWhereIn4Ghc = parsedFileGhc "./test/testdata/Demote/WhereIn4.hs"

-- ----------------------------------------------------

parsedFileTokenTestGhc :: IO (ParseResult,[PosToken])
parsedFileTokenTestGhc = parsedFileGhc "./test/testdata/TokenTest.hs"

-- ----------------------------------------------------

parsedFileTypeSigs :: IO (ParseResult, [PosToken])
parsedFileTypeSigs = parsedFileGhc "./test/testdata/TypeUtils/TypeSigs.hs"

-- ----------------------------------------------------

parsedFileAddParams1 :: IO (ParseResult, [PosToken])
parsedFileAddParams1 = parsedFileGhc "./test/testdata/AddParams1.hs"

-- ----------------------------------------------------

parsedFileRenamingField1 :: IO (ParseResult, [PosToken])
parsedFileRenamingField1 = parsedFileGhc "./test/testdata/Renaming/Field1.hs"

-- ----------------------------------------------------

parsedFileRenamingB1 :: IO (ParseResult, [PosToken])
parsedFileRenamingB1 = parsedFileGhc "./test/testdata/Renaming/B1.hs"

-- ----------------------------------------------------

parsedFileScopeAndQual :: IO (ParseResult, [PosToken])
parsedFileScopeAndQual = parsedFileGhc "./test/testdata/ScopeAndQual.hs"

-- ----------------------------------------------------

parsedFileLayoutIn2 :: IO (ParseResult, [PosToken])
parsedFileLayoutIn2 = parsedFileGhc "./test/testdata/Renaming/LayoutIn2.hs"

-- ----------------------------------------------------

parsedFileLayoutLet1 :: IO (ParseResult, [PosToken])
parsedFileLayoutLet1 = parsedFileGhc "./test/testdata/TypeUtils/LayoutLet1.hs"

-- ----------------------------------------------------
parsedFileLayoutIn1 :: IO (ParseResult, [PosToken])
parsedFileLayoutIn1 = parsedFileGhc "./test/testdata/Renaming/LayoutIn1.hs"

-- ----------------------------------------------------
parsedFileLayoutIn4 :: IO (ParseResult, [PosToken])
parsedFileLayoutIn4 = parsedFileGhc "./test/testdata/Renaming/LayoutIn4.hs"

-- ----------------------------------------------------
