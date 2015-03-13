module RenamingSpec (main, spec) where

import           Test.Hspec

import Language.Haskell.Refact.Refactoring.Renaming

import TestUtils

import System.Directory

-- import Language.Haskell.GhcMod

-- ---------------------------------------------------------------------

main :: IO ()
main = do
  hspec spec

spec :: Spec
spec = do

  describe "Renaming" $ do
    it "renames in D1 B1 C1 A1 6 6" $ do
     r <- rename (testSettingsMainfile "./test/testdata/Renaming/A1.hs") testCradle "./test/testdata/Renaming/D1.hs" "AnotherTree" (6,6)
     -- rename logTestSettings testCradle (Just "./test/testdata/Renaming/A1.hs") "./test/testdata/Renaming/D1.hs" "AnotherTree" (6,6)

     r' <- mapM makeRelativeToCurrentDirectory r

     r' `shouldBe` [ "./test/testdata/Renaming/D1.hs"
                  , "./test/testdata/Renaming/C1.hs"
                  , "test/testdata/Renaming/A1.hs"
                  , "./test/testdata/Renaming/B1.hs"
                  ]

     diffD <- compareFiles "./test/testdata/Renaming/D1.hs.expected"
                           "./test/testdata/Renaming/D1.refactored.hs"
     diffD `shouldBe` []

     diffC <- compareFiles "./test/testdata/Renaming/C1.hs.expected"
                           "./test/testdata/Renaming/C1.refactored.hs"
     diffC `shouldBe` []

     diffB <- compareFiles "./test/testdata/Renaming/B1.hs.expected"
                           "./test/testdata/Renaming/B1.refactored.hs"
     diffB `shouldBe` []

     diffA <- compareFiles "./test/testdata/Renaming/A1.hs.expected"
                           "./test/testdata/Renaming/A1.refactored.hs"
     diffA `shouldBe` []

    -- ---------------------------------

    it "renames in D2 B2 C2 A2 6 24" $ do
     r <- rename (testSettingsMainfile "./test/testdata/Renaming/A2.hs") testCradle "./test/testdata/Renaming/D2.hs" "SubTree" (6,24)
     -- rename logTestSettings testCradle (Just "./test/testdata/Renaming/A2.hs") "./test/testdata/Renaming/D2.hs" "SubTree" (6,24)

     r `shouldBe` [ "./test/testdata/Renaming/D2.hs"
                  , "./test/testdata/Renaming/C2.hs"
                  -- , "./test/testdata/Renaming/A2.hs"
                  , "./test/testdata/Renaming/B2.hs"
                  ]

     diffD <- compareFiles "./test/testdata/Renaming/D2.hs.expected"
                           "./test/testdata/Renaming/D2.refactored.hs"
     diffD `shouldBe` []

     diffC <- compareFiles "./test/testdata/Renaming/C2.hs.expected"
                           "./test/testdata/Renaming/C2.refactored.hs"
     diffC `shouldBe` []

     diffB <- compareFiles "./test/testdata/Renaming/B2.hs.expected"
                           "./test/testdata/Renaming/B2.refactored.hs"
     diffB `shouldBe` []

     -- diffA <- compareFiles "./test/testdata/Renaming/A2.hs.expected"
     --                       "./test/testdata/Renaming/A2.refactored.hs"
     -- diffA `shouldBe` []

    -- ---------------------------------

    it "renames in D3 B3 C3 A3 12 7" $ do
     --     (["D3.hs","B3.hs","C3.hs","A3.hs"],["Same","12","7"]),
     r <- rename (testSettingsMainfile "./test/testdata/Renaming/A3.hs") testCradle "./test/testdata/Renaming/D3.hs" "Same" (12,7)
     -- rename (logTestSettingsMainfile "./test/testdata/Renaming/A3.hs") testCradle "./test/testdata/Renaming/D3.hs" "Same" (12,7)

     r `shouldBe` [ "./test/testdata/Renaming/D3.hs"
                  , "./test/testdata/Renaming/C3.hs"
                  -- , "./test/testdata/Renaming/A3.hs"
                  , "./test/testdata/Renaming/B3.hs"
                  ]

     diffD <- compareFiles "./test/testdata/Renaming/D3.hs.expected"
                           "./test/testdata/Renaming/D3.refactored.hs"
     diffD `shouldBe` []

     diffC <- compareFiles "./test/testdata/Renaming/C3.hs.expected"
                           "./test/testdata/Renaming/C3.refactored.hs"
     diffC `shouldBe` []

     diffB <- compareFiles "./test/testdata/Renaming/B3.hs.expected"
                           "./test/testdata/Renaming/B3.refactored.hs"
     diffB `shouldBe` []

     -- diffA <- compareFiles "./test/testdata/Renaming/A3.hs.expected"
     --                       "./test/testdata/Renaming/A3.refactored.hs"
     -- diffA `shouldBe` []

    -- ---------------------------------

    it "renames in D4 B4 C4 A4 13 4" $ do
     --     (["D4.hs","B4.hs","C4.hs","A4.hs"],["isSameOrNot","13","4"]),
     r <- rename (testSettingsMainfile "./test/testdata/Renaming/A4.hs") testCradle "./test/testdata/Renaming/D4.hs" "isSameOrNot" (13,4)
     -- rename logTestSettings testCradle (Just "./test/testdata/Renaming/A4.hs") "./test/testdata/Renaming/D4.hs" "isSameOrNot" (13,4)

     r' <- mapM makeRelativeToCurrentDirectory r

     r' `shouldBe` [ "./test/testdata/Renaming/D4.hs"
                   , "./test/testdata/Renaming/C4.hs"
                   , "test/testdata/Renaming/A4.hs"
                   , "./test/testdata/Renaming/B4.hs"
                  ]

     diffD <- compareFiles "./test/testdata/Renaming/D4.hs.expected"
                           "./test/testdata/Renaming/D4.refactored.hs"
     diffD `shouldBe` []

     diffC <- compareFiles "./test/testdata/Renaming/C4.hs.expected"
                           "./test/testdata/Renaming/C4.refactored.hs"
     diffC `shouldBe` []

     diffB <- compareFiles "./test/testdata/Renaming/B4.hs.expected"
                           "./test/testdata/Renaming/B4.refactored.hs"
     diffB `shouldBe` []

     diffA <- compareFiles "./test/testdata/Renaming/A4.hs.expected"
                           "./test/testdata/Renaming/A4.refactored.hs"
     diffA `shouldBe` []

    -- ---------------------------------

    it "renames in D5 B5 C5 A5 24 1" $ do
     --     (["D5.hs","B5.hs","C5.hs","A5.hs"],["sum","24","1"]),
     r <- rename (testSettingsMainfile "./test/testdata/Renaming/A5.hs") testCradle "./test/testdata/Renaming/D5.hs" "sum" (24,1)
     -- rename (logTestSettingsMainfile "./test/testdata/Renaming/A5.hs") testCradle "./test/testdata/Renaming/D5.hs" "sum" (24,1)
     -- rename logTestSettings testCradle "./test/testdata/Renaming/D5.hs" "sum" (24,1)

     r' <- mapM makeRelativeToCurrentDirectory r

     r' `shouldBe` [ "./test/testdata/Renaming/D5.hs"
                   , "./test/testdata/Renaming/C5.hs"
                   , "test/testdata/Renaming/A5.hs"
                   , "./test/testdata/Renaming/B5.hs"
                   ]

     diffD <- compareFiles "./test/testdata/Renaming/D5.hs.expected"
                           "./test/testdata/Renaming/D5.refactored.hs"
     diffD `shouldBe` []

     diffC <- compareFiles "./test/testdata/Renaming/C5.hs.expected"
                           "./test/testdata/Renaming/C5.refactored.hs"
     diffC `shouldBe` []

     diffB <- compareFiles "./test/testdata/Renaming/B5.hs.expected"
                           "./test/testdata/Renaming/B5.refactored.hs"
     diffB `shouldBe` []

     diffA <- compareFiles "./test/testdata/Renaming/A5.hs.expected"
                           "./test/testdata/Renaming/A5.refactored.hs"
     diffA `shouldBe` []

    -- ---------------------------------

    it "renames in D7 C7  10 1" $ do
     --     (["D7.hs","C7.hs"],["myFringe","10","1"]),
     r <- rename (testSettingsMainfile "./test/testdata/Renaming/C7.hs") testCradle "./test/testdata/Renaming/D7.hs" "myFringe" (10,1)
     -- rename logTestSettings testCradle (Just "./test/testdata/Renaming/C7.hs") "./test/testdata/Renaming/D7.hs" "myFringe" (10,1)

     r' <- mapM makeRelativeToCurrentDirectory r
     r' `shouldBe` [ "./test/testdata/Renaming/D7.hs"
                   , "test/testdata/Renaming/C7.hs"
                   ]

     diffD <- compareFiles "./test/testdata/Renaming/D7.hs.expected"
                           "./test/testdata/Renaming/D7.refactored.hs"
     diffD `shouldBe` []

     diffC <- compareFiles "./test/testdata/Renaming/C7.hs.expected"
                           "./test/testdata/Renaming/C7.refactored.hs"
     diffC `shouldBe` []


    -- ---------------------------------

    it "renames in Field1 5 18" $ do
     r <- rename defaultTestSettings testCradle "./test/testdata/Renaming/Field1.hs" "pointx1" (5,18)
     -- rename logTestSettings testCradle Nothing "./test/testdata/Renaming/Field1.hs" "pointx1" (5,18)
     r `shouldBe` [ "./test/testdata/Renaming/Field1.hs"
                  ]
     diff <- compareFiles "./test/testdata/Renaming/Field1.hs.expected"
                          "./test/testdata/Renaming/Field1.refactored.hs"
     diff `shouldBe` []

    -- ---------------------------------

    it "renames in Field3 9 1" $ do
     r <- rename defaultTestSettings testCradle "./test/testdata/Renaming/Field3.hs" "abs" (9,1)
     -- rename logTestSettings testCradle Nothing "./test/testdata/Renaming/Field3.hs" "abs" (9,1)
     r `shouldBe` [ "./test/testdata/Renaming/Field3.hs"
                  ]
     diff <- compareFiles "./test/testdata/Renaming/Field3.hs.expected"
                          "./test/testdata/Renaming/Field3.refactored.hs"
     diff `shouldBe` []

    -- ---------------------------------

    it "renames in Field4 5 23" $ do
     --     (["Field4.hs"],["value2","5","23"]),
     r <- rename defaultTestSettings testCradle "./test/testdata/Renaming/Field4.hs" "value2" (5,23)
     -- rename logTestSettings Nothing "./test/testdata/Renaming/Field4.hs" "value2" (5,23)
     r `shouldBe` [ "./test/testdata/Renaming/Field4.hs"
                  ]
     diff <- compareFiles "./test/testdata/Renaming/Field4.hs.expected"
                          "./test/testdata/Renaming/Field4.refactored.hs"
     diff `shouldBe` []

    -- ---------------------------------

    it "renames in IdIn1 11 1" $ do
     --     (["IdIn1.hs"],["x1","11","1"]),
     r <- rename defaultTestSettings testCradle "./test/testdata/Renaming/IdIn1.hs" "x1" (11,1)
     -- rename logTestSettings Nothing "./test/testdata/Renaming/IdIn1.hs" "x1" (11,1)
     r `shouldBe` [ "./test/testdata/Renaming/IdIn1.hs"
                  ]
     diff <- compareFiles "./test/testdata/Renaming/IdIn1.hs.expected"
                          "./test/testdata/Renaming/IdIn1.refactored.hs"
     diff `shouldBe` []

    -- ---------------------------------

    it "renames in IdIn2 15 7" $ do
     --     (["IdIn2.hs"],["x1","15","7"]),
     r <- rename defaultTestSettings testCradle "./test/testdata/Renaming/IdIn2.hs" "x1" (15,7)
     -- rename logTestSettings testCradle Nothing "./test/testdata/Renaming/IdIn2.hs" "x1" (15,7)
     r `shouldBe` [ "./test/testdata/Renaming/IdIn2.hs"
                  ]
     diff <- compareFiles "./test/testdata/Renaming/IdIn2.hs.expected"
                          "./test/testdata/Renaming/IdIn2.refactored.hs"
     diff `shouldBe` []

    -- ---------------------------------

    it "renames in ClassIn1 7 7" $ do
     --     (["ClassIn1.hs"],["MyReversable","7","7"]),
     r <- rename defaultTestSettings testCradle "./test/testdata/Renaming/ClassIn1.hs" "MyReversable" (7,7)
     -- rename logTestSettings testCradle Nothing "./test/testdata/Renaming/ClassIn1.hs" "MyReversable" (7,7)
     r `shouldBe` [ "./test/testdata/Renaming/ClassIn1.hs"
                  ]
     diff <- compareFiles "./test/testdata/Renaming/ClassIn1.hs.expected"
                          "./test/testdata/Renaming/ClassIn1.refactored.hs"
     diff `shouldBe` []

    -- ---------------------------------

    it "renames in ClassIn2 8 3" $ do
     --     (["ClassIn2.hs"],["reversable","8","3"]),
     r <- rename defaultTestSettings testCradle "./test/testdata/Renaming/ClassIn2.hs" "reversable" (8,3)
     -- rename logTestSettings testCradle Nothing "./test/testdata/Renaming/ClassIn2.hs" "reversable" (8,3)
     r `shouldBe` [ "./test/testdata/Renaming/ClassIn2.hs"
                  ]
     diff <- compareFiles "./test/testdata/Renaming/ClassIn2.hs.expected"
                          "./test/testdata/Renaming/ClassIn2.refactored.hs"
     diff `shouldBe` []

    -- ---------------------------------

    it "renames in ConstructorIn1 8 6" $ do
     --     (["ConstructorIn1.hs"],["MyBTree","8","6"]),
     r <- rename defaultTestSettings testCradle "./test/testdata/Renaming/ConstructorIn1.hs" "MyBTree" (8,6)
     -- rename logTestSettings testCradle "./test/testdata/Renaming/ConstructorIn1.hs" "MyBTree" (8,6)
     r `shouldBe` [ "./test/testdata/Renaming/ConstructorIn1.hs"
                  ]
     diff <- compareFiles "./test/testdata/Renaming/ConstructorIn1.hs.expected"
                          "./test/testdata/Renaming/ConstructorIn1.refactored.hs"
     diff `shouldBe` []

    -- ---------------------------------

    it "renames in ConstructorIn2 8 6" $ do
     --     (["ConstructorIn2.hs"],["Tree","8","24"]),
     r <- rename defaultTestSettings testCradle "./test/testdata/Renaming/ConstructorIn2.hs" "Tree" (8,24)
     -- rename logTestSettings testCradle Nothing "./test/testdata/Renaming/ConstructorIn2.hs" "Tree" (8,24)
     r `shouldBe` [ "./test/testdata/Renaming/ConstructorIn2.hs"
                  ]
     diff <- compareFiles "./test/testdata/Renaming/ConstructorIn2.hs.expected"
                          "./test/testdata/Renaming/ConstructorIn2.refactored.hs"
     diff `shouldBe` []

    -- ---------------------------------

    it "renames in ConstructorIn3 9 12" $ do
     --     (["ConstructorIn3.hs"],["b","9","12"]),
     r <- rename defaultTestSettings testCradle "./test/testdata/Renaming/ConstructorIn3.hs" "b" (9,13)
     -- rename logTestSettings testCradle Nothing "./test/testdata/Renaming/ConstructorIn3.hs" "b" (9,13)
     r `shouldBe` [ "./test/testdata/Renaming/ConstructorIn3.hs"
                  ]
     diff <- compareFiles "./test/testdata/Renaming/ConstructorIn3.hs.expected"
                          "./test/testdata/Renaming/ConstructorIn3.refactored.hs"
     diff `shouldBe` []

    -- ---------------------------------

    it "renames in LayoutIn1 7 17" $ do
     --     (["LayoutIn1.hs"],["square","7","17"]),
     r <- rename defaultTestSettings testCradle "./test/testdata/Renaming/LayoutIn1.hs" "square" (7,17)
     -- rename logTestSettings testCradle "./test/testdata/Renaming/LayoutIn1.hs" "square" (7,17)
     r `shouldBe` [ "./test/testdata/Renaming/LayoutIn1.hs"
                  ]
     diff <- compareFiles "./test/testdata/Renaming/LayoutIn1.hs.expected"
                          "./test/testdata/Renaming/LayoutIn1.refactored.hs"
     diff `shouldBe` []

    -- ---------------------------------

    it "renames in LayoutIn2 8 7" $ do
     --     (["LayoutIn2.hs"],["ls","8","7"]),
     r <- rename defaultTestSettings testCradle "./test/testdata/Renaming/LayoutIn2.hs" "ls" (8,7)
     -- rename logTestSettings testCradle Nothing "./test/testdata/Renaming/LayoutIn2.hs" "ls" (8,7)
     r `shouldBe` [ "./test/testdata/Renaming/LayoutIn2.hs"
                  ]
     diff <- compareFiles "./test/testdata/Renaming/LayoutIn2.hs.expected"
                          "./test/testdata/Renaming/LayoutIn2.refactored.hs"
     diff `shouldBe` []

    -- ---------------------------------

    it "renames in LayoutIn3 7 13" $ do
     --     (["LayoutIn3.hs"],["anotherX","7","13"]),
     r <- rename defaultTestSettings testCradle "./test/testdata/Renaming/LayoutIn3.hs" "anotherX" (7,13)
     -- rename logTestSettings testCradle "./test/testdata/Renaming/LayoutIn3.hs" "anotherX" (7,13)
     r `shouldBe` [ "./test/testdata/Renaming/LayoutIn3.hs"
                  ]
     diff <- compareFiles "./test/testdata/Renaming/LayoutIn3.hs.expected"
                          "./test/testdata/Renaming/LayoutIn3.refactored.hs"
     diff `shouldBe` []

    -- ---------------------------------

    it "renames in LayoutIn4 7 8" $ do
     --     (["LayoutIn4.hs"],["io","7","8"])],
     r <- rename defaultTestSettings testCradle "./test/testdata/Renaming/LayoutIn4.hs" "io" (7,8)
     -- rename logTestSettings testCradle "./test/testdata/Renaming/LayoutIn4.hs" "io" (7,8)
     r `shouldBe` [ "./test/testdata/Renaming/LayoutIn4.hs"
                  ]
     diff <- compareFiles "./test/testdata/Renaming/LayoutIn4.hs.expected"
                          "./test/testdata/Renaming/LayoutIn4.refactored.hs"
     diff `shouldBe` []

    -- ---------------------------------
    -- Negative tests
    -- ---------------------------------

    it "naming clash at top level IdIn3" $ do
     -- (["IdIn3.hs"],["foo","10","1"]),
     -- rename logTestSettings testCradle Nothing "./test/testdata/Renaming/IdIn3.hs" "foo" (10,1)
     res <- catchException (rename defaultTestSettings testCradle "./test/testdata/Renaming/IdIn3.hs" "foo" (10,1))
     (show res) `shouldBe` "Just \"Name 'foo'  already existed\\n\""

    -- ---------------------------------

    it "upper case name for fn fails IdIn4" $ do
     --     (["IdIn4.hs"],["Foo","12","1"]),
     -- rename logTestSettings testCradle Nothing "./test/testdata/Renaming/IdIn4.hs" "Foo" (12,1)
     res <- catchException (rename defaultTestSettings testCradle "./test/testdata/Renaming/IdIn4.hs" "Foo" (12,1))
     (show res) `shouldBe` "Just \"The new name should be an identifier!\""

    -- ---------------------------------

    it "naming clash IdIn5" $ do
     --     (["IdIn5.hs"],["y","10","1"]),
     -- rename logTestSettings testCradle "./test/testdata/Renaming/IdIn5.hs" "y" (10,1)
     res <- catchException (rename defaultTestSettings testCradle "./test/testdata/Renaming/IdIn5.hs" "y" (10,1))
     (show res) `shouldBe` "Just \"Name 'y'  already existed, or rename 'IdIn5.x' to 'y' will change the program's semantics!\\n\""

    -- ---------------------------------

    it "must rename in home module ClassIn3" $ do
     --     (["ClassIn3.hs"],["Eq1","16","10"]),
     -- rename logTestSettings testCradle Nothing "./test/testdata/Renaming/ClassIn3.hs" "Eq1" (16,10)
     res <- catchException (rename defaultTestSettings testCradle "./test/testdata/Renaming/ClassIn3.hs" "Eq1" (16,10))
     (show res) `shouldBe` "Just \"This identifier is defined in module GHC.Classes, please do renaming in that module!\""

    -- ---------------------------------

    it "will not rename existing name Field2" $ do
     --     (["Field2.hs"], ["absPoint", "5", "18"]),
     -- rename logTestSettings testCradle Nothing "./test/testdata/Renaming/Field2.hs" "absPoint" (5,18)
     res <- catchException (rename defaultTestSettings testCradle "./test/testdata/Renaming/Field2.hs" "absPoint" (5,18))
     (show res) `shouldBe` "Just \"Name 'absPoint'  already existed\\n\""

    -- ---------------------------------

    it "must qualify clashes Qualifier" $ do
     --     (["Qualifier.hs"],["sum","13","1"]),
     -- rename logTestSettings testCradle "./test/testdata/Renaming/Qualifier.hs" "sum" (13,1)
     res <- catchException (rename defaultTestSettings testCradle "./test/testdata/Renaming/Qualifier.hs" "sum" (13,1))
     (show res) `shouldBe` "Just \"The new name will cause ambiguous occurrence problem, please select another new name or qualify the use of ' sum' before renaming!\\n\""

    -- ---------------------------------

    it "cannot rename main Main" $ do
     --     (["Main.hs"],["main1", "11","1"]),
     -- rename logTestSettings testCradle Nothing "./test/testdata/Renaming/Main.hs" "main1" (11,1)
     res <- catchException (rename defaultTestSettings testCradle "./test/testdata/Renaming/Main.hs" "main1" (11,1))
     (show res) `shouldBe` "Just \"The 'main' function defined in a 'Main' module should not be renamed!\""

    -- ---------------------------------

    it "cannot rename main Main2" $ do
     -- rename logTestSettings testCradle Nothing "./test/testdata/Renaming/Main2.hs" "main1" (4,1)
     res <- catchException (rename defaultTestSettings testCradle "./test/testdata/Renaming/Main2.hs" "main1" (4,1))
     (show res) `shouldBe` "Just \"The 'main' function defined in a 'Main' module should not be renamed!\""

    -- ---------------------------------

    it "rename with default main Main2" $ do
     -- rename logTestSettings testCradle Nothing "./test/testdata/Renaming/Main2.hs" "baz" (6,1)
     r <- rename defaultTestSettings testCradle "./test/testdata/Renaming/Main2.hs" "baz" (6,1)

     r `shouldBe` [ "./test/testdata/Renaming/Main2.hs"
                  ]
     diff <- compareFiles "./test/testdata/Renaming/Main2.hs.expected"
                          "./test/testdata/Renaming/Main2.refactored.hs"
     diff `shouldBe` []

    -- ---------------------------------

    it "rename in a do statement" $ do
     -- rename logTestSettings testCradle "./test/testdata/Layout/Do1.hs" "g2" (10,3)
     r <- rename defaultTestSettings testCradle "./test/testdata/Layout/Do1.hs" "g2" (10,3)

     r `shouldBe` [ "./test/testdata/Layout/Do1.hs"
                  ]
     diff <- compareFiles "./test/testdata/Layout/Do1.hs.expected"
                          "./test/testdata/Layout/Do1.refactored.hs"
     diff `shouldBe` []

    -- ---------------------------------

    it "renames in QualServer QualClient" $ do
     r <- rename (testSettingsMainfile "./test/testdata/Renaming/QualClient.hs") testCradle "./test/testdata/Renaming/QualServer.hs" "foo1" (11,1)
     -- rename (logTestSettingsMainfile "./test/testdata/Renaming/QualClient.hs") testCradle "./test/testdata/Renaming/QualServer.hs" "foo1" (11,1)

     r' <- mapM makeRelativeToCurrentDirectory r
     r' `shouldBe` ["./test/testdata/Renaming/QualServer.hs",
                    "test/testdata/Renaming/QualClient.hs"
                  ]

     diffD <- compareFiles "./test/testdata/Renaming/QualServer.expected.hs"
                           "./test/testdata/Renaming/QualServer.refactored.hs"
     diffD `shouldBe` []

     diffC <- compareFiles "./test/testdata/Renaming/QualClient.expected.hs"
                           "./test/testdata/Renaming/QualClient.refactored.hs"
     diffC `shouldBe` []

    -- ---------------------------------

{-
    it "rename gives noRebindableInfo MoveDef" $ do
     -- rename logTestSettings testCradle "./src/Language/Haskell/Refact/MoveDef.hs" "t2" (1105,20)
     r <- rename defaultTestSettings (testCradle { cradleCabalDir = Just ".", cradleCabalFile = Just "HaRe.cabal"}) "./src/Language/Haskell/Refact/MoveDef.hs" "t2" (1105,20)

     r `shouldBe` [ "./test/testdata/Renaming/Main2.hs"
                  ]
     diff <- compareFiles "./test/testdata/Renaming/Main2.hs.expected"
                          "./test/testdata/Renaming/Main2.refactored.hs"
     diff `shouldBe` []
-}

    -- ---------------------------------

    it "ConflictExports" $ do
     --     (["ConflictExport.hs","D6.hs"],["fringe","7","1"])]
     -- rename (logTestSettingsMainfile "./test/testdata/Renaming/ConflictExport.hs") testCradle "./test/testdata/Renaming/ConflictExport.hs" "fringe" (7,1)
     res <- catchException (rename (testSettingsMainfile "./test/testdata/Renaming/ConflictExport.hs") testCradle "./test/testdata/Renaming/ConflictExport.hs" "fringe" (7,1))
     (show res) `shouldBe` "Just \"The new name will cause conflicting exports, please select another new name!\""

{-
TestCases{refactorCmd="rename",
positive=[
          (["D1.hs","B1.hs","C1.hs","A1.hs"],["AnotherTree", "6", "6"]),
          (["D2.hs","B2.hs","C2.hs","A2.hs"],["SubTree" , "6", "24"]),
          (["D3.hs","B3.hs","C3.hs","A3.hs"],["Same","12","7"]),
          (["D4.hs","B4.hs","C4.hs","A4.hs"],["isSameOrNot","13","4"]),
          (["D5.hs","B5.hs","C5.hs","A5.hs"],["sum","24","1"]),
          (["D7.hs","C7.hs"],["myFringe","10","1"]),
          (["Field1.hs"],["pointx1","5","18"]),
          (["Field3.hs"],["abs", "9","1"]),
          (["Field4.hs"],["value2","5","23"]),
          (["IdIn1.hs"],["x1","11","1"]),
          (["IdIn2.hs"],["x1","15","7"]),
          (["ClassIn1.hs"],["MyReversable","7","7"]),
          (["ClassIn2.hs"],["reversable","8","3"]),
          (["ConstructorIn1.hs"],["MyBTree","8","6"]),
          (["ConstructorIn2.hs"],["Tree","8","24"]),
          (["ConstructorIn3.hs"],["b","9","12"]),
          (["LayoutIn1.hs"],["square","7","17"]),
          (["LayoutIn2.hs"],["ls","8","7"]),
          (["LayoutIn3.hs"],["anotherX","7","13"]),
          (["LayoutIn4.hs"],["io","7","8"])],
negative=[(["IdIn3.hs"],["foo","10","1"]),
          (["IdIn4.hs"],["Foo","12","1"]),
          (["IdIn5.hs"],["y","10","1"]),
          (["ClassIn3.hs"],["Eq1","16","10"]),
          (["Field2.hs"], ["absPoint", "5", "18"]),
          (["Qualifier.hs"],["sum","13","1"]),
          (["Main.hs"],["main1", "11","1"]),
          (["ConflictExport.hs","D6.hs"],["fringe","7","1"])]
}
-}

    -- ---------------------------------

    it "rename preserving layout Utils.hs" $ do
     -- rename logTestSettings testCradle "./test/testdata/Renaming/Utils.hs" "parsed1" (5,11)
     r <- rename defaultTestSettings testCradle "./test/testdata/Renaming/Utils.hs" "parsed1" (5,11)

     r `shouldBe` [ "./test/testdata/Renaming/Utils.hs"
                  ]
     diff <- compareFiles "./test/testdata/Renaming/Utils.expected.hs"
                          "./test/testdata/Renaming/Utils.refactored.hs"
     diff `shouldBe` []

    -- -----------------------------------------------------------------

    it "passes RenameInExportedType.hs 1" $ do
     r <- rename defaultTestSettings testCradle "./test/testdata/Renaming/RenameInExportedType.hs" "NewType" (6,6)
     -- rename logTestSettings testCradle "./test/testdata/Renaming/RenameInExportedType.hs" "NewType" (6,6)

     (show r) `shouldBe` "[\"./test/testdata/Renaming/RenameInExportedType.hs\"]"
     diff <- compareFiles "./test/testdata/Renaming/RenameInExportedType.refactored.hs"
                          "./test/testdata/Renaming/RenameInExportedType.expected.hs"
     diff `shouldBe` []

    -- -----------------------------------------------------------------

    it "passes RenameInExportedType2.hs" $ do
     r <- rename defaultTestSettings testCradle "./test/testdata/Renaming/RenameInExportedType2.hs" "NewType" (6,24)
     -- rename logTestSettings testCradle "./test/testdata/Renaming/RenameInExportedType2.hs" "NewType" (6,24)

     (show r) `shouldBe` "[\"./test/testdata/Renaming/RenameInExportedType2.hs\"]"
     diff <- compareFiles "./test/testdata/Renaming/RenameInExportedType2.refactored.hs"
                          "./test/testdata/Renaming/RenameInExportedType2.expected.hs"
     diff `shouldBe` []



-- ---------------------------------------------------------------------
-- Helper functions

