{-# LANGUAGE ScopedTypeVariables #-}
module HaskellGhcParser where

-- container
import Data.Tree (Tree(Node,rootLabel),drawTree)

-- syb
import Data.Generics (Data)

-- base
import Unsafe.Coerce (unsafeCoerce)


import Data.Generics
import qualified Data.Generics.Schemes as SYB
import qualified Data.Generics.Aliases as SYB
import qualified GHC.SYB.Utils         as SYB

import qualified Bag                   as GHC
import qualified DynFlags              as GHC
import qualified ErrUtils              as GHC
import qualified FastString            as GHC
import qualified GHC
import qualified GHC.Paths             as GHC
import qualified MonadUtils            as GHC
import qualified NameSet               as GHC
import qualified OccName               as GHC
import qualified Outputable            as GHC
import qualified SrcLoc                as GHC
import qualified Var                   as GHC

import GHC.Paths ( libdir )
import System.IO.Unsafe


-- local imports
import Language.Astview.Parser as Astview
import Language.Astview.DataTree
import Data.Tree (Tree(Node,rootLabel))

import Language.Haskell.Exts (parseFileContents)
import Language.Haskell.Exts.Parser (ParseResult(ParseOk))
import Language.Haskell.Exts.Syntax (Module)
import Data.List

haskellghc = Parser "Haskell" [".hs"] buildTreeHaskellGhc

buildTreeHaskellGhc :: String -> Tree String
buildTreeHaskellGhc s = case parseHaskellGhc s of
     Right ast -> flat $ data2treeGhc (ast::GHC.Located (GHC.HsModule GHC.RdrName))
     -- Right ast -> flat $ data2tree (ast::GHC.Located (GHC.HsModule GHC.RdrName))
     Left ParseError -> Node "ParseError" []

-- parseHaskellGhc :: (Data a) => String -> Either ParseError a
parseHaskellGhc :: String -> Either ParseError (GHC.Located (GHC.HsModule GHC.RdrName))
parseHaskellGhc s = case (foo s) of
    -- Right (_,p)  -> unsafeCoerce $ Right p
    Right (_,p)  -> Right p
    Left err -> Left ParseError


-- | Trealise Data to Tree (from SYB 2, sec. 3.4 )
--   bearing in mind the GHC parser stage holes
data2treeGhc :: Data a => a -> Tree String
data2treeGhc = data2treeGhcStaged SYB.Parser 0
-- data2treeGhc = data2tree


-- | Generic Data-based show, with special cases for GHC Ast types,
--   and simplistic indentation-based layout (the 'Int' parameter); 
--   showing abstract types abstractly and avoiding known potholes 
--   (based on the 'Stage' that generated the Ast)
-- data2treeGhcStaged stage n = const (Node "foo" [])
{-
data2treeGhcStaged :: Data a => SYB.Stage -> a -> Tree String
-- showData :: Data a => Stage -> Int -> a -> String
data2treeGhcStaged stage n = 
  {- generic 
          `ext1Q` list 
          `extQ` string 
          `extQ` fastString 
          `extQ` srcSpan 
          `extQ` name `extQ` occName `extQ` moduleName `extQ` var `extQ` dataCon
          `extQ` bagName `extQ` bagRdrName `extQ` bagVar 
          -}
   {- (gdefault n)
          `ext1Q` -}
   'mkQ' (nameSet stage n)
          {-
          `extQ` postTcType `extQ` -}
   -- fixity n
          {-
          `extQ` gdefault
          -}
  where -- generic :: Data a => a -> Tree String
        -- generic t =  Node "(" ++ showConstr (toConstr t)
        --          ++ space (concat (intersperse " " (gmapQ (data2treeGhcStaged stage (n+1)) t))) ++ ")"
        -- space "" = ""
        -- space s  = ' ':s


        -- gdefault :: Data a => SYB.Stage -> a -> Tree String
        -- gdefault :: Data a => a -> Tree String
        gdefault x = Node (showConstr $ toConstr x) (gmapQ (data2treeGhcStaged stage) x) 

       
        -- nameSet x 
        nameSet stage x 
                | stage `elem` [SYB.Parser,SYB.TypeChecker] 
                = const ( Node "{!NameSet placeholder here!}" []) -- :: GHC.NameSet -> Tree String
                | otherwise     
                -- = const (Node (showConstr $ toConstr x) (gmapQ (data2treeGhcStaged stage) x)) :: GHC.NameSet -> Tree String
                = const ( Node "{!NameSet placeholder here!}" []) -- :: GHC.NameSet -> Tree String

        postTcType | stage<SYB.TypeChecker = const (Node "{!type placeholder here?!}" []) :: GHC.PostTcType -> Tree String
                   -- | otherwise     = GHC.showSDoc . GHC.ppr :: GHC.Type -> Tree String
                   | otherwise     = const (Node "{!type placeholder here!}" []) :: GHC.Type -> Tree String

        fixity | stage<SYB.Renamer = const (Node "{!fixity placeholder here?!}" []) :: GHC.Fixity -> Tree String
               | otherwise     = const (Node ("{Fixity: ") []) :: GHC.Fixity -> Tree String
               -- | otherwise     = const (Node (("{Fixity: "++) . (++"}") . GHC.showSDoc . GHC.ppr) []) :: GHC.Fixity -> Tree String
-}

{-
-- | Generic Data-based show, with special cases for GHC Ast types,
--   and simplistic indentation-based layout (the 'Int' parameter); 
--   showing abstract types abstractly and avoiding known potholes 
--   (based on the 'Stage' that generated the Ast)
data2treeGhcStaged :: Data a => SYB.Stage -> a -> Tree String
-- showData :: Data a => Stage -> Int -> a -> String
data2treeGhcStaged stage n = 
  generic `ext1Q` list `extQ` string `extQ` fastString `extQ` srcSpan 
          `extQ` name `extQ` occName `extQ` moduleName `extQ` var `extQ` dataCon
          `extQ` bagName `extQ` bagRdrName `extQ` bagVar `extQ` nameSet
          `extQ` postTcType `extQ` fixity
  where generic :: Data a => a -> String
        generic t = indent n ++ "(" ++ showConstr (toConstr t)
                 ++ space (concat (intersperse " " (gmapQ (data2treeGhcStaged stage (n+1)) t))) ++ ")"
        space "" = ""
        space s  = ' ':s
        indent n = "\n" ++ replicate n ' ' 
        string     = show :: String -> String
        fastString = ("{FastString: "++) . (++"}") . show :: GHC.FastString -> String
        list l     = indent n ++ "[" 
                              ++ concat (intersperse "," (map (data2treeGhc stage (n+1)) l)) ++ "]"

        name       = ("{Name: "++) . (++"}") . GHC.showSDoc . GHC.ppr :: GHC.Name -> String
        occName    = ("{OccName: "++) . (++"}") .  GHC.occNameString 
        moduleName = ("{ModuleName: "++) . (++"}") . GHC.showSDoc . GHC.ppr :: GHC.ModuleName -> String
        srcSpan    = ("{"++) . (++"}") . GHC.showSDoc . GHC.ppr :: GHC.SrcSpan -> String
        var        = ("{Var: "++) . (++"}") . GHC.showSDoc . GHC.ppr :: GHC.Var -> String
        dataCon    = ("{DataCon: "++) . (++"}") . GHC.showSDoc . GHC.ppr :: GHC.DataCon -> String

        bagRdrName:: GHC.Bag (GHC.Located (GHC.HsBind GHC.RdrName)) -> String
        bagRdrName = ("{Bag(Located (HsBind RdrName)): "++) . (++"}") . list . GHC.bagToList 
        bagName   :: GHC.Bag (GHC.Located (GHC.HsBind GHC.Name)) -> String
        bagName    = ("{Bag(Located (HsBind Name)): "++) . (++"}") . list . GHC.bagToList 
        bagVar    :: GHC.Bag (GHC.Located (GHC.HsBind GHC.Var)) -> String
        bagVar     = ("{Bag(Located (HsBind Var)): "++) . (++"}") . list . GHC.bagToList 

        nameSet | stage `elem` [SYB.Parser,SYB.TypeChecker] 
                = const ("{!NameSet placeholder here!}") :: GHC.NameSet -> String
                | otherwise     
                = ("{NameSet: "++) . (++"}") . list . GHC.nameSetToList 

        postTcType | stage<SYB.TypeChecker = const "{!type placeholder here?!}" :: GHC.PostTcType -> String
                   | otherwise     = GHC.showSDoc . GHC.ppr :: GHC.Type -> String

        fixity | stage<SYB.Renamer = const "{!fixity placeholder here?!}" :: GHC.Fixity -> String
               | otherwise     = ("{Fixity: "++) . (++"}") . GHC.showSDoc . GHC.ppr :: GHC.Fixity -> String
-}


-- ---------------------------------------------------------------------

-- | Generic Data-based show, with special cases for GHC Ast types,
--   and simplistic indentation-based layout (the 'Int' parameter); 
--   showing abstract types abstractly and avoiding known potholes 
--   (based on the 'Stage' that generated the Ast)
data2treeGhcStaged :: Data a => SYB.Stage -> Int -> a -> Tree String
-- data2treeGhcStaged' :: Data a => SYB.Stage -> Int -> a -> String
data2treeGhcStaged stage n = 
  generic `ext1Q` list 
          `extQ` string 
          -- `extQ` fastString 
          -- `extQ` gname 
          -- `extQ` occName 
          -- `extQ` moduleName 
          -- `extQ` srcSpan 
          -- `extQ` var 
          -- `extQ` dataCon
          -- `extQ` bagName `extQ` bagRdrName `extQ` bagVar 
          `extQ` nameSet
          `extQ` postTcType 
          `extQ` fixity
  where generic :: Data a => a -> Tree String
        generic t = Node ("T:" ++ (showConstr (toConstr t))) (gmapQ (data2treeGhcStaged stage (n+1)) t)

        space "" = ""
        space s  = ' ':s
        -- indent n' = "\n" ++ replicate n' ' ' 
        indent n' = ""

        -- string     = show :: String -> String
        string     = const (Node ("show t") []) :: String -> Tree String
        

        -- fastString = ("{FastString: "++) . (++"}") . show :: GHC.FastString -> String

        -- list l     = indent n ++ "[" 
        --                        ++ concat (intersperse "," (map (data2treeGhcStaged' stage (n+1)) l)) ++ "]"

        -- list l     = Node (indent n ++ "[" 
        --                         ++ concat (intersperse "," ["a","b"]{- (map (data2treeGhcStaged' stage (n+1)) l) -}) ++ "]") []

        list l     = Node "list" ((map (data2treeGhcStaged stage (n+1)) l))


        -- gname      = ("{Name: "++) . (++"}") . GHC.showSDoc . GHC.ppr :: GHC.Name -> String
        -- occName    = ("{OccName: "++) . (++"}") .  GHC.occNameString 
        -- moduleName = ("{ModuleName: "++) . (++"}") . GHC.showSDoc . GHC.ppr :: GHC.ModuleName -> String
        -- srcSpan    = ("{"++) . (++"}") . GHC.showSDoc . GHC.ppr :: GHC.SrcSpan -> String
        -- var        = ("{Var: "++) . (++"}") . GHC.showSDoc . GHC.ppr :: GHC.Var -> String
        -- dataCon    = ("{DataCon: "++) . (++"}") . GHC.showSDoc . GHC.ppr :: GHC.DataCon -> String

        {-
        bagRdrName:: GHC.Bag (GHC.Located (GHC.HsBind GHC.RdrName)) -> String
        bagRdrName = ("{Bag(Located (HsBind RdrName)): "++) . (++"}") . list . GHC.bagToList 
        bagName   :: GHC.Bag (GHC.Located (GHC.HsBind GHC.Name)) -> String
        bagName    = ("{Bag(Located (HsBind Name)): "++) . (++"}") . list . GHC.bagToList 
        bagVar    :: GHC.Bag (GHC.Located (GHC.HsBind GHC.Var)) -> String
        bagVar     = ("{Bag(Located (HsBind Var)): "++) . (++"}") . list . GHC.bagToList 
        -}

        nameSet | stage `elem` [SYB.Parser,SYB.TypeChecker] 
                = const (Node ("{!NameSet placeholder here!}") []) :: GHC.NameSet -> Tree String
        postTcType | stage<SYB.TypeChecker = const (Node "{!type placeholder here?!}" []) :: GHC.PostTcType -> Tree String
        fixity | stage<SYB.Renamer = const (Node "{!fixity placeholder here?!}" []) :: GHC.Fixity -> Tree String


-- ---------------------------------------------------------------------




parseHaskellGhc' ::
  String
  -> Either
       ParseError
       (GHC.WarningMessages, GHC.Located (GHC.HsModule GHC.RdrName))
parseHaskellGhc' s = case (foo s) of
    Right p  -> Right p
    Left err -> Left ParseError


foo s = do
  res <- unsafePerformIO $ parseSourceFile s
  return res


parseSourceFile ::
  String
  -> IO
       (Either
          GHC.ErrorMessages
          (GHC.WarningMessages, GHC.Located (GHC.HsModule GHC.RdrName)))
parseSourceFile s =
  GHC.defaultErrorHandler GHC.defaultLogAction $ do
    GHC.runGhc (Just GHC.libdir) $ do
      dflags <- GHC.getSessionDynFlags
      let dflags' = foldl GHC.xopt_set dflags
                    [GHC.Opt_Cpp, GHC.Opt_ImplicitPrelude, GHC.Opt_MagicHash]
      GHC.setSessionDynFlags dflags
      let result = GHC.parser s  dflags' "filename.hs"
          -- -> Either ErrorMessages (WarningMessages, Located (HsModule RdrName))	 
      return result


-- ---------------------------------------------------------------------

-- | A simple test function to launch parsers from ghci.
--   When this works, astview should work too.
testParser :: Parser -> String -> IO ()
testParser p s = putStrLn $ drawTree $ (tree p) s

tsrc = "main = putStrLn \"Hello World\""

t = testParser haskellghc tsrc


p = putStrLn $ SYB.showData SYB.Parser 2 (parseHaskellGhc tsrc)



