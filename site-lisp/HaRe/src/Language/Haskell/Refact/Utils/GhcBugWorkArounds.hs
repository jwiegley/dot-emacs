{-# LANGUAGE CPP #-}
-- | Provide workarounds for bugs detected in GHC, until they are
-- fixed in a later version

module Language.Haskell.Refact.Utils.GhcBugWorkArounds
    (
    bypassGHCBug7351
    , getRichTokenStreamWA
    ) where

import qualified Bag                   as GHC
import qualified DynFlags              as GHC
import qualified ErrUtils              as GHC
import qualified FastString            as GHC
import qualified GHC                   as GHC
import qualified HscTypes              as GHC
import qualified Lexer                 as GHC
import qualified MonadUtils            as GHC
import qualified Outputable            as GHC
import qualified SrcLoc                as GHC
import qualified StringBuffer          as GHC

import Control.Exception
import Data.IORef

import System.Directory
import System.FilePath
import qualified Data.Map as Map
import qualified Data.Set as Set

import Language.Haskell.Refact.Utils.TypeSyn

-- ---------------------------------------------------------------------

-- http://hackage.haskell.org/trac/ghc/ticket/7351
bypassGHCBug7351 :: [PosToken] -> [PosToken]
bypassGHCBug7351 ts = map go ts
  where
   go :: (GHC.Located GHC.Token, String) -> (GHC.Located GHC.Token, String)
   go rt@(GHC.L (GHC.UnhelpfulSpan _) _t,_s) = rt
   go    (GHC.L (GHC.RealSrcSpan l) t,s) = (GHC.L (fixCol l) t,s)

   fixCol l = GHC.mkSrcSpan (GHC.mkSrcLoc (GHC.srcSpanFile l) (GHC.srcSpanStartLine l) ((GHC.srcSpanStartCol l) - 1))
                            (GHC.mkSrcLoc (GHC.srcSpanFile l) (GHC.srcSpanEndLine l) ((GHC.srcSpanEndCol l) - 1))

-- ---------------------------------------------------------------------

-- | Replacement for original 'getRichTokenStream' which will return
-- the tokens for a file processed by CPP.
-- See bug <http://ghc.haskell.org/trac/ghc/ticket/8265>
getRichTokenStreamWA :: GHC.GhcMonad m => GHC.Module -> m [(GHC.Located GHC.Token, String)]
getRichTokenStreamWA modu = do
  (sourceFile, source, flags) <- getModuleSourceAndFlags modu
  let startLoc = GHC.mkRealSrcLoc (GHC.mkFastString sourceFile) 1 1
  case GHC.lexTokenStream source startLoc flags of
    GHC.POk _ ts -> return $ GHC.addSourceToTokens startLoc source ts
    GHC.PFailed _span _err ->
        do
           strSrcBuf <- getPreprocessedSrc sourceFile
           case GHC.lexTokenStream strSrcBuf startLoc flags of
             GHC.POk _ ts ->
               do directiveToks <- GHC.liftIO $ getPreprocessorAsComments sourceFile
                  nonDirectiveToks <- tokeniseOriginalSrc startLoc flags source
                  let toks = GHC.addSourceToTokens startLoc source ts
                  return $ combineTokens directiveToks nonDirectiveToks toks
                  -- return directiveToks
                  -- return nonDirectiveToks
                  -- return toks
             GHC.PFailed sspan err -> parseError flags sspan err

-- ---------------------------------------------------------------------

-- | Combine the three sets of tokens to produce a single set that
-- represents the code compiled, and will regenerate the original
-- source file.
-- [@directiveToks@] are the tokens corresponding to preprocessor
--                   directives, converted to comments
-- [@origSrcToks@] are the tokenised source of the original code, with
--                 the preprocessor directives stripped out so that
--                 the lexer  does not complain
-- [@postCppToks@] are the tokens that the compiler saw originally
-- NOTE: this scheme will only work for cpp in -nomacro mode
combineTokens ::
     [(GHC.Located GHC.Token, String)]
  -> [(GHC.Located GHC.Token, String)]
  -> [(GHC.Located GHC.Token, String)]
  -> [(GHC.Located GHC.Token, String)]
combineTokens directiveToks origSrcToks postCppToks = toks
  where
    locFn (GHC.L l1 _,_) (GHC.L l2 _,_) = compare l1 l2
    m1Toks = mergeBy locFn postCppToks directiveToks

    -- We must now find the set of tokens that are in origSrcToks, but
    -- not in m1Toks

    -- GHC.Token does not have Ord, can't use a set directly
    origSpans = map (\(GHC.L l _,_) -> l) origSrcToks
    m1Spans = map (\(GHC.L l _,_) -> l) m1Toks
    missingSpans = (Set.fromList origSpans) Set.\\ (Set.fromList m1Spans)

    missingToks = filter (\(GHC.L l _,_) -> Set.member l missingSpans) origSrcToks

    missingAsComments = map mkCommentTok missingToks
      where
        mkCommentTok :: (GHC.Located GHC.Token,String) -> (GHC.Located GHC.Token,String)
        mkCommentTok (GHC.L l _,s) = (GHC.L l (GHC.ITlineComment s),s)

    toks = mergeBy locFn m1Toks missingAsComments

-- ---------------------------------------------------------------------

tokeniseOriginalSrc ::
  GHC.GhcMonad m
  => GHC.RealSrcLoc -> GHC.DynFlags -> GHC.StringBuffer
  -> m [(GHC.Located GHC.Token, String)]
tokeniseOriginalSrc startLoc flags buf = do
  let src = stripPreprocessorDirectives buf
  case GHC.lexTokenStream src startLoc flags of
    GHC.POk _ ts -> return $ GHC.addSourceToTokens startLoc src ts
    GHC.PFailed sspan err -> parseError flags sspan err

-- ---------------------------------------------------------------------

-- | Strip out the CPP directives so that the balance of the source
-- can tokenised.
stripPreprocessorDirectives :: GHC.StringBuffer -> GHC.StringBuffer
stripPreprocessorDirectives buf = buf'
  where
    srcByLine = lines $ sbufToString buf
    noDirectivesLines = map (\line -> if line /= [] && head line == '#' then "" else line) srcByLine
    buf' = GHC.stringToStringBuffer $ unlines noDirectivesLines

-- ---------------------------------------------------------------------

sbufToString :: GHC.StringBuffer -> String
sbufToString sb@(GHC.StringBuffer _buf len _cur) = GHC.lexemeToString sb len

-- ---------------------------------------------------------------------

-- | The preprocessed files are placed in a temporary directory, with
-- a temporary name, and extension .hscpp. Each of these files has
-- three lines at the top identifying the original origin of the
-- files, which is ignored by the later stages of compilation except
-- to contextualise error messages.
getPreprocessedSrc ::
  GHC.GhcMonad m => FilePath -> m GHC.StringBuffer
getPreprocessedSrc srcFile = do
  df <- GHC.getSessionDynFlags
  d <- GHC.liftIO $ getTempDir df
  fileList <- GHC.liftIO $ getDirectoryContents d
  let suffix = "hscpp"

  let cppFiles = filter (\f -> getSuffix f == suffix) fileList
  origNames <- GHC.liftIO $ mapM getOriginalFile $ map (\f -> d </> f) cppFiles
  let tmpFile = head $ filter (\(o,_) -> o == srcFile) origNames
  buf <- GHC.liftIO $ GHC.hGetStringBuffer $ snd tmpFile

  return buf

-- ---------------------------------------------------------------------

getSuffix :: FilePath -> String
getSuffix fname = reverse $ fst $ break (== '.') $ reverse fname

-- | A GHC preprocessed file has the following comments at the top
-- @
-- # 1 "./test/testdata/BCpp.hs"
-- # 1 "<command-line>"
-- # 1 "./test/testdata/BCpp.hs"
-- @
-- This function reads the first line of the file and returns the
-- string in it.
-- NOTE: no error checking, will blow up if it fails
getOriginalFile :: FilePath -> IO (FilePath,FilePath)
getOriginalFile fname = do
  fcontents <- readFile fname
  let firstLine = head $ lines fcontents
  let (_,originalFname) = break (== '"') firstLine
  return $ (tail $ init $ originalFname,fname)

-- ---------------------------------------------------------------------

-- | Get the preprocessor directives as comment tokens from the
-- source.
getPreprocessorAsComments :: FilePath -> IO [(GHC.Located GHC.Token, String)]
getPreprocessorAsComments srcFile = do
  fcontents <- readFile srcFile
  let directives = filter (\(_lineNum,line) -> line /= [] && head line == '#') $ zip [1..] $ lines fcontents

  let mkTok (lineNum,line) = (GHC.L l (GHC.ITlineComment line),line)
       where
         start = GHC.mkSrcLoc (GHC.mkFastString srcFile) lineNum 1
         end   = GHC.mkSrcLoc (GHC.mkFastString srcFile) lineNum (length line)
         l = GHC.mkSrcSpan start end

  let toks = map mkTok directives
  return toks

-- ---------------------------------------------------------------------

#if __GLASGOW_HASKELL__ > 704
parseError :: GHC.GhcMonad m => GHC.DynFlags -> GHC.SrcSpan -> GHC.MsgDoc -> m b
parseError dflags sspan err = do
     throw $ GHC.mkSrcErr (GHC.unitBag $ GHC.mkPlainErrMsg dflags sspan err)
#else
parseError :: GHC.GhcMonad m => GHC.DynFlags -> GHC.SrcSpan -> GHC.Message -> m b
parseError _dflags sspan err = do
     throw $ GHC.mkSrcErr (GHC.unitBag $ GHC.mkPlainErrMsg        sspan err)
#endif

-- ---------------------------------------------------------------------
-- Copied from the GHC source, since not exported

getModuleSourceAndFlags :: GHC.GhcMonad m => GHC.Module -> m (String, GHC.StringBuffer, GHC.DynFlags)
getModuleSourceAndFlags modu = do
  m <- GHC.getModSummary (GHC.moduleName modu)
  case GHC.ml_hs_file $ GHC.ms_location m of
    Nothing ->
#if __GLASGOW_HASKELL__ > 704
               do dflags <- GHC.getDynFlags
                  GHC.liftIO $ throwIO $ GHC.mkApiErr dflags (GHC.text "No source available for module " GHC.<+> GHC.ppr modu)
#else
                  GHC.liftIO $ throwIO $ GHC.mkApiErr        (GHC.text "No source available for module " GHC.<+> GHC.ppr modu)
#endif
                  -- error $ ("No source available for module " ++ showGhc mod)
    Just sourceFile -> do
        source <- GHC.liftIO $ GHC.hGetStringBuffer sourceFile
        return (sourceFile, source, GHC.ms_hspp_opts m)

-- return our temporary directory within tmp_dir, creating one if we
-- don't have one yet
getTempDir :: GHC.DynFlags -> IO FilePath
getTempDir dflags
  = do let ref = GHC.dirsToClean dflags
           tmp_dir = GHC.tmpDir dflags
       mapping <- readIORef ref
       case Map.lookup tmp_dir mapping of
           Nothing -> error "should already be a tmpDir"
           Just d -> return d

-- ---------------------------------------------------------------------

-- Copied over from MissingH, the dependency cause travis to fail

{- | Merge two sorted lists using into a single, sorted whole,
allowing the programmer to specify the comparison function.

QuickCheck test property:

prop_mergeBy xs ys =
    mergeBy cmp (sortBy cmp xs) (sortBy cmp ys) == sortBy cmp (xs ++ ys)
          where types = xs :: [ (Int, Int) ]
                cmp (x1,_) (x2,_) = compare x1 x2
-}
mergeBy :: (a -> a -> Ordering) -> [a] -> [a] -> [a]
mergeBy _cmp [] ys = ys
mergeBy _cmp xs [] = xs
mergeBy cmp (allx@(x:xs)) (ally@(y:ys))
        -- Ordering derives Eq, Ord, so the comparison below is valid.
        -- Explanation left as an exercise for the reader.
        -- Someone please put this code out of its misery.
    | (x `cmp` y) <= EQ = x : mergeBy cmp xs ally
    | otherwise = y : mergeBy cmp allx ys


