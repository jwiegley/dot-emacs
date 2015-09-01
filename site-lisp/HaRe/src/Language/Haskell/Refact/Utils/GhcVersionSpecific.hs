{-# LANGUAGE CPP #-}

-- |This module contains all the code that depends on a specific
-- version of GHC, and should be the only one requiring CPP
module Language.Haskell.Refact.Utils.GhcVersionSpecific
  (
    showGhc
  , prettyprint
  , prettyprint2
  , ppType
  -- , lexStringToRichTokens
  , getDataConstructors
  , setGhcContext
  )
  where

import qualified DynFlags      as GHC
import qualified GHC           as GHC
import qualified GHC.Paths     as GHC
import qualified Lexer         as GHC
import qualified Outputable    as GHC
import qualified StringBuffer  as GHC

import Language.Haskell.Refact.Utils.TypeSyn


-- ---------------------------------------------------------------------

-- |Show a GHC API structure
showGhc :: (GHC.Outputable a) => a -> String
#if __GLASGOW_HASKELL__ > 704
showGhc x = GHC.showSDoc GHC.tracingDynFlags $ GHC.ppr x
#else
showGhc x = GHC.showSDoc                     $ GHC.ppr x
#endif

-- ---------------------------------------------------------------------


prettyprint :: (GHC.Outputable a) => a -> String
#if __GLASGOW_HASKELL__ > 704
prettyprint x = GHC.renderWithStyle GHC.tracingDynFlags (GHC.ppr x) (GHC.mkUserStyle GHC.neverQualify GHC.AllTheWay)
#else
prettyprint x = GHC.renderWithStyle                     (GHC.ppr x) (GHC.mkUserStyle GHC.neverQualify GHC.AllTheWay)
#endif

-- ---------------------------------------------------------------------

prettyprint2 :: (GHC.Outputable a) => a -> String
#if __GLASGOW_HASKELL__ > 704
prettyprint2 x = GHC.renderWithStyle GHC.tracingDynFlags (GHC.ppr x) (GHC.cmdlineParserStyle)
#else
prettyprint2 x = GHC.renderWithStyle                     (GHC.ppr x) (GHC.cmdlineParserStyle)
#endif

-- ---------------------------------------------------------------------

ppType :: GHC.Type -> String
#if __GLASGOW_HASKELL__ > 704
ppType x = GHC.renderWithStyle GHC.tracingDynFlags (GHC.pprParendType x) (GHC.mkUserStyle GHC.neverQualify GHC.AllTheWay)
#else
ppType x = GHC.renderWithStyle                     (GHC.pprParendType x) (GHC.mkUserStyle GHC.neverQualify GHC.AllTheWay)
#endif


-- ---------------------------------------------------------------------

{- moved to haskell-token-utils
lexStringToRichTokens :: GHC.RealSrcLoc -> String -> IO [PosToken]
lexStringToRichTokens startLoc str = do
  -- error $ "lexStringToRichTokens: (startLoc,str)=" ++ (showGhc (startLoc,str)) -- ++AZ
#if __GLASGOW_HASKELL__ > 704
  GHC.defaultErrorHandler GHC.defaultFatalMessager GHC.defaultFlushOut $ do
#else
  GHC.defaultErrorHandler GHC.defaultLogAction $ do
#endif
    GHC.runGhc (Just GHC.libdir) $ do
      dflags <- GHC.getSessionDynFlags
      let dflags' = foldl GHC.xopt_set dflags
                    [GHC.Opt_Cpp, GHC.Opt_ImplicitPrelude, GHC.Opt_MagicHash]
      _ <- GHC.setSessionDynFlags dflags'

      -- lexTokenStream :: StringBuffer -> RealSrcLoc -> DynFlags -> ParseResult [Located Token]
      let res = GHC.lexTokenStream (GHC.stringToStringBuffer str) startLoc dflags'
      case res of
        GHC.POk _ toks -> return $ GHC.addSourceToTokens startLoc (GHC.stringToStringBuffer str) toks 
        GHC.PFailed _srcSpan _msg -> error $ "lexStringToRichTokens:" -- ++ (show $ GHC.ppr msg)

        -- addSourceToTokens :: RealSrcLoc -> StringBuffer -> [Located Token] -> [(Located Token, String)]
-}

-- ---------------------------------------------------------------------

getDataConstructors :: GHC.LHsDecl n -> [GHC.LConDecl n]
#if __GLASGOW_HASKELL__ > 704
getDataConstructors (GHC.L _ (GHC.TyClD (GHC.TyDecl _ _ (GHC.TyData _ _ _ _ cons _) _))) = cons
#else
getDataConstructors (GHC.L _ (GHC.TyClD (GHC.TyData _ _ _ _ _ _ cons _))) = cons
      -- TyClD - Type definitions
      -- GHC7.4.2: defines' decl@(GHC.L l (GHC.TyClD (GHC.TyData _ _ name _ _ _ cons _)))
      -- GHC7.6.3: defines' decl@(GHC.L l (GHC.TyClD (GHC.TyDecl _name _vars (GHC.TyData _ _ _ _ cons _) _fvs)))
#endif
getDataConstructors _ = []

-- ---------------------------------------------------------------------

setGhcContext :: GHC.GhcMonad m => GHC.ModSummary -> m ()
#if __GLASGOW_HASKELL__ > 704
setGhcContext modSum = GHC.setContext [GHC.IIModule (GHC.moduleName $ GHC.ms_mod modSum)]
#else
setGhcContext modSum = GHC.setContext [GHC.IIModule (                 GHC.ms_mod modSum)]
#endif
