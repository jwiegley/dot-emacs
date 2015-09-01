{-# LANGUAGE ScopedTypeVariables #-}
module Language.Haskell.Refact.Refactoring.SwapArgs (swapArgs) where

import qualified Data.Generics.Aliases as SYB
import qualified GHC.SYB.Utils         as SYB

import qualified Name                  as GHC
import qualified GHC

import Language.Haskell.GhcMod
import Language.Haskell.Refact.API

-- TODO: replace args with specific parameters
swapArgs :: RefactSettings -> Cradle -> [String] -> IO [FilePath]
swapArgs settings cradle args
  = do let fileName = args!!0
           row = (read (args!!1)::Int)
           col = (read (args!!2)::Int)
       runRefacSession settings cradle (comp fileName (row,col))


comp :: String -> SimpPos
     -> RefactGhc [ApplyRefacResult]
comp fileName (row, col) = do
       getModuleGhc fileName
       renamed <- getRefactRenamed

       let name = locToName (row, col) renamed

       case name of
            -- (Just pn) -> do refactoredMod@(_, (_t, s)) <- applyRefac (doSwap pnt pn) (Just modInfo) fileName
            (Just pn) -> do
                            (refactoredMod,_) <- applyRefac (doSwap pn) (RSFile fileName)
                            return [refactoredMod]
            Nothing   -> error "Incorrect identifier selected!"
       --if isFunPNT pnt mod    -- Add this back in ++ CMB +++
       -- then do
              --        rs <-if isExported pnt exps
       --               then  applyRefacToClientMods (doSwap pnt) fileName
       --               else  return []
       -- writeRefactoredFiles False (r:rs)
       -- else error "\nInvalid cursor position!"

       -- putStrLn (showToks t)
       -- writeRefactoredFiles False [refactoredMod]
       -- putStrLn ("here" ++ (SYB.showData SYB.Parser 0 mod))  -- $ show [fileName, beginPos, endPos]
       -- putStrLn "Completd"


doSwap ::
 (GHC.Located GHC.Name) -> RefactGhc () -- m GHC.ParsedSource
doSwap name = do
    -- inscopes <- getRefactInscopes
    renamed  <- getRefactRenamed
    -- parsed   <- getRefactParsed
    reallyDoSwap name renamed

reallyDoSwap :: (GHC.Located GHC.Name) -> GHC.RenamedSource -> RefactGhc ()
reallyDoSwap (GHC.L _s n1) renamed = do
    renamed' <- everywhereMStaged SYB.Renamer (SYB.mkM inMod `SYB.extM` inExp `SYB.extM` inType) renamed -- this needs to be bottom up +++ CMB +++
    putRefactRenamed renamed'
    return ()

    where
         -- 1. The definition is at top level...
         inMod (_func@(GHC.FunBind (GHC.L x n2) infixity (GHC.MatchGroup matches p) a locals tick)::(GHC.HsBindLR GHC.Name GHC.Name ))
            | GHC.nameUnique n1 == GHC.nameUnique n2
                    = do logm ("inMatch>" ++ SYB.showData SYB.Parser 0 (GHC.L x n2) ++ "<")
                         newMatches <- updateMatches matches
                         return (GHC.FunBind (GHC.L x n2) infixity (GHC.MatchGroup newMatches p) a locals tick)
         inMod func = return func

         -- 2. All call sites of the function...
         inExp expr@((GHC.L _x (GHC.HsApp (GHC.L _y (GHC.HsApp e e1)) e2))::GHC.Located (GHC.HsExpr GHC.Name))
            | GHC.nameUnique (expToName e) == GHC.nameUnique n1
                   =  update e2 e1 =<< update e1 e2 expr
         inExp e = return e

         -- 3. Type signature...
         inType (GHC.L x (GHC.TypeSig [GHC.L x2 name] types)::GHC.LSig GHC.Name)
           | GHC.nameUnique name == GHC.nameUnique n1
                = do let (t1:t2:ts) = tyFunToList types
                     t1' <- update t1 t2 t1
                     t2' <- update t2 t1 t2
                     return (GHC.L x (GHC.TypeSig [GHC.L x2 name] (tyListToFun (t1':t2':ts))))

         inType (GHC.L _x (GHC.TypeSig (n:ns) _types)::GHC.LSig GHC.Name)
           | GHC.nameUnique n1 `elem` (map (\(GHC.L _ n') -> GHC.nameUnique n') (n:ns))
            = error "Error in swapping arguments in type signature: signauture bound to muliple entities!"

         inType ty = return ty

         tyFunToList (GHC.L _ (GHC.HsForAllTy _ _ _ (GHC.L _ (GHC.HsFunTy t1 t2)))) = t1 : (tyFunToList t2)
         tyFunToList (GHC.L _ (GHC.HsFunTy t1 t2)) = t1 : (tyFunToList t2)
         tyFunToList t = [t]

         tyListToFun [t1] = t1
         tyListToFun (t1:ts) = GHC.noLoc (GHC.HsFunTy t1 (tyListToFun ts))

         updateMatches [] = return []
         updateMatches ((GHC.L x (GHC.Match pats nothing rhs)::GHC.Located (GHC.Match GHC.Name)):matches)
           = case pats of
               (p1:p2:ps) -> do p1' <- update p1 p2 p1
                                p2' <- update p2 p1 p2
                                matches' <- updateMatches matches
                                return ((GHC.L x (GHC.Match (p1':p2':ps) nothing rhs)):matches')
               [p] -> return [GHC.L x (GHC.Match [p] nothing rhs)]
               []  -> return [GHC.L x (GHC.Match [] nothing rhs)]


