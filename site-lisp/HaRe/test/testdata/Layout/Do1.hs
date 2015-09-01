module Layout.Do1 where

getCurrentModuleGraph = undefined
topSortModuleGraph = undefined

-- sortCurrentModuleGraph :: GHC.Ghc [GHC.SCC GHC.ModSummary]
sortCurrentModuleGraph :: IO [Int]
sortCurrentModuleGraph = do
  -- g <- GHC.getModuleGraph
  g <- getCurrentModuleGraph
  let scc = topSortModuleGraph False g Nothing
  return scc

