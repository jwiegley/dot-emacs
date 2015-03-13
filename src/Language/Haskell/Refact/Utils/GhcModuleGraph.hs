{-# LANGUAGE PatternGuards #-}

module Language.Haskell.Refact.Utils.GhcModuleGraph
  (
    getModulesAsGraph
  , summaryNodeSummary
  ) where

-- GHC imports
import Digraph
import FastString
import GHC
import HscTypes
import Maybes
import Panic

-- Other imports
import qualified Data.Map as Map

{-

--------------------------------------------------
graph:

Vertices:
  (ModSummary {main:Main,},1,[3])
  (ModSummary {main:S1,},  2, [])
  (ModSummary {main:M3,},  3,[4])
  (ModSummary {main:M2,},  4,[2])

Edges:
  (ModSummary {main:Main,},1,[3]) -> (ModSummary {main:M3,},3,[4])
  (ModSummary {main:M3,},  3,[4]) -> (ModSummary {main:M2,},4,[2])
  (ModSummary {main:M2,},  4,[2]) -> (ModSummary {main:S1,},2,[])


transposeG:

Vertices:
  (ModSummary {main:Main,}, 1,[3])
  (ModSummary {main:S1,},   2, [])
  (ModSummary {main:M3,},   3,[4])
  (ModSummary {main:M2,},   4,[2])
Edges:
  (ModSummary {main:S1,},   2, []) -> (ModSummary {main:M2,},   4,[2])
  (ModSummary {main:M3,},   3,[4]) -> (ModSummary {main:Main,}, 1,[3])
  (ModSummary {main:M2,},   4,[2]) -> (ModSummary {main:M3,},   3,[4])


-}
-- ---------------------------------------------------------------------

getModulesAsGraph
  :: Bool -> [ModSummary] -> Maybe ModuleName -> Graph SummaryNode
getModulesAsGraph drop_hs_boot_nodes summaries mb_root_mod
  = initial_graph
  -- = map (fmap summaryNodeSummary) $ stronglyConnCompG initial_graph
  where
    (graph, lookup_node) = moduleGraphNodes drop_hs_boot_nodes summaries

    initial_graph = case mb_root_mod of
        Nothing -> graph
        Just root_mod ->
            -- restrict the graph to just those modules reachable from
            -- the specified module.  We do this by building a graph with
            -- the full set of nodes, and determining the reachable set from
            -- the specified node.
            let root | Just node <- lookup_node HsSrcFile root_mod, graph `hasVertexG` node = node
                     | otherwise = ghcError (ProgramError "module does not exist")
            in graphFromEdgedVertices (seq root (reachableG graph root))




-- ---------------------------------------------------------------------
-- This bit is from the GHC source >>>>>>>
type SummaryNode = (ModSummary, Int, [Int])

{-
topSortModuleGraph
  :: Bool -> [ModSummary] -> Maybe ModuleName -> [SCC ModSummary]
topSortModuleGraph drop_hs_boot_nodes summaries mb_root_mod
  = map (fmap summaryNodeSummary) $ stronglyConnCompG initial_graph
  where
    (graph, lookup_node) = moduleGraphNodes drop_hs_boot_nodes summaries

    initial_graph = case mb_root_mod of
        Nothing -> graph
        Just root_mod ->
            -- restrict the graph to just those modules reachable from
            -- the specified module.  We do this by building a graph with
            -- the full set of nodes, and determining the reachable set from
            -- the specified node.
            let root | Just node <- lookup_node HsSrcFile root_mod, graph `hasVertexG` node = node
                     | otherwise = ghcError (ProgramError "module does not exist")
            in graphFromEdgedVertices (seq root (reachableG graph root))
-}

summaryNodeKey :: SummaryNode -> Int
summaryNodeKey (_, k, _) = k

summaryNodeSummary :: SummaryNode -> ModSummary
summaryNodeSummary (s, _, _) = s

moduleGraphNodes :: Bool -> [ModSummary]
  -> (Graph SummaryNode, HscSource -> ModuleName -> Maybe SummaryNode)
moduleGraphNodes drop_hs_boot_nodes summaries = (graphFromEdgedVertices nodes, lookup_node)
  where
    numbered_summaries = zip summaries [1..]

    lookup_node :: HscSource -> ModuleName -> Maybe SummaryNode
    lookup_node hs_src modName = Map.lookup (modName, hs_src) node_map

    lookup_key :: HscSource -> ModuleName -> Maybe Int
    lookup_key hs_src modName = fmap summaryNodeKey (lookup_node hs_src modName)

    node_map :: NodeMap SummaryNode
    node_map = Map.fromList [ ((moduleName (ms_mod s), ms_hsc_src s), node)
                            | node@(s, _, _) <- nodes ]

    -- We use integers as the keys for the SCC algorithm
    nodes :: [SummaryNode]
    nodes = [ (s, key, out_keys)
            | (s, key) <- numbered_summaries
             -- Drop the hi-boot ones if told to do so
            , not (isBootSummary s && drop_hs_boot_nodes)
            , let out_keys = out_edge_keys hs_boot_key (map unLoc (ms_home_srcimps s)) ++
                             out_edge_keys HsSrcFile   (map unLoc (ms_home_imps s)) ++
                             (-- see [boot-edges] below
                              if drop_hs_boot_nodes || ms_hsc_src s == HsBootFile 
                              then []
                              else case lookup_key HsBootFile (ms_mod_name s) of
                                    Nothing -> []
                                    Just k  -> [k]) ]

    -- [boot-edges] if this is a .hs and there is an equivalent
    -- .hs-boot, add a link from the former to the latter.  This
    -- has the effect of detecting bogus cases where the .hs-boot
    -- depends on the .hs, by introducing a cycle.  Additionally,
    -- it ensures that we will always process the .hs-boot before
    -- the .hs, and so the HomePackageTable will always have the
    -- most up to date information.

    -- Drop hs-boot nodes by using HsSrcFile as the key
    hs_boot_key | drop_hs_boot_nodes = HsSrcFile
                | otherwise          = HsBootFile

    out_edge_keys :: HscSource -> [ModuleName] -> [Int]
    out_edge_keys hi_boot ms = mapCatMaybes (lookup_key hi_boot) ms
        -- If we want keep_hi_boot_nodes, then we do lookup_key with
        -- the IsBootInterface parameter True; else False

type NodeKey   = (ModuleName, HscSource)  -- The nodes of the graph are
type NodeMap a = Map.Map NodeKey a	  -- keyed by (mod, src_file_type) pairs

{-
msKey :: ModSummary -> NodeKey
msKey (ModSummary { ms_mod = mod, ms_hsc_src = boot }) = (moduleName mod,boot)

mkNodeMap :: [ModSummary] -> NodeMap ModSummary
mkNodeMap summaries = Map.fromList [ (msKey s, s) | s <- summaries]

nodeMapElts :: NodeMap a -> [a]
nodeMapElts = Map.elems
-}

{-
msDeps :: ModSummary -> [(Located ModuleName, IsBootInterface)]
-- (msDeps s) returns the dependencies of the ModSummary s.
-- A wrinkle is that for a {-# SOURCE #-} import we return
--      *both* the hs-boot file
--      *and* the source file
-- as "dependencies".  That ensures that the list of all relevant
-- modules always contains B.hs if it contains B.hs-boot.
-- Remember, this pass isn't doing the topological sort.  It's
-- just gathering the list of all relevant ModSummaries
msDeps s =
    concat [ [(m,True), (m,False)] | m <- ms_home_srcimps s ]
         ++ [ (m,False) | m <- ms_home_imps s ]
-}

home_imps :: [Located (ImportDecl RdrName)] -> [Located ModuleName]
home_imps imps = [ ideclName i |  L _ i <- imps, isLocal (ideclPkgQual i) ]
  where isLocal Nothing = True
        isLocal (Just pkg) | pkg == fsLit "this" = True -- "this" is special
        isLocal _ = False

{-
ms_home_allimps :: ModSummary -> [ModuleName]
ms_home_allimps ms = map unLoc (ms_home_srcimps ms ++ ms_home_imps ms)
-}

ms_home_srcimps :: ModSummary -> [Located ModuleName]
ms_home_srcimps = home_imps . ms_srcimps

ms_home_imps :: ModSummary -> [Located ModuleName]
ms_home_imps = home_imps . ms_imps

-- GHC source end
