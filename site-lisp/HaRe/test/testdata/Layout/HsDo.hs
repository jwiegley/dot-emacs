module Layout.HsDo where

import qualified Data.Map as Map

moduleGraphNodes drop_hs_boot_nodes summaries = (graphFromEdgedVertices nodes, lookup_node)
  where
    numbered_summaries = zip summaries [1..]

    node_map :: NodeMap SummaryNode
    node_map = Map.fromList [ ((moduleName (ms_mod s), ms_hsc_src s), node)
                            | node@(s, _, _) <- nodes ]


graphFromEdgedVertices = undefined
nodes = undefined
lookup_node = undefined
type NodeMap a = Map.Map (Int,Int) (Int,Int,Int)
data SummaryNode = SummaryNode
moduleName = undefined
ms_mod = undefined
ms_hsc_src = undefined

