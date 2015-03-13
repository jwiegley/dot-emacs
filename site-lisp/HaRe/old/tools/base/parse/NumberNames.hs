module NumberNames(module NumberNames,module UniqueNames) where
import NameMaps
import StateM
import UniqueNames
import MUtils

numberNames m = withSt (1::Int) . mapNamesM num $ m
  where
    num i = local i # fresh
    fresh = updSt (+1)
    local i = PN i . L
