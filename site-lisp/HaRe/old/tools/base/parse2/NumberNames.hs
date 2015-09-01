module NumberNames(module NumberNames,module UniqueNames) where
import NameMaps
import UniqueNames
import SourceNames

--numberNames = id
--
numberNames m = mapNames conv m
  where
    conv (SN i p) = PN i (S p)
--}
