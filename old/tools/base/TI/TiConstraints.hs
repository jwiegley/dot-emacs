-- Collecting constraints efficiently...
module TiConstraints(Constraints,empty,single,Tree.merge,Tree.toList) where
import qualified Tree

type Constraints c = Tree.Tree c

empty = Tree.Empty
single = Tree.Single
