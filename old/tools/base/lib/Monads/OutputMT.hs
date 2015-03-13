module OutputMT (module IxOutputMT, F.MT(..), 
                 F.HasOutput, output, outputs, outputTree, listOutput) where

import IxOutputMT hiding (HasOutput(..))
import qualified MT as F 
import Tree

outputTree  :: F.HasOutput m F.Z o => Tree o -> m ()
output      :: F.HasOutput m F.Z o => o -> m ()
outputs     :: F.HasOutput m F.Z o => [o] -> m ()

outputTree  = F.outputTree F.this
output      = F.output F.this
outputs     = F.outputs F.this


