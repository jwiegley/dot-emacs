
--import System(getArgs)
import PPU(getPPopts)

import HsParser(parse)
import HsLexerPass1(lexerPass0)
--import DefinedNamesBase()
import FreeNamesBase()
import ScopeNamesBase()
import NameMapsBase()
import ReAssocBase()
import RemoveListCompBase()
import SimpPatMatchBase()

import TiDecorate(TiDecls) -- to choose result type from the type checker
import HsModule
import qualified System.IO as IO
import Pfe0Cmds(addHelpCmd)
import Pfe4Cmds(pfe4Cmds)
import PFE4(PFE4Info)
import Pfe3Metrics(pfe3MetricsCmds)
import PFEdeps(clean5)
import PfeHtmlCmds(pfeHtmlCmds)
import PfeChase(pfeChaseCmds)
import PfeTransformCmds(pfeTransformCmds)
import PfeDepCmds(runPFE5Cmds,pfeDepCmds)
import PfeCleanCmd(pfeCleanCmd)
-- import PfeInteractive(pfeiAllCmds,runSIO)
import MapDeclMBase() -- for removing pattern bindings in PfeTransformCmds.
--import RemoveIrrefPatsBase()
-- ---------------------------------------------------------------------
import Control.Monad.CatchIO -- ++AZ++
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import IxStateMT
import PFE0
import SourceNames
import HsName
import PosSyntax
import System.Time
import Data.Set
import Ents
import PNT
import PFEdeps
-- ---------------------------------------------------------------------


import PfeRefactoringCmds(pfeRefactoringCmds) 

main = do
          IO.hSetBuffering IO.stdout IO.NoBuffering
          x <- getPPopts
          runPFE5Cmds () pfeCmds (lexerPass0,parse) x   


-- main = runPFE5Cmds () pfeCmds (lexerPass0,parse) =<< getPPopts

pfeCmds = pfe4Cmds tcOutput++pfeTransformCmds
          ++pfeChaseCmds++pfeHtmlCmds++pfeDepCmds++pfeCleanCmd clean5
          ++pfeRefactoringCmds 

tcOutput = id :: I (PFE4Info i2 (TiDecls i2))
--tcOutput = id :: I [[HsModuleR]]
type I a = a->a

-- ---------------------------------------------------------------------

instance (MonadCatchIO
         (IxStateMT.WithState
            (PFE0.State0
               (SourceNames.SN [Char])
               (SourceNames.SN HsName.HsName)
               [PosSyntax.HsDecl],
             ([(HsName.ModuleName, -- Might be PosSyntax.ModuleName
                (System.Time.ClockTime,
                 Data.Set.Set
                   (SourceNames.SN [Char], Ents.Ent (SourceNames.SN [Char]))))],
              (PFE4Info PNT.PNT (TiDecls PNT.PNT), (PFEdeps.Deps2 PNT.PNT, ()))))
            IO)) where
  catch = Control.Monad.CatchIO.catch
  block = block
  unblock = unblock
  
instance (MonadIO
         (WithState
            (State0 (SN [Char]) (SN HsName.HsName) [HsDecl],
             ([(HsName.ModuleName,
                (ClockTime, Set (SN [Char], Ent (SN [Char]))))],
              (PFE4Info PNT (TiDecls PNT), (Deps2 PNT, ()))))
            IO)) where
  liftIO = liftIO
  -- liftIO = undefined

{-
instance (MonadTrans
         (WithState
            (State0 (SN [Char]) (SN HsName.HsName) [HsDecl],
             ([(HsName.ModuleName,
                (ClockTime, Set (SN [Char], Ent (SN [Char]))))],
              (PFE4Info PNT (TiDecls PNT), (Deps2 PNT, ())))))) where
  -}