
import PPfeMain(mainPFE)
import PPfeInstances
import PfeInteractive(pfeiAllCmds)
import PPfeCmds(ppfeCmds)
--import TraceIO(traceIO)

--main = traceIO main'

main = mainPFE (pfeiAllCmds ppfeCmds)
