
import PPfeMain(mainPFE)
import PPfeInstances
import PfeInteractive(pfeiAllCmds)
import PPfeCmds(ppfeCmds)
import PfeAlfaCmds(pfeAlfaCmds)

main = mainPFE (pfeiAllCmds apfeCmds)

apfeCmds = ppfeCmds++pfeAlfaCmds
