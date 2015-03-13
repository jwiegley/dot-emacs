import System(getArgs)
import PfeSocket(connectToPFE,pfeClient)
import ImpUtils()

main =
  do h <- connectToPFE "hi"
     args <- getArgs
     pfeClient h args
