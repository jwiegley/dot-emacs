module CPUTime where
import Prelude

foreign import getCPUTime :: IO Integer
foreign import cpuTimePrecision :: Integer
