-- Functions for manipulating FilePaths
module PathUtils where

import System.Info(os)

-- Normalize file names:
normf ('.':x:s) | x==pathSep = normf s
normf s = s

pathSep = if os=="mingw32" then '\\' else '/'
