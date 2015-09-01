-- $Id: GenSym.hs,v 1.1 2001/07/24 17:39:10 moran Exp $

{-

   Horribly hacked up gensym.

-}

module GenSym (newName) where

import IOExts

count :: IORef Int
count = unsafePerformIO $
    newIORef 0

incCount :: Int
incCount = unsafePerformIO $
    do c <- readIORef count
       writeIORef count $! (c + 1)
       return c

newName :: String
newName = show incCount
