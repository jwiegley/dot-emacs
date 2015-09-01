{-# LANGUAGE FlexibleContexts #-}

module StateM 
  (module IxStateM, F.HasState, updSt, updSt_, getSt, setSt, setSt_) where

import IxStateM hiding (HasState(..))
import qualified MT as F 

updSt   :: F.HasState m F.Z s => (s -> s) -> m s
updSt_  :: F.HasState m F.Z s => (s -> s) -> m ()
getSt   :: F.HasState m F.Z s => m s
setSt   :: F.HasState m F.Z s => s -> m s
setSt_  :: F.HasState m F.Z s => s -> m ()

updSt   = F.updSt F.this 
updSt_  = F.updSt_ F.this 
getSt   = F.getSt F.this
setSt   = F.setSt F.this
setSt_  = F.setSt_ F.this


