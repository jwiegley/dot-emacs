{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
module Layout.TH where

import Language.Haskell.TH

emptyShow :: Name -> Q [Dec]
emptyShow name = [d|instance Show $(conT name) where show _ = ""|]

foo = 1
