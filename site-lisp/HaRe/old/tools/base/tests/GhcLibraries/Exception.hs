-- Dummy Exception module
module Exception where

data Exception

finally :: IO a -> IO b -> IO a
finally = undefined

catch   :: IO a -> (Exception -> IO a) -> IO a
catch   = undefined

instance Show Exception where
    show _ = "*"
