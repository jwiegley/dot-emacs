{-# LANGUAGE ForeignFunctionInterface #-}
module Layout.Foreign where


import Foreign.C.Types
import GHC.Exts

foreign import ccall "wxStyledTextCtrl_ShowLines" wxStyledTextCtrl_ShowLines :: Ptr (Int) -> CInt -> CInt -> IO ()

foreign export ccall "wxStyledTextCtrl_ShowLines" wxStyledTextCtrl_ShowLines :: Ptr (Int) -> CInt -> CInt -> IO ()

foo = 0



