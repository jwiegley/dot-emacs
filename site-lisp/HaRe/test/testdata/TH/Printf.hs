{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{- Printf.hs -}
module TH.Printf where

-- Skeletal printf from the paper.
-- It needs to be in a separate module to the one where
-- you intend to use it.

-- Import some Template Haskell syntax
-- import Language.Haskell.THSyntax
import Language.Haskell.TH
import Language.Haskell.TH.Quote
import qualified Language.Haskell.TH as TH

-- Describe a format string
data Format = D | S | L String

-- Parse a format string.  This is left largely to you
-- as we are here interested in building our first ever
-- Template Haskell program and not in building printf.
parse :: String -> [Format]
parse s   = [ L s ]

-- Generate Haskell source code from a parsed representation
-- of the format string.  This code will be spliced into
-- the module which calls "pr", at compile time.
gen :: [Format] -> ExpQ
gen [D]   = [| \n -> show n |]
gen [S]   = [| \s -> s |]
gen [L s] = stringE s

-- Here we generate the Haskell code for the splice
-- from an input format string.
pr :: String -> ExpQ
pr s      = gen (parse s)

-- str :: QuasiQuoter
-- str = QuasiQuoter { quoteExp = stringE }

silly :: QuasiQuoter
silly = QuasiQuoter { quoteExp = \_ -> [| "yeah!!!" |] }

silly2 :: QuasiQuoter
silly2 = QuasiQuoter { quoteExp = \_ -> stringE "yeah!!!"
                     , quotePat = undefined
                     , quoteType = undefined
                     , quoteDec = undefined
                     }

