-- | Testing that HaRe can find source files from a cabal file

-- This is main module 2

import qualified Foo.Bar as B

main = putStrLn "foo"

baz = 3 + B.baz
