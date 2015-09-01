{-+
This is a small utility to strip blank lines and comments from a Haskell file.
This version takes a Haskell program on stdin and writes the result to
stdout. Literate files are not supported.
-}

import StripComments(stripcomments)

main = interact stripcomments
