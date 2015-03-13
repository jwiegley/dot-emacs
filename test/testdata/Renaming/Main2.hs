-- This is a main module without an explicit module statement.
-- renaming "bar" should succeed, but "main" fail.

main = putStrLn "hello"

bar x = x ^ 2

