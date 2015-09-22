Feature: hyai indent
  In order to code Haskell faster
  As an Emacs user
  I want to indent code automatically

  Scenario: Beginning of buffer
    Given the buffer is empty
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(0)"

  Scenario: Before module
    Given the buffer is empty
    When I insert:
    """
    module Main where
    """
    And I place the cursor before "module"
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(0)"

    Given the buffer is empty
    When I insert:
    """
    
    module Main where
    """
    And I place the cursor before "module"
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(0)"

    Given the buffer is empty
    When I insert:
    """
    {-# LANGUAGE OverloadedStrings #-}
    module Main where
    """
    And I place the cursor before "module"
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(0)"

  Scenario: After do
    Given the buffer is empty
    When I insert:
    """
    main = do
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(4)"

    Given the buffer is empty
    When I insert:
    """
    foo = bar
      where
        bar = do
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(8)"

  Scenario: After where
    Given the buffer is empty
    When I insert:
    """
    module Main where
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(0)"

    Given the buffer is empty
    When I insert:
    """
    module Foo
        ( foo
        , bar
        , baz
        ) where
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(0)"

    Given the buffer is empty
    When I insert:
    """
    class Foo a where
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(4)"

    Given the buffer is empty
    When I insert:
    """
    foo = bar
      where
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(4)"

    Given the buffer is empty
    When I insert:
    """
    foo = bar
      where
        bar = baz
          where
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(8)"

  Scenario: Before where
    Given the buffer is empty
    When I insert:
    """
    foo = bar
    where
    """
    And I place the cursor before "where"
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(2)"

    Given the buffer is empty
    When I insert:
    """
    foo = do
        bar
    where
    """
    And I place the cursor before "where"
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(2)"

    Given the buffer is empty
    When I insert:
    """
    foo = bar
      where
        bar = baz
    where
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(6)"

    Given the buffer is empty
    When I insert:
    """
    module Main where
    foo = bar
    where
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(2)"

  Scenario: After case
    Given the buffer is empty
    When I insert:
    """
    foobar = case baz of
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(4 13)"

    Given the buffer is empty
    When I insert:
    """
    foobar = case baz of
    [
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(4 13)"

  Scenario: After then
    Given the buffer is empty
    When I insert:
    """
    foobar = do
        if foo
            then
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(12)"

  Scenario: Before then
    Given the buffer is empty
    When I insert:
    """
    foobar = do
        if foo
    then
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(8)"

  Scenario: After else
    Given the buffer is empty
    When I insert:
    """
    foobar = if foo
                 then
                     bar
                 else
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(17)"

  Scenario: Before else
    Given the buffer is empty
    When I insert:
    """
    foobar = do
        if foo
            then
    else
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(8)"

    Given the buffer is empty
    When I insert:
    """
    foobar = do
        if foo then
            bar
    else
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(4)"

  Scenario: Before in
    Given the buffer is empty
    When I insert:
    """
    foobar = let bar = 1
    in
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(9)"

  Scenario: After (
    Given the buffer is empty
    When I insert:
    """
    module Foo
        (
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(6)"

  Scenario: Before (
    Given the buffer is empty
    When I insert:
    """
    module Foo
    (
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(4)"

    Given the buffer is empty
    When I insert:
    """
    import Data.ByteString
    (
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(4)"

    Given the buffer is empty
    When I insert:
    """
    foobar = bazqux
    (
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(9 0)"

  Scenario: Before )
    Given the buffer is empty
    When I insert:
    """
    module Foo
        (
          foo
        , bar
        , baz
    )
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(4)"

    Given the buffer is empty
    When I insert:
    """
    module Foo
        (
          foo
        , (<^^>)
        , bar
    )
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(4)"

  Scenario: After {
    Given the buffer is empty
    When I insert:
    """
    data Person = Person {
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(4)"

    Given the buffer is empty
    When I insert:
    """
    data Person = Person
        {
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(6)"

  Scenario: Before {
    Given the buffer is empty
    When I insert:
    """
    data Person = Person
    {
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(4)"

  Scenario: Before }
    Given the buffer is empty
    When I insert:
    """
    data Person = Person {
    }
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(21)"

    Given the buffer is empty
    When I insert:
    """
    data Person = Person
        { firstName :: !String  -- ^ First name
        , lastName  :: !String  -- ^ Last name
        , age       :: !Int     -- ^ Age
    } deriving (Eq, Show)
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(4)"

    Given the buffer is empty
    When I insert:
    """
    main = do
        run defaultConfig {
            path = "test.txt"
    }
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(4)"

  Scenario: After [
    Given the buffer is empty
    When I insert:
    """
    foobarbaz = [ qux
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(14)"

    Given the buffer is empty
    When I insert:
    """
    foo = do
        bar <- baz [
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(8)"

  Scenario: Before ]
    Given the buffer is empty
    When I insert:
    """
    foobarbaz = [
    ]
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(12)"

    Given the buffer is empty
    When I insert:
    """
    foobarbaz = [
        qux
    ]
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(4)"

    Given the buffer is empty
    When I insert:
    """
    foobar = [
        foo,
        bar
    ]
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(4)"

    Given the buffer is empty
    When I insert:
    """
    foobar = [ foo
             , bar
    ]
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(9)"

    Given the buffer is empty
    When I insert:
    """
    foobar = [ foo,
               bar
    ]
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(9)"

    Given the buffer is empty
    When I insert:
    """
    foobar = [
        foobar
            baz,
        foobar
            qux
    ]
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(4)"

  Scenario: After ,
    Given the buffer is empty
    When I insert:
    """
    import Data.Text (foo,
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(18)"

  Scenario: Before ,
    Given the buffer is empty
    When I insert:
    """
    module Foo
        (
          foo
    ,
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(4)"

    Given the buffer is empty
    When I insert:
    """
    import Data.Text ( foo
                     , bar
    ,
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(17)"

    Given the buffer is empty
    When I insert:
    """
    import System.Process ( CreateProcess(..)
                          , StdStream(..)
    ,
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(22)"

    Given the buffer is empty
    When I insert:
    """
    foo = mconcat [ "This is ("
    ,
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(14)"

    Given the buffer is empty
    When I insert:
    """
    foo = bar {
        baz = 1,
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(4)"

  Scenario: Before ->
    Given the buffer is empty
    When I insert:
    """
    foobar :: ByteString
    ->
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(7)"

    Given the buffer is empty
    When I insert:
    """
    foobar :: ByteString
           -> (Char -> Char)
    ->
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(7)"

    Given the buffer is empty
    When I insert:
    """
    foo xs = case xs of
        (x:xs') | x == 'a'
    ->
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(14)"

  Scenario: Before =>
    Given the buffer is empty
    When I insert:
    """
    foobar :: (Monad m)
    =>
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(7)"

  Scenario: After =
    Given the buffer is empty
    When I insert:
    """
    foobar =
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(4)"

  Scenario: After = line
    Given the buffer is empty
    When I insert:
    """
    main = foobar
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(7 0)"

  Scenario: After let line
    Given the buffer is empty
    When I insert:
    """
    foobar = let bar = True
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(13 19 0)"

    Given the buffer is empty
    When I insert:
    """
    main = do
        let foo = 1
            bar = 2
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(8 14 0 4)"

    Given the buffer is empty
    When I insert:
    """
    main = foo
      where
        bar = do
            baz
            let qux = 1
                quux = 2
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(12 19 0 4 8)"

  Scenario: Before |
    Given the buffer is empty
    When I insert:
    """
    data Foo = Bar
    |
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(9)"

    Given the buffer is empty
    When I insert:
    """
    data Foo = Bar
             | Baz
    |
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(9)"

    Given the buffer is empty
    When I insert:
    """
    filter p (x:xs)
    |
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(4)"

    Given the buffer is empty
    When I insert:
    """
    filter p (x:xs)
        | p x       = x : filter p xs
    |
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(4)"

    Given the buffer is empty
    When I insert:
    """
    filter p (x:xs) | p x       = x : filter p xs
    |
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(16)"

  Scenario: Before | in where context
    Given the buffer is empty
    When I insert:
    """
    main = do
        foo
      where
        foo
    |
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(8)"

  Scenario: Before | in case context
    Given the buffer is empty
    When I insert:
    """
    foobar x = case x of
        Just y
    |
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(8)"

    Given the buffer is empty
    When I insert:
    """
    foobar x = case x of
                   Just y
    |
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(19)"

  Scenario: After import
    Given the buffer is empty
    When I insert:
    """
    import System.IO

    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(0 4)"

    Given the buffer is empty
    When I insert:
    """
    import System.IO (getChar)

    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(0)"

    Given the buffer is empty
    When I insert:
    """
    import qualified System.IO as IO
        ( getChar
        , putChar
        )
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(0)"

  Scenario: After then line
    Given the buffer is empty
    When I insert:
    """
    foobar = do
        if foo
            then bar
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(13)"

  Scenario: After else line
    Given the buffer is empty
    When I insert:
    """
    foobar = do
        if foo
            then bar
            else baz
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(13 0 4)"

  Scenario: After if then line
    Given the buffer is empty
    When I insert:
    """
    foobar = do
        if foo then
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(8)"

    Given the buffer is empty
    When I insert:
    """
    foobar = if foo then
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(13)"

  Scenario: After <- line
    Given the buffer is empty
    When I insert:
    """
    main = do
        args <- getArgs
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(4 12 0)"

  Scenario: After ( line
    Given the buffer is empty
    When I insert:
    """
    main = do
        putStrLn (foo
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(14)"

    Given the buffer is empty
    When I insert:
    """
    main = do
        foobar (Baz "qux"
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(12)"

  Scenario: After normal line
    Given the buffer is empty
    When I insert:
    """
    main = do
        foobar
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(4 8 0)"

    Given the buffer is empty
    When I insert:
    """
    import Data.Text
    
    main = do
        foobar ()
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(4 8 0)"

    Given the buffer is empty
    When I insert:
    """
    foo a' = do
        bar a' 'a'
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(4 8 0)"

    Given the buffer is empty
    When I insert:
    """
    foo x y = case x of
        True | y == 'a'
               -> putStrLn "a"
             | y == 'b'
               -> putStrLn "b"
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(14 0 4)"

  Scenario: In list comprehension
    Given the buffer is empty
    When I insert:
    """
    foo = let xy = [ (x, y) | x <- [1, 2, 3],
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(26)"

  Scenario: Hanging lambda
    Given the buffer is empty
    When I insert:
    """
    foo = alloca 10 $ \a ->
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(4 6)"

    Given the buffer is empty
    When I insert:
    """
    foobar = alloca 10 $ \a ->
        alloca 20 $ \b ->
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(4 8)"

  Scenario: After type signature
    Given the buffer is empty
    When I insert:
    """
    main :: IO ()
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(0 8)"

    Given the buffer is empty
    When I insert:
    """
    sort :: [a] -> [a]
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(0 8 15)"

    Given the buffer is empty
    When I insert:
    """
    foobar :: (Monad m) => a -> m a
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(0 10 28)"

    Given the buffer is empty
    When I insert:
    """
    foobar :: Text
           -> (Char -> Char)
           -> Text
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(0 10)"
