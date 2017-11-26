Feature: Hoogle search

  Scenario: Hoogle search results parsing
    Given the buffer is empty
    When I insert:
    """
    Prelude abs :: Num a => a -> a
    Prelude acosh :: Floating a => a -> a
    Prelude all :: (a -> Bool) -> [a] -> Bool
    Data.List all :: (a -> Bool) -> [a] -> Bool
    Prelude and :: [Bool] -> Bool
    package accelerate
    System.IO appendFile :: FilePath -> String -> IO ()
    Data.Monoid newtype All
    Network.Socket accept :: Socket -> IO (Socket, SockAddr)
    Control.Applicative class Applicative f => Alternative f
    Control.Exception data ArithException
    Control.Applicative module Control.Applicative
    Test.QuickCheck.Exception type AnException = SomeException
    Network.Socket AF_ARP :: Family
    keyword case
    Data.Array accumArray :: Ix i => (e -> a -> e) -> e -> (i, i) -> [(i, a)] -> Array i e
    """
    And I parse hoogle search results
    Then hoogle search candidates are:
    """
    ("abs" "acosh" "all" "all" "and" "appendFile"
     "accept" "AF_ARP" "accumArray")
    """

  Scenario: Hoogle search not found
    Given the buffer is empty
    When I insert:
    """
    No results found
    """
    And I parse hoogle search results
    Then hoogle search candidates are "()"

  Scenario Hoogle database not found
    Given the buffer is empty
    When I insert:
    """
    Could not find some databases: default
    """
    And I parse hoogle search results
    Then hoogle search candidates are "()"
