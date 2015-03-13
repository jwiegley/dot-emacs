Feature: company-ghc prefix

  Scenario: Pragma prefix
    Given the buffer is empty
    When I insert:
    """
    {-#
    """
    And I execute company-ghc prefix command at current point
    Then company-ghc prefix is ""

    Given the buffer is empty
    When I insert:
    """
    {-##-}
    """
    And I place the cursor before "#-}"
    And I execute company-ghc prefix command at current point
    Then company-ghc prefix is ""

    Given the buffer is empty
    When I insert:
    """
    {-# SomePrefix
    """
    And I execute company-ghc prefix command at current point
    Then company-ghc prefix is "SomePrefix"

    Given the buffer is empty
    When I insert:
    """
    {-#SomePrefix
    """
    And I execute company-ghc prefix command at current point
    Then company-ghc prefix is "SomePrefix"

    Given the buffer is empty
    When I insert:
    """
    {-#SomePrefix#-}
    """
    And I place the cursor before "#-}"
    And I execute company-ghc prefix command at current point
    Then company-ghc prefix is "SomePrefix"

  Scenario: LANGUAGE prefix
    Given the buffer is empty
    When I insert:
    """
    {-# LANGUAGE SomeFeature
    """
    And I execute company-ghc prefix command at current point
    Then company-ghc prefix is "SomeFeature"

    Given the buffer is empty
    When I insert:
    """
    {-#LANGUAGE SomeFeature
    """
    And I execute company-ghc prefix command at current point
    Then company-ghc prefix is "SomeFeature"

    Given the buffer is empty
    When I insert:
    """
    {-#LANGUAGE SomeFeature#-}
    """
    And I place the cursor before "#-}"
    And I execute company-ghc prefix command at current point
    Then company-ghc prefix is "SomeFeature"

    Given the buffer is empty
    When I insert:
    """
    {-# LANGUAGE SomeFeature, AnotherFeature
    """
    And I execute company-ghc prefix command at current point
    Then company-ghc prefix is "AnotherFeature"

    Given the buffer is empty
    When I insert:
    """
    {-# LANGUAGE SomeFeature,
    """
    And I execute company-ghc prefix command at current point
    Then company-ghc prefix is ""

    Given the buffer is empty
    When I insert:
    """
    {-# LANGUAGE SomeFeature,
                 AnotherFeature
    """
    And I execute company-ghc prefix command at current point
    Then company-ghc prefix is "AnotherFeature"

  Scenario: OPTIONS_GHC prefix
    Given the buffer is empty
    When I insert:
    """
    {-# OPTIONS_GHC -fSomeOption
    """
    And I execute company-ghc prefix command at current point
    Then company-ghc prefix is "-fSomeOption"

    Given the buffer is empty
    When I insert:
    """
    {-# OPTIONS_GHC -fSomeOption, AnotherOption
    """
    And I execute company-ghc prefix command at current point
    Then company-ghc prefix is "AnotherOption"

  Scenario: Import module prefix
    Given the buffer is empty
    When I insert:
    """
    import Some.Module
    """
    And I execute company-ghc prefix command at current point
    Then company-ghc prefix is "Some.Module"

    Given the buffer is empty
    When I insert:
    """
    import safe qualified "package" Some.Module
    """
    And I execute company-ghc prefix command at current point
    Then company-ghc prefix is "Some.Module"

  Scenario: Imported variable prefix
    Given the buffer is empty
    When I insert:
    """
    import Some.Module (SomeVar
    """
    And I execute company-ghc prefix command at current point
    Then company-ghc prefix is "SomeVar"

    Given the buffer is empty
    When I insert:
    """
    import Some.Module (SomeVar, AnotherVar
    """
    And I execute company-ghc prefix command at current point
    Then company-ghc prefix is "AnotherVar"

    Given the buffer is empty
    When I insert:
    """
    import safe qualified "package" Some.Module ( SomeVar
                                                  , AnotherVar
    """
    And I execute company-ghc prefix command at current point
    Then company-ghc prefix is "AnotherVar"

  Scenario: Keyword prefix
    Given the buffer is empty
    When I insert:
    """
    main = do
        someFunc
    """
    And I execute company-ghc prefix command at current point
    Then company-ghc prefix is "someFunc"

        Given the buffer is empty
    When I insert:
    """
    main = do
        some$func
    """
    And I execute company-ghc prefix command at current point
    Then company-ghc prefix is "func"

  Scenario: Stopping prefix
    Given the buffer is empty
    When I insert:
    """
    main = do
        putStrLn "someFunc  "
    """
    And I place the cursor after "someFunc"
    And I execute company-ghc prefix command at current point
    Then company-ghc prefix stopped

  Scenario: No prefix
    Given the buffer is empty
    When I insert:
    """
    someLocalFunc
    """
    And I execute company-ghc prefix command at current point
    Then company-ghc prefix none

  Scenario: Qualified prefix
    Given the buffer is empty
    When I insert:
    """
    main = do
        T.someFunc
    """
    And I execute company-ghc prefix command at current point
    Then company-ghc prefix is cons with "someFunc" and "t"
