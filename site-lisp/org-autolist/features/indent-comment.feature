Feature: hyai indent comment
  In order to write comment efficiently
  As an Emacs user
  I want not to indent comment start, to indent relative in comment

  Scenario: Comment start
    Given the buffer is empty
    When I insert:
    """
    {-# LANGUAGE OverloadedStrings #-}
    """
    And I place the cursor before "{-"
    And I press "<tab>"
    Then current indentation is 0
    Then current column is 0

    Given the buffer is empty
    When I insert:
    """
    {-# LANGUAGE OverloadedStrings #-}
    {-# G
    """
    And I place the cursor before "{-# G"
    And I press "<tab>"
    Then current indentation is 0
    Then current column is 0

    Given the buffer is empty
    When I insert:
    """
      {-
    """
    And I place the cursor before "  {-"
    And I press "<tab>"
    Then current indentation is 2
    Then current column is 2

    Given the buffer is empty
    When I insert:
    """
    module Foo
        (
          -- bar
    """
    And I place the cursor before " --"
    And I press "<tab>"
    Then current indentation is 6
    Then current column is 6

  Scenario: Comment end
    Given the buffer is empty
    When I insert:
    """
       {-
          foo = bar
    -}
    """
    And I press "<tab>"
    Then current indentation is 3
    Then current column is 5

    Given the buffer is empty
    When I insert:
    """
      {-
          foo = bar
           -}
    """
    And I place the cursor before "  -}"
    And I press "<tab>"
    Then current indentation is 2
    Then current column is 2

  Scenario: In nestable comment
    Given the buffer is empty
    When I insert:
    """
    {- foo
    """
    And I press "<tab>"
    Then current indentation is 0
    Then current column is 6

    Given the buffer is empty
    When I insert:
    """
      {-
    
    """
    And I press "<tab>"
    Then current indentation is 5
    And I press "<tab>"
    Then current indentation is 5

    Given the buffer is empty
    When I insert:
    """
    {-
      main = do
    
    """
    And I press "<tab>"
    Then current indentation is 2
    And I press "<tab>"
    Then current indentation is 2

    Given the buffer is empty
    When I insert:
    """
    {- main = do
          foo
    """
    And I press "<tab>"
    Then current indentation is 3
    And current column is 6

  Scenario: In one line comment
    Given the buffer is empty
    When I insert:
    """
    module Foo
        (
          -- bar
    """
    And I place the cursor before "bar"
    And I press "<tab>"
    Then current indentation is 6
    Then current column is 9

    Given the buffer is empty
    When I insert:
    """
    foo = do
    putStrLn "foo" -- bar
    """
    And I place the cursor after "bar"
    And I press "<tab>"
    Then current indentation is 4
    Then current column is 25

  Scenario: Across one line comment
    Given the buffer is empty
    When I insert:
    """
    main = do
        -- foo
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(4)"

    Given the buffer is empty
    When I insert:
    """
    main = do -- foo
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(4)"

    Given the buffer is empty
    When I insert:
    """
    main = do -- foo
        -- bar
        -- baz
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(4)"

  Scenario: Across nestable comment
    Given the buffer is empty
    When I insert:
    """
    main = do
        {- foo -}
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(4)"

    Given the buffer is empty
    When I insert:
    """
    main = do {- foo
        bar
        -}
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(4)"

    Given the buffer is empty
    When I insert:
    """
    main = do
    {- foo
       bar
    -}
    
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(4)"

  Scenario: Keyword in comment
    Given the buffer is empty
    When I insert:
    """
    main = foo {-
    module Foo -}
           foo
    (
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(7 11 0)"
