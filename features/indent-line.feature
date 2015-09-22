Feature: hyai indent line
  In order to choose indent candidates
  As an Emacs user
  I want to change indent by tab press

  Scenario: retain cursor position
    Given the buffer is empty
    When I insert:
    """
    main = do
    foobar
    """
    And I go to beginning of line
    And I press "<tab>"
    Then current indentation is 4
    Then current column is 4

    Given the buffer is empty
    When I insert:
    """
    main = do
    foobar
    """
    And I place the cursor after "foo"
    And I press "<tab>"
    Then current indentation is 4
    Then current column is 7

    Given the buffer is empty
    When I insert:
    """
    main = do
    foobar
    """
    And I place the cursor after "foobar"
    And I press "<tab>"
    Then current indentation is 4
    Then current column is 10

  Scenario: move cursor position at the beginning
    Given the buffer is empty
    When I insert:
    """
    main = do
             foobar
    """
    And I go to beginning of line
    And I press "<tab>"
    Then current indentation is 4
    Then current column is 4

  Scenario: indentation cycle
    Given the buffer is empty
    When I insert:
    """
    main = do
        foobar
    baz
    """
    And I go to beginning of line
    And I press "<tab>"
    Then current indentation is 4
    Then current column is 4
    When I press "<tab>"
    Then current indentation is 8
    Then current column is 8
    When I press "<tab>"
    Then current indentation is 0
    Then current column is 0

  Scenario: indentation cycle and retain cursor position
    Given the buffer is empty
    When I insert:
    """
    main = do
        foobar
    baz
    """
    And I place the cursor after "baz"
    And I press "<tab>"
    Then current indentation is 4
    Then current column is 7
    When I press "<tab>"
    Then current indentation is 8
    Then current column is 11
    When I press "<tab>"
    Then current indentation is 0
    Then current column is 3

  Scenario: newline and indent after normal line
    Given the buffer is empty
    When I insert:
    """
    main = do
        foobar
    """
    And I press "RET"
    Then current indentation is 4
    And I press "<tab>"
    Then current indentation is 8
    When I press "<tab>"
    Then current indentation is 0

  Scenario: newline and indent after empty line
    Given the buffer is empty
    When I insert:
    """
    main = do
    
    """
    And I press "RET"
    Then current indentation is 4

    Given the buffer is empty
    When I insert:
    """
    main = foo
      where
    
    """
    And I press "RET"
    Then current indentation is 4

    Given the buffer is empty
    When I insert:
    """
    main = do
        foobar
    
    """
    And I press "RET"
    Then current indentation is 0
    And I press "<tab>"
    Then current indentation is 4
    When I press "<tab>"
    Then current indentation is 8
    When I press "<tab>"
    Then current indentation is 0

    Given the buffer is empty
    When I insert:
    """
    main = do
        foobar
      where
        barbaz = do
            qux
    
    
    """
    And I press "RET"
    Then current indentation is 0
    And I press "<tab>"
    Then current indentation is 4
    When I press "<tab>"
    Then current indentation is 8
    When I press "<tab>"
    Then current indentation is 12
    And I press "<tab>"
    Then current indentation is 0

    Given the buffer is empty
    When I insert:
    """
    main = do
        foobar
    
        -- comment
    """
    And I press "RET"
    Then current indentation is 0
    And I press "<tab>"
    Then current indentation is 4
    When I press "<tab>"
    Then current indentation is 8
    And I press "<tab>"
    Then current indentation is 0

  Scenario: tab in string
    Given the buffer is empty
    When I insert:
    """
    main = do
    putStrLn "foobar"
    """
    And I place the cursor after "foo"
    And I press "<tab>"
    Then current indentation is 4

  Scenario: multiline string
    Given the buffer is empty
    When I insert:
    """
    foobar = "baz\
    """
    And I press "RET"
    Then current indentation is 0
    And I press "<tab>"
    Then current indentation is 0

    Given the buffer is empty
    When I insert:
    """
    foobar = "baz\
             \qux\
    """
    And I press "RET"
    Then current indentation is 9
    And I press "<tab>"
    Then current indentation is 9

    Given the buffer is empty
    When I insert:
    """
    foo = "bar\
          \baz\
             \qux\
    """
    And I press "<tab>"
    Then current indentation is 6
    And current column is 11
