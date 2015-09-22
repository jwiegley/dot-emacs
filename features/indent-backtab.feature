Feature: hyai indent backtab
  In order to cycle indent candidates backward
  As an Emacs user
  I want to change indent in reverse order by backtab press

  Scenario: retain cursor position
    Given the buffer is empty
    When I insert:
    """
    main = do
    foobar
    """
    And I go to beginning of line
    And I press "<backtab>"
    Then current indentation is 4
    Then current column is 4

    Given the buffer is empty
    When I insert:
    """
    main = do
    foobar
    """
    And I place the cursor after "foo"
    And I press "<backtab>"
    Then current indentation is 4
    Then current column is 7

    Given the buffer is empty
    When I insert:
    """
    main = do
    foobar
    """
    And I place the cursor after "foobar"
    And I press "<backtab>"
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
    And I press "<backtab>"
    Then current indentation is 4
    Then current column is 4

  Scenario: indentation cycle backward
    Given the buffer is empty
    When I insert:
    """
    main = do
        foobar
    baz
    """
    And I go to beginning of line
    And I press "<backtab>"
    Then current indentation is 8
    Then current column is 8
    When I press "<backtab>"
    Then current indentation is 4
    Then current column is 4
    When I press "<backtab>"
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
    And I press "<backtab>"
    Then current indentation is 4
    Then current column is 7
    When I press "<backtab>"
    Then current indentation is 0
    Then current column is 3
    When I press "<backtab>"
    Then current indentation is 8
    Then current column is 11
