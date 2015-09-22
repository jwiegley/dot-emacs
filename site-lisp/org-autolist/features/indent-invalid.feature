Feature: hyai indent for invalid Haskell code
  In order to code smoothly
  As an Emacs user
  I want error not to be thrown by invalid code

  Scenario: in without let
    Given the buffer is empty
    When I insert:
    """
    foo = bar
    in
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(6 0)"

  Scenario: then without if
    Given the buffer is empty
    When I insert:
    """
    foo = bar
    then
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(6 0)"

  Scenario: else without then
    Given the buffer is empty
    When I insert:
    """
    foo = bar
    else
    """
    And I call hyai-indent-candidates at the current point
    Then indent candidates are "(6 0)"
