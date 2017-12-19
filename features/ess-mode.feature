Feature: R specific operators
  Background:
    When the buffer is empty
    When I turn on R-mode
    When I turn on electric-operator-mode

  Scenario: dot-tilde operator
    When I type "Species~."
    Then I should see "Species ~ ."

  Scenario: Interaction with ess-smart-comma when enabled
    When I set ess-smart-operators to t
    When I type "f(x,y)"
    Then I should see "f(x, y)"

  Scenario: Interaction with ess-smart-comma when disabled
    When I set ess-smart-operators to nil
    When I type "f(x,y)"
    Then I should see "f(x, y)"

  Scenario: Interaction with ess-smart-command when disabled and mode disabled
    When I turn off minor mode electric-operator-mode
    When I set ess-smart-operators to nil
    When I type "f(x,y)"
    Then I should see "f(x,y)"

  Scenario: Spaced equals for keyword args
    When I set electric-operator-R-named-argument-style to spaced
    When I type "somefunc(a=1, b=2)"
    Then I should see "somefunc(a = 1, b = 2)"

  Scenario: Equals for keyword args
    When I set electric-operator-R-named-argument-style to unspaced
    When I type "somefunc(a=1, b=2)"
    Then I should see "somefunc(a=1, b=2)"
