Feature: Julia mode basics
  Background:
    When the buffer is empty
    When I turn on julia-mode
    When I turn on electric-operator-mode

  ## Keyword argument =
  Scenario: Space standard assignment as normal
    When I type "a=b"
    Then I should see "a = b"

  Scenario: Don't space assignment inside function call
    When I type "f(a=b)"
    Then I should see "f(a=b)"

  Scenario: Declare functions with keyword arguments
    When I type "function f(x;y=0,kwargs...)"
    Then I should see "function f(x; y=0, kwargs...)"
