Feature: Fix whitespace after operator
  Background:
    When I turn on prog-mode
    When I turn on electric-operator-mode
    When the buffer is empty

  Scenario: Adding a comma in the middle of a list
    When I type "foo(a, b c)"
    When I place the cursor between "a, b" and " c"
    When I type ","
    Then I should see "foo(a, b, c)"
