Feature: Double spacing when requested
  Background:
    When the buffer is empty
    When I turn on text-mode
    When I turn on electric-operator-mode
    When I set electric-operator-enable-in-docs to t

  Scenario: Single space '.'
    When I set electric-operator-double-space-docs to nil
    When I type "hello.World"
    Then I should see "hello. World"

  Scenario: Double space '.'
    When I set electric-operator-double-space-docs to t
    When I type "hello.World"
    Then I should see "hello.  World"
