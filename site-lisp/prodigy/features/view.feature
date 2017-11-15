Feature: View

  Background:
    Given I am in a log buffer with output

  Scenario: Clear log output
    When I press "k"
    Then the buffer should be empty
