Feature: Default directory

  Scenario: Set default directory to cwd for service at point
    Given I add the following services:
      | name | cwd |
      | foo  | foo |
      | bar  | bar |
    And I start prodigy
    Then default directory should be "bar"
    When I press "n"
    Then default directory should be "foo"
    When I press "p"
    Then default directory should be "bar"
