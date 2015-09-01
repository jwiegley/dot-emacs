Feature: Browse

  Scenario: No port or args containing port
    Given I add the following services:
      | name |
      | foo  |
    And I start prodigy
    When I press "o"
    Then I should see message "Could not determine port"
