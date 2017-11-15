Feature: First

  Background:
    Given I add the following services:
      | name |
      | foo  |
      | bar  |
    And I start prodigy

  Scenario: At first line
    When I press "M-<"
    Then I should see services:
      | name | highlighted |
      | bar  | t           |
      | foo  | nil         |

  Scenario: Not at first line
    When I press "n"
    And I press "M-<"
    Then I should see services:
      | name | highlighted |
      | bar  | t           |
      | foo  | nil         |
