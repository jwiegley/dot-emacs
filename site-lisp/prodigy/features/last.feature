Feature: Last

  Background:
    Given I add the following services:
      | name |
      | foo  |
      | bar  |
    And I start prodigy

  Scenario: At last line
    When I press "n"
    And I press "M->"
    Then I should see services:
      | name | highlighted |
      | bar  | nil         |
      | foo  | t           |

  Scenario: Not at last line
    And I press "M->"
    Then I should see services:
      | name | highlighted |
      | bar  | nil         |
      | foo  | t           |
