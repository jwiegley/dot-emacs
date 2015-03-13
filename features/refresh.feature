Feature: Refresh

  Scenario: Refresh buffer
    Given I add the following services:
      | name |
      | foo  |
      | bar  |
    And I start prodigy
    When I press "m"
    Then I should see services:
      | name | highlighted | marked |
      | bar  | nil         | t      |
      | foo  | t           | nil    |
    When I press "g"
    Then I should see services:
      | name | highlighted | marked |
      | bar  | nil         | t      |
      | foo  | t           | nil    |

