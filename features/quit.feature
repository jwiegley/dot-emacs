Feature: Quit

  Background:
    Given I add the following services:
      | name |
      | foo  |
      | bar  |
    And I start prodigy

  Scenario: Quit Prodigy mode
    When I press "q"
    Then I should not be in prodigy mode

  Scenario: Quit remembers state
    When I press "m"
    Then I should see services:
      | name | highlighted | marked |
      | bar  | nil         | t      |
      | foo  | t           | nil    |
    When I press "q"
    Then I should not be in prodigy mode
    When I start prodigy
    Then I should see services:
      | name | highlighted | marked |
      | bar  | nil         | t      |
      | foo  | t           | nil    |

  Scenario: Quit hard does not remember state
    When I press "m"
    Then I should see services:
      | name | highlighted | marked |
      | bar  | nil         | t      |
      | foo  | t           | nil    |
    When I kill the prodigy buffer
    Then I should not be in prodigy mode
    When I start prodigy
    Then I should see services:
      | name | highlighted | marked |
      | bar  | t           | nil    |
      | foo  | nil         | nil    |
