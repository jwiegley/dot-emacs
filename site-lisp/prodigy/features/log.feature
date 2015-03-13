Feature: Log

  Background:
    Given I add the following services:
      | name | cwd | command | args    |
      | foo  | foo | echo    | ("foo") |
    And I start prodigy

  Scenario: Not started
    When I press "$"
    Then I should see services:
      | name | highlighted |
      | foo  | t           |

  Scenario: Log mode
    When I press "s"
    And I press "$"
    Then I should be in buffer "*prodigy-foo*"
    And I should be in prodigy log mode

  Scenario: Quit
    When I press "s"
    And I press "$"
    Then I should be in prodigy log mode
    When I press "q"
    Then I should not be in prodigy log mode
    And the buffer "*prodigy-foo*" should exist
