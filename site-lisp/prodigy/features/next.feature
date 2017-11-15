Feature: Next

  Scenario: No services
    Given I start prodigy
    When I press "n"
    Then I should see message "Cannot move further down"

  Scenario: Single service
    Given I add the following services:
      | name |
      | foo  |
    And I start prodigy
    Then I should see services:
      | name | highlighted |
      | foo  | t           |
    When I press "n"
    Then I should see message "Cannot move further down"

  Scenario: Multiple services
    Given I add the following services:
      | name |
      | foo  |
      | bar  |
    And I start prodigy
    Then I should see services:
      | name | highlighted |
      | bar  | t           |
      | foo  | nil         |
    When I press "n"
    Then I should see services:
      | name | highlighted |
      | bar  | nil         |
      | foo  | t           |
    When I press "n"
    Then I should see message "Cannot move further down"

  Scenario: Next with status
    Given I add the following services:
      | name | status  |
      | bar  | nil     |
      | baz  | running |
      | foo  | nil     |
      | qux  | failed  |
    And I start prodigy
    When I press "M-n"
    Then I should see services:
      | name | highlighted |
      | bar  | nil         |
      | baz  | t           |
      | foo  | nil         |
      | qux  | nil         |
    When I press "M-n"
    Then I should see services:
      | name | highlighted |
      | bar  | nil         |
      | baz  | nil         |
      | foo  | nil         |
      | qux  | t           |
    When I press "M-n"
    Then I should see services:
      | name | highlighted |
      | bar  | nil         |
      | baz  | nil         |
      | foo  | nil         |
      | qux  | t           |
