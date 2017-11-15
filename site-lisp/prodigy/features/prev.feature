Feature: Prev

  Scenario: No services
    Given I start prodigy
    When I press "p"
    Then I should see message "Cannot move further up"

  Scenario: Single service
    Given I add the following services:
      | name |
      | foo  |
    And I start prodigy
    When I press "p"
    Then I should see services:
      | name | highlighted |
      | foo  | t           |
    Then I should see message "Cannot move further up"

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
    When I press "p"
    Then I should see services:
      | name | highlighted |
      | bar  | t           |
      | foo  | nil         |
    When I press "p"
    Then I should see services:
      | name | highlighted |
      | bar  | t           |
      | foo  | nil         |
    Then I should see message "Cannot move further up"

  Scenario: Prev with status
    Given I add the following services:
      | name | status  |
      | bar  | running |
      | baz  | nil     |
      | foo  | failed  |
      | qux  | nil     |
    And I start prodigy
    When I press "M->"
    And I press "M-p"
    Then I should see services:
      | name | highlighted |
      | bar  | nil         |
      | baz  | nil         |
      | foo  | t           |
      | qux  | nil         |
    When I press "M-p"
    Then I should see services:
      | name | highlighted |
      | bar  | t           |
      | baz  | nil         |
      | foo  | nil         |
      | qux  | nil         |
    When I press "M-p"
    Then I should see services:
      | name | highlighted |
      | bar  | t           |
      | baz  | nil         |
      | foo  | nil         |
      | qux  | nil         |
