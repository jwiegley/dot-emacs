Feature: Filter

  Background:
    Given I add the following services:
      | name | tags          |
      | bar  | (tag-3)       |
      | baz  | (tag-2)       |
      | foo  | (tag-1 tag-2) |
    And I start prodigy

  Scenario: Filter by single tag
    When I filter by tag "tag-2"
    Then I should see services:
      | name | highlighted |
      | baz  | t           |
      | foo  | nil         |

  Scenario: Filter by muldiple tags
    When I filter by tag "tag-2"
    Then I should see services:
      | name | highlighted |
      | baz  | t           |
      | foo  | nil         |
    When I filter by tag "tag-1"
    Then I should see services:
      | name | highlighted |
      | foo  | t           |

  Scenario: Filter by name
    When I filter by name "ba"
    Then I should see services:
      | name | highlighted |
      | bar  | t           |
      | baz  | nil         |

  Scenario: Filter by name - case ignored
    When I filter by name "BA"
    Then I should see services:
      | name | highlighted |
      | bar  | t           |
      | baz  | nil         |

  Scenario: Filter all
    When I filter by tag "tag-2"
    Then I should see services:
      | name | highlighted |
      | baz  | t           |
      | foo  | nil         |
    When I filter by tag "tag-1"
    Then I should see services:
      | name | highlighted |
      | foo  | t           |
    When I filter by tag "tag-3"
    Then I should see services no services

  Scenario: Clear filters
    When I filter by tag "tag-2"
    Then I should see services:
      | name | highlighted |
      | baz  | t           |
      | foo  | nil         |
    When I press "F"
    Then I should see services:
      | name | highlighted |
      | bar  | t           |
      | baz  | nil         |
      | foo  | nil         |
