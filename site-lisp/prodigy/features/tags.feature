Feature: Tags

  Scenario: Single tag
    Given I add the following services:
      | name | tags    |
      | foo  | (tag-1) |
    When I start prodigy
    Then I should see services:
      | name | tags    |
      | foo  | (tag-1) |

  Scenario: Multiple tags
    Given I add the following services:
      | name | tags          |
      | foo  | (tag-1 tag-2) |
    When I start prodigy
    Then I should see services:
      | name | tags          |
      | foo  | (tag-1 tag-2) |

  Scenario: Services with and services without
    Given I add the following services:
      | name | tags          |
      | foo  | (tag-1 tag-2) |
      | bar  | ()            |
      | baz  | (tag-2)       |
    When I start prodigy
    Then I should see services:
      | name | tags          |
      | bar  | ()            |
      | baz  | (tag-2)       |
      | foo  | (tag-1 tag-2) |
