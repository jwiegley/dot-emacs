Feature: Mark

  Scenario: No service
    Given I start prodigy
    When I press "m"
    Then the buffer should be empty

  Scenario: Single service
    Given I add the following services:
      | name |
      | foo  |
    And I start prodigy
    When I press "m"
    Then I should see services:
      | name | highlighted | marked |
      | foo  | t           | t      |

  Scenario: Multiple services
    Given I add the following services:
      | name |
      | foo  |
      | bar  |
    And I start prodigy
    When I press "m"
    And I press "m"
    Then I should see services:
      | name | highlighted | marked |
      | bar  | nil         | t      |
      | foo  | t           | t      |

  Scenario: Already marked
    Given I add the following services:
      | name |
      | foo  |
    And I start prodigy
    When I press "m"
    And I press "m"
    Then I should see services:
      | name | highlighted | marked |
      | foo  | t           | t      |

  Scenario: Mark all
    Given I add the following services:
      | name |
      | foo  |
      | bar  |
    And I start prodigy
    When I press "M"
    Then I should see services:
      | name | highlighted | marked |
      | bar  | t           | t      |
      | foo  | nil         | t      |

  Scenario: Mark tag
    Given I add the following services:
      | name | tags          |
      | foo  | (tag-1 tag-2) |
      | bar  | ()            |
      | baz  | (tag-2)       |
    And I start prodigy
    When I start an action chain
    And I press "t"
    And I type "tag-2"
    And I press "RET"
    And I execute the action chain
    Then I should see services:
      | name | marked |
      | bar  | nil    |
      | baz  | t      |
      | foo  | t      |
