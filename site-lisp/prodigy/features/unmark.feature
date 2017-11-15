Feature: Unmark

  Scenario: No service
    Given I start prodigy
    When I press "u"
    Then the buffer should be empty

  Scenario: Single service
    Given I add the following services:
      | name |
      | foo  |
    And I start prodigy
    When I press "m"
    And I press "u"
    Then I should see services:
      | name | highlighted | marked |
      | foo  | t           | nil    |

  Scenario: Multiple services
    Given I add the following services:
      | name |
      | foo  |
      | bar  |
    And I start prodigy
    When I press "m"
    And I press "p"
    And I press "u"
    Then I should see services:
      | name | highlighted | marked |
      | bar  | nil         | nil    |
      | foo  | t           | nil    |
    When I press "m"
    And I press "u"
    Then I should see services:
      | name | highlighted | marked |
      | bar  | nil         | nil    |
      | foo  | t           | nil    |

  Scenario: Already marked
    Given I add the following services:
      | name |
      | foo  |
    And I start prodigy
    When I press "u"
    And I press "u"
    Then I should see services:
      | name | highlighted | marked |
      | foo  | t           | nil    |

  Scenario: Unmark all
    Given I add the following services:
      | name |
      | foo  |
      | bar  |
    And I start prodigy
    When I press "M"
    And I press "U"
    Then I should see services:
      | name | highlighted | marked |
      | bar  | t           | nil    |
      | foo  | nil         | nil    |

  Scenario: Unmark tag
    Given I add the following services:
      | name | tags          |
      | foo  | (tag-1 tag-2) |
      | bar  | ()            |
      | baz  | (tag-2)       |
    And I start prodigy
    When I start an action chain
    And I press "M"
    And I press "T"
    And I type "tag-2"
    And I press "RET"
    And I execute the action chain
    Then I should see services:
      | name | marked |
      | bar  | t      |
      | baz  | nil    |
      | foo  | nil    |
