Feature: Hooks
  In order to more easily customize wrap region
  As a wrap region user
  I want to hook it up

  Scenario: Mode hook
    Given I add a mode hook that erases buffer
    And I insert "This is some text"
    When I turn on wrap-region
    Then the buffer should be empty

  Scenario: Before wrap hook
    Given I add a before wrap hook that replaces "is some" with "some is"
    When I turn on wrap-region
    And I insert "This is some text"
    And I select "is some"
    And I press "("
    Then I should not see "This (is some) text"
    But I should see "This (some is) text"

  Scenario: After wrap hook
    Given I add an after wrap hook that replaces "(" with "["
    And I add an after wrap hook that replaces ")" with "]"
    When I turn on wrap-region
    And I insert "This is some text"
    And I select "is some"
    And I press "("
    Then I should not see "This (is some) text"
    But I should see "This [is some] text"

