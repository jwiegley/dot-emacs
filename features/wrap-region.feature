Feature: Wrap Region
  In order to put text between puctuations and tags
  As an Emacs user
  I want to wrap it

  Scenario: No wrap when wrap-region is inactive
    Given I add wrapper "$/$"
    And I turn off wrap-region
    When I insert "This is some text"
    And I select "is some"
    And I press "$"
    Then I should not see "This $is some$ text"
    But I should see "This $is some text"

  Scenario: Fallback when no region selected
    Given there is no region selected
    When I insert "This is some text"
    And I press "("
    Then I should see "This is some text("

  Scenario: Global mode
    Given I add wrapper "$/$"
    And I turn on wrap-region globally
    When I open temp file "global"
    And I insert "This is some text"
    And I select "is some"
    And I press "$"
    Then I should see "This $is some$ text"

  Scenario: Negative prefix required - don't wrap
    Given I add wrapper "$/$"
    And I turn on wrap-region
    And I require negative prefix to wrap
    Then key "$" should not wrap

  Scenario: Negative prefix required - do wrap
    Given I add wrapper "$/$"
    And I turn on wrap-region
    And I require negative prefix to wrap
    When I insert "this is some text"
    And I select "is some"
    And I press "C-- $"
    Then I should see "this $is some$ text"

  Scenario: Except modes
    Given I add wrapper "$/$"
    And I turn on wrap-region globally
    And I add "text-mode" as an except mode
    When I open temp file "global"
    And I turn on text-mode
    And I insert "this is some text"
    And I select "is some"
    And I press "("
    Then I should not see "this (is some) text"
    But I should see "this (is some text"

  Scenario: Wrapped region is not activate by default
    Given I add wrapper "$/$"
    And I turn on wrap-region
    And I insert "this is some text"
    And I select "is some"
    And I press "$"
    Then I should see "this $is some$ text"
    Then there is no region selected

  Scenario: Keep the wrapped region active
    Given I add wrapper "$/$"
    Given I add wrapper "#/#"
    And I turn on wrap-region
    And I require region to remain active after wrapping
    And I insert "this is some text"
    And I select "is some"
    And I press "$"
    Then I should see "this $is some$ text"
    Then the region should be "is some"
    And I press "#"
    Then I should see "this $#is some#$ text"
    Then the region should be "is some"

  Scenario: Cursor placement when point is after mark
    Given I add wrapper "$/$"
    And I turn on wrap-region
    And I insert "this is some text"
    And I place the cursor before "is some"
    And I press "C-SPC"
    And I press "C-u 7 C-f"
    And I press "$"
    Then I should see "this $is some$ text"
    And the cursor should be between "some$" and " text"

  Scenario: Cursor placement when mark is after point
    Given I add wrapper "$/$"
    And I turn on wrap-region
    And I insert "this is some text"
    And I place the cursor after "is some"
    And I press "C-SPC"
    And I press "C-u 7 C-b"
    And I press "$"
    Then I should see "this $is some$ text"
    And the cursor should be between "this " and "$is"
