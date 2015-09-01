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

