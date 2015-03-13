Feature: Wrap with tags
  In order to make wrap region more useful in tag modes
  As a wrap region user
  I want to wrap region with tags

  Scenario: No tag wrap when no tag mode
    Given I turn on text-mode
    And I turn on wrap-region
    When I insert "this is some text"
    And I select "is some"
    And I start an action chain
    And I press "<"
    And I type "div"
    And I execute the action chain
    Then I should not see "this <div>is some</div> text"
    But I should see "this div<is some> text"

  Scenario: Wrap with tag
    Given I turn on html-mode
    And I turn on wrap-region
    When I insert "this is some text"
    And I select "is some"
    And I start an action chain
    And I press "<"
    And I type "div"
    And I execute the action chain
    Then I should see "<div>is some</div>"

  Scenario: Wrap with tag incuding attribute
    Given I turn on html-mode
    When I insert "this is some text"
    And I select "is some"
    And I turn on wrap-region
    And I start an action chain
    And I press "<"
    And I type "div class=\"some-class\""
    And I execute the action chain
    Then I should see "<div class=\"some-class\">is some</div>"

