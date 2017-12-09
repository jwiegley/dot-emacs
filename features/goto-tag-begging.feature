Feature: Goto tag begging

  Scenario: Goto unpaired tag begging
    Given I insert "<meta charset=\"utf-8\" /> "
    When I place the cursor after "utf"
    And I press "C-^"
    Then the cursor should be before "<meta"

  Scenario: Goto paired tag begging
    Given I insert "<p align=\"left\">The content</p><br />"
    When I place the cursor after "The"
    And I press "C-^"
    Then the cursor should be before "<p"
