Feature: Goto tag end

  Scenario: Goto unpaired tag end
    Given I insert "<meta charset=\"utf-8\" /> "
    When I place the cursor after "utf"
    And I press "C-$"
    Then the cursor should be before ">"

  Scenario: Goto paired tag end
    Given I insert "<p align=\"left\">The content</p><br />"
    When I place the cursor after "The"
    And I press "C-$"
    Then the cursor should be between "p" and ">"
