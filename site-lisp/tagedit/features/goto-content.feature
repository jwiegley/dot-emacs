Feature: Goto tag content

  Scenario: Paired tag
    Given I insert "<p align=\"left\">The content</p>"
    When I place the cursor after "<p"
    And I press "M-'"
    Then the cursor should be between ">" and "T"

  Scenario: Unpaired tag
    Given I insert "<meta charset=\"utf-8\" />"
    When I place the cursor after "<meta"
    And I press "M-'"
    Then the cursor should be after "/>"
