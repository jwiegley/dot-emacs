Feature: Goto tag match

  Scenario: Goto unpaired tag match
    Given I insert "<meta charset=\"utf-8\" /> "
    When I place the cursor after "<"
    And I press "C-%"
    Then the cursor should be before ">"
    When I press "C-%"
    # Gocha: when it's unpaired tag, only accept one time C-%
    Then the cursor should be before ">"

  Scenario: Goto paired tag match
    Given I insert "<p align=\"left\">The content</p><br />"
    When I place the cursor after "<p"
    And I press "C-%"
    Then the cursor should be between "p" and ">"
    When I press "C-%"
    Then the cursor should be at point "1"
