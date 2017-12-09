Feature: Misc

  Scenario: Insert quotes when writing attribute (but not otherwise)
    Given I insert "<div>abc</div>"
    When I go to the end of the word "div"
    And I type " id=d=f"
    And I press "C-3 C-f"
    And I type "="
    Then I should see "<div id="d=f">a=bc</div>"

  Scenario: Don't insert more quotes when they're there already
    Given I insert "<div "123">abc</div>"
    When I go to the end of the word "div"
    And I press "C-f"
    And I type "id="
    Then I should see "<div id="123">abc</div>"

  Scenario: If pressing quotes just after it was inserted, skip it
    Given I insert "<div>abc</div>"
    When I go to the end of the word "div"
    And I type " id="def"
    Then I should see "<div id="def">abc</div>"
