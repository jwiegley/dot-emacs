Feature: Insert id

  Scenario: Insert id name attribute with solitary dot
    Given I insert "<div>abc</div>"
    When I go to the end of the word "div"
    And I type " #hmm"
    Then I should see "<div id="hmm">abc</div>"

  Scenario: Make room for id attribute, right side
    Given I insert "<div class="def">abc</div>"
    When I go to the front of the word "class"
    And I type "#hmm"
    Then I should see "<div id="hmm" class="def">abc</div>"

  Scenario: Make room for id attribute, left side
    Given I insert "<div>abc</div>"
    When I go to the end of the word "div"
    And I type "#hmm"
    Then I should see "<div id="hmm">abc</div>"

  Scenario: Insert normal dot, part 1
    Given I insert "<div>abc</div>"
    When I go to the end of the word "abc"
    And I type " #hmm"
    Then I should see "<div>abc #hmm</div>"

  Scenario: Insert normal dot, part 2
    Given I insert "<div href="def">abc</div>"
    When I go to the end of the word "def"
    And I type " #hmm"
    Then I should see "<div href="def #hmm">abc</div>"

  Scenario: Insert normal dot, part 3
    Given I insert "<!-- abc -->"
    When I go to the end of the word "abc"
    And I type "#hmm"
    Then I should see "<!-- abc#hmm -->"

  Scenario: Mark existing id attribute
    Given I insert "<div id="hmm">abc</div>"
    When I go to the end of the word "div"
    And I type "#"
    Then the region should be "hmm"
