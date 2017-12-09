Feature: Insert class

  Scenario: Insert class name attribute with solitary dot
    Given I insert "<div>abc</div>"
    When I go to the end of the word "div"
    And I type " .hmm"
    Then I should see "<div class="hmm">abc</div>"

  Scenario: Make room for class attribute, right side
    Given I insert "<div id="def">abc</div>"
    When I go to the front of the word "id"
    And I type ".hmm"
    Then I should see "<div class="hmm" id="def">abc</div>"

  Scenario: Make room for class attribute, left side
    Given I insert "<div>abc</div>"
    When I go to the end of the word "div"
    And I type ".hmm"
    Then I should see "<div class="hmm">abc</div>"

  Scenario: Insert normal dot, part 1
    Given I insert "<div>abc</div>"
    When I go to the end of the word "abc"
    And I type " .hmm"
    Then I should see "<div>abc .hmm</div>"

  Scenario: Insert normal dot, part 2
    Given I insert "<div href="def">abc</div>"
    When I go to the end of the word "def"
    And I type " .hmm"
    Then I should see "<div href="def .hmm">abc</div>"

  Scenario: Insert normal dot, part 3
    Given I insert "<!-- abc -->"
    When I go to the end of the word "abc"
    And I type ".hmm"
    Then I should see "<!-- abc.hmm -->"

  Scenario: Expand existing class attribute
    Given I insert "<div class="hmm">abc</div>"
    When I go to the end of the word "div"
    And I type ".hum"
    Then I should see "<div class="hmm hum">abc</div>"
