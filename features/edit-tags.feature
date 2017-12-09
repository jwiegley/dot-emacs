Feature: Edit tags

  Background:
    Given I activate tagedit experimental features

  Scenario: Insert tag
    When I type "<div"
    Then I should see "<div></div>"

  Scenario: Insert tag with attribute
    When I type "<div data-something"
    Then I should see "<div data-something></div>"

  Scenario: Insert self-closing tag
    When I type "<input"
    Then I should see "<input>"
    And I should not see "</input>"

  Scenario: Jump inside tag with TAB
    When I type "<div"
    And I press "TAB"
    And I type "abc"
    Then I should see "<div>abc</div>"

  Scenario: Edit tag
    Given I insert "<div id="abc">def</div>"
    When I go to the end of the word "div"
    And I type "s"
    Then I should see "<divs id="abc">def</divs>"

  Scenario: Break up a tag
    Given I insert "<div id="abc">def</div>"
    When I go to the end of the word "div"
    And I press "C-b"
    And I type " "
    Then I should see "<di v id="abc">def</di>"

  Scenario: Edit self-closing tag
    Given I insert "<input type="text"> abc"
    When I go to the end of the word "input"
    And I type "ss"
    Then I should see "<inputss type="text"></inputss> abc"

  Scenario: Closing a tag with />
    When I type "<h3/"
    Then I should see "<h3/>"
    And I should not see "</h3>"

  Scenario: Closing tag, don't bug out
    When I type "<h3/"
    And I press "C-f"
    And I type " "
    Then I should not see "</h3>"

  Scenario: Editing a self-closed tag
    Given I insert "<h2/>"
    When I go to the end of the word "h2"
    And I press "DEL"
    And I should not see "</"
    And I type "3"
    Then I should see "<h3/>"
    And I should not see "</h3>"

# Known bug:

#  Scenario: Re-opening a self-closing tag
#    Given I insert "<h3/>"
#    When I go to the end of the word "h3"
#    And I press "C-f"
#    And I press "DEL"
#    Then I should see "<h3></h3>"
#
#  Scenario: Re-opening a self-closing tag, from outside
#    Given I insert "<h3/>"
#    And I press "C-e"
#    And I press "C-b"
#    And I press "DEL"
#    Then I should see "<h3></h3>"

  Scenario: Do not allow self-closing divs
    When I type "<div/"
    Then I should see "<div></div>"

  Scenario: Do not allow self-closing divs
    When I type "<div uri=/"
    Then I should see "<div uri="/"></div>"

  Scenario: Do not allow self-closing spans
    When I type "<span/"
    Then I should see "<span></span>"

  Scenario: JSTL tags
    When I type "<c:forEach"
    Then I should see "<c:forEach></c:forEach>"

  Scenario: Don't destroy invalid markup
    Given I insert "<div id>"
    When I go to the end of the word "div"
    And I type "ss"
    Then I should see "<divss id>"

  Scenario: Tags with dashes
    When I type "<abc-def"
    Then I should see "<abc-def></abc-def>"

  Scenario: HTML comments
    When I type "<!-- abc --"
    Then I should see "<!-- abc -->"
    And I should not see "><"

  Scenario: Interaction with slurp
    Given I insert "<li></li>"
    And I go to point "1"
    And I type "<ul"
    Then I should see "<ul></ul><li></li>"
    When I press "C-<right>"
    Then I should see "<ul><li></li></ul>"
    When I type "e"
    Then I should see "<ule><li></li></ule>"

  # removing <></> when backspace on opening <
  # editing a self-closing tag <something />
  # remove closing tag when adding /
  # add closing tag when removing /

  # editing the end-tag
  # support for multiple cursors

  # <!-- -->
