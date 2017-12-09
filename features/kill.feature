Feature: Kill

  Scenario: Kill newline
    Given I insert:
    """
    <div
         id="def">
      ghi
    </div>
    """
    When I go to the end of the word "div"
    And I press "C-k"
    Then I should see:
    """
    <div     id="def">
      ghi
    </div>
    """

  Scenario: Kill inside quotes
    Given I insert "<div id="abc def">ghi</div>"
    When I go to the front of the word "def"
    And I press "C-k"
    Then I should see "<div id="abc ">ghi</div>"

  Scenario: Kill inside tag details, one line
    Given I insert "<div id="abc" class="def">ghi</div>"
    When I go to the front of the word "id"
    And I press "C-k"
    Then I should see "<div >ghi</div>"

  Scenario: Kill inside tag details, multiline
    Given I insert:
    """
    <div class="abc"
         id="def">
      ghi
    </div>
    """
    When I go to the end of the word "div"
    And I press "C-k"
    Then I should see:
    """
    <div
         id="def">
      ghi
    </div>
    """

  Scenario: Kill inside tag details, multiline attribute
    Given I insert:
    """
    <div class="abc
                def
                ghi" id="jkl">
      ghi
    </div>
    """
    When I go to the end of the word "div"
    And I press "C-k"
    Then I should see:
    """
    <div id="jkl">
      ghi
    </div>
    """

  Scenario: Kill tag contents, one line
    Given I insert "<div id="abc">def ghi</div>"
    When I go to the front of the word "ghi"
    And I press "C-k"
    Then I should see "<div id="abc">def </div>"

  Scenario: Kill tag contents, multiline
    Given I insert:
    """
    <div id="abc">def
      ghi
    </div>
    """
    When I go to the front of the word "def"
    And I press "C-k"
    Then I should see:
    """
    <div id="abc">
      ghi
    </div>
    """

  Scenario: Kill tag contents, multiline tag
    Given I insert:
    """
    <div id="abc">
      def ghi <p>
        jkl
      </p> mno
    </div>
    """
    When I go to the end of the word "def"
    And I press "C-k"
    Then I should see:
    """
    <div id="abc">
      def mno
    </div>
    """

  Scenario: Kill a nameless tag
    Given I insert "<!-- abc -->"
    When I go to point "1"
    And I press "C-k"
    Then I should not see "abc"

  Scenario: Kill a comment inside a tag
    Given I insert:
    """
    <div>
      <!-- abc -->
    </div>
    """
    When I go to the front of the word "abc"
    And I press "C-a"
    And I press "C-k"
    Then I should see:
    """
    <div>

    </div>
    """

  Scenario: Kill a tag
    Given I insert "abc<div></div>"
    When I go to the end of the word "abc"
    And I press "C-k"
    Then I should see "abc"
    And I should not see "div"

  Scenario: Kill stuff outside of tags
    Given I insert "stuff"
    When I go to point "3"
    And I press "C-k"
    Then I should see "st"
    And I should not see "uff"

  Scenario: Kill stuff outside of tags, part 2
    Given I insert:
    """
    stuff <p>hello
      there
    </p> whee
    """
    When I go to point "3"
    And I press "C-k"
    Then I should see "st whee"
