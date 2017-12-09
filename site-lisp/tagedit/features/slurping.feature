Feature: Slurping

  Scenario: Slurp it up, tight tags
    Given I insert:
    """
    <div>
      <ul>
      </ul>
      <li>abc</li>
      <li>
        def
      </li>
    </div>
    """
    When I go to the front of the word "ul"
    And I press "C-<right>"
    Then I should see:
    """
    <div>
      <ul>
        <li>abc</li>
      </ul>
      <li>
        def
      </li>
    </div>
    """
    When I press "C-<right>"
    Then I should see:
    """
    <div>
      <ul>
        <li>abc</li>
        <li>
          def
        </li>
      </ul>
    </div>
    """

  Scenario: Slurp it up, inline
    Given I insert "<div><p></p>Some text with <em>emphasis</em>, don'tcha know.</div>"
    When I go to the front of the word "p"
    And I press "C-<right>"
    Then I should see "<div><p>Some text with</p> <em>emphasis</em>, don'tcha know.</div>"
    And I press "C-<right>"
    Then I should see "<div><p>Some text with <em>emphasis</em></p>, don'tcha know.</div>"
    And I press "C-<right>"
    Then I should see "<div><p>Some text with <em>emphasis</em>, don'tcha know.</p></div>"

  Scenario: Slurp it up, loose tags
    Given I insert:
    """
    <div>
      <ul>
      </ul>

      <li>abc</li>

      <li>
        def
      </li>
    </div>
    """
    When I go to the front of the word "ul"
    And I press "C-<right>"
    Then I should see:
    """
    <div>
      <ul>

        <li>abc</li>
      </ul>

      <li>
        def
      </li>
    </div>
    """
    When I press "C-<right>"
    Then I should see:
    """
    <div>
      <ul>

        <li>abc</li>

        <li>
          def
        </li>
      </ul>
    </div>
    """

  Scenario: Slurp it up, stand-alone tags
    Given I insert:
    """
    <div></div>
    <hr>
    <div></div>
    """
    When I go to the front of the word "div"
    And I press "C-<right>"
    Then I should see:
    """
    <div>
      <hr>
    </div>
    <div></div>
    """

  Scenario: Slurp it up, inline to multiline
    Given I insert:
    """
    <div>
      <ul></ul>
      <li>abc</li>
      <li>def</li>
    </div>
    """
    When I go to the front of the word "ul"
    And I press "C-<right>"
    Then I should see:
    """
    <div>
      <ul>
        <li>abc</li>
      </ul>
      <li>def</li>
    </div>
    """

  Scenario: Slurp it up, inline to multiline, part 2
    Given I insert:
    """
    <div>
      <ul><li>abc</li></ul>
      <li>def</li>
    </div>
    """
    When I go to the front of the word "ul"
    And I press "C-<right>"
    Then I should see:
    """
    <div>
      <ul>
        <li>abc</li>
        <li>def</li>
      </ul>
    </div>
    """

  Scenario: Slurp it up, open self-closing
    Given I insert:
    """
    <div>
      <ul/>
      <li>abc</li>
      <li>def</li>
    </div>
    """
    When I go to the front of the word "ul"
    And I press "C-<right>"
    Then I should see:
    """
    <div>
      <ul>
        <li>abc</li>
      </ul>
      <li>def</li>
    </div>
    """

  Scenario: Slurp it up, not closest sibling
    Given I insert:
    """
    <div>
      <div>
        <ul>
          <li>abc</li>
        </ul>
      </div>
      <li>def</li>
    </div>
    """
    When I go to the front of the word "ul"
    And I press "C-<right>"
    Then I should see:
    """
    <div>
      <div>
        <ul>
          <li>abc</li>
        </ul>
        <li>def</li>
      </div>
    </div>
    """
    When I press "C-<right>"
    Then I should see:
    """
    <div>
      <div>
        <ul>
          <li>abc</li>
          <li>def</li>
        </ul>
      </div>
    </div>
    """
