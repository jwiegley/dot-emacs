Feature: Barfing

  Scenario: Barf it out, tight
    Given I insert:
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
    When I go to the front of the word "ul"
    And I press "C-<left>"
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
    And I press "C-<left>"
    Then I should see:
    """
    <div>
      <ul></ul>
      <li>abc</li>
      <li>
        def
      </li>
    </div>
    """

  Scenario: Barf it out, inline
    Given I insert "<div><p>Some text with <em>emphasis</em>, don'tcha know.</p></div>"
    When I go to the front of the word "p"
    And I press "C-<left>"
    Then I should see "<div><p>Some text with <em>emphasis</em></p>, don'tcha know.</div>"
    And I press "C-<left>"
    Then I should see "<div><p>Some text with</p> <em>emphasis</em>, don'tcha know.</div>"
    And I press "C-<left>"
    Then I should see "<div><p></p>Some text with <em>emphasis</em>, don'tcha know.</div>"

  Scenario: Barf it out, loose tags
    Given I insert:
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
    When I go to the front of the word "ul"
    And I press "C-<left>"
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
    When I press "C-<left>"
    Then I should see:
    """
    <div>
      <ul></ul>

      <li>abc</li>

      <li>
        def
      </li>
    </div>
    """
