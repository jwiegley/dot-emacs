Feature: Splice tag

  Scenario: Splice tag, multiline
    Given I insert:
    """
    <div>
      <ul>
        <li>abc</li>
        <li>def</li>
      </ul>
    </div>
    """
    When I go to the front of the word "li"
    And I press "M-s"
    Then I should see:
    """
    <div>
      <li>abc</li>
      <li>def</li>
    </div>
    """
    And I press "M-s"
    Then I should see:
    """
    <li>abc</li>
    <li>def</li>
    """

  Scenario: Splice tag, inline
    Given I insert "<div><p>hi</p><p>yo</p> greetings</div>"
    When I go to the front of the word "p"
    And I press "M-s"
    Then I should see "<p>hi</p><p>yo</p> greetings"
    And I should not see "<div>"
    And I should not see "</div>"
