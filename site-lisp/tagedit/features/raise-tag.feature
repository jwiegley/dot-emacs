Feature: Raise tag

  Scenario: Raise one, ditch others
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
    And I press "M-r"
    Then I should see:
    """
    <div>
      <li>abc</li>
    </div>
    """

# raise contents of attribute
# raise contents of tag
