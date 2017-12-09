Feature: Join tags

  Scenario: Simple join, inline
    Given I insert "<p>Abc</p> <p>def</p>"
    When I place the cursor after " "
    And I press "M-J"
    Then I should see "<p>Abc def</p>"

  Scenario: Simple join, multiline
    Given I insert:
    """
    <p>
      Abc
    </p>
    <p>
      def
    </p>
    """
    When I place the cursor after "</p>"
    And I press "M-J"
    Then I should see:
    """
    <p>
      Abc
      def
    </p>
    """

  Scenario: Complex join, different tags
    Given I insert:
    """
    <ul>
      Abc
    </ul>
    <ol>
      def
    </ol>
    """
    When I place the cursor after "</ul>"
    And I start an action chain
    And I press "M-J"
    And I type "div"
    And I press "RET"
    And I execute the action chain
    Then I should see:
    """
    <div>
      Abc
      def
    </div>
    """
