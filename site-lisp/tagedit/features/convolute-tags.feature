Feature: Convolute tags

  Scenario: Simple, inline
    Given I insert "<a href="abc"><div id="def"><h1></h1></div></a>"
    When I place the cursor before "<h1>"
    And I press "M-?"
    Then I should see "<div id="def"><a href="abc"><h1></h1></a></div>"

  Scenario: Simple, multiline
    Given I insert:
    """
    <a href="abc">
      <div id="def">
        <h1></h1>
      </div>
    </a>
    """
    When I place the cursor before "<h1>"
    And I press "M-?"
    Then I should see:
    """
    <div id="def">
      <a href="abc">
        <h1></h1>
      </a>
    </div>
    """

  Scenario: With siblings to convolute
    Given I insert:
    """
    <a href="abc">
      <div id="def">
        <h1></h1>
        <h2></h2>
        <h3></h3>
      </div>
    </a>
    """
    When I place the cursor before "<h2>"
    And I press "M-?"
    Then I should see:
    """
    <div id="def">
      <h1></h1>
      <a href="abc">
        <h2></h2>
        <h3></h3>
      </a>
    </div>
    """
