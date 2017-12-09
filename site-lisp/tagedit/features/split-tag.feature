Feature: Split tag

  Scenario: Simple, inline
    Given I insert "<p>Abc def</p>"
    When I place the cursor after " "
    And I press "M-S"
    Then I should see "<p>Abc </p><p>def</p>"

  Scenario: Simple, multiline
    Given I insert:
    """
    <p class="article">
      Abc
      def
    </p>
    """
    When I place the cursor after "Abc"
    And I press "M-S"
    Then I should see:
    """
    <p class="article">
      Abc
    </p>
    <p class="article">
      def
    </p>
    """
