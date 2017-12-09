Feature: Edit string at point

  Scenario: Open string in new buffer, then close again
    Given I turn on javascript-mode
    And I insert "var s = "my string";"
    When I go to the front of the word "string"
    And I edit the string at point
    Then I should be in buffer "*string-edit*"
    And I should see "my string"
    And I should not see "var s = "my string";"
    When I press "C-c C-k"
    Then I should be in buffer "*string-edit-main-buffer*"

  Scenario: Keep point position after entering edit buffer
    Given I turn on javascript-mode
    And I insert "var s = "my string";"
    When I go to the front of the word "string"
    And I edit the string at point
    And I type "test"
    Then I should see "my teststring"

  Scenario: Use edited text
    Given I turn on javascript-mode
    And I insert "var s = "my string";"
    When I go to the front of the word "string"
    And I edit the string at point
    And I type "test"
    And I press "C-c C-c"
    Then I should be in buffer "*string-edit-main-buffer*"
    And I should see "var s = "my teststring";"

  Scenario: Keep point position after exiting edit buffer
    Given I turn on javascript-mode
    And I insert "var s = "my string";"
    When I go to the front of the word "string"
    And I edit the string at point
    And I press "C-c C-c"
    And I type "test"
    Then I should see "var s = "my teststring";"

  Scenario: Un-escape quotes
    Given I turn on javascript-mode
    And I insert "var s = "my \"string\"";"
    When I go to the front of the word "string"
    And I edit the string at point
    Then I should see "my "string""

  Scenario: Un-escape slashes
    Given I turn on javascript-mode
    And I insert "var s = "my \\string";"
    When I go to the front of the word "string"
    And I edit the string at point
    Then I should see "my \string"

  Scenario: Un-escape newlines (not in js-mode)
    Given I turn on emacs-lisp-mode
    And I insert "(looking-at "ab\ncd")"
    When I go to the front of the word "ab"
    And I edit the string at point
    Then I should see:
    """
    ab
    cd
    """
    When I go to the end of the word "ab"
    And I press "RET"
    And I press "C-c C-c"
    Then I should see "(looking-at "ab\n\ncd")"

  Scenario: Re-escape
    Given I turn on javascript-mode
    And I insert "var s = "my string";"
    When I go to the front of the word "string"
    And I edit the string at point
    And I type ""\\""
    And I press "C-c C-c"
    Then I should see "var s = "my \"\\\\\"string";"

  Scenario: Concat js-strings, left side
    Given I turn on javascript-mode
    And I insert "var s = "my " + "string";"
    When I go to the front of the word "string"
    And I edit the string at point
    Then I should see "my string"

  Scenario: Concat js-strings, right side
    Given I turn on javascript-mode
    And I insert "var s = "my " + "string " + "yeah";"
    When I go to the front of the word "string"
    And I edit the string at point
    Then I should see "my string yeah"

  Scenario: Concat js-strings, newlines
    Given I turn on javascript-mode
    And I insert:
    """
    var s = "my" +
            "string" +
            "yeah";
    """
    When I go to the front of the word "string"
    And I edit the string at point
    Then I should see:
    """
    my
    string
    yeah
    """

  Scenario: Split js-strings by newlines
    Given I turn on javascript-mode
    And I insert:
    """
    var s = "my" +
            "string" +
            "yeah";
    """
    When I go to the front of the word "string"
    And I edit the string at point
    And I press "C-c C-c"
    Then I should see:
    """
    var s = "my" +
        "string" +
        "yeah";
    """

  Scenario: Open string in major with with generic string delimiters
    Given I turn on python-mode
    And I insert "s = "my string""
    When I go to the front of the word "string"
    And I edit the string at point
    And I type "test"
    And I press "C-c C-c"
    Then I should see "s = "my teststring""
