Feature: Restart

  Background:
    Given I add the following services:
      | name | cwd | command | args                             |
      | foo  | foo | python  | ("-m" "SimpleHTTPServer" "6001") |
      | bar  | bar | python  | ("-m" "SimpleHTTPServer" "6002") |
    And I start prodigy

  Scenario: At line not started
    When I press "r"
    Then requesting "http://127.0.0.1:6002/index.html" should respond with:
      """
      <!DOCTYPE>
      <html>
        <head></head>
        <body>
          BAR
        </body>
      </html>
      """

  Scenario: At line started
    When I press "s"
    And I press "r"
    Then requesting "http://127.0.0.1:6002/index.html" should respond with:
      """
      <!DOCTYPE>
      <html>
        <head></head>
        <body>
          BAR
        </body>
      </html>
      """

  Scenario: Marked not started
    When I press "M"
    And I press "r"
    Then requesting "http://127.0.0.1:6001/index.html" should respond with:
      """
      <!DOCTYPE>
      <html>
        <head></head>
        <body>
          FOO
        </body>
      </html>
      """
    And requesting "http://127.0.0.1:6002/index.html" should respond with:
      """
      <!DOCTYPE>
      <html>
        <head></head>
        <body>
          BAR
        </body>
      </html>
      """

  Scenario: Marked started
    When I press "M"
    And I press "s"
    And I press "r"
    Then requesting "http://127.0.0.1:6001/index.html" should respond with:
      """
      <!DOCTYPE>
      <html>
        <head></head>
        <body>
          FOO
        </body>
      </html>
      """
    And requesting "http://127.0.0.1:6002/index.html" should respond with:
      """
      <!DOCTYPE>
      <html>
        <head></head>
        <body>
          BAR
        </body>
      </html>
      """
