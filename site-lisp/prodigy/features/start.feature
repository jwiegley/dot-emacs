Feature: Start

  Background:
    Given I add the following services:
      | name | cwd | command | args                             |
      | foo  | foo | python  | ("-m" "SimpleHTTPServer" "6001") |
      | bar  | bar | python  | ("-m" "SimpleHTTPServer" "6002") |
    And I start prodigy

  Scenario: Already started
    When I press "s"
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
    When I press "s"
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
    And I should see services:
      | name | highlighted | marked | started |
      | bar  | t           | nil    | t       |

  Scenario: Start process at line
    When I press "s"
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
    Then I should see services:
      | name | highlighted | marked | started |
      | bar  | t           | nil    | t       |

  Scenario: Start marked processes
    When I press "M"
    And I press "s"
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
    Then I should see services:
      | name | highlighted | marked | started |
      | bar  | t           | t      | t       |
      | foo  | nil         | t      | t       |
