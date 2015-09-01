Feature: Path

  Scenario: Add path
    Given I add the following services:
      | name | cwd | command | args     | path    |
      | baz  | baz | server  | ("6003") | ("baz") |
    And I start prodigy
    When I press "s"
    Then requesting "http://127.0.0.1:6003/index.html" should respond with:
      """
      <!DOCTYPE>
      <html>
        <head></head>
        <body>
          BAZ
        </body>
      </html>
      """
