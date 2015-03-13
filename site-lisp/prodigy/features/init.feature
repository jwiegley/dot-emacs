Feature: Init

  Scenario: Run init function before starting process
    Given I add the following services:
      | name | cwd | command | args                             | init                         |
      | foo  | foo | python  | ("-m" "SimpleHTTPServer" "6001") | (lambda () (setq foo "BAR")) |
    And I start prodigy
    When I press "s"
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
    And the variable "foo" should have value "BAR"

