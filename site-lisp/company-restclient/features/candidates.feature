Feature: company-restclient candidate

  Scenario: Method candidates
    Given the buffer is empty
    When I insert:
    """
    G
    """
    And I execute company-restclient candidates command at current point
    Then company-restclient candidates are "("GET")"

  Scenario: Header candidates
    Given the buffer is empty
    When I insert:
    """
    GET http://example.com
    Coo
    """
    And I execute company-restclient candidates command at current point
    Then company-restclient candidates are "("cookie")"

  Scenario: Variable candidates
    Given the buffer is empty
    When I insert:
    """
    :var1 = 1
    :var2 = 2
    GET http://example.com/:v
    """
    And I execute company-restclient candidates command at current point
    Then company-restclient candidates are "(":var1" ":var2")"

  Scenario: Header value candidates
    Given the buffer is empty
    When I insert:
    """
    POST http://example.com
    Content-Type: text
    """
    And I execute company-restclient candidates command at current point
    Then company-restclient candidates are "("text/csv" "text/html" "text/plain")"
