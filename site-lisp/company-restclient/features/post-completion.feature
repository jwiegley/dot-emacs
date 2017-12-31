Feature: company-restclient post-completion

  Scenario: Method
    Given the buffer is empty
    When I set company-restclient--current-context to method
    When I insert:
    """
    GET
    """
    And I execute company-restclient post-completion with "GET"
    Then I should see:
    """
    GET 
    """

  Scenario: Header lowercase
    Given the buffer is empty
    When I set company-restclient--current-context to header
    When I insert:
    """
    content-type
    """
    And I execute company-restclient post-completion with "content-type"
    Then I should see:
    """
    content-type: 
    """

  Scenario: Header capitalized
    Given the buffer is empty
    When I set company-restclient--current-context to header
    When I insert:
    """
    Content-type
    """
    And I execute company-restclient post-completion with "content-type"
    Then I should see:
    """
    Content-Type: 
    """
