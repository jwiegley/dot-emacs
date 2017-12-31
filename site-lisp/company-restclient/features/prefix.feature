Feature: company-restclient prefix

  Scenario: Method prefix at bob
    Given the buffer is empty
    When I execute company-restclient prefix command at current point
    Then company-restclient prefix is ""

    Given the buffer is empty
    When I insert:
    """
    g
    """
    When I execute company-restclient prefix command at current point
    Then company-restclient prefix none

    Given the buffer is empty
    When I insert:
    """
    GE
    """
    When I execute company-restclient prefix command at current point
    Then company-restclient prefix is "GE"

  Scenario: Method prefix after empty line
    Given the buffer is empty
    When I insert:
    """
    
    g
    """
    When I execute company-restclient prefix command at current point
    Then company-restclient prefix none

    Given the buffer is empty
    When I insert:
    """
    
    GE
    """
    When I execute company-restclient prefix command at current point
    Then company-restclient prefix is "GE"

  Scenario: Method prefix after #
    Given the buffer is empty
    When I insert:
    """
    #
    g
    """
    When I execute company-restclient prefix command at current point
    Then company-restclient prefix none

    Given the buffer is empty
    When I insert:
    """
    #
    GE
    """
    When I execute company-restclient prefix command at current point
    Then company-restclient prefix is "GE"

    Given the buffer is empty
    When I insert:
    """
    Test
    #
    po
    """
    When I execute company-restclient prefix command at current point
    Then company-restclient prefix none

    Given the buffer is empty
    When I insert:
    """
    Test
    #
    PO
    """
    When I execute company-restclient prefix command at current point
    Then company-restclient prefix is "PO"

  Scenario: Method prefix after variable
    Given the buffer is empty
    When I insert:
    """
    :ua := emacs/restclient
    del
    """
    When I execute company-restclient prefix command at current point
    Then company-restclient prefix none

    Given the buffer is empty
    When I insert:
    """
    :ua := emacs/restclient
    DEL
    """
    When I execute company-restclient prefix command at current point
    Then company-restclient prefix is "DEL"

  Scenario: Header prefix after method
    Given the buffer is empty
    When I insert:
    """
    GET http://example.com
    
    """
    When I execute company-restclient prefix command at current point
    Then company-restclient prefix is ""

    Given the buffer is empty
    When I insert:
    """
    GET http://example.com
    ac
    """
    When I execute company-restclient prefix command at current point
    Then company-restclient prefix is "ac"

    Given the buffer is empty
    When I insert:
    """
    
    POST http://example.com
    Coo
    """
    When I execute company-restclient prefix command at current point
    Then company-restclient prefix is "Coo"

    Given the buffer is empty
    When I insert:
    """
    #
    PUT http://example.com
    Content-T
    """
    When I execute company-restclient prefix command at current point
    Then company-restclient prefix is "Content-T"

  Scenario: Header prefix after header
    Given the buffer is empty
    When I insert:
    """
    GET http://example.com
    Host: example.com
    
    """
    When I execute company-restclient prefix command at current point
    Then company-restclient prefix is ""

    Given the buffer is empty
    When I insert:
    """
    GET http://example.com
    Host: example.com
    ac
    """
    When I execute company-restclient prefix command at current point
    Then company-restclient prefix is "ac"

    Given the buffer is empty
    When I insert:
    """
    
    POST http://example.com
    Host: example.com
    Coo
    """
    When I execute company-restclient prefix command at current point
    Then company-restclient prefix is "Coo"

    Given the buffer is empty
    When I insert:
    """
    #
    PUT http://example.com
    Host: example.com
    Content-T
    """
    When I execute company-restclient prefix command at current point
    Then company-restclient prefix is "Content-T"

  Scenario: Header value prefix
    Given the buffer is empty
    When I insert:
    """
    GET http://example.com/
    Content-Type: app
    """
    When I execute company-restclient prefix command at current point
    Then company-restclient prefix is "app"

    Given the buffer is empty
    When I insert:
    """
    GET http://example.com/
    Accept-Language: ja
    Content-Type: application/j
    """
    When I execute company-restclient prefix command at current point
    Then company-restclient prefix is "application/j"

  Scenario: Variable prefix
    Given the buffer is empty
    When I insert:
    """
    GET http://example.com/users/:uid
    """
    When I execute company-restclient prefix command at current point
    Then company-restclient prefix is ":uid"

    Given the buffer is empty
    When I insert:
    """
    GET http://example.com/users
    Cookie: sid=:sid
    """
    When I execute company-restclient prefix command at current point
    Then company-restclient prefix is ":sid"

    Given the buffer is empty
    When I insert:
    """
    PUT http://example.com/users
    Cookie: sid=1234567890
    
    {
       "name": ":the-name"
    }
    """
    When I place the cursor after "the-name"
    And I execute company-restclient prefix command at current point
    Then company-restclient prefix is ":the-name"

  Scenario: No prefix
    Given the buffer is empty
    When I insert:
    """
    PUT http
    """
    When I execute company-restclient prefix command at current point
    Then company-restclient prefix none

    Given the buffer is empty
    When I insert:
    """
    :var
    """
    When I execute company-restclient prefix command at current point
    Then company-restclient prefix none
