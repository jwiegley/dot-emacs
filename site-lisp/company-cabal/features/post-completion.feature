Feature: company-cabal post-completion

  Scenario: Field lowercase
    Given the buffer is empty
    When I insert:
    """
    cabal-version
    """
    And I execute company-cabal post-completion with "cabal-version"
    Then I should see:
    """
    cabal-version:       
    """

  Scenario: Field capitalized
    Given the buffer is empty
    When I insert:
    """
    Cabal-version
    """
    And I execute company-cabal post-completion with "cabal-version"
    Then I should see:
    """
    Cabal-Version:       
    """
