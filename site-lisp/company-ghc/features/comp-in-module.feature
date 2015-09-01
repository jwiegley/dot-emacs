Feature: in-module completion

  Scenario: Completion from the specified module only
    Given the buffer is empty
    And these module keywords:
      | module          | keywords                     |
      | Data.Text       | Text singleton splitOn       |
      | Data.ByteString | ByteString singleton splitAt |
    And these imported modules:
      | module          | alias |
      | Data.Text       | T     |
      | Data.ByteString |       |
    When I start an action chain
    And I press "M-x"
    And I type "company-ghc-complete-in-module"
    And I press "RET"
    And I type "Data.Text"
    And I press "RET"
    And I type "sp"
    And I press "RET"
    And I execute the action chain
    Then I should see "splitOn"

    Given the buffer is empty
    When I start an action chain
    And I press "M-x"
    And I type "company-ghc-complete-in-module"
    And I press "RET"
    And I type "Data.ByteString"
    And I press "RET"
    And I type "sp"
    And I press "RET"
    And I execute the action chain
    Then I should see "splitAt"
