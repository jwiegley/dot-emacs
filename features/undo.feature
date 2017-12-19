Feature: Interaction with undo
  Background:
    When I turn on prog-mode
    When I turn on electric-operator-mode
    When the buffer is empty

  Scenario: Undoing the electric expansion doesn't undo previous text
    When I type "const auto a="
    Then I should see "const auto a ="
    When I press "C-_"
    Then I should see "const auto a="
