Feature: Java specific operators
  Background:
    When the buffer is empty
    When I turn on java-mode
    When I turn on electric-operator-mode

  Scenario: Division / still works
    When I type "int a = x/y"
    Then I should see "int a = x / y"

  Scenario: // adds space before if not on empty line
    When I type "expression;//"
    Then I should see "expression; //"

  Scenario: // does not add space before when at indentation of line
    When I set c-electric-flag to nil
    When I type "   //"
    Then I should see pattern "^   // $"

  Scenario: /* adds space before if not on empty line
    When I type "expression;/*"
    Then I should see "expression; /*"

  Scenario: /* does not add space before when at indentation of line
    When I set c-electric-flag to nil
    When I type "   /*"
    Then I should see pattern "^   /\* $"
