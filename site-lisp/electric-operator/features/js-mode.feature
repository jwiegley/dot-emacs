Feature: Javascript specific operators
  Background:
    When the buffer is empty
    When I turn on js-mode
    When I turn on electric-operator-mode

  Scenario: Colon inside objects
    When I type "{a:1}"
    Then I should see "{a: 1}"

  Scenario: Ternary operator
    When I type "bool?1:2"
    Then I should see "bool ? 1 : 2"


  Scenario: Division
    When I type "x=b/a.foo"
    Then I should see "x = b / a.foo"

  Scenario: Regex literals simple
    When I type "/a.foo/"
    Then I should see "/a.foo/"

  Scenario: Regex literals with spacing before
    When I type "x=/a.foo/"
    Then I should see "x = /a.foo/"

  Scenario: Correctly space #! paths
    When I type "#! /usr/bin/node"
    Then I should see "#! /usr/bin/node"

  # Had some problems with this because probably-unary-operator was wrong in
  # some cases, so a " / " was inserted by the first /, combined with the fact
  # that regexes are strings this goes wrong.
  Scenario: // comments
    When I type "//a comment"
    Then I should see "// a comment"

  Scenario: // comments in unary-operator context
    When I type "function() {//a comment"
    Then I should see "// a comment"

  Scenario: // comments inside IIFEs
    When I type "function() {"
    When I press "<return>"
    When I type "//a comment"
    Then I should see "// a comment"

  Scenario: /* comments
    When I type "/*a comment */"
    Then I should see "/* a comment */"

  # We can't really handle this at the moment, we need some kind of special case
  # for comments "operators".
  @known-failure
  Scenario: Comment after division
    When I type "x=a/ // divide x"
    Then I should see "x = a / // divide x"

  Scenario: Division / still works
    When I type "int a = x/y"
    Then I should see "int a = x / y"

  Scenario: // adds space before if not on empty line
    When I type "expression;//"
    Then I should see "expression; //"

  Scenario: // does not add space before when at indentation of line
    When I type "   //"
    Then I should see pattern "^   // $"

  Scenario: /* adds space before if not on empty line
    When I type "expression;/*"
    Then I should see "expression; /*"

  Scenario: /* does not add space before when at indentation of line
    When I type "   /*"
    Then I should see pattern "^   /\* $"
