Feature: Rust specific operators

  Background:
    When the buffer is empty
    When I turn on rust-mode
    When I turn on electric-operator-mode

  Scenario: Comments
    When I type "//a comment"
    Then I should see "// a comment"

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


  Scenario: Function return value
    When I type "fn foo()->i32"
    Then I should see "fn foo() -> i32"

  Scenario: Pattern matching fat arrow
    When inside a rust pattern matching statement
    When I type "1=>pri"
    Then I should see "1 => pri"


  # Templates
  @known-failure
  Scenario: Greater than operator
    When inside a rust function
    When I type "if i>42"
    Then I should see "if i > 42"

  @known-failure
  Scenario: Less than operator
    When inside a rust function
    When I type "if i<42"
    Then I should see "if i < 42"

  @known-failure
  Scenario: Template brackets
    When I type "type Pair<'a>"
    Then I should see "type Pair<'a>"


  # Ref vs bitwise and
  @known-failure
  Scenario: Reference argument
    When I type "fn insert(&mut self"
    Then I should see "fn insert(&mut self"

  @known-failure
  Scenario: Bitwise and
    When I type "let a = b&c"
    Then I should see "let a = b & c"


  # or vs lambda
  @known-failure
  Scenario: Bitwise or
    When inside a rust function
    When I type "Foo|Foo;"
    Then I should see "Foo | Foo;"

  @known-failure
  Scenario: Lambda functions
    When I type "ten_times(|j| println!(\"hello, {}\", j));"
    Then I should see "ten_times(|j| println!(\"hello, {}\", j));"


  # Should deal with pointer dereference as well?
