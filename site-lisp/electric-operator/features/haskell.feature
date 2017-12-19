Feature: Haskell mode
  Background:
    When the buffer is empty
    When I turn on haskell-mode
    When I turn on electric-operator-mode


  # Partially evaluated binary operators
  Scenario: Infix +
    When I type "1+2"
    Then I should see "1 + 2"

  Scenario: Infix + inside parens
    When I type "(1+2)"
    Then I should see "(1 + 2)"

  Scenario: Prefix +
    When I type "(+ 1 2)"
    Then I should see "(+ 1 2)"

  Scenario: Potential prefix operator as first character of file
    When I type "-1"
    Then I should see "-1"

  Scenario: Prefix + alone in brackets
    When I type "foo=(+)"
    Then I should see "foo = (+)"

  Scenario: Infix with one argument before
    When I type "(1+)"
    Then I should see "(1 +)"

  Scenario: Infix with one argument after
    When I type "(+1)"
    Then I should see "(+ 1)"

 Scenario: multi character operator
    When I type "(++)"
    Then I should see "(++)"



  # Partially evaluated binary operators, with electric-pair mode
  Scenario: Infix + inside parens, brackets typed first
    When I type "()"
    When I place the cursor after "("
    When I type "1+2"
    Then I should see "(1 + 2)"

  Scenario: Prefix +, brackets typed first
    When I type "()"
    When I place the cursor after "("
    When I type "+1 2"
    Then I should see "(+ 1 2)"

  Scenario: Prefix + alone in brackets, brackets typed first
    When I type "()"
    When I place the cursor after "("
    When I type "+"
    Then I should see "(+)"

  Scenario: Infix with one argument after, brackets typed first
    When I type "()"
    When I place the cursor after "("
    When I type "+1"
    Then I should see "(+ 1)"

  Scenario: With one argument before, brackets typed first
    When I type "()"
    When I place the cursor after "("
    When I type "1+"
    Then I should see "(1 +)"

  Scenario: With badly spaced brackets
    When I type "()"
    When I place the cursor after "("
    When I type "   +"
    Then I should see "(+)"

  Scenario: multi character operator, brackets typed first
    When I type "()"
    When I place the cursor after "("
    When I type "++"
    Then I should see "(++)"


  # Infix - doesn't break other things
  Scenario: Infix - operator
    When I type "e-b"
    Then I should see "e - b"

  Scenario: Negative numbers
    When I type "a=-1"
    Then I should see "a = -1"

  Scenario: Prefix -
    When I type "(-1 2)"
    Then I should see "(- 1 2)"

  Scenario: Infix in brackets
    When I type "(1-2)"
    Then I should see "(1 - 2)"


  # Infix / doesn't break other things
  Scenario: #! / operator
    When I type "#! /bin/bash"
    Then I should see "#! /bin/bash"

  Scenario: Infix /
    When I type "a/b"
    Then I should see "a / b"

  Scenario: Prefix /
    When I type "(/1 2)"
    Then I should see "(/ 1 2)"

  Scenario: Infix in brackets
    When I type "(1/2)"
    Then I should see "(1 / 2)"



  Scenario: Comments don't change the current indentation
    When I type "            --"
    Then I should see "            -- "
