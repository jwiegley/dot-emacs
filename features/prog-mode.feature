Feature: Generic programming mode spacing
  Background:
    When I turn on prog-mode
    When I turn on electric-operator-mode
    When the buffer is empty

  # Make sure we actually managed to enable electric-operator-mode
  Scenario: Enable electric spacing
    Then electric-operator-mode is on

  # Make sure the mode is really always being turned on and not just
  # toggling!
  Scenario: Enable electric spacing again
    Then electric-operator-mode is on

  # Basic stuff
  Scenario: Space a simple operator
    When I type "a=b"
    Then I should see "a = b"

  Scenario: Space an operator with spacing after
    When I type "f(a,b)"
    Then I should see "f(a, b)"

  Scenario: Space an operator with spacing before
    # There are no pre-spaced operators in default mode, so use c-mode
    When I turn on c-mode
    When I turn on electric-operator-mode
    When I type "char*a"
    Then I should see "char *a"

  Scenario: Space a double character operator
    When I type "a==b"
    Then I should see "a == b"


  # Digraphs work correctly
  Scenario: Don't space ! operator
    When I type "if(!b)"
    Then I should see "if(!b)"

  Scenario: Space != as single operator
    When I type "a!=b"
    Then I should see "a != b"

  Scenario: But don't space =! as a single operator
    When I type "a=!b"
    Then I should see "a = !b"

  Scenario: Don't space =* as single operator
    # Interesting because * and = are both operators
    When I type "a=*b"
    Then I should see "a = * b"


  # Decimal numbers
  Scenario: Don't space the dot in decimals
    When I type "0.235"
    Then I should see "0.235"


  # Negative exponents
  Scenario: Space - operator
    When I type "e-b"
    Then I should see "e - b"

  Scenario: Don't space negative exponent (lower case)
    When I type "1.2e-10"
    Then I should see "1.2e-10"

  Scenario: Don't space negative exponent (upper case)
    When I type "1.2E-10"
    Then I should see "1.2E-10"

  Scenario: Don't space negative exponent (integer)
    When I type "5e-10"
    Then I should see "5e-10"


  # Unix #! paths
  Scenario: Correctly space #!
    When I type "#! /bin/bash"
    Then I should see "#! /bin/bash"

  Scenario: But also space division
    When I type "a/b"
    Then I should see "a / b"


  # Negative numbers
  Scenario: Space - operator
    When I type "e-b"
    Then I should see "e - b"

  Scenario: Don't space -1
    When I type "-1"
    Then I should see "-1"

  Scenario: a = -1
    When I type "a=-1"
    Then I should see "a = -1"

  Scenario: a * -1
    When I type "a*-1"
    Then I should see "a * -1"

  Scenario: a + -1
    When I type "a+-1"
    Then I should see "a + -1"

  Scenario: a - -1
    When I type "a--1"
    Then I should see "a - -1"

  Scenario: a / -1
    When I type "a/-1"
    Then I should see "a / -1"

  Scenario: a ^ -1
    When I type "a^-1"
    Then I should see "a ^ -1"

  Scenario: a < -1
    When I type "a<-1"
    Then I should see "a < -1"

  Scenario: a > -1
    When I type "a>-1"
    Then I should see "a > -1"

  Scenario: a = [-1]
    When I type "a=[-1]"
    Then I should see "a = [-1]"

  Scenario: f(-1)
    When I type "f(-1)"
    Then I should see "f(-1)"

  Scenario: f(x, -1)
    When I type "f(x,-1)"
    Then I should see "f(x, -1)"

  Scenario: return
    When I type "return -1"
    Then I should see "return -1"
