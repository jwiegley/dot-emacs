Feature: Function declaration pointer/reference types
  Background:
    When the buffer is empty
    When I turn on c-mode
    When I turn on electric-operator-mode

  Scenario: Handle pointer type in function decl.
    When I type "void foo(my_struct*s"
    Then I should see "void foo(my_struct *s"

  Scenario: Handle reference type in function decl.
    When I type "void foo(my_struct&s"
    Then I should see "void foo(my_struct &s"

  Scenario: Handle pointer types with bracket on new lines
    When I insert:
    """
    void foo
    (
    """
    When I type "my_struct*s"
    Then I should see "my_struct *s"

  Scenario: Handle pointer types with argument on new lines
    When I insert:
    """
    void foo(

    """
    When I type "my_struct*s"
    Then I should see "my_struct *s"

  Scenario: Handle pointer types with arguments continued on new line
    When I insert:
    """
    void foo(int a,

    """
    When I type "my_struct*s"
    Then I should see "my_struct *s"
