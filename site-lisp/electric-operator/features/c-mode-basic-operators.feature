Feature: C basic operators
  Background:
    When I turn on c-mode
    When I turn on electric-operator-mode
    When I'm inside C main

  # Some simple cases
  Scenario: Ternary operator
    When I type "a?b:c"
    Then I should see "a ? b : c"

  Scenario: Label
    When I type "error:"
    Then I should see "error:"


  # Pointer dereference
  Scenario: Space >
    When I type "a>b"
    Then I should see "a > b"

  Scenario: Space -
    When I type "a-b"
    Then I should see "a - b"

  Scenario: Don't space ->
    When I type "a->b"
    Then I should see "a->b"


  # Increment/decrement
  Scenario: Post-increment
    When I type "b=c+a++"
    Then I should see "b = c + a++"

  Scenario: Pre-increment
    When I type "b=++a+c"
    Then I should see "b = ++a + c"

  Scenario: Post-decrement
    When I type "b=c-a--"
    Then I should see "b = c - a--"

  Scenario: Pre-decrement
    When I type "b=--a-c"
    Then I should see "b = --a - c"

  Scenario: Post-increment with semi-colon
    When I type "a++;"
    Then I should see "a++;"

  Scenario: Post-decrement with semi-colon
    When I type "a--;"
    Then I should see "a--;"

  # It might be possible to handle some of these without brackets. There's
  # also cases like `a++ + b` vs `a + ++b`, is this possible to parse?


  # * operator
  Scenario: Multiplication
    When I type "a*b"
    Then I should see "a * b"

  Scenario: Pointer type
    When I type "char*a"
    Then I should see "char *a"

  Scenario: Non-builtin pointer type
    When I type "size_t*a"
    Then I should see "size_t *a"

  Scenario: Assign pointer dereference
    When I type "a=*b"
    Then I should see "a = *b"

  Scenario: Pointer dereference and increment
    When I type "*p++"
    Then I should see "*p++"

  Scenario: Function call with dereference
    Then I type "f(*p,*q)"
    Then I should see "f(*p, *q)"

  Scenario: pointer to pointer type
      When I type "char**a"
      Then I should see "char **a"


  # & operator
  Scenario: Bitwise and
    When I type "a&b"
    Then I should see "a & b"

  Scenario: Reference type
    When I type "char&a"
    Then I should see "char &a"

  Scenario: Assign address of
    When I type "a=&b"
    Then I should see "a = &b"

  Scenario: Function call with address of
    Then I type "f(&p,&q)"
    Then I should see "f(&p, &q)"


  # Respect option to have pointer operators touching the type or the
  # variable name
  Scenario: Operator * on type
    When I set electric-operator-c-pointer-type-style to type
    When I type "int*x"
    Then I should see "int* x"

  Scenario: Operator * on variable
    When I set electric-operator-c-pointer-type-style to variable
    When I type "int*x"
    Then I should see "int *x"

  Scenario: Operator & on type
    When I set electric-operator-c-pointer-type-style to type
    When I type "int&x"
    Then I should see "int& x"

  Scenario: Operator & on variable
    When I set electric-operator-c-pointer-type-style to variable
    When I type "int&x"
    Then I should see "int &x"

  Scenario: Operator ** on type
    When I set electric-operator-c-pointer-type-style to type
    When I type "int**x"
    Then I should see "int** x"

  Scenario: Operator ** on variable
    When I set electric-operator-c-pointer-type-style to variable
    When I type "int**x"
    Then I should see "int **x"


  # Comments
  Scenario: Division / still works
    When I type "int a = x/y"
    Then I should see "int a = x / y"

  Scenario: // is not spaced internally
    When I type "//"
    Then I should see "//"

  Scenario: // adds space before if not on empty line
    When I type "expression;//"
    Then I should see "expression; //"

  Scenario: // does not add space before when at indentation of line
    When I set c-electric-flag to nil
    When I type "  expression;"
    When I execute newline-and-indent
    When I type "//"
    Then I should see pattern "^  expression;$"
    Then I should see pattern "^  // $"

  Scenario: /* is not spaced internally
    When I type "/*"
    Then I should see "/*"

  Scenario: /* */ is not spaced internally
    When I type "/**/"
    Then I should see "/* */"

  Scenario: /* adds space before if not on empty line
    When I set c-electric-flag to nil
    When I type "expression;/*"
    Then I should see "expression; /*"

  Scenario: /* does not add space before when at indentation of line
    When I set c-electric-flag to nil
    When I type "  expression;"
    When I execute newline-and-indent
    When I type "/*"
    Then I should see pattern "^  expression;$"
    Then I should see pattern "^  /\* $"



  # Type keywords for pointers vs multiplication
  Scenario: Pointer to struct
    When I set electric-operator-c-pointer-type-style to variable
    When I type "struct s*foo"
    Then I should see "struct s *foo"

  Scenario: Variable with struct in the name
    When I set electric-operator-c-pointer-type-style to variable
    When I type "struct_ure*foo"
    Then I should see "struct_ure * foo"

  Scenario: Another variable with struct in the name
    When I set electric-operator-c-pointer-type-style to variable
    When I type "a_struct*foo"
    Then I should see "a_struct * foo"

  Scenario: Pointer to struct then multiply
    When I set electric-operator-c-pointer-type-style to variable
    When I type "struct s*foo=a*b"
    Then I should see "struct s *foo = a * b"

  Scenario: Pointer to oddly named struct
    When I set electric-operator-c-pointer-type-style to variable
    When I type "struct my_type_2*foo"
    Then I should see "struct my_type_2 *foo"

  Scenario: Pointer to union
    When I set electric-operator-c-pointer-type-style to variable
    When I type "union s*foo"
    Then I should see "union s *foo"

  Scenario: Pointer to enum
    When I set electric-operator-c-pointer-type-style to variable
    When I type "enum s*foo=a*b"
    Then I should see "enum s *foo = a * b"


  Scenario: Multiplication with pointer deref
    When I type "result = foo * *bar"
    Then I should see "result = foo * *bar"
