Feature: C++ specific operators
  Background:
    When the buffer is empty
    When I turn on c++-mode
    When I turn on electric-operator-mode

  Scenario: Automatic type references
    When I type "auto&thing"
    Then I should see "auto &thing"

  # Move constructor type
  Scenario: and operator still works
    When I'm inside C main
    When I type "x=a&&b"
    Then I should see "a && b"

  Scenario: Move constructor works
    When I type "A(A&&a)"
    Then I should see "A(A &&a)"


  # Type detection works inside classes
  Scenario: Move constructor
    When I insert:
    """
    struct A {

    }
    """
    When I go to line "2"
    When I type "A(A&&a)"
    Then I should see "A(A &&a)"


  # Templates
  @known-failure
  Scenario: Greater than still works
    When I'm inside C main
    When I type "bool x=0>1"
    Then I should see "bool x = 0 > 1"

  @known-failure
  Scenario: Less than still works
    When I'm inside C main
    When I type "bool x=0<1"
    Then I should see "bool x = 0 < 1"

  @known-failure
  Scenario: >> still works
    When I'm inside C main
    When I type "std::cin>>x;"
    Then I should see "std::cin>>x;"

  @known-failure
  Scenario: Template in function rvalue
    When I type "MyType<double> f()"
    Then I should see "MyType<double> f()"

  @known-failure
  Scenario: Template in function argument
    When I type "void f(MyType<double> x)"
    Then I should see "void f(MyType<double> x)"

  @known-failure
  Scenario: Nested template in function argument
    When I type "void f(MyType<d<int>> x)"
    Then I should see "void f(MyType<d<int>> x)"

  @known-failure
  Scenario: Template type definition
    When I'm inside C main
    When I type "MyType<double> x"
    Then I should see "MyType<double> x"

  @known-failure
  Scenario: Nested template type definition
    When I'm inside C main
    When I type "MyType<Template<double>> x"
    Then I should see "MyType<Template<double>> x"


  # Colon operator
  Scenario: For each loops
    When I type "for(int x:list)"
    Then I should see "for(int x : list)"

  Scenario: Standard ternary operator still works
    When I type "a?b:c"
    Then I should see "a ? b : c"

  Scenario: Ternary operator in parens
    When I type "(a?b:c)"
    Then I should see "(a ? b : c)"

  Scenario: Namespaces in parens
    When I type "f(a::foo::bar(x))"
    Then I should see "f(a::foo::bar(x))"

  Scenario: Inheritance
    When I type "class Foo:public Bar"
    Then I should see "class Foo : public Bar"

  Scenario: Public methods
    When I type "public:"
    Then I should see "public:"

  Scenario: Private methods
    When I type "private:"
    Then I should see "private:"


  # Operator overloads should never be spaced
  Scenario: operator<<
    When I type "operator<<"
    Then I should see "operator<<"

  Scenario: operator+
    When I type "operator+"
    Then I should see "operator+"

  Scenario: operator=
    When I type "operator="
    Then I should see "operator="


  # Lambdas
  Scenario: ref inside operator[] still unspaced
    When I'm inside C main
    When I type "mymap[&a_pt]"
    Then I should see "mymap[&a_pt]"

  Scenario: reference captures in lambda functions unspaced
    When I'm inside C main
    When I type "[&ticket, &i]"
    Then I should see "[&ticket, &i]"

  Scenario: value captures in lambda functions unspaced
    When I'm inside C main
    When I type "[=ticket, =i]"
    Then I should see "[=ticket, =i]"

  Scenario: space -> in simple lambda return type
    When I'm inside C main
    When I type "[] ()->bool {"
    Then I should see "[] () -> bool {"

  Scenario: space -> in mutable lambda return type
    When I'm inside C main
    When I type "[] () mutable->bool {"
    Then I should see "[] () mutable -> bool {"

  Scenario: default capture by value
    When I'm inside C main
    When I type "const auto x = [=]"
    Then I should see "const auto x = [=]"

  Scenario: default capture by reference
    When I'm inside C main
    When I type "const auto x = [&]"
    Then I should see "const auto x = [&]"

  Scenario: default capture by value with autopair
    When I'm inside C main
    When I type "const auto x = []"
    When I place the cursor after "["
    When I type "="
    Then I should see "const auto x = [=]"

  Scenario: default capture by reference with autopair
    When I'm inside C main
    When I type "const auto x = []"
    When I place the cursor after "["
    When I type "&"
    Then I should see "const auto x = [&]"

  # I'm not even going to try to parse exception specifications...
