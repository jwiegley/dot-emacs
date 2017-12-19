Feature: Python mode basics
  Background:
    When the buffer is empty
    When I turn on python-mode
    When I turn on electric-operator-mode


  ## * and ** operators
  Scenario: Space *
    When I type "a*b"
    Then I should see "a * b"

  Scenario: Multiplication after a function
    When I type "f(x)*a"
    Then I should see "f(x) * a"

  Scenario: Exponentiation after a function
    When I type "f(x)**a"
    Then I should see "f(x) ** a"

  Scenario: Space * inside function
    When I type "f(a*b)"
    Then I should see "f(a * b)"

  Scenario: Space **
    When I type "a**b"
    Then I should see "a ** b"

  Scenario: Space ** inside function
    When I type "f(a**b)"
    Then I should see "f(a ** b)"

  # Check *args works ok
  Scenario: Space *args on its own
    When I type "f(*args)"
    Then I should see "f(*args)"

  Scenario: Space *args with other args
    When I type "f(a,*args)"
    Then I should see "f(a, *args)"

  Scenario: Space *args with a newline before it
    When I insert:
    """
    f(a,

    """
    When I type "*args)"
    Then I should see:
    """
    f(a,
    *args)
    """

  # And **kwargs
  Scenario: Space **kwargs on its own
    When I type "f(**kwargs)"
    Then I should see "f(**kwargs)"

  Scenario: Space **kwargs with other args
    When I type "f(a,**kwargs)"
    Then I should see "f(a, **kwargs)"

  Scenario: Space **kwargs with a newline before it
    When I insert:
    """
    f(a,

    """
    When I type "**kwargs)"
    Then I should see:
    """
    f(a,
    **kwargs)
    """


  ## Colons

  # keywords
  Scenario: Don't space : in ifs
    When I type "if x:"
    Then I should see "if x:"

  Scenario: Leave any existing space after : in ifs
    When I type "if x: "
    Then I should see "if x: "

  Scenario: Don't space : in else
    When I type "else:"
    Then I should see "else:"

  Scenario: Don't space : in elif
    When I type "elif y:"
    Then I should see "elif y:"

  Scenario: Don't space : in for
    When I type "for x in y:"
    Then I should see "for x in y:"

  Scenario: Don't space : in while
    When I type "while x:"
    Then I should see "while x:"

  Scenario: Don't space : in with
    When I type "with X as Y:"
    Then I should see "with X as Y:"


  # python dictionaries
  Scenario: Space after : in dict
    When I type "{a:1}"
    Then I should see "{a: 1}"


  # Lambda functions
  Scenario: Space after lambda arguments
    When I type "lambda x:x"
    Then I should see "lambda x: x"

  Scenario: Space after lambda arguments inside dict
    When I type "{a:lambda x:x, b:2}"
    Then I should see "{a: lambda x: x, b: 2}"

  Scenario: Lambda containing dict
    When I type "lambda x:{a:x, b:2}"
    Then I should see "lambda x: {a: x, b: 2}"

  Scenario: Lambda containing slice
    When I type "lambda x:x[1:2]"
    Then I should see "lambda x: x[1:2]"

  @known-failure
  Scenario: Lambda with default argument containing dict
    When I type "lambda x={a:1}:print x"
    Then I should see "lambda x={a: 1}: print x"

  @known-failure
  Scenario: Lambda with default argument containing slice
    When I type "lambda x=y[1:5]:print x"
    Then I should see "lambda x=y[1:5]: print x"


  # Slice operator
  Scenario: Don't space : inside slices
    When I type "a[1:2]"
    Then I should see "a[1:2]"

  Scenario: Don't space negative slices
    When I type "a[-1:-2]"
    Then I should see "a[-1:-2]"


  # Types
  Scenario: Types in function declarations
    When I type "def foo(x:int)->str:"
    Then I should see "def foo(x: int) -> str:"
    Then I should not see "str: "

  @known-failure
  Scenario: Types in variable declarations --auto insert space
    When I type "self._first_name:str = first_name"
    Then I should see "self._first_name: str = first_name"

  Scenario: Types in variable declarations -- space is not removed
    When I type "self._first_name: str = first_name"
    Then I should see "self._first_name: str = first_name"


  ## Member access
  Scenario: Don't space accessing class members
    When I type "my_class.a"
    Then I should see "my_class.a"


  ## Keyword argument =
  Scenario: Space standard assignment as normal
    When I type "a=b"
    Then I should see "a = b"

  Scenario: Don't space assignment inside function call
    When I type "f(a=b)"
    Then I should see "f(a=b)"

  Scenario: Don't space default args in lambda
    When I type "lambda x=1: print x"
    Then I should see "lambda x=1: print x"
