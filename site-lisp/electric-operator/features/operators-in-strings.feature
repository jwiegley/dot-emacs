Feature: Spacing inside strings
  Background:
    When I turn on python-mode
    When I turn on electric-operator-mode
    When the buffer is empty
    When I set electric-operator-enable-in-docs to t

  # Never space % in strings

  # Unfortunately this is currently untestable with ecukes: % signs can't
  # appear in steps (see bug #58)

  # Scenario: Normally space %
  #   When I type "a%b"
  #   Then I should see "a % b"

  # Scenario: C mode format string
  #   When I turn on c-mode
  #   When I turn on electric-operator-mode
  #   When I type "printf('an integer \%i'"
  #   Then I should see "printf('an integer \%i'"

  Scenario: Don't space UNIX separators
    # The second string checks that we did manage to turn on
    # electric-operator in strings.
    When I type "a='/usr/bin/python3'"
    Then I should see "a = '/usr/bin/python3'"

  Scenario: Don't space windows separators
    When I type "a='C:\WINDOWS'"
    Then I should see "a = 'C:\WINDOWS'"
