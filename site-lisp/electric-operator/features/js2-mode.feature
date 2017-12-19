Feature: js2-mode (an alternative javascript major mode)
  Background:
    When the buffer is empty
    When I turn on js2-mode
    When I turn on electric-operator-mode

  Scenario: It gets the javascript rules
    When I type "{a:1}"
    Then I should see "{a: 1}"

  Scenario: Regex literals simple
    When I type "/a.foo"
    When I let js2-mode reparse
    When I type "/"
    Then I should see "/a.foo/"

  # js2-mode doesn't immediately parse the code and set properties, unlike the
  # built in emacs parsing. So if you type fast enough regex literals won't
  # work.
  @known-failure
  Scenario: Regex literals without time for a reparse
    When I type "/a.foo/"
    Then I should see "/a.foo/"
