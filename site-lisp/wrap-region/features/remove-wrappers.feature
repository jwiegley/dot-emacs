Feature: Remove Wrappers
  In order to extend wrap region
  As a wrap region user
  I want to remove wrappers

  Scenario: Remove wrapper
    Given I add wrapper "$/$"
    Then key "$" should wrap with "$" and "$"
    When I remove wrapper "$"
    Then key "$" should not wrap

  Scenario: Remove wrapper with custom trigger
    Given I add wrapper "{-/-}/$"
    Then key "$" should wrap with "{-" and "-}"
    When I remove wrapper "$"
    Then key "$" should not wrap

  Scenario: Remove wrapper when exist for mode
    Given I add wrapper "$/$" for "text-mode"
    Then key "$" should wrap with "$" and "$" in "text-mode"
    When I remove wrapper "$"
    Then key "$" should not wrap

  Scenario: Remove wrapper from mode when exist for mode
    Given I add wrapper "$/$" for "text-mode"
    Then key "$" should wrap with "$" and "$" in "text-mode"
    When I remove wrapper "$" from "text-mode"
    Then key "$" should not wrap in "text-mode"

  Scenario: Remove wrapper with custom trigger when exist for mode
    Given I add wrapper "{-/-}/#" for "text-mode"
    Then key "#" should wrap with "{-" and "-}" in "text-mode"
    When I remove wrapper "#"
    Then key "#" should not wrap in "text-mode"

  Scenario: Remove wrapper with custom trigger from mode when exist for mode
    Given I add wrapper "{-/-}/#" for "text-mode"
    Then key "#" should wrap with "{-" and "-}" in "text-mode"
    When I remove wrapper "#" from "text-mode"
    Then key "#" should not wrap in "text-mode"

  Scenario: Remove wrapper when exist for modes
    Given I add wrapper "$/$" for "text-mode,fundamental-mode"
    Then key "$" should wrap with "$" and "$" in "text-mode"
    And key "$" should wrap with "$" and "$" in "fundamental-mode"
    When I remove wrapper "$"
    Then key "$" should not wrap in "text-mode"
    And key "$" should not wrap in "fundamental-mode"

  Scenario: Remove wrapper from mode when exist for modes
    Given I add wrapper "$/$" for "text-mode,fundamental-mode"
    Then key "$" should wrap with "$" and "$" in "text-mode"
    And key "$" should wrap with "$" and "$" in "fundamental-mode"
    When I remove wrapper "$" from "text-mode"
    Then key "$" should not wrap in "text-mode"
    But key "$" should wrap with "$" and "$" in "fundamental-mode"

  Scenario: Remove wrapper from modes when exist for modes
    Given I add wrapper "$/$" for "text-mode,fundamental-mode"
    Then key "$" should wrap with "$" and "$" in "text-mode"
    And key "$" should wrap with "$" and "$" in "fundamental-mode"
    When I remove wrapper "$" from "text-mode"
    And I remove wrapper "$" from "fundamental-mode"
    Then key "$" should not wrap in "text-mode"
    And key "$" should not wrap in "fundamental-mode"

  Scenario: Remove wrapper with custom trigger when exist for modes
    Given I add wrapper "{-/-}/#" for "text-mode,fundamental-mode"
    Then key "#" should wrap with "{-" and "-}" in "text-mode"
    And key "#" should wrap with "{-" and "-}" in "fundamental-mode"
    When I remove wrapper "#"
    Then key "#" should not wrap in "text-mode"
    And key "#" should not wrap in "fundamental-mode"

  Scenario: Remove wrapper with custom trigger from mode when exist for modes
    Given I add wrapper "{-/-}/#" for "text-mode,fundamental-mode"
    Then key "#" should wrap with "{-" and "-}" in "text-mode"
    And key "#" should wrap with "{-" and "-}" in "fundamental-mode"
    When I remove wrapper "#" from "text-mode"
    Then key "#" should not wrap in "text-mode"
    But key "#" should wrap with "{-" and "-}" in "fundamental-mode"

  Scenario: Remove wrapper with custom trigger from modes when exist for modes
    Given I add wrapper "{-/-}/#" for "text-mode,fundamental-mode"
    Then key "#" should wrap with "{-" and "-}" in "text-mode"
    And key "#" should wrap with "{-" and "-}" in "fundamental-mode"
    When I remove wrapper "#" from "text-mode"
    And I remove wrapper "#" from "fundamental-mode"
    Then key "#" should not wrap in "text-mode"
    And key "#" should not wrap in "fundamental-mode"

  Scenario: Remove wrapper when mix exist
    Given I add wrapper "#/#"
    And I add wrapper "$/$/#" for "text-mode"
    And I add wrapper "{-/-}/#" for "fundamental-mode,emacs-lisp-mode"
    Then key "#" should wrap with "#" and "#" in "latex-mode"
    And key "#" should wrap with "$" and "$" in "text-mode"
    And key "#" should wrap with "{-" and "-}" in "fundamental-mode"
    And key "#" should wrap with "{-" and "-}" in "emacs-lisp-mode"
    When I remove wrapper "#"
    Then key "#" should not wrap in "text-mode"
    And key "#" should not wrap in "fundamental-mode"
    And key "#" should not wrap in "emacs-lisp-mode"
    And key "#" should not wrap in "lisp-mode"

  Scenario: Remove wrapper from mode when mix exist
    Given I add wrapper "#/#"
    And I add wrapper "$/$/#" for "text-mode"
    And I add wrapper "{-/-}/#" for "fundamental-mode,emacs-lisp-mode"
    Then key "#" should wrap with "#" and "#" in "latex-mode"
    And key "#" should wrap with "$" and "$" in "text-mode"
    And key "#" should wrap with "{-" and "-}" in "fundamental-mode"
    And key "#" should wrap with "{-" and "-}" in "emacs-lisp-mode"
    When I remove wrapper "#" from "text-mode"
    Then key "#" should wrap with "#" and "#" in "text-mode"
    But key "#" should wrap with "{-" and "-}" in "fundamental-mode"
    And key "#" should wrap with "{-" and "-}" in "emacs-lisp-mode"

  Scenario: Remove wrapper from modes when mix exist
    Given I add wrapper "#/#"
    And I add wrapper "$/$/#" for "text-mode"
    And I add wrapper "{-/-}/#" for "fundamental-mode,emacs-lisp-mode"
    Then key "#" should wrap with "#" and "#" in "latex-mode"
    And key "#" should wrap with "$" and "$" in "text-mode"
    And key "#" should wrap with "{-" and "-}" in "fundamental-mode"
    And key "#" should wrap with "{-" and "-}" in "emacs-lisp-mode"
    When I remove wrapper "#" from "text-mode,emacs-lisp-mode"
    Then key "#" should wrap with "{-" and "-}" in "fundamental-mode"
    And key "#" should wrap with "#" and "#" in "text-mode"
    And key "#" should wrap with "#" and "#" in "emacs-lisp-mode"

  Scenario: Remove wrapper should unbind key when no wrapper left
    Given I turn on wrap-region
    And I add wrapper "$/$"
    And I remove wrapper "$"
    Then key "$" should be bound to "self-insert-command"

