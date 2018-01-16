Feature: Editing parts of multiple files in one buffer

  Background:
    Given I switch to buffer "*multifile*"
    And I press "<return>"
    And I open and erase file "/tmp/test1.rb"
    And I insert:
    """
    outside
    line a
    line b
    line c
    outside
    """
    And I go to the front of the word "line"
    And I set the mark
    And I go to the end of the word "c"
    And I press "C-!"

  Scenario: Opening multi-buffer from region
    When I switch to buffer "*multifile*"
    Then I should see:
    """
    line a
    line b
    line c
    """

  Scenario: Editing from multifile, center
    When I switch to buffer "*multifile*"
    And I go to the end of the word "line b"
    And I insert "ooya!"
    And I switch to buffer "test1.rb"
    Then I should see "booya!"

  Scenario: Editing from multifile, beginning
    When I switch to buffer "*multifile*"
    And I go to the front of the word "a"
    And I press "M-b"
    And I insert "sp"
    And I switch to buffer "test1.rb"
    Then I should see "spline a"

  Scenario: Editing from multifile, end
    When I switch to buffer "*multifile*"
    And I go to the end of the word "c"
    And I insert "ool"
    And I switch to buffer "test1.rb"
    Then I should see "cool"

  Scenario: Editing from multifile, outside top
    When I switch to buffer "*multifile*"
    And I go to the front of the word "a"
    And I press "M-b"
    And I press "C-b"
    And I insert "mirror-only"
    And I switch to buffer "test1.rb"
    Then I should not see "mirror-only"

  Scenario: Editing from multifile, outside bottom
    When I switch to buffer "*multifile*"
    And I go to the end of the word "c"
    And I press "C-f"
    And I insert "mirror-only"
    And I switch to buffer "test1.rb"
    Then I should not see "mirror-only"

  Scenario: Editing from original file
    When I switch to buffer "test1.rb"
    And I go to the end of the word "line b"
    And I insert "ooya!"
    And I switch to buffer "*multifile*"
    Then I should see "booya!"

  Scenario: Editing from original, beginning
    When I switch to buffer "test1.rb"
    And I go to the front of the word "a"
    And I press "M-b"
    And I insert "sp"
    And I switch to buffer "*multifile*"
    Then I should see "spline a"

  Scenario: Editing from original, end
    When I switch to buffer "test1.rb"
    And I go to the end of the word "c"
    And I insert "ool"
    And I switch to buffer "*multifile*"
    Then I should see "cool"

  Scenario: Editing from original, outside top
    When I switch to buffer "test1.rb"
    And I go to the front of the word "a"
    And I press "M-b"
    And I press "C-b"
    And I insert "mirror-only"
    And I switch to buffer "*multifile*"
    Then I should not see "mirror-only"

  Scenario: Editing from original, outside bottom
    When I switch to buffer "test1.rb"
    And I go to the end of the word "c"
    And I press "C-f"
    And I insert "mirror-only"
    And I switch to buffer "*multifile*"
    Then I should not see "mirror-only"

  Scenario: Removing mirror
    When I switch to buffer "*multifile*"
    And I press "C-x h"
    And I press "C-w"
    And I switch to buffer "test1.rb"
    Then I should see:
    """
    outside
    line a
    line b
    line c
    outside
    """

  Scenario: Removing original
    And I switch to buffer "test1.rb"
    And I press "C-x h"
    And I press "C-w"
    When I switch to buffer "*multifile*"
    Then I should not see:
    """
    line a
    line b
    line c
    """

  Scenario: Support for delete-selection-mode
    Given I turn on delete-selection-mode
    And I switch to buffer "test1.rb"
    And I go to the end of the word "a"
    And I insert "ff"
    And I select "line b"
    And I press "f"
    Then I should see:
    """
    line aff
    f
    line c
    """

  Scenario: Same major mode as first original
    When I switch to buffer "*multifile*"
    Then the major-mode should be "ruby-mode"

  Scenario: Saving original files
    When I switch to buffer "*multifile*"
    And I go to the end of the word "line b"
    And I insert "ooya!"
    And I press "C-x C-s yes"
    And I switch to buffer "test1.rb"
    Then the buffer should be saved
