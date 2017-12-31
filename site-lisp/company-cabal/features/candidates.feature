Feature company-cabal candidates

  Scenario: Library candidates
    Given the buffer is empty
    When I insert:
    """
    library
      
    """
    And I execute company-cabal candidates command at current point
    Then company-cabal candidates contains "exposed-modules"

    Given the buffer is empty
    When I insert:
    """
    library
      build-depends: bytestring
      if os(windows)
        
    """
    And I execute company-cabal candidates command at current point
    Then company-cabal candidates contains "exposed-modules"

    Given the buffer is empty
    When I insert:
    """
    library
      ghc-options: -Wall
      if os(windows)
        build-depends: Win32
      else
        
    """
    And I execute company-cabal candidates command at current point
    Then company-cabal candidates contains "exposed-modules"

  Scenario: Executable candidates
    Given the buffer is empty
    When I insert:
    """
    executable foo
      
    """
    And I execute company-cabal candidates command at current point
    Then company-cabal candidates contains "main-is"

  Scenario: Test-suite candidates
    Given the buffer is empty
    When I insert:
    """
    test-suite test-foo
      
    """
    And I execute company-cabal candidates command at current point
    Then company-cabal candidates contains "type"
    And company-cabal candidates contains "main-is"
    And company-cabal candidates contains "test-module"

  Scenario: Benchmark candidates
    Given the buffer is empty
    When I insert:
    """
    benchmark bench-foo
      
    """
    And I execute company-cabal candidates command at current point
    Then company-cabal candidates contains "type"
    And company-cabal candidates contains "main-is"

  Scenario: Flag candidates
    Given the buffer is empty
    When I insert:
    """
    flag flag-foo
      
    """
    And I execute company-cabal candidates command at current point
    Then company-cabal candidates are:
    """
    ("default" "description" "manual")
    """

  Scenario: Source-repoistory candidates
    Given the buffer is empty
    When I insert:
    """
    source-repository head
      
    """
    And I execute company-cabal candidates command at current point
    Then company-cabal candidates are:
    """
    ("branch" "location" "module" "subdir" "tag" "type")
    """

  Scenario: Build-type candidates
    Given the buffer is empty
    When I insert:
    """
    build-type: 
    """
    And I execute company-cabal candidates command at current point
    Then company-cabal candidates are:
    """
    ("Simple" "Configure" "Make" "Custom")
    """

  Scenario: After build-type candidates
    Given the buffer is empty
    When I insert:
    """
    build-type: Simple
    li
    """
    And I execute company-cabal candidates command at current point
    Then company-cabal candidates contains "license"

    Given the buffer is empty
    When I insert:
    """
    build-type: Simple

    executable foo
      
    """
    And I execute company-cabal candidates command at current point
    Then company-cabal candidates contains "main-is"

  Scenario: Type candidates
    Given the buffer is empty
    When I insert:
    """
    benchmark bench-foo
      type: 
    """
    And I execute company-cabal candidates command at current point
    Then company-cabal candidates are:
    """
    ("exitcode-stdio-1.0")
    """

    Given the buffer is empty
    When I insert:
    """
    test-suite test-foo
      type: 
    """
    And I execute company-cabal candidates command at current point
    Then company-cabal candidates are:
    """
    ("exitcode-stdio-1.0" "detailed-1.0")
    """

    Given the buffer is empty
    When I insert:
    """
    source-repository head
      branch: master
      type:   g
    """
    And I execute company-cabal candidates command at current point
    Then company-cabal candidates are:
    """
    ("git")
    """

  Scenario: After type candidates
    Given the buffer is empty
    When I insert:
    """
    source-repository head
      type:   git
      bra
    """
    And I execute company-cabal candidates command at current point
    Then company-cabal candidates are:
    """
    ("branch")
    """

  Scenario: Build-depends candidates
    Given the buffer is empty
    And the following packages are installed:
    """
    Cabal base bytestring directory haskell2010 haskell98 text
    """
    When I insert:
    """
    library
      build-depends: b
    """
    And I execute company-cabal candidates command at current point
    Then company-cabal candidates are:
    """
    ("base" "bytestring")
    """

    Given the buffer is empty
    When I insert:
    """
    library
      build-depends: base, h
    """
    And I execute company-cabal candidates command at current point
    Then company-cabal candidates are:
    """
    ("haskell2010" "haskell98")
    """

    Given the buffer is empty
    When I insert:
    """
    library
      build-depends: base >=4.6 && <4.8, h
    """
    And I execute company-cabal candidates command at current point
    Then company-cabal candidates are:
    """
    ("haskell2010" "haskell98")
    """

    Given the buffer is empty
    When I insert:
    """
    library
      build-depends: base >=4.6 && <4.8,
                     t
    """
    And I execute company-cabal candidates command at current point
    Then company-cabal candidates are:
    """
    ("text")
    """

    Given the buffer is empty
    When I insert:
    """
    library
      build-depends: base >=4.6 && <4.8,
                     text >=1.1,
                     d
    """
    And I execute company-cabal candidates command at current point
    Then company-cabal candidates are:
    """
    ("directory")
    """

  Scenario: Ghc-Options candidates
    Given the buffer is empty
    And the following ghc-options are set:
    """
    -Wall -fasm -fno-warn-missing-signatures -threaded
    """
    When I insert:
    """
    library
      ghc-options: -f
    """
    And I execute company-cabal candidates command at current point
    Then company-cabal candidates are:
    """
    ("-fasm" "-fno-warn-missing-signatures")
    """

    Given the buffer is empty
    When I insert:
    """
    library
      ghc-prof-options: -O2 -W
    """
    And I execute company-cabal candidates command at current point
    Then company-cabal candidates are:
    """
    ("-Wall")
    """

    Given the buffer is empty
    When I insert:
    """
    library
      ghc-shared-options: -O2 -
    """
    And I execute company-cabal candidates command at current point
    Then company-cabal candidates are:
    """
    ("-Wall" "-fasm" "-fno-warn-missing-signatures" "-threaded")
    """

  Scenario: Extensions candidates
    Given the buffer is empty
    And the following ghc-extensions are set:
    """
    CApiFFI CPP BangPatterns QuasiQuotes TemplateHaskell TypeFamilies
    """
    When I insert:
    """
    library
      Extensions: C
    """
    And I execute company-cabal candidates command at current point
    Then company-cabal candidates are:
    """
    ("CApiFFI" "CPP")
    """

    When I insert:
    """
    library
      default-extensions: T
    """
    And I execute company-cabal candidates command at current point
    Then company-cabal candidates are:
    """
    ("TemplateHaskell" "TypeFamilies")
    """

    When I insert:
    """
    library
      Other-Extensions: Q
    """
    And I execute company-cabal candidates command at current point
    Then company-cabal candidates are:
    """
    ("QuasiQuotes")
    """

  Scenario: No candidate
    Given the buffer is empty
    When I insert:
    """
    library
      type: 
    """
    And I execute company-cabal candidates command at current point
    Then company-cabal candidates are "nil"
