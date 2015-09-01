Feature: company-ghc candidates

  Scenario: Pragma candidates
    Given the buffer is empty
    Given these GHC pragmas "LANGUAGE OPTIONS_GHC"
    When I insert "{-# "
    And I execute company-ghc candidates command at current point
    Then company-ghc candidates are:
    """
    ("LANGUAGE" "OPTIONS_GHC")
    """

    Given these GHC pragmas "LANGUAGE INCLUDE OPTIONS_GHC INLINE UNPACK"
    When I insert "IN"
    And I execute company-ghc candidates command at current point
    Then company-ghc candidates are:
    """
    ("INCLUDE" "INLINE")
    """

  Scenario: LANGUAGE candidates
    Given the buffer is empty
    Given these GHC language extensions:
    """
    Haskell98
    Haskell2010
    Unsafe
    Trustworthy
    Safe
    CPP
    NoCPP
    PostfixOperators
    NoPostfixOperators
    """
    When I insert "{-# LANGUAGE "
    And I execute company-ghc candidates command at current point
    Then company-ghc candidates are:
    """
    (
    "Haskell98"
    "Haskell2010"
    "Unsafe"
    "Trustworthy"
    "Safe"
    "CPP"
    "NoCPP"
    "PostfixOperators"
    "NoPostfixOperators"
    )
    """

    When I insert "Haskell"
    And I execute company-ghc candidates command at current point
    Then company-ghc candidates are "("Haskell98" "Haskell2010")"

    When I insert:
    """
    2010,
                 No
    """
    And I execute company-ghc candidates command at current point
    Then company-ghc candidates are "("NoCPP" "NoPostfixOperators")"

    Given the buffer is empty
    When I insert "{-#LANGUAGE C"
    And I execute company-ghc candidates command at current point
    Then company-ghc candidates are "("CPP")"

  Scenario: OPTIONS_GHC candidates
    Given the buffer is empty
    Given these GHC option flags:
    """
    -ferror-spans
    -fno-error-spans
    -fprint-explicit-foralls
    -fno-print-explicit-foralls
    -fprint-explicit-kinds
    -fno-print-explicit-kinds
    -fstrictness
    -fno-strictness
    """
    When I insert "{-# OPTIONS_GHC "
    And I execute company-ghc candidates command at current point
    Then company-ghc candidates are:
    """
    (
    "-ferror-spans"
    "-fno-error-spans"
    "-fprint-explicit-foralls"
    "-fno-print-explicit-foralls"
    "-fprint-explicit-kinds"
    "-fno-print-explicit-kinds"
    "-fstrictness"
    "-fno-strictness"
    )
    """

    When I insert "-fe"
    And I execute company-ghc candidates command at current point
    Then company-ghc candidates are "("-ferror-spans")"

    When I insert:
    """
    error-spans,
                    -fno
    """
    And I execute company-ghc candidates command at current point
    Then company-ghc candidates are:
    """
    (
    "-fno-error-spans"
    "-fno-print-explicit-foralls"
    "-fno-print-explicit-kinds"
    "-fno-strictness"
    )
    """

  Scenario: Import module candidates
    Given the buffer is empty
    Given these GHC modules:
    """
    Data.Text
    Data.Text.Lazy
    Data.ByteString
    Data.ByteString.Lazy
    Prelude
    System.Environment
    System.IO
    """

    When I insert "import "
    And I execute company-ghc candidates command at current point
    Then company-ghc candidates are:
    """
    (
    "Data.Text"
    "Data.Text.Lazy"
    "Data.ByteString"
    "Data.ByteString.Lazy"
    "Prelude"
    "System.Environment"
    "System.IO"
    )
    """

    When I insert "Data."
    And I execute company-ghc candidates command at current point
    Then company-ghc candidates are:
    """
    (
    "Data.Text"
    "Data.Text.Lazy"
    "Data.ByteString"
    "Data.ByteString.Lazy"
    )
    """

    Given the buffer is empty
    When I insert "import safe qualified System"
    And I execute company-ghc candidates command at current point
    Then company-ghc candidates are:
    """
    (
    "System.Environment"
    "System.IO"
    )
    """

  Scenario: Imported module keyword candidates
    Given the buffer is empty
    Given these module keywords:
      | module          | keywords                               |
      | Predule         | head readFile splitAt tail writeFile   |
      | Data.Text       | Text singleton splitOn strip           |
      | Data.Text.IO    | readFile writeFile                     |
      | Data.ByteString | ByteString singleton splitAt           |
      | System.IO       | readFile stderr stdin stdout writeFile |

    When I insert "import Data.Text ("
    And I execute company-ghc candidates command at current point
    Then company-ghc candidates are:
    """
    (
    "Text"
    "singleton"
    "splitOn"
    "strip"
    )
    """

    When I insert "s"
    And I execute company-ghc candidates command at current point
    Then company-ghc candidates are:
    """
    (
    "singleton"
    "splitOn"
    "strip"
    )
    """

    When I insert:
    """
    strip,
                     T
    """
    And I execute company-ghc candidates command at current point
    Then company-ghc candidates are "("Text")"

    When I insert:
    """
    ext)
    import qualified Data.ByteString as B (
    """
    And I execute company-ghc candidates command at current point
    Then company-ghc candidates are:
    """
    (
    "ByteString"
    "singleton"
    "splitAt"
    )
    """

    When I insert:
    """
    )
    import safe "base" System.IO hiding (r
    """
    And I execute company-ghc candidates command at current point
    Then company-ghc candidates are "("readFile")"

  Scenario: Loaded modules keyword candidates
    Given the buffer is empty
    And these imported modules:
      | module    | alias |
      | Data.Text |       |
      | System.IO |       |

    When I insert:
    """
    main = do
        s
    """
    And I execute company-ghc candidates command at current point
    Then company-ghc candidates are:
    """
    (
    "singleton"
    "splitOn"
    "stderr"
    "stdin"
    "stdout"
    "strip"
    )
    """

  Scenario: Qualified imported keyword candidates
    Given the buffer is empty
    And these imported modules:
      | module          | alias           |
      | Data.Text       | T               |
      | Data.Text.IO    | T               |
      | Data.ByteString | Data.ByteString |
      | System.IO       |                 |

    When I insert:
    """
    foo = T.
    """
    And I execute company-ghc candidates command at current point
    Then company-ghc candidates are:
    """
    (
    "Text"
    "readFile"
    "singleton"
    "splitOn"
    "strip"
    "writeFile"
    )
    """

    Given the buffer is empty
    When I insert:
    """
    foo = T.s
    """
    And I execute company-ghc candidates command at current point
    Then company-ghc candidates are:
    """
    (
    "singleton"
    "splitOn"
    "strip"
    )
    """

    Given the buffer is empty
    When I insert:
    """
    foo = Data.ByteString.s
    """
    And I execute company-ghc candidates command at current point
    Then company-ghc candidates are:
    """
    (
    "singleton"
    "splitAt"
    )
    """
