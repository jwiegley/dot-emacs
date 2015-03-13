Feature: company-ghc scan modules

  Scenario: Scan simple import
    Given the haskell buffer template
    When I replace template "IMPORT" by:
    """
    import System.IO
    """
    And I execute company-ghc-scan-modules
    # Prelude always added
    Then scanned modules are:
    """
    (("System.IO") ("Prelude"))
    """

    Given the haskell buffer template
    When I replace template "IMPORT" by:
    """
    import           Data.Text
    import           System.IO
    """
    And I execute company-ghc-scan-modules
    # Prelude always added
    Then scanned modules are:
    """
    (("System.IO") ("Data.Text") ("Prelude"))
    """

    Given the haskell buffer template
    When I replace template "IMPORT" by ""
    And I execute company-ghc-scan-modules
    # Prelude always added
    Then scanned modules are "(("Prelude"))"

  Scenario: Scan qualified import
    Given the haskell buffer template
    When I replace template "IMPORT" by:
    """
    import qualified Data.Text
    """
    And I execute company-ghc-scan-modules
    Then scanned modules are:
    """
    (("Data.Text" . "Data.Text") ("Prelude"))
    """

    Given the haskell buffer template
    When I replace template "IMPORT" by:
    """
    import qualified Data.Text as T
    import qualified Data.Text.Lazy as TL
    """
    And I execute company-ghc-scan-modules
    Then scanned modules are:
    """
    (("Data.Text.Lazy" . "TL") ("Data.Text" . "T") ("Prelude"))
    """

  Scenario: Scan selective import
    Given the haskell buffer template
    When I replace template "IMPORT" by:
    """
    import Control.Monad ()
    import Data.Text (Text, strip)
    import Data.ByteString hiding (splitAt)
    """
    And I execute company-ghc-scan-modules
    Then scanned modules are:
    """
    (("Data.ByteString") ("Data.Text") ("Control.Monad") ("Prelude"))
    """

  Scenario: Scan safe import
    Given the haskell buffer template
    When I replace template "IMPORT" by:
    """
    import safe Control.Applicative
    import safe qualified Data.Monoid
    """
    And I execute company-ghc-scan-modules
    Then scanned modules are:
    """
    (("Data.Monoid" . "Data.Monoid") ("Control.Applicative") ("Prelude"))
    """

  Scenario: Scan package import
    Given the haskell buffer template
    When I replace template "IMPORT" by:
    """
    import "mtl" Control.Monad.Trans
    import safe qualified "mtl" Control.Monad.State as State
    """
    And I execute company-ghc-scan-modules
    Then scanned modules are:
    """
    (("Control.Monad.State" . "State") ("Control.Monad.Trans") ("Prelude"))
    """

  Scenario: Scan import with newline
    Given the haskell buffer template
    When I replace template "IMPORT" by:
    """
    import
        Data.Text
    import
        safe
        qualified
        "bytestring"
        Data.ByteString
        as
        B
        (
          readFile,
          writeFile
        )
    """
    And I execute company-ghc-scan-modules
    Then scanned modules are:
    """
    (("Data.ByteString" . "B") ("Data.Text") ("Prelude"))
    """

  Scenario: Scan incomplete import
    Given the haskell buffer template
    When I replace template "IMPORT" by:
    """
    import
    import Control.Applicative
    import
    import Control.
    """
    And I execute company-ghc-scan-modules
    Then scanned modules are:
    """
    (("Control.") ("Control.Applicative") ("Prelude"))
    """

    Given the haskell buffer template
    When I replace template "IMPORT" by:
    """
    import Control.Applicative ((<$>),
    import Data.Text
    """
    And I execute company-ghc-scan-modules
    Then scanned modules are:
    """
    (("Data.Text") ("Control.Applicative") ("Prelude"))
    """

    Given the buffer is empty
    When I insert:
    """
    import Control.Monad
    import qualified Data.Map as M (
    """
    And I execute company-ghc-scan-modules
    Then scanned modules are:
    """
    (("Data.Map" . "M") ("Control.Monad") ("Prelude"))
    """

  Scenario: Not scan import in string,comment
    Given the haskell buffer template
    When I replace template "IMPORT" by:
    """
    {-
    import Data.Text
    -}
    "import Data.ByteString"
    """
    And I execute company-ghc-scan-modules
    Then scanned modules are "(("Prelude"))"
