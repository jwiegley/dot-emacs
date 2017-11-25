master (in development)
=======================

- Support GHC 8.2 with Cabal 2.0 [GH-66]
- Use `cpp-options` cabal file field to get more options for GHC [GH-68]
- Fix obtaining configuration from cabal file if current directory has Prelude module in it [GH-70]
- Get correct location of stack’s dist directory. Fixes the case when GHC was installed via stack [GH-73]
- Improve `flycheck-haskell-setup` to perform initialization the first time a Haskell file is opened [https://github.com/flycheck/flycheck/issues/1346]

0.8 (May 24, 2016)
==================

- Remove `flycheck-haskell-runhaskell` in favour of `flycheck-haskell-runghc`
- Use `stack runghc` by default
- Only make dependent packages visible to GHC [GH-47] [GH-48]
- Add Stack build directories to GHC search path [GH-48]
- Add Cabal macros to GHC and hlint [GH-51]
- Make sure to use the right Cabal library with Stack [GH-60]

0.7.2 (Jun 02, 2015)
====================

- Don’t choke when a configuration key is missing [GH-37]

0.7.1 (May 30, 2015)
====================

- Don’t choke when sandbox no is present [GH-35]
- Don’t change GHC executable when compiler is not configured

0.7 (May 28, 2015)
==================

- Extract compiler from `cabal.config` [GH-28] [GH-29]
- Handle Cabal conditionals [GH-31]

0.6 (Apr 04, 2015)
==================

- Fix error when `default-directory` does not exist
- Extract various additional GHC options [GH-25] [GH-26]
- Extract dependencies to avoid package conflicts [GH-25] [GH-26]

0.5.1 (Dec 27, 2014)
====================

- Explicitly set local values of variables

0.5 (Oct 3, 2014)
=================

- Extract language extensions from Cabal projects [GH-3]
- Set the language from Cabal [GH-9]
- Merge all helpers into a single one [GH-13]
- Cache cabal configurations [GH-16] [GH-18]

0.4 (Apr 25, 2014)
==================

- Add build files from executables to GHC path
- Add interactive `flycheck-haskell-configure` to explicitly re-configure
  Flycheck

0.3 (Apr 14, 2014)
==================

- Use sandboxes even without Cabal files
- Add build files from Cabal to GHC path

0.2 (Apr 3, 2014)
=================

- Postpone setup until after local variables were set up
- Add auto-generated files from Cabal to GHC path

0.1 (Jan 13, 2014)
==================

Initial release
