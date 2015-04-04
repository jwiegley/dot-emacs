master (in development)
=======================

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
