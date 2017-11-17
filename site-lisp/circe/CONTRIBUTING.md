We welcome patches to improve Circe. This file will help you set up a
local development environment.

## Preparation

You will need the following software installed:

- [Cask](https://github.com/cask/cask)

Once you have that, you can clone the repository locally:

```
git clone https://github.com/jorgenschaefer/circe
```

In the repository, run the setup script to create your development
environment:

```
cd .../circe
./scripts/setup
```

## Running Tests

Now, every time you change code, you can run the tests:

```
./scripts/test
```

There’s also a `test-full` to run the tests in all supported Emacs
versions. Use the normal `test` script during development and for TDD.
Use `test-full` before submitting patches.

## Coding Style

- Do adhere to normal Emacs Lisp coding conventions as in the rest of
  Circe
- Do write tests if at all possible. Changes to `irc.el` MUST be
  accompanied by a test.
- Do feel free to use `cl-lib`
- Do not add further external requirements (outside of the standard
  Emacs distribution) without talking with us first

## Discussions

Join us in `#emacs-circe` on `irc.freenode.net`!
