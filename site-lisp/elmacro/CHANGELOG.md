# Changelog

## 1.1.0 (2017-03-12)

- Handle `self-insert-command` interceptors.
- Add changelog

## 1.0.1 (2016-04-10)

- Reintroduce defun name for elmacro-show-last-macro

## 1.0.0 (2016-02-10)

- Big refactoring of code
- Implement processors
- Add inserts concatenator processor
- Add elmacro-show-last-commands-default variable
- Update dependencies
- Ensure elmacro is turned on before using it
- Improve documentation

## 0.3.0 (2014-09-11)

- New interactive command `elmacro-clear-recorded-commands'.
- Correct bug with symbols quoting (#11).
- Filter unwanted commands using a regexp.
- README improvements.

## 0.2.0 (2014-07-07)

- interactive function `elmacro-show-last-commands`
- add `#<frame>`, `#<window>` and `#<buffer>` support

## 0.1.0 (2014-28-08)

- interactive function `elmacro-show-last-macro`
- interactive function `elmacro-show-lossage`
- option `elmacro-filters`
- option `elmacro-custom-recorded-functions`
- option `elmacro-concatenate-multiple-inserts`
