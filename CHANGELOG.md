# Changelog

##  master (unreleased)

### 2.2.0 2017-04-02

* [#68] Better handling of background messages
* [#67] Abort all operations on user input, for better performance.

### 2.1.0 2017-03-31

* [#66](https://github.com/expez/company-quickhelp/issues/66) Create a buffer local minor mode.
* [64](https://github.com/expez/company-quickhelp/pull/64) Prevent errors if activated in terminal.
* [#53](https://github.com/expez/company-quickhelp/issues/53) Allow colours in popup.

### 2.0.0 2016-08-24

*[#44](https://github.com/expez/company-quickhelp/issues/44) Fix shadowing keybinding for mark-region.

### 1.3.0 2016-02-11

* Fix an issue where `company-tooltip-minimum-width` was set to `nil` when user disabled the mode without first enabling it.
* [#28](https://github.com/expez/company-quickhelp/issues/28)  Handle doc backends returning `(doc-buffer . start-pos)`.

### 1.2.0 2015-08-04

* [#22](https://github.com/expez/company-quickhelp/issues/22) Keybinding to manually display the documentation popup.

### 1.0.1 - 2015-05-01

* Error out when mac users running an emacs build we don't support (Cocoa instead of X) try to start company-quickhelp.
