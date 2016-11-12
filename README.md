[![Build Status](https://travis-ci.org/sigma/marshal.el.svg?branch=master)](https://travis-ci.org/sigma/marshal.el)

EIEIO marshalling, inspired by Go tagged structs.

alist, plist and json drivers are provided, but implementing others just requires to inherit
from `marshal-driver'.

It's also possible to maintain a private drivers "namespace", by providing
the :marshal-base-cls option to `marshal-defclass'.

This is particularly useful to maintain different "views" of the same object
(potentially using the same driver) without having to register many drivers in
the global space.

See inline documentation for examples.
