# password-store-otp
[![Emacs](https://img.shields.io/badge/Emacs-25-8e44bd.svg)](https://www.gnu.org/software/emacs/)
[![Build Status](https://travis-ci.org/volrath/password-store-otp.el.svg?branch=master)](https://travis-ci.org/volrath/password-store-otp.el)

Emacs functions to interact with
the [`pass-otp`](https://github.com/tadfisher/pass-otp) extension
for [`pass`](https://www.passwordstore.org/).

It include functions to import OTP URIs from screenshots of QR codes, and to
export them back to QR codes if needed. These features have been tested on OSX
and Linux, YMMV.

## Dependencies

Shares all dependencies with `pass` and `pass-otp`, and introduces these for SS
handling and QR code generation:

- imagemagick (--with-x11 support)
- zbar-tools
- qrencode

## Getting started

Place `password-store-otp.el` somewhere in your `load-path`.

# Available functions

- `password-store-otp-code` entry

  Return an OTP code/token from ENTRY.

- `password-store-otp-uri` entry

  Return an OTP URI from ENTRY.

- `password-store-otp-qrcode` entry &optional type

  Display a QR Code from ENTRY's OTP URI.
  An optional TYPE might be passed, this argument reflects `qrencode` command
  type, please refer to its man page.

- `password-store-otp-code-copy` (interactive) entry

  Copy an OTP code/token from ENTRY to clipboard.

- `password-store-otp-uri-copy` (interactive) entry

  Copy an OTP URI from ENTRY to clipboard.

- `password-store-otp-insert` (interactive) entry otp-uri

  Insert a new ENTRY containing OTP-URI.

- `password-store-otp-append` (interactive) entry otp-uri

  Append OTP-URI to an ENTRY.

- `password-store-otp-append-from-image` (interactive) entry

  Signals OS to take a (area) screenshot and scan the image to get an OTP URI,
  then appends it to ENTRY.

## LICENSE

&copy; 2017 Daniel Barreto

Distributed under the terms of the GNU GENERAL PUBLIC LICENSE, version 3.
