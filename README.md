# pass

A major-mode to manage your
[password-store](http://passwordstore.org/) (pass) keychain.  The
keychain entries are displayed in a directory-like structure.

Canonical repository: https://gitlab.petton.fr/nico/pass.

## Installing

Use [melpa](https://melpa.org/).


## Getting started

This library depends on `password-store.el` and `password-store-otp.el`.

    M-x pass

The following keybindings are available:

- `i`: Insert a new entry (With a prefix argument, generate the password)
- `n`: Go to the next entry
- `p`: Go to the previous entry
- `M-n`: Go to the next directory
- `M-p`: Go to the previous directory
- `k`: Remove the entry at point
- `s`: Trigger iSearch
- `r`: Trigger iSearch (backward)
- `?`: Help
- `g`: Update the password-store buffer
- `RET` or `v`: Go to the entry at point
- `q`: Quit pass

#### 2FA / OTP Support

If you have the [`pass-otp`](https://github.com/tadfisher/pass-otp) extension
installed, you will be able to use the following keybindings as well:

- `o i`: Insert an OTP key URI in a new entry (as in `pass otp insert`)
- `o a`: Append an OTP key URI to an existing entry (as in `pass otp append`)\*
- `o s`: Take a screenshot of an OTP QR Code and have its related URI be appended to an existing entry
- `o o`: Copy OTP token for entry at point (as in `pass otp -c`)
- `o u`: Copy OTP key URI for entry at point (as in `pass otp uri -c`)

\* `o a` works exactly as `pass otp append`, in the sense that it will only
"append" a URI to an entry if said entry does not have a URI already. `pass otp
append` will not add several OTP key URIs to the same entry, but it will
substitute the existing OTP key URI with a new one in each call. For more
information, please refer to [`pass-otp`](https://github.com/tadfisher/pass-otp)
documentation.

#### Pass View Mode

`pass` entry files are displayed in buffers that run under
`pass-view-mode`. This major mode provides some features:

- It will mask the password line automatically, you can hit `C-c C-c` to unmask it.
- You can hit `C-c C-w` to copy your password to your clipbard.
- In case of having OTP information in an entry, the buffer will display a
  header line with the OTP token and remaining seconds until expiration.
- You can hit `C-c C-o` to copy the OTP token to your clipboard.
- You can hit `C-c C-q` to display the QR Code for the OTP URI in the entry.

## Pass in Emacs

Users of this package may also be interested in functionality provided
by other Emacs packages dealing with pass:

- [password-store](https://git.zx2c4.com/password-store/tree/contrib/emacs/password-store.el): password store (pass) support;
- [auth-password-store](https://github.com/DamienCassou/auth-password-store): integrate Emacs' auth-source with password-store;
- [helm-pass](https://github.com/jabranham/helm-pass): helm interface for pass.

## Contributing

Yes, please do! See [CONTRIBUTING][] for guidelines.

## License

See [LICENSE][]. Copyright (c) 2015-2016 Nicolas Petton & Damien Cassou.


[CONTRIBUTING]: ./CONTRIBUTING.md
[LICENSE]: ./LICENSE
