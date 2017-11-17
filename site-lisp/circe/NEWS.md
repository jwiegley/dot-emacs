# New in 2.6

- No new features, but some bug fixes.

# New in 2.5

- Update the openssl invocation to current versions of openssl. For
  some reason, they just remove a command line argument.
- Some other bug fixes.

# New in 2.4

- `circe-server-killed-confirmation` now can kill every buffer even
  without asking (thanks to Rudi Grinberg)
- lui has been improved to know about past messages to facilitate
  editing and deletion of old messages, primarily for protocols like
  Slack (thanks to Tom Willemse)
- Lots of bug fixes

# New in 2.3

- Circe (Lui) now has a track bar. Use `(enable-lui-track-bar)` to get
  a bar where you stopped reading when you did hide a buffer.
- Buffers are now by default limited to 100k, as large buffers cause
  unreasonable slowdown in Emacs.
- Autopaste now defaults to ix.io and also knows about ptpb.pw.
- A number of faces have been updated to be nicer to the eye.
- Improve compatibility with the Slack IRC gateway.
- Lots of bug fixes.

# New in 2.2

- Server configuration now accepts the `:reduce-lurker-spam` keyword
  to set that variable.
- Lui now supports inline markup with `*bold*` and similar. Customize
  `lui-formatting-list` for this.
- `lui-add-input` is a new function to tell lui about new input that
  did not originate from lui itself. It is added to the history.
- Circe now adds the argument to `/query` to the chat history of a
  query buffer.
- The new variables `lui-time-stamp-time` and `lui-time-stamp-zone`
  allow programmers to customize the time zone for time stamps in lui.
- And lots of bug fixes.

# New in 2.1

- New option: `circe-inhibit-nick-highlight-function` – this allows
  you to disable nick highlighting in some messages.
- New extension: `circe-new-day-notifier.el` – show date changes in
  chat buffers. (Thanks to Pásztor János!)
- Improve Bitlbee support by adding a default port (6667) and
  disabling lagmon if it is used.
- Improved buttonizing of various references, like PEP links or Emacs
  debbugs references.
- Fix a bug that would confuse Emacs with lots of `nil` faces
- Lots of other bug fixes.

# New in 2.0

- Circe has had its IRC backend completely rewritten. It is now a
  separate library, `irc.el`, and much more powerful. Alas, this means
  a lot of existing configuration code will break.
- Because of this, Circe now fully supports SASL authentication,
  extended joins, and a few other modern IRC capabilities.
- XKCD references, CVE numbers and github issues are now buttonized.
- All IRC buffers change to the home directory by default.
- Circe now uses [buttercup][] for tests and Travis-CI for continuous
  integration tests.
- A number of options were removed to focus on sensible defaults.
  Re-check your configuration.
- Nick colors are now pre-computed to make them more appropriate for
  the current display and more distinct from each other.
- A lot of format strings have been added. Check the `circe-format`
  customization group.

[buttercup]: https://github.com/jorgenschaefer/emacs-buttercup
