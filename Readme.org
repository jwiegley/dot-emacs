#+TITLE: Beacon --- Never lose your cursor again

This is a global minor-mode.  Turn it on everywhere with:
#+BEGIN_SRC emacs-lisp
(beacon-mode 1)
#+END_SRC

[[file:example-beacon.gif]]

Whenever the window scrolls a light will shine on top of your cursor
so you know where it is.

That’s it.

** Customizations

- The appearance of the beacon is configured by ~beacon-size~ and
  ~beacon-color~.

- The duration is configured by ~beacon-blink-duration~ and
  ~beacon-blink-delay~.

- To customize /when/ the beacon should blink at all, configure
  ~beacon-blink-when-window-scrolls~,
  ~beacon-blink-when-window-changes~, and
  ~beacon-blink-when-point-moves~.

- To prevent the beacon from blinking only on specific situations
  configure ~beacon-dont-blink-major-modes~,
  ~beacon-dont-blink-predicates~, or ~beacon-dont-blink-commands~. You
  can also disable it only in specific buffers by doing
  ~(setq-local beacon-mode nil)~.

- Beacon can also push the mark for you whenever point moves a long
  distance. For this, configure ~beacon-push-mark~.

** Contributors

- [[https://github.com/tsdh][Tassilo Horn]]

If you’d like to help too, just open a PR.
