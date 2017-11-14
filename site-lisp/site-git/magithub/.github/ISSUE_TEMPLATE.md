# Thanks for helping out!

Reporting an error?  Oh no!  I'm happy to take a look at it, but *please* provide the backtrace in your issue: before triggering the error make sure `debug-on-error` is set to `t` (interactively, you can use `M-x toggle-debug-on-error`).  Then, just copy the backtrace that's provided :smile:

As you're probably aware, Magithub is a synthesis of two very fantastic tools: [the magit porcelain for Emacs][magit] and [the `hub` command-line utility][hub].  Please be mindful of which project you're opening this issue against.

Since this project has a familiarity with *both* tools, an issue opened here can easily be redirected somewhere else.

# Feature Requests

Since Magithub relies on [`hub`][hub], there are some features that are yet beyond reach.  I'm using [the 2.2-stable branch][hub-2.2] to create Magithub's commands -- anything that's not implemented there will be difficult to implement here.  When a new version of Hub is released, Magithub will be similarly updated to account for any new commands/switches/options.  Feel free to open an feature-request issue for tracking, though!

[magit]: //www.github.com/magit/magit
[hub]: //hub.github.com
[hub-2.2]: //github.com/github/hub/tree/2.2-stable
