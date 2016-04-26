# nnreddit
A Reddit backend for the [Gnus newsreader](http://www.gnus.org/).

NOTE: currently for reading only, login and posting not yet implemented. Message status (read vs. unread, new, flagged) is also not yet handled. Contributions welcome!

## Usage

Add these lines to your `.emacs` or `.gnus` file:
```lisp
(require 'nnreddit "/path/to/nnreddit.el")
(add-to-list 'gnus-secondary-select-methods
             '(nnreddit ""))
```

Then subscribe to a group from within Gnus, either by pressing 'U' in the Group buffer and entering "nnreddit:some-subreddit", or with the following command:
```lisp
(gnus-group-unsubscribe-group "nnreddit:some-subreddit")
```


***

**IMPORTANT:** you need to add a `(display 'all)` parameter to every nnreddit group (use 'G c' or 'G p' from the group buffer to set this parameter), since there is currently no proper tracking of the read/unread status of each message. Without this parameter some articles or comments may not be displayed.

Until the read/unread status is implemented, you may also want to set the `gnus-summary-goto-unread` variable to `'never` in nnreddit buffers to ease navigation.

***


You can also browse individual threads (or sub-threads) with the following syntax:
```lisp
;; Single thread
(gnus-group-unsubscribe-group "nnreddit:some-subreddit/comments/link-id")
;; Sub-thread
(gnus-group-unsubscribe-group "nnreddit:some-subreddit/comments/link-id/comments/comment-id")
```
In other words, simply take the URL of any Reddit thread, replace "ht<b></b>tps://ww<b></b>w.reddit.com/r/" with "nnreddit:" and subscribe to that in Gnus.

Alternatively, you can subscribe to a thread or sub-thread directly from the summary buffer with the `nnreddit-subscribe-to-thread' command.

(make sure to set the `(display 'all)` parameter for such groups as well)

## Screenshots

<a href="https://raw.githubusercontent.com/paul-issartel/nnreddit/master/screenshot.png"><img src="https://raw.githubusercontent.com/paul-issartel/nnreddit/master/screenshot.png" alt="Screenshot of a Reddit link article in Gnus" width="500"/></a>

<a href="https://raw.githubusercontent.com/paul-issartel/nnreddit/master/screenshot2.png"><img src="https://raw.githubusercontent.com/paul-issartel/nnreddit/master/screenshot2.png" alt="Screenshot of a Reddit comment in Gnus" width="500"/></a>
