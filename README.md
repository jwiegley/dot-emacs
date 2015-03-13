Alert is a Growl-workalike for Emacs which uses a common notification
interface and multiple, selectable "styles", whose use is fully customizable
by the user.

# For module writers

Just use `alert` instead of `message` as follows:

``` lisp
(require 'alert)

;; This is the most basic form usage
(alert "This is an alert")

;; You can adjust the severity for more important messages
(alert "This is an alert" :severity 'high)

;; Or decrease it for purely informative ones
(alert "This is an alert" :severity 'trivial)

;; Alerts can have optional titles.  Otherwise, the title is the
;; buffer-name of the (current-buffer) where the alert originated.
(alert "This is an alert" :title "My Alert")

;; Further, alerts can have categories.  This allows users to
;; selectively filter on them.
(alert "This is an alert" :title "My Alert" :category 'debug)
```

# For users

For the user, there are several variables to control when and how alerts
are presented.  By default, they appear in the minibuffer much the same
as a normal Emacs message.  But there are many more possibilities:

  - `alert-fade-time`  
    Normally alerts disappear after this many seconds, if the style
    supports it.  The default is 5 seconds.

  - `alert-default-style`  
    Pick the style to use if no other config rule matches.  The
    default is `message`, but `growl` works well too.

  - `alert-reveal-idle-time`  
    If a config rule choose to match on `idle`, this is how many
    seconds idle the user has to be.  Defaults to 5 so that users
    don't miss any alerts, but 120 is also good.

  - `alert-persist-idle-time`  
    After this many idle seconds, alerts will become sticky, and not
    fade away more.  The default is 15 minutes.

  - `alert-log-messages`  
    By default, all alerts are logged to *Alerts* (and to *Messages*,
    if the `message` style is being used).  Set to nil to disable.

  - `alert-hide-all-notifications`  
    Want alerts off entirely?  They still get logged, however, unless
    you've turned that off too.

  - `alert-user-configuration`  
    This variable lets you control exactly how and when a particular
    alert, a class of alerts, or all alerts, get reported -- or if at
    all.  Use this to make some alerts use Growl, while others are
    completely silent.

# Programmatically adding rules

Users can also programmatically add configuration rules, in addition to
customizing `alert-user-configuration`.  Here is one that the author
currently uses with ERC, so that the fringe gets colored whenever people
chat on BitlBee:

``` lisp
(alert-add-rule :status   '(buried visible idle)
                :severity '(moderate high urgent)
                :mode     'erc-mode
                :predicate
                #'(lambda (info)
                    (string-match (concat "\\`[^&].*@BitlBee\\'")
                                  (erc-format-target-and/or-network)))
                :persistent
                #'(lambda (info)
                    ;; If the buffer is buried, or the user has been
                    ;; idle for `alert-reveal-idle-time' seconds,
                    ;; make this alert persistent.  Normally, alerts
                    ;; become persistent after
                    ;; `alert-persist-idle-time' seconds.
                    (memq (plist-get info :status) '(buried idle)))
                :style 'fringe
                :continue t)
```

# Builtin alert styles

There are several builtin styles, and it is trivial to create new ones.
The builtins are:

| Name          | Summary                                                           |
| ------------- | ------------------------------------------------------------------|
| message       | Uses the Emacs `message` facility                                 |
| log           | Logs the alert text to *Alerts*, with a timestamp                 |
| ignore        | Ignores the alert entirely                                        |
| fringe        | Changes the current frame's fringe background color               |
| growl         | Uses Growl on OS X, if growlnotify is on the PATH                 |
| gntp          | Uses gntp, it requires [gntp.el](https://github.com/tekai/gntp.el)|
| notifications | Uses notifications library via D-Bus                              |

# Defining new styles

To create a new style, you need to at least write a `notifier`, which is
a function that receives the details of the alert.  These details are
given in a plist which uses various keyword to identify the parts of the
alert.  Here is a prototypical style definition:

``` lisp
(alert-define-style 'style-name :title "My Style's title"
                    :notifier
                    (lambda (info)
                      ;; The message text is :message
                      (plist-get info :message)
                      ;; The :title of the alert
                      (plist-get info :title)
                      ;; The :category of the alert
                      (plist-get info :category)
                      ;; The major-mode this alert relates to
                      (plist-get info :mode)
                      ;; The buffer the alert relates to
                      (plist-get info :buffer)
                      ;; Severity of the alert.  It is one of:
                      ;;   `urgent'
                      ;;   `high'
                      ;;   `moderate'
                      ;;   `normal'
                      ;;   `low'
                      ;;   `trivial'
                      (plist-get info :severity)
                      ;; Whether this alert should persist, or fade away
                      (plist-get info :persistent)
                      ;; Data which was passed to `alert'.  Can be
                      ;; anything.
                      (plist-get info :data))

                    ;; Removers are optional.  Their job is to remove
                    ;; the visual or auditory effect of the alert.
                    :remover
                    (lambda (info)
                      ;; It is the same property list that was passed to
                      ;; the notifier function.
                      ))
```