;;; prodigy.el --- Manage external services from within Emacs -*- lexical-binding: t; -*-

;; Copyright (C) 2013-2014 Johan Andersson

;; Author: Johan Andersson <johan.rejeep@gmail.com>
;; Maintainer: Johan Andersson <johan.rejeep@gmail.com>
;; Version: 0.7.0
;; URL: http://github.com/rejeep/prodigy.el
;; Package-Requires: ((s "1.8.0") (dash "2.4.0") (f "0.14.0") (emacs "24"))

;; This file is NOT part of GNU Emacs.

;;; License:

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;; Commentary:

;;; Code:

(require 's)
(require 'dash)
(require 'f)
(require 'ansi-color)
(require 'tabulated-list)
(require 'easymenu)
(require 'hl-line)

(eval-when-compile
  (declare-function discover-add-context-menu "discover")
  (declare-function magit-status "magit"))

(defgroup prodigy nil
  "Manage external services from within Emacs."
  :prefix "prodigy-"
  :group 'tools
  :link '(url-link :tag "Github" "https://github.com/rejeep/prodigy.el"))

(defface prodigy-red-face
  '((((class color)) :foreground "#cd4d40"))
  "Red color indicating failure."
  :group 'prodigy)

(defface prodigy-green-face
  '((((class color)) :foreground "#61b361"))
  "Green color indicating success."
  :group 'prodigy)

(defface prodigy-yellow-face
  '((((class color)) :foreground "#e7e24c"))
  "Yellow color used to indicate something that is not success of failure.

An example is restarting a service."
  :group 'prodigy)

(defcustom prodigy-completion-system 'ido
  "The completion system to be used by Prodigy."
  :group 'prodigy
  :type 'symbol
  :options '(ido default))

(defcustom prodigy-init-async-timeout 10
  "Seconds to wait for init async callback before failing."
  :group 'prodigy
  :type 'number)

(defcustom prodigy-stop-tryouts 10
  "Number of times to check for service being stopped."
  :group 'prodigy
  :type 'number)

(defcustom prodigy-start-tryouts 10
  "Number of times to check for service being started."
  :group 'prodigy
  :type 'number)

(defcustom prodigy-kill-process-buffer-on-stop nil
  "Will kill process buffer on stop if this is true."
  :group 'prodigy
  :type 'boolean)

(defcustom prodigy-timer-interval 1
  "How often to check for process changes, in seconds."
  :group 'prodigy
  :type 'number)

(defvar prodigy-mode-hook nil
  "Mode hook for `prodigy-mode'.")

(defvar prodigy-view-confirm-clear-buffer t
  "`prodigy-view-clear-buffer' will require confirmation if non-nil.")

(defvar prodigy-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "n") 'prodigy-next)
    (define-key map (kbd "p") 'prodigy-prev)
    (define-key map (kbd "M-<") 'prodigy-first)
    (define-key map (kbd "M->") 'prodigy-last)
    (define-key map (kbd "m") 'prodigy-mark)
    (define-key map (kbd "t") 'prodigy-mark-tag)
    (define-key map (kbd "M") 'prodigy-mark-all)
    (define-key map (kbd "u") 'prodigy-unmark)
    (define-key map (kbd "T") 'prodigy-unmark-tag)
    (define-key map (kbd "U") 'prodigy-unmark-all)
    (define-key map (kbd "s") 'prodigy-start)
    (define-key map (kbd "S") 'prodigy-stop)
    (define-key map (kbd "r") 'prodigy-restart)
    (define-key map (kbd "$") 'prodigy-display-process)
    (define-key map (kbd "o") 'prodigy-browse)
    (define-key map (kbd "f t") 'prodigy-add-tag-filter)
    (define-key map (kbd "f n") 'prodigy-add-name-filter)
    (define-key map (kbd "F") 'prodigy-clear-filters)
    (define-key map (kbd "j m") 'prodigy-jump-magit)
    (define-key map (kbd "j d") 'prodigy-jump-dired)
    (define-key map (kbd "M-n") 'prodigy-next-with-status)
    (define-key map (kbd "M-p") 'prodigy-prev-with-status)
    (define-key map (kbd "C-w") 'prodigy-copy-cmd)
    map)
  "Keymap for `prodigy-mode'.")

(defvar prodigy-view-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "k") 'prodigy-view-clear-buffer)
    map)
  "Keymap for `prodigy-view-mode'.")

(defvar prodigy-timer nil
  "Timer object checking for process changes.

Do not use or modify this variable, this is purely internal and
only used for caching.")

(defvar prodigy-services nil
  "List of services.

The list is a property list with the following properties:

`name'
  Name of service.

`command'
  Command to run.  This can be either a string or a lambda that return
  a string.

`args'
  Arguments passed to command.  This can be either a list of strings or
  a lambda that return a list of strings.

`cwd'
  Run command with this as `default-directory'.

`sudo'
  Run command as `sudo'

`port'
  Specify service port for use with open function.

`tags'
  List of tags.

`init'
  Function called before process is started.

`init-async'
  Function called before process is started with async callback.

`stop-signal'
  How to signal processes when stopping it.  This property can have
  any of the following values:
   * `int' - Will use the function `interrupt-process'.
   * `kill' - Will use the function `kill-process'.
   * `quit' - Will use the function `quit-process'.
   * `stop' - Will use the function `stop-process'.
   * If neither of the above, the function `signal-process' will be
     called with that value.

`path'
  Use this to add directories to PATH when starting service process.
  This can be a string, a list or a function.  For more information
  see doc-string for `prodigy-service-path'.

`env'
  List of lists (with two items).  First item is the name of an
  environment variable and second item is the value of the variable.

`url'
  Single url or list of urls to use for browsing.  If single url is
  specified, use that.  If a list of urls are specified, ask for what
  url to browse.

`kill-process-buffer-on-stop'
  Kill associated process buffer when process stops.

`truncate-output'
 Truncates the process ouptut buffer.  If set to t, truncates to
 `prodigy-view-buffer-maximum-size' lines.  If set to an integer,
 truncates to that number of lines.

`on-output'
  Call this function with (service, output), each time process gets
  new output.

`ready-message'
  The text that a service displays when it is ready.  Will be
  matched as a regexp.")

(defvar prodigy-tags nil
  "List of tags.

The list is a property list.  The allowed properties are
these (see `prodigy-services' doc-string for more information):

 * `command'
 * `args'
 * `cwd'
 * `tags'
 * `init'
 * `init-async'
 * `stop-signal'
 * `path'
 * `env'
 * `url'
 * `kill-process-buffer-on-stop'
 * `on-output'
 * `truncate-output'

These properties are also valid for a tag:

`hide'
  If set to true, the tag will not show up in the tags column.")

(defvar prodigy-filters nil
  "List of filters.

Each filter is a list of two elements where the first item is the
type of filter and the value is what should be filtered.

Supported filters:

`tag'
  Name of tag that service must include.

`name'
  String that service name must contain.")

(defvar prodigy-status-list nil
  "List of statues.

`id'
  Status identifier.  This is a symbol value.

`name'
  The default string representation of the status is by default the id
  capitalized.  If name is set, this is used instead.

`face'
  The face to use for the status.")

(defconst prodigy-buffer-name "*prodigy*"
  "Name of Prodigy mode buffer.")

(defconst prodigy-list-format
  [("Marked" 6 t :right-align t)
   ("Name" 35 t)
   ("Status" 15 t)
   ("Tags" 25 nil)]
  "List format.")

(defconst prodigy-list-sort-key
  '("Name" . nil)
  "Sort table on this key.")

(defvar prodigy-view-buffer-maximum-size 1024
  "The maximum size in lines for process view buffers.

Only enabled if `prodigy-view-truncate-by-default' is non-nil or
for services where :truncate-output is set to t.")

(defvar prodigy-view-truncate-by-default nil
  "Truncate all prodigy view buffers by default.

If enabled, view buffers will be truncated at
`prodigy-view-buffer-maximum-size' lines.")

(defvar prodigy-process-on-output-hook
  '(prodigy-on-output
    prodigy-check-for-ready-message
    prodigy-insert-output
    prodigy-truncate-buffer)
  "Hook to run after the process has produced output.

Functions will be run with 2 arguments, `service' and `output'.")

(defvar prodigy-output-filters
  '(ansi-color-apply
    prodigy-strip-ctrl-m)
  "Functions to run on process output.

Each function should take the output string as an argument and
return a string.")

(defconst prodigy-discover-context-menu
  '(prodigy
    (actions
     ("Navigation"
      ("n" "next service" prodigy-next)
      ("p" "prev service" prodigy-prev)
      ("M-<" "first service" prodigy-first)
      ("M->" "last service" prodigy-last))
     ("Marking"
      ("m" "mark service" prodigy-mark)
      ("t" "mark services with tag" prodigy-mark-tag)
      ("M" "mark all services" prodigy-mark-all)
      ("u" "unmark service" prodigy-unmark)
      ("T" "unmark services with tag" prodigy-unmark-tag)
      ("U" "unmark all services" prodigy-unmark-all))
     ("Process"
      ("s" "start service" prodigy-start)
      ("S" "stop service" prodigy-stop)
      ("r" "restart service" prodigy-restart)
      ("$" "display service process buffer" prodigy-display-process))
     ("Filters"
      ("f t" "add tag filter" prodigy-add-tag-filter)
      ("f n" "add name filter" prodigy-add-name-filter)
      ("F" "clear all filters" prodigy-clear-filters))
     ("Misc"
      ("o" "open in browser" prodigy-browse))))
  "The discover context menu.")

(easy-menu-define prodigy-mode-menu prodigy-mode-map
  "Prodigy menu"
  '("Prodigy"
    ["Next service" prodigy-next t]
    ["Previous service" prodigy-prev t]
    ["First service" prodigy-first t]
    ["Last service" prodigy-last t]
    "---"
    ["Mark service" prodigy-mark]
    ["Mark services with tag" prodigy-mark-tag]
    ["Mark all services" prodigy-mark-all]
    ["Unmark service" prodigy-unmark]
    ["Unmark services with tag" prodigy-unmark-tag]
    ["Unmark all services" prodigy-unmark-all]
    "---"
    ["Start service" prodigy-start]
    ["Stop service" prodigy-stop]
    ["Restart service" prodigy-restart]
    ["Display service process buffer" prodigy-display-process]
    "---"
    ["Add tag filter" prodigy-add-tag-filter]
    ["Add name filter" prodigy-add-name-filter]
    ["Clear all filters" prodigy-clear-filters]
    "---"
    ["Open in browser" prodigy-browse]))


;;;; Internal macros

(defmacro prodigy-callback-with-plist (function &rest properties)
  "Call FUNCTION with PROPERTIES as plist."
  `(if (help-function-arglist ,function nil)
       (apply
        ,function
        ,(cons
          'list
          (apply
           'append
           (-map
            (lambda (property)
              `(,(intern (concat ":" (symbol-name property))) ,property)) properties))))
     (funcall ,function)))

(defmacro prodigy-with-refresh (&rest body)
  "Execute BODY and then refresh."
  `(progn ,@body (prodigy-refresh)))

(defmacro prodigy-with-service-process-buffer (service &rest body)
  "Switch to SERVICE process buffer and yield BODY.

Buffer will be writable for BODY."
  (declare (indent 1))
  `(let ((buffer (get-buffer-create (prodigy-buffer-name ,service))))
     (let ((inhibit-read-only t))
       (-if-let (buffer-window (car (get-buffer-window-list buffer)))
           (with-selected-window buffer-window
             ,@body)
         (with-current-buffer buffer
           ,@body)))))


;;;; Service accessors

(defun prodigy-service-tags (service)
  "Return list of SERVICE tag objects.

This function will find SERVICE tags recursively.  So if SERVICE
has a tag foo and tag foo has a tag bar, this function would
return a list with both tags foo and bar.

If SERVICE has a tag that is not defined, it is not returned in
the list."
  (let ((tags (prodigy-taggable-tags service)))
    (apply 'append (--map (cons it (prodigy-taggable-tags it)) tags))))

(defun prodigy-service-port (service)
  "Find something that look like a port in SERVICE arguments.

If PORT is specified, use that.  If not, try to find something
that looks like a port in the ARGS list."
  (or
   (plist-get service :port)
   (-when-let (port (-first
                     (lambda (arg)
                       (s-matches? "^\\([0-9]\\)\\{4,5\\}$" arg))
                     (prodigy-service-args service)))
     (string-to-number port))))

(defun prodigy-service-command (service)
  "Return SERVICE command.

If SERVICE command exists, use that.  If not, find the first
SERVICE tag that has a command and return that."
  (let ((command (prodigy-service-or-first-tag-with service :command)))
    (if (functionp command)
        (prodigy-callback-with-plist command service)
      command)))

(defun prodigy-service-args (service)
  "Return SERVICE args list.

If SERVICE args exists, use that.  If not, find the first SERVICE
tag that has and return that."
  (let ((args (prodigy-service-or-first-tag-with service :args)))
    (if (functionp args)
        (prodigy-callback-with-plist args service)
      args)))

(defun prodigy-service-cwd (service)
  "Return SERVICE current working directory.

If SERVICE cwd exists, use that.  If not, find the first SERVICE
tag that has and return that."
  (prodigy-service-or-first-tag-with service :cwd))

(defun prodigy-service-init (service)
  "Return SERVICE init callback function.

If SERVICE init exists, use that.  If not, find the first SERVICE
tag that has and return that."
  (prodigy-service-or-first-tag-with service :init))

(defun prodigy-service-init-async (service)
  "Return SERVICE init async callback function.

If SERVICE init exists, use that.  If not, find the first SERVICE
tag that has and return that."
  (prodigy-service-or-first-tag-with service :init-async))

(defun prodigy-service-stop-signal (service)
  "Return SERVICE stop signal.

If SERVICE stop-signal exists, use that.  If not, find the first
SERVICE tag that has and return that."
  (prodigy-service-or-first-tag-with service :stop-signal))

(defun prodigy-service-kill-process-buffer-on-stop (service)
  "Return weather SERVICE should kill process buffer on stop or not.

If SERVICE kill-process-buffer-on-stop exists, use that.  If not, find the first
SERVICE tag that has and return that."
  (prodigy-service-or-first-tag-with service :kill-process-buffer-on-stop))

(defun prodigy-service-path (service)
  "Return list of SERVICE path extended with all tags path."
  (-uniq
   (-flatten
    (append
     (prodigy-resolve-pathy (plist-get service :path))
     (-map (lambda (tag)
             (prodigy-resolve-pathy (plist-get tag :path)))
           (prodigy-service-tags service))))))

(defun prodigy-service-env (service)
  "Return list of SERVICE env extended with all tags env."
  (let ((-compare-fn
         (lambda (a b)
           (equal (car a) (car b)))))
    (-uniq
     (append
      (plist-get service :env)
      (apply 'append (-map (lambda (tag)
                             (plist-get tag :env))
                           (prodigy-service-tags service)))))))

(defun prodigy-service-url (service)
  "Return SERVICE url.

If SERVICE url exists, use that.  If not, find the first SERVICE
tag that has and return that."
  (prodigy-service-or-first-tag-with service :url))

(defun prodigy-service-on-output (service)
  "Return SERVICE and its tags on-output functions as list.

First item in the list is the SERVICE on-output function, then
comes the SERVICE tags on-output functions."
  (prodigy-service-and-tags-with service :on-output))

(defun prodigy-service-ready-message (service)
  "Return the ready message for SERVICE."
  (prodigy-service-and-tags-with service :ready-message))

(defun prodigy-service-truncate-output (service)
  "Return SERVICE truncate output size.

If SERVICE truncate-output exists, use that.  If not, find the
first SERVICE tag that has and return that."
  (prodigy-service-or-first-tag-with service :truncate-output))


;;;; Internal functions

(defun prodigy-taggable-tags (taggable)
  "Return list of tags objects for TAGGABLE."
  (-reject 'null (-map 'prodigy-find-tag (plist-get taggable :tags))))

(defun prodigy-find-tag (name)
  "Return tag with NAME or nil if none."
  (--first (eq (plist-get it :name) name) prodigy-tags))

(defun prodigy-resolve-pathy (pathy)
  "Resolve PATHY to a string path.

PATHY can be either of:

`string'
  String path.

`list'
  List of string paths.

`lambda'
  A lambda function that return either a string path or a list of
  string paths."
  (cond ((functionp pathy)
         (prodigy-resolve-pathy (funcall pathy)))
        ((listp pathy)
         (-map 'prodigy-resolve-pathy pathy))
        ((stringp pathy)
         (list pathy))))

;; In Emacs < 24.4, there is a (known) bug with `run-at-time'. If the
;; callback takes longer than the REPEAT time, the timer could not be
;; cleared.
(defun prodigy-every (seconds callback)
  "Every SECONDS, run CALLBACK.

CALLBACK is called with a function that must be called in order
for this function to continue.  If that function is not called,
the timeouts stop."
  (declare (indent 2))
  (run-at-time
   seconds
   nil
   (lambda ()
     (funcall callback
              (lambda ()
                (prodigy-every seconds callback))))))

(defun prodigy-service-stopping-p (service)
  "Return true if SERVICE is currently stopping, false otherwise."
  (eq (plist-get service :status) 'stopping))

(defun prodigy-switch-to-process-buffer (service)
  "Switch to the process buffer for SERVICE."
  (-if-let (buffer (get-buffer (prodigy-buffer-name service)))
      (progn (pop-to-buffer buffer) (prodigy-view-mode))
    (message "Nothing to show for %s" (plist-get service :name))))

(defun prodigy-maybe-kill-process-buffer (service)
  "Kill SERVICE buffer if kill-process-buffer-on-stop is t."
  (let ((kill-process-buffer-on-stop (prodigy-service-kill-process-buffer-on-stop service)))
    (when (or kill-process-buffer-on-stop prodigy-kill-process-buffer-on-stop)
      (-when-let (buffer (get-buffer (prodigy-buffer-name service)))
        (kill-buffer buffer)))))

(defun prodigy-service-started-p (service)
  "Return true if SERVICE is started, false otherwise."
  (-when-let (process (plist-get service :process))
    (process-live-p process)))

(defun prodigy-service-or-first-tag-with (service property)
  "Return SERVICE PROPERTY or tag with PROPERTY.

If SERVICE has PROPERTY, return the value of that property.  Note
that '(:foo nil) means that the list has the property :foo.  If
SERVICE does not have property, find the first SERVICE tag that
has that property and return its value."
  (if (plist-member service property)
      (plist-get service property)
    (-when-let (tag (--first (plist-member it property) (prodigy-service-tags service)))
      (plist-get tag property))))

(defun prodigy-service-and-tags-with (service property)
  "Return a list of all values of SERVICE PROPERTY from SERVICE and its tags."
  (-reject 'null
           (cons (plist-get service property)
                 (--map (plist-get it property) (prodigy-service-tags service)))))

(defun prodigy-services ()
  "Return list of services, with applied filters."
  (let ((services (-clone prodigy-services)))
    (-each
        prodigy-filters
      (lambda (filter)
        (let ((type (-first-item filter))
              (value (-last-item filter)))
          (cond ((eq type :tag)
                 (setq services (-select
                                 (lambda (service)
                                   (prodigy-service-tagged-with? service value))
                                 services)))
                ((eq type :name)
                 (setq services (-select
                                 (lambda (service)
                                   (s-contains? value (plist-get service :name) 'ignore-case))
                                 services)))))))
    services))

(defun prodigy-find-status (id)
  "Find status by with ID.

If ID is nil, use id stopped, which is the default service
status."
  (unless prodigy-status-list
    (prodigy-define-default-status-list))
  (unless id (setq id 'stopped))
  (-first
   (lambda (status)
     (eq id (plist-get status :id)))
   prodigy-status-list))

(defun prodigy-start-status-check-timer ()
  "Start timer and call `prodigy-service-status-check' for each time.

The timer is not created if already exists."
  (or prodigy-timer
      (setq prodigy-timer
            (progn
              (prodigy-service-status-check)
              (prodigy-every prodigy-timer-interval 'prodigy-service-status-check)))))

(defun prodigy-buffer ()
  "Return prodigy buffer if it exists."
  (get-buffer prodigy-buffer-name))

(defun prodigy-buffer-visible-p ()
  "Retrun true if the prodigy buffer is visible in any window."
  (-any?
   (lambda (window)
     (equal (window-buffer window) (prodigy-buffer)))
   (window-list)))

(defun prodigy-service-status-check (&optional next)
  "Check for service process change and update service status.

If status has been changed since last time, update the service
status.

When NEXT is specifed, call that to start a new timer.  See
`prodigy-every'."
  (when (prodigy-buffer-visible-p)
    (-each prodigy-services
      (lambda (service)
        (-when-let (process (plist-get service :process))
          (let ((last-process-status (plist-get service :process-status))
                (this-process-status (process-status process)))
            (unless (eq last-process-status this-process-status)
              (plist-put service :process-status this-process-status)
              (let ((status
                     (if (eq this-process-status 'run)
                         'running
                       (if (= (process-exit-status process) 0)
                           'stopped
                         'failed))))
                (prodigy-set-status service status))))))))
  (when next (funcall next)))

(defun prodigy-tags ()
  "Return uniq list of tags."
  (-uniq (-flatten (--map (plist-get it :tags) prodigy-services))))

(defun prodigy-service-tagged-with? (service tag)
  "Return true if SERVICE is tagged with TAG."
  (-contains? (plist-get service :tags) tag))

(defun prodigy-services-tagged-with (tag)
  "Return list of services tagged with TAG."
  (--filter (prodigy-service-tagged-with? it tag) prodigy-services))

(defun prodigy-marked-services ()
  "Return list of services that are marked."
  (--filter (plist-get it :marked) prodigy-services))

(defun prodigy-completing-read (prompt collection)
  "Read a string in the minibuffer, with completion.

PROMPT is a string to prompt with.
COLLECTION is the list of strings that the user will be asked to
select between.

The completion system used is determined by
`prodigy-completion-system'."
  (let ((args `(,prompt ,collection nil 'require-match)))
    (cond ((eq prodigy-completion-system 'ido)
           (apply 'ido-completing-read args))
          ((eq prodigy-completion-system 'default)
           (apply 'completing-read args)))))

(defun prodigy-read-tag ()
  "Read tag from list of all possible tags."
  (let ((tag-names (-map 'symbol-name (prodigy-tags))))
    (intern (prodigy-completing-read "tag: " tag-names))))

(defun prodigy-buffer-name (service)
  "Return name of process buffer for SERVICE."
  (concat "*prodigy-" (s-dashed-words (s-downcase (plist-get service :name))) "*"))

(defun prodigy-find-service (name)
  "Find service with NAME."
  (-first
   (lambda (service)
     (equal (plist-get service :name) name))
   prodigy-services))

(defun prodigy-service-id (service)
  "Return SERVICE identifier."
  (let* ((name (plist-get service :name))
         (name (s-downcase name))
         (name (s-replace " " "-" name)))
    (intern name)))

(defun prodigy-find-by-id (id)
  "Find service by identifier ID."
  (--first (eq (prodigy-service-id it) id) prodigy-services))

(defun prodigy-url (service)
  "Return SERVICE url."
  (or
   (prodigy-service-url service)
   (-when-let (port (prodigy-service-port service))
     (format "http://localhost:%d" port))))

(defun prodigy-discover-initialize ()
  "Initialize discover by adding prodigy context menu."
  (discover-add-context-menu
   :context-menu prodigy-discover-context-menu
   :bind "?"
   :mode 'prodigy-mode
   :mode-hook 'prodigy-mode-hook))

(defun prodigy-define-default-status-list ()
  "Define the default status list."
  (prodigy-define-status :id 'stopped :name "")
  (prodigy-define-status :id 'running :face 'prodigy-green-face)
  (prodigy-define-status :id 'ready :face 'prodigy-green-face)
  (prodigy-define-status :id 'stopping :face 'prodigy-yellow-face)
  (prodigy-define-status :id 'failed :face 'prodigy-red-face))

(defun prodigy-service-has-status-p (service)
  "Return true if SERVICE has a status, except for stopped."
  (let ((status (plist-get service :status)))
    (and status (not (eq status 'stopped)))))

(defun prodigy-move-until (direction callback)
  "Move in DIRECTION until while CALLBACK return false.

DIRECTION is either 'up or 'down."
  (let ((pos (line-beginning-position))
        (found
         (catch 'break
           (while t
             (condition-case nil
                 (cond ((eq direction 'down)
                        (prodigy-goto-next-line))
                       ((eq direction 'up)
                        (prodigy-goto-prev-line)))
               (error (throw 'break nil)))
             (when (funcall callback (prodigy-service-at-pos))
               (throw 'break t))))))
    (unless found
      (prodigy-goto-pos pos))))

(defun prodigy-process-output (output)
  "Apply each of `prodigy-output-filters' to OUTPUT."
  (--each prodigy-output-filters
    (setq output (funcall it output)))
  output)

(defun prodigy-insert-output (service output)
  "Switch to SERVICE process view buffer and insert OUTPUT."
  (prodigy-with-service-process-buffer service
    (let ((current-position (point))
          (at-buffer-end (equal (point) (point-max))))
      (goto-char (point-max))
      (insert (prodigy-process-output output))
      (unless at-buffer-end
        (goto-char current-position)))))

(defun prodigy-truncate-buffer (service _)
  "Truncate SERVICE process view buffer to its maximum size."
  (prodigy-with-service-process-buffer service
    (-when-let (truncate-property
                (or (prodigy-service-truncate-output service)
                    prodigy-view-truncate-by-default))
      (let ((max-buffer-size (if (numberp truncate-property)
                                 truncate-property
                               prodigy-view-buffer-maximum-size)))
        (save-excursion
          (goto-char (point-max))
          (forward-line (- max-buffer-size))
          (beginning-of-line)
          (delete-region (point-min) (point)))))))

(defun prodigy-on-output (service output)
  "Call SERVICE on-output hooks with OUTPUT."
  (-when-let (on-output (prodigy-service-on-output service))
    (--each on-output (apply it (list :service service :output output)))))

(defun prodigy-check-for-ready-message (service output)
  "Check SERVICE's OUTPUT for a ready message.

If a ready message is found, update the service's status
accordingly."
  (-when-let (ready-messages (prodigy-service-ready-message service))
    (when (and (not (eq (plist-get service :status) 'ready))
               (--any? (s-matches? it output) ready-messages))
      (prodigy-set-status service 'ready))))


;;;; GUI

(defun prodigy-marked-col (service)
  "Return SERVICE marked column."
  (if (plist-get service :marked) "*" ""))

(defun prodigy-name-col (service)
  "Return SERVICE name column."
  (plist-get service :name))

(defun prodigy-status-col (service)
  "Return SERVICE status column."
  (-if-let (status-name (prodigy-status-name service))
      (propertize status-name 'face (prodigy-status-face service))
    ""))

(defun prodigy-tags-col (service)
  "Return SERVICE tags column."
  (s-join ", " (-map 'symbol-name
                     (--reject
                      (plist-get (prodigy-find-tag it) :hide)
                      (plist-get service :tags)))))

(defun prodigy-list-entries ()
  "Create the entries for the service list."
  (-map
   (lambda (service)
     (list
      (prodigy-service-id service)
      (apply 'vector
             (--map
              (funcall it service)
              '(prodigy-marked-col
                prodigy-name-col
                prodigy-status-col
                prodigy-tags-col)))))
   (prodigy-services)))

(defun prodigy-service-at-pos (&optional pos)
  "Return service at POS or current position."
  (prodigy-find-by-id (tabulated-list-get-id pos)))

(defun prodigy-service-at-pos-p (&optional pos)
  "Return true if there is a service at POS or current position."
  (not (null (prodigy-service-at-pos pos))))

(defun prodigy-goto-next-line ()
  "Go to next line."
  (if (= (line-beginning-position 1)
         (line-beginning-position 2))
      (error "No next line")
    (prodigy-goto-pos (line-beginning-position 2))))

(defun prodigy-goto-prev-line ()
  "Go to previous line."
  (if (= (line-beginning-position 0)
         (line-beginning-position 1))
      (error "No previous line")
    (prodigy-goto-pos (line-beginning-position 0))))

(defun prodigy-goto-first-line ()
  "Go to first line."
  (prodigy-goto-pos (point-min)))

(defun prodigy-goto-last-line ()
  "Go to first line."
  (prodigy-goto-pos
   (save-excursion
     (goto-char (point-max))
     (line-beginning-position 0))))

(defun prodigy-goto-pos (pos)
  "Go to POS."
  (if (prodigy-service-at-pos-p pos)
      (goto-char pos)
    (error "No service at point %s" pos)))

(defun prodigy-status-name (service)
  "Return string representation of SERVICE status."
  (let ((status-id (plist-get service :status)))
    (-when-let (status (prodigy-find-status status-id))
      (or (plist-get status :name) (s-capitalize (symbol-name status-id))))))

(defun prodigy-status-face (service)
  "Return SERVICE status face."
  (let ((status (prodigy-find-status (plist-get service :status))))
    (plist-get status :face)))

(defun prodigy-relevant-services ()
  "Return list of relevant services.

If there are any marked services, those are returned.  Otherwise,
the service at pos is returned.

Note that the return value is always a list."
  (or (prodigy-marked-services) (list (prodigy-service-at-pos))))

(defun prodigy-set-default-directory ()
  "Set default directory to :cwd for service at point."
  (when (eq major-mode 'prodigy-mode)
    (-when-let (service (prodigy-service-at-pos))
      (setq default-directory
            (-if-let (cwd (prodigy-service-cwd service))
                cwd
              (f-expand (getenv "HOME")))))))


;;;; Process handling

(defun prodigy-start-sudo-process (name buffer program &rest program-args)
  "Prompt the user for a password and start a process with sudo.
NAME, BUFFER, PROGRAM, and PROGRAM-ARGS are as in `start-process.'"
  (let* ((sudo-args (cons program program-args))
         (pwd (read-passwd (concat "Sudo password for `" (mapconcat #'identity sudo-args " ") "': ")))
         (process
         (start-process-shell-command
          name buffer (concat "sudo " (mapconcat #'shell-quote-argument sudo-args " ")))))
    (process-send-string process pwd)
    (clear-string pwd)
    (process-send-string process "\r")
    (process-send-eof process)
    process))

(defun prodigy-start-service (service &optional callback)
  "Start process associated with SERVICE unless already started.

When CALLBACK function is specified, that is called when the
process has been started.

When the process is started, a timer starts and checks every
second for `prodigy-start-tryouts' times if the process is live.
If the process is not live after `prodigy-start-tryouts' seconds,
the process is put in failed status."
  (declare (indent 1))
  (unless (prodigy-service-started-p service)
    (let* ((default-directory
             (-if-let (cwd (prodigy-service-cwd service))
                 (f-full cwd)
               default-directory))
           (name (plist-get service :name))
           (sudo (plist-get service :sudo))
           (command (prodigy-service-command service))
           (args (prodigy-service-args service))
           (exec-path (append (prodigy-service-path service) exec-path))
           (env (--map (s-join "=" it) (prodigy-service-env service)))
           (process-environment (append env process-environment))
           (process nil)
           (create-process
            (lambda ()
              (unless process
                (setq process (apply (if sudo 'prodigy-start-sudo-process 'start-process)
                                     (append (list name nil  command) args)))))))
      (-when-let (init (prodigy-service-init service))
        (funcall init))
      (-when-let (init-async (prodigy-service-init-async service))
        (let (callbacked)
          (funcall
           init-async
           (lambda ()
             (setq callbacked t)
             (funcall create-process)))
          (with-timeout
              (prodigy-init-async-timeout
               (error "Did not callback async callback within %s seconds"
                      prodigy-init-async-timeout))
            (while (not callbacked) (accept-process-output nil 0.005)))))
      (funcall create-process)
      (let ((tryout 0))
        (prodigy-every 1
            (lambda (next)
              (setq tryout (1+ tryout))
              (if (process-live-p process)
                  (when callback (funcall callback))
                (if (= tryout prodigy-start-tryouts)
                    (prodigy-set-status service 'failed)
                  (funcall next))))))
      (plist-put service :process process)
      (set-process-filter
       process
       (lambda (_ output)
         (run-hook-with-args 'prodigy-process-on-output-hook service output)))
      (set-process-query-on-exit-flag process nil))))

(defun prodigy-stop-service (service &optional force callback)
  "Stop process associated with SERVICE.

If FORCE is t, the process will be killed instead of signaled
with a SIGKILL signal.

When CALLBACK function is specified, that is called when the
process has been stopped or when it was not possible to stop the
process and the number of retries for the status check has
exceeded.

When the process has been signaled/killed, a timer starts and
checks every second for `prodigy-stop-tryouts' times if the
process is live.  If the process lives after
`prodigy-stop-tryouts' seconds, the process is put in failed
status.  If the process is successfully stopped, the process is
put in stopped status."
  (declare (indent 2))
  (unless (prodigy-service-stopping-p service)
    (-when-let (process (plist-get service :process))
      (when (process-live-p process)
        (prodigy-set-status service 'stopping)
        (let ((stop-signal (prodigy-service-stop-signal service)))
          (cond ((eq stop-signal 'int)
                 (interrupt-process process))
                ((or force (eq stop-signal 'kill))
                 (kill-process process))
                ((eq stop-signal 'quit)
                 (quit-process process))
                ((eq stop-signal 'stop)
                 (stop-process process))
                (t
                 (signal-process process (or stop-signal 'int)))))
        (let ((tryout 0))
          (prodigy-every 1
              (lambda (next)
                (setq tryout (1+ tryout))
                (unless (process-live-p process)
                  (plist-put service :process nil)
                  (plist-put service :process-status nil)
                  (prodigy-set-status service 'stopped))
                (when (= tryout prodigy-stop-tryouts)
                  (prodigy-set-status service 'failed))
                (if (or (= tryout prodigy-stop-tryouts) (not (process-live-p process)))
                    (progn
                      (unless (process-live-p process)
                        (prodigy-maybe-kill-process-buffer service))
                      (when (and callback (not (process-live-p process)))
                        (funcall callback)))
                  (funcall next)))))))))

(defun prodigy-restart-service (service &optional callback)
  "Restart SERVICE.

If SERVICE is not started, it will be started.

If CALLBACK is specified, it will be called when SERVICE is
started."
  (declare (indent 1))
  (if (prodigy-service-started-p service)
      (prodigy-stop-service service nil
        (lambda ()
          (prodigy-start-service service callback)))
    (prodigy-start-service service callback)))


;;;; User functions

(defun prodigy-next ()
  "Go to next service."
  (interactive)
  (condition-case nil
      (prodigy-goto-next-line)
    (error
     (message "Cannot move further down"))))

(defun prodigy-prev ()
  "Go to previous service."
  (interactive)
  (condition-case nil
      (prodigy-goto-prev-line)
    (error
     (message "Cannot move further up"))))

(defun prodigy-first ()
  "Go to first service."
  (interactive)
  (prodigy-goto-first-line))

(defun prodigy-last ()
  "Go to last service."
  (interactive)
  (prodigy-goto-last-line))

(defun prodigy-mark ()
  "Mark service at point."
  (interactive)
  (prodigy-with-refresh
   (-when-let (service (prodigy-service-at-pos))
     (plist-put service :marked t)
     (ignore-errors
       (prodigy-goto-next-line)))))

(defun prodigy-mark-tag ()
  "Mark all services with tag."
  (interactive)
  (prodigy-with-refresh
   (let ((tag (prodigy-read-tag)))
     (-each
         (prodigy-services-tagged-with tag)
       (lambda (service)
         (plist-put service :marked t))))))

(defun prodigy-mark-all ()
  "Mark all services."
  (interactive)
  (prodigy-with-refresh
   (-each
       prodigy-services
     (lambda (service)
       (plist-put service :marked t)))))

(defun prodigy-unmark ()
  "Unmark service at point."
  (interactive)
  (-when-let (service (prodigy-service-at-pos))
    (prodigy-with-refresh
     (plist-put service :marked nil)
     (ignore-errors
       (prodigy-goto-next-line)))))

(defun prodigy-unmark-tag ()
  "Unmark all services with tag."
  (interactive)
  (prodigy-with-refresh
   (let ((tag (prodigy-read-tag)))
     (-each
         (prodigy-services-tagged-with tag)
       (lambda (service)
         (plist-put service :marked nil))))))

(defun prodigy-unmark-all ()
  "Unmark all services."
  (interactive)
  (prodigy-with-refresh
   (-each
       prodigy-services
     (lambda (service)
       (plist-put service :marked nil)))))

(defun prodigy-copy-cmd ()
  "Copy cmd at line."
  (interactive)
  (let* ((service (prodigy-service-at-pos))
         (cmd (prodigy-service-command service))
         (args (prodigy-service-args service))
         (cmd-str (concat cmd " " (s-join " " args))))
    (kill-new cmd-str)
    (message "%s" cmd-str)))

(defun prodigy-start ()
  "Start service at line or marked services."
  (interactive)
  (prodigy-with-refresh
   (-each (prodigy-relevant-services) 'prodigy-start-service)))

(defun prodigy-stop (&optional force)
  "Stop service at line or marked services.

If prefix argument (or FORCE is t), force kill the process with a
SIGNINT signal."
  (interactive "P")
  (prodigy-with-refresh
   (-each (prodigy-relevant-services)
     (lambda (service)
       (prodigy-stop-service service force)))))

(defun prodigy-restart ()
  "Restart service at line or marked services."
  (interactive)
  (-each (prodigy-relevant-services)
    (lambda (service)
      (prodigy-with-refresh
       (prodigy-restart-service service)))))

(defun prodigy-display-process ()
  "Switch to process buffer for service at current line."
  (interactive)
  (-when-let (service (prodigy-service-at-pos))
    (prodigy-switch-to-process-buffer service)))

(defun prodigy-browse ()
  "Browse service url at point if possible to figure out."
  (interactive)
  (-when-let (service (prodigy-service-at-pos))
    (-if-let (url (prodigy-url service))
        (progn
          (when (listp url)
            (setq url (prodigy-completing-read "URL: " url)))
          (browse-url url))
      (message "Service does not specify url or port, cannot determine url"))))

(defun prodigy-refresh ()
  "Refresh list of services."
  (interactive)
  (-when-let (buffer (prodigy-buffer))
    (with-current-buffer buffer
      (tabulated-list-print :remember-pos)
      (hl-line-highlight))))

(defun prodigy-add-tag-filter ()
  "Read tag and add filter so that only services with that tag show."
  (interactive)
  (prodigy-with-refresh
   (let ((tag (prodigy-read-tag)))
     (prodigy-add-filter :tag tag)))
  (ignore-errors
    (prodigy-goto-first-line)))

(defun prodigy-add-name-filter ()
  "Read string and add filter for name."
  (interactive)
  (prodigy-with-refresh
   (let ((string (read-string "string: ")))
     (prodigy-add-filter :name string))
   (ignore-errors
     (prodigy-goto-first-line))))

(defun prodigy-clear-filters ()
  "Clear all filters."
  (interactive)
  (prodigy-with-refresh
   (setq prodigy-filters nil))
  (prodigy-goto-first-line))

(defun prodigy-jump-magit ()
  "Jump to magit status mode for service at point."
  (interactive)
  (-when-let (service (prodigy-service-at-pos))
    (magit-status (prodigy-service-cwd service))))

(defun prodigy-jump-dired ()
  "Jump to dired mode for service at point."
  (interactive)
  (-when-let (service (prodigy-service-at-pos))
    (dired (prodigy-service-cwd service))))

(defun prodigy-next-with-status ()
  "Move to next service with status."
  (interactive)
  (prodigy-move-until 'down 'prodigy-service-has-status-p))

(defun prodigy-prev-with-status ()
  "Move to prev service with status."
  (interactive)
  (prodigy-move-until 'up 'prodigy-service-has-status-p))


;;;; View mode functions

(defun prodigy-strip-ctrl-m (output)
  "Strip  line endings from OUTPUT."
  (s-replace "" "" output))

(defun prodigy-view-clear-buffer ()
  "Clear the current buffer.

If `prodigy-view-confirm-clear-buffer' is non-nil, will require
confirmation."
  (interactive)
  (when (or (not prodigy-view-confirm-clear-buffer)
            (y-or-n-p "Clear buffer? "))
    (let ((inhibit-read-only t))
      (erase-buffer))))


;;;; Public API functions

(defmacro prodigy-callback (properties &rest body)
  "Return function that make PROPERTIES available in BODY."
  (declare (indent 1))
  `(lambda (&rest args)
     (let ,(--map `(,it (plist-get args ,(intern (concat ":" (symbol-name it))))) properties)
       ,@body)))

(defun prodigy-set-status (service status)
  "Set SERVICE status to STATUS.

STATUS is the id of a status that has been defined (see
`prodigy-status-list' for a list of defined statuses).  If status
is not defined an error is raised.

This function will refresh the Prodigy buffer."
  (if (prodigy-find-status status)
      (prodigy-with-refresh
       (plist-put service :status status))
    (error "Status %s not defined" status)))

;;;###autoload
(defun prodigy-add-filter (type value)
  "Add filter TYPE, that filters for VALUE."
  (push (list type value) prodigy-filters))

;;;###autoload
(defun prodigy-define-service (&rest args)
  "Define a new service with ARGS.

If service with that name already exists, the service is updated.
The old service process is transfered to the new service."
  (declare (indent defun))
  (let* ((service-name (plist-get args :name))
         (fn
          (lambda (service)
            (string= (plist-get service :name) service-name)))
         (service (-first fn prodigy-services)))
    (when service
      (-when-let (process (plist-get service :process))
        (plist-put args :process process))
      (setq prodigy-services (-reject fn prodigy-services)))
    (push args prodigy-services)))

;;;###autoload
(defun prodigy-define-tag (&rest args)
  "Define a new tag with ARGS."
  (declare (indent defun))
  (-when-let (tag-name (plist-get args :name))
    (setq
     prodigy-tags
     (-reject
      (lambda (tag)
        (string= (plist-get tag :name) tag-name))
      prodigy-tags)))
  (push args prodigy-tags))

;;;###autoload
(defun prodigy-define-status (&rest args)
  "Define a new status with ARGS."
  (declare (indent defun))
  (-when-let (id (plist-get args :id))
    (setq
     prodigy-status-list
     (-reject
      (lambda (status)
        (string= (plist-get status :id) id))
      prodigy-status-list)))
  (push args prodigy-status-list))

;;;###autoload
(define-derived-mode prodigy-mode tabulated-list-mode "Prodigy"
  "Special mode for prodigy buffers."
  (buffer-disable-undo)
  (kill-all-local-variables)
  (setq truncate-lines t)
  (setq mode-name "Prodigy")
  (setq major-mode 'prodigy-mode)
  (use-local-map prodigy-mode-map)
  (add-hook 'post-command-hook 'prodigy-set-default-directory)
  (setq tabulated-list-format prodigy-list-format)
  (setq tabulated-list-entries 'prodigy-list-entries)
  (setq tabulated-list-sort-key prodigy-list-sort-key)
  (tabulated-list-init-header)
  (tabulated-list-print)
  (prodigy-set-default-directory)
  (prodigy-define-default-status-list)
  (hl-line-mode 1)
  (when (featurep 'discover)
    (prodigy-discover-initialize))
  (setq imenu-prev-index-position-function
        #'prodigy--imenu-prev-index-position-function)
  (setq imenu-extract-index-name-function
        #'prodigy--imenu-extract-index-name-function)
  (run-mode-hooks 'prodigy-mode-hook))

(defun prodigy--imenu-prev-index-position-function ()
  "Move point to previous line in prodigy buffer.
This function is used as a value for
`imenu-prev-index-position-function'."
  (unless (bobp)
    (forward-line -1)))

(defun prodigy--imenu-extract-index-name-function ()
  "Return imenu name for line at point.
This function is used as a value for
`imenu-extract-index-name-function'.  Point should be at the
beginning of the line."
  (elt (tabulated-list-get-entry) 1))

;;;###autoload
(define-derived-mode prodigy-view-mode special-mode "Prodigy-view"
  "Mode for viewing prodigy process output."
  (view-mode 1)
  (font-lock-mode 1)
  (use-local-map prodigy-view-mode-map))

;;;###autoload
(defun prodigy ()
  "Manage external services from within Emacs."
  (interactive)
  (let ((buffer-p (prodigy-buffer))
        (buffer (get-buffer-create prodigy-buffer-name)))
    (pop-to-buffer buffer)
    (unless buffer-p
      (prodigy-mode))
    (prodigy-start-status-check-timer)))

(provide 'prodigy)

;;; prodigy.el ends here
