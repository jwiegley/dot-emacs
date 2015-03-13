# github-issues.el

An [Emacs](http://www.gnu.org/software/emacs/) mode for managing project's issues on [GitHub](https://github.com/).

The final goal for using `github-issues.el` is to list, show, add, edit, remove, comment and assign issues on GitHub hosted projects without leaving Emacs.

## Dependencies

I've tried to keep the dependencies to a minimum. Current dependencies are:

* `tabulated-list`
* `url`
* `font-lock`

## Functions

### `github-issues (user repo)`

Opens a `github-issues-mode` buffer listing the issues for the given user and repository.

### `github-issue (user repo number)` **NOT IMPLEMENTED**

Interactive function that opens a new `github-issue-mode` buffer with the given issue description.

## Non-interactive functions

### `github-issues-buffer (user repo)`

Creates or return the buffer for the given user and repository.

### `github-issue-buffer (user repo number)`

Creates or return the buffer for the given issue.

### `github-parse-response`

Parses the JSON response from a GitHub API call.

### `github-api-repository-issues (user repo)`

Returns a list of issues in `plist` format.

### `github-api-repository-issue (user repo number)`

Return an issue data in `plist` format.

### `github-issues-populate (buffer issues)`

Populates the given buffer with a list of issues. See `github-api-repository-issues`.

### `github-issue-populate (buffer issue)`

Populates the given buffer with an issue description. See `github-api-repository-issue`.

## Modes

### `github-issues-mode`

Major mode derived from `tabulated-list-mode`, to display a list of issues.

In this mode the following keymap is active:

* `C-c r`: refresh the list of issues.

### `github-issue-mode`

Major mode derived from `font-lock-mode` to display a given issue data.

In this mode the following keymap is active:

* `C-c r`: refresh the issue data.
* `C-c o`: open the issue in a browser.
* `C-c a`: open the issue author page in a browser.

## TODO

* Cache results and add refresh functions.
* Improve descriptions.
* Add keymaps.
* Improve issue information.
* Add GitHub's authentication for issue management.
* Add issues pagination.
* Add customization options.
* Add comments on issues buffers.
* Allow comments on issues.