# copy-as-format

[![MELPA](https://melpa.org/packages/copy-as-format-badge.svg)](https://melpa.org/#/copy-as-format)

Emacs function to copy buffer locations as GitHub/Slack/JIRA/HipChat/...
formatted code

![copy-as-format demo](demo.gif)

## Supported Formats/Services

* Bitbucket
* Disqus
* GitHub
* GitLab
* HipChat
* HTML
* JIRA
* Markdown
* MediaWiki
* Org-mode
* POD
* reStructuredText
* Slack

## Usage

`M-x copy-as-format` or `C-u M-x copy-as-format`

Copy the current line or active region and add it to the kill ring as
GitHub/Slack/JIRA/HipChat/... formatted code. Format defaults to `copy-as-format-default`.
The buffer will not be modified.

With a prefix argument prompt for the format.

`M-x copy-as-format-SERVICE`

Where `SERVICE` is one of the supported services.

It's a good idea to bind these functions to a key sequence:

```el
(global-set-key (kbd "C-c w s") 'copy-as-format-slack)
(global-set-key (kbd "C-c w g") 'copy-as-format-github)
```

## Adding Formats

Create a format function with a signature of `TEXT MULTILINE`:

* `TEXT` - the text to be formatted
* `MULTILINE` - `t` if `TEXT` spans multiple lines, otherwise `nil`

For example:

```el
(defun some-great-format (text multiline)
  (if multiline
      (multiline-format text)
    (single-line-format text)))
```

Then, add an entry to `copy-as-format-format-alist`. The key is the format's name
and the value is the format function:

```el
(add-to-list 'copy-as-format-format-alist '("great-format" some-great-format))
```

## See Also

* [git-link](https://github.com/sshaw/git-link)
* [output-as-format](https://github.com/sshaw/output-as-format) - A command line version of copy-as-format
