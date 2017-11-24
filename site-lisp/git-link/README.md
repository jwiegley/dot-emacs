# git-link

[![MELPA](http://melpa.org/packages/git-link-badge.svg)](http://melpa.org/#/git-link)

Interactive Emacs functions that create URLs for files and commits in GitHub/Bitbucket/GitLab/... repositories.

`git-link` returns the URL for the current buffer's file location at the current line number or active region.

`git-link-commit` returns the URL for the commit at point.

`git-link-homepage` returns the URL for the repository's homepage.

URLs are added to the kill ring.

## Usage

Functions can be called interactively (`M-x git-link`) or via the key binding
of your choice e.g., `(global-set-key (kbd "C-c g l") 'git-link)`

With a prefix argument prompt for the remote's name. Defaults to `"origin"`.

Works with dired and magit too.

### Settings

Global setting are elisp variables. They can be set directly or via `M-x customize`.

Local settings are managed via the repository's git configuration. They can be set via:

```
git config --local --add setting value
```

Local settings have precedence over global settings.

#### Global

##### `git-link-default-remote`

Name of the remote to link to, defaults to `nil`.

##### `git-link-default-branch`

Name of the remote branch to link to, defaults to the current branch.

##### `git-link-open-in-browser`

If non-`nil` also open link in browser via `browse-url`, defaults to `nil`.

##### `git-link-use-commit`

If non-`nil` use the latest commit's hash in the link instead of the branch name, defaults to `nil`.

#### Local

##### `git-link.remote`

Name of the remote to link to.

##### `git-link.branch`

Name of the remote branch to link to.

### Supported Services

* [Bitbucket](http://bitbucket.com)
* [GitHub](http://github.com)
* [GitLab](https://gitlab.com)
* [Gitorious](http://gitorious.org)

### Git Timemachine

If [`git-timemachine-mode`](https://github.com/pidu/git-timemachine)
is active `git-link` generates a URL for the version of the file being
visited.

### Building Links and Adding Services

`git-link-remote-alist` is an alist containing `(REGEXP FUNCTION)`
elements. The FUNCTION creates URLs for file on remote host names that
match the REGEXP. To add (or modify) how URLs are created for a given
host, add appropriate elements to this list.

As an example, one of the default elements in this alist is
`("gitlab" git-link-gitlab)`. So the `git-link-gitlab` function
will be used to create URLs to files in remotes that match the
*regexp* `"gitlab"`.  That would cover common Gitlab host URLs like
*"gitlab.com"*, *"gitlab.example.com"* and *"gitlab.example.org"*.

`git-link-commit-remote-alist` is also an alist containing `(REGEXP
FUNCTION)` elements. Here, the FUNCTION creates URLs to the commit
pages, for remote hosts matching REGEXP.

If you use a self-hosted version of one of the supported services, but
your remote URL does match with the defaults, you can configure these
link function alists.  For example, for a GitHub Enterprise instance
at `gh.example.com`, you could add the following to your `.emacs`
file:

    (eval-after-load 'git-link
      '(progn
        (add-to-list 'git-link-remote-alist
          '("gh\\.example\\.com" git-link-github))
        (add-to-list 'git-link-commit-remote-alist
          '("gh\\.example\\.com" git-link-commit-github))))

The `git-link` signature is:

`HOSTNAME DIRNAME FILENAME BRANCH COMMIT START END`

* `HOSTNAME` hostname of the remote
* `DIRNAME` directory portion of the remote
* `FILENAME` source file, relative to `DIRNAME`
* `BRANCH` active branch, may be `nil` if the repo's in "detached HEAD" state
* `COMMIT` SHA of the latest commit
* `START` starting line number
* `END`  ending line number, `nil` unless region is active

The `git-link-commit` signature is:

`HOSTNAME DIRNAME COMMIT`

* `HOSTNAME` hostname of the remote
* `DIRNAME` directory portion of the remote
* `COMMIT` SHA of the commit

### See Also

* [copy-as-format](https://github.com/sshaw/copy-as-format)
* [output-as-format](https://github.com/sshaw/output-as-format)

### TODO

* Tests!
* Consolidate `git-link-*-alist`s
* `git-link-grep`
