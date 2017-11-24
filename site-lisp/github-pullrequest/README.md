# github-pullrequest
Emacs package to smoothly create and checkout Github pull requests. Uses the [Github access token](https://github.com/settings/tokens) for authorization to Github. This means you can use this package even if your Github account uses [Two-Factor Authentication](https://help.github.com/articles/about-two-factor-authentication/). 

![Emacs github-pullrequest](https://jakoblind.github.io/img/githubcheckout.gif)

## Installation
It's available on [MELPA](https://melpa.org/)

```
M-x package-install github-pullrequest
```

And then add to your Emacs settings
```lisp
(require 'github-pullrequest)
```

Use [ido-ubiquitous](https://github.com/DarwinAwardWinner/ido-ubiquitous) to enable IDO

## Usage

First time you run any command, it will ask for your Github access token. You can create a new access token under [github settings](https://github.com/settings/tokens). It is then saved in your git setting for the current repository under the key `github.token`, so you don't have to enter it next time.

### Prerequisite

The git repository you want to work with must have a remote called `origin` which is a github remote.

### New pull request

```lisp
M-x github-pullrequest-new
```

![Emacs github-pullrequest](https://jakoblind.github.io/img/githubnewpr.gif)

Creates a pull request with `current branch` as `head` and `master` as `base`. The title of the pull request is the branch name and there is no describing text.

### Checkout pull request

```lisp
M-x github-pullrequest-checkout
```

![Emacs github-pullrequest](https://jakoblind.github.io/img/githubcheckout.gif)

Lists all open pull requests in current repository. When selecting one of them, the branch for the pull request is checked out, and created if it doesn't exist.
