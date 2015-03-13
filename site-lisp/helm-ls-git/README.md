# helm-ls-git

Yet another helm for listing the files in a git repo.

## Features:

* Similar in scope to `helm-git.el` but has no dependency on magit.

* Allows you to toggle the full path of files with `C-]`

* Inherits actions from helm-locate.

* Signals an error in helm-buffer when trying to use it in a non git
  based repo.

* Action pop-up in action buffer of helm-find-files only when current
  directory is git based.

## Installation

* We assume that you have `git` installed and that OSX users have
  solved [any `$PATH` issues](https://gist.github.com/jhrr/8852178)
  that prevent them being able to call `git` from emacs.

* Ensure you are running at least >= Emacs-24.3.

* Install `helm` according to the [instructions on its repo
  page](https://github.com/emacs-helm/helm#getting-started)

* If you are using the MELPA package manager then `M-x list-packages`
  and install `helm-ls-git`.

* Or, if you are using `el-get` then invoke `M-x el-get-install` and at
  the `Install package:` prompt type `helm-ls-git` and hit enter.

* Otherwise, clone this repo and put `helm-ls-git.el` somewhere on the
  emacs `load-path`.

* Finally, add to your `.emacs.el`:

Assuming you are already using helm and it is installed properly (See [Install helm](http://emacs-helm.github.io/helm/))

```elisp
(require 'helm-ls-git)
```

And then bind the command `helm-ls-git-ls` to a keybinding of your
choice; for example:

```elisp
(global-set-key (kbd "C-<f6>") 'helm-ls-git-ls)
```

Or even better use M-x `helm-browse-project` or bind it to a key, for example:

```elisp
(global-set-key (kbd "C-x C-d") 'helm-browse-project)
```

If you are using `helm-find-files` you will be able to browse any git repo unrelated
to the `current-buffer`:
M-x `helm-find-files`
navigate to some git repo and hit `C-x C-d`

## Usage

* By calling `helm-ls-git-ls` or `helm-browse-project` in any buffer that is a part of a git
  repo (or if you have navigated to a git repo from `helm-find-files`),
  you will be presented with a corresponding helm buffer
  containing a list of all the files currently in that same
  repository. In the usual `helm` style you can just type at the
  prompt in the minibuffer and see the results narrow according to the
  input of your search pattern.

* When the helm-buffer is active and displaying results, the user can
  invoke `C-]` to toggle between showing filenames or full pathnames
  for the data that helm is listing.
