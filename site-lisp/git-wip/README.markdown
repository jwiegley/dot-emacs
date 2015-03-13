# About

git-wip is a script that will manage Work In Progress (or WIP) branches.
WIP branches are mostly throw away but identify points of development
between commits.  The intent is to tie this script into your editor so
that each time you save your file, the git-wip script captures that
state in git.  git-wip also helps you return back to a previous state of
development.

Latest git-wip can be obtained from [github.com](http://github.com/bartman/git-wip)
git-wip was written by [Bart Trojanowski](mailto:bart@jukie.net)

# WIP branches

Wip branches are named after the branch that is being worked on, but are
prefixed with 'wip/'.  For example if you are working on a branch named
'feature' then the git-wip script will only manipulate the 'wip/feature'
branch.

When you run git-wip for the first time, it will capture all changes to
tracked files and all untracked (but not ignored) files, create a
commit, and make a new wip/*topic* branch point to it.

    --- * --- * --- *          <-- topic
                     \
                      *        <-- wip/topic

The next invocation of git-wip after a commit is made will continue to
evolve the work from the last wip/*topic* point.

    --- * --- * --- *          <-- topic
                     \
                      *
                       \
                        *      <-- wip/topic

When git-wip is invoked after a commit is made, the state of the
wip/*topic* branch will be reset back to your *topic* branch and the new
changes to the working tree will be caputred on a new commit.

    --- * --- * --- * --- *    <-- topic
                     \     \
                      *     *  <-- wip/topic
                       \
                        *

While the old wip/*topic* work is no longer accessible directly, it can
always be recovered from git-reflog.  In the above example you could use
`wip/topic@{1}` to access the dangling references.

# git-wip command

The git-wip command can be invoked in several differnet ways.

* `git wip`
  
  In this mode, git-wip will create a new commit on the wip/*topic*
  branch (creating it if needed) as described above.

* `git wip save "description"`
  
  Similar to `git wip`, but allows for a custom commit message.

* `git wip log`
  
  Show the list of the work that leads upto the last WIP commit.  This
  is similar to invoking:
  
  `git log --stat wip/$branch...$(git merge-base wip/$branch $branch)`

# editor hooking

To use git-wip effectively, you should tie it into your editor so you
don't have to remember to run git-wip manually.

## vim

To add git-wip support to vim you can install the provided vim plugin.  There
are a few ways to do this.

**(1)** If you're using [Vundle](https://github.com/gmarik/Vundle.vim), you
just need to include the following line in your `.vimrc`.

    Bundle 'bartman/git-wip', {'rtp': 'vim/'}

**(2)** You can slo copy the `git-wip.vim` into your vim runtime:

    cp vim/plugin/git-wip ~/.vim/plugin/git-wip

**(3)** Alternatively, you can add the following to your `.vimrc`.  Doing so
will make it be invoked after every `:w` operation.

    augroup git-wip
      autocmd!
      autocmd BufWritePost * :silent !cd "`dirname "%"`" && git wip save "WIP from vim" --editor -- "`basename "%"`"
    augroup END

The `--editor` option puts git-wip into a special mode that will make it
more quiet and not report errors if there were no changes made to the
file.

## emacs

To add git-wip support to emacs add the following to your `.emacs`. Doing
so will make it be invoked after every `save-buffer` operation.

    (load "/{path_to_git-wip}/emacs/git-wip.el")

Or you may also copy the content of git-wip.el in your `.emacs`.

## sublime

A sublime plugin was contributed as well.  You will find it in the `sublime`
directory.

# recovery

Should you discover that you made some really bad changes in your code,
from which you want to recover, here is what to do.

First we need to find the commit we are interested in.  If it's the most recent
then it can be referenced with `wip/master` (assuming your branch is `master`),
otherwise you may need to find the one you want using:

    git reflog show wip/master

I personally prefer to inspect the reflog with `git log -g`, and sometimes 
with `-p` also:

    git log -g -p wip/master

Once you've picked a commit, you need to checkout the files, note that we are not
switching the commit that your branch points to (HEAD will continue to reference
the last real commit on the branch).  We are just checking out the files:

    git checkout ref -- .

Here `ref` could be a SHA1 or `wip/master`.  If you only want to recover one file,
then use it's path instead of the *dot*.

The changes will be staged in the index and checked out into the working tree, to
review what the differences are between the last commit, use:

    git diff --cached

If you want, you can unstage all or some with `git reset`, optionally specifying a
filename to unstage.  You can then stage them again using `git add` or `git add -p`.
Finally, when you're happy with the changes, commit them.


<!-- vim: set ft=markdown -->
