# Contributing

First off, thanks for contributing to this project.  It's people like
you -- your time and effort in reporting bugs, suggesting features, or
submitting pull requests -- that make this project and so many others
like it in the Emacs world a joy to work with.  Stay awesome!

## Roadmap

Magithub's vision is to become the bridge between the `git` VCS and
GitHub social network.  Not only do I want to replicate the standard
functionality you would expect from a GitHub client, but I want to
closely *integrate* Magit's workflows with GitHub's featureset to
develop and optimize the broader experience of using `git` with other
people.

Magit itself may include such support in the future, though probably
to a less-specialized extent.  At present, Magithub is focusing on
GitHub (although the lessons learned here could be applied to a
Magitlab, for instance).

## Reporting Bugs

Ugh, nasty bugs!  Every software project has them (except
[TeX, vπ][tex-bug]), and many of them are found only by users like
you.  As you write your issue, please follow the instructions the
issue template provides.  A stack trace helps tremendously!

## Suggesting Features

Feature requests are always welcome!  Pull requests even more so.
:wink: Know however that this is a project I do in my free time;
sometimes life gets in the way of doing this development -- or even
reviewing development from a pull request.  Don't let that deter you
:smile: It *will* be reviewed.

## Unit Tests

Additions of more unit tests are always appreciated -- as well as
improvements to the overall unit test approach.  The *only* thing I
would like to continue to avoid is making real API requests (since
this makes pull requests difficult), so please mock the response for
any such test you write.  Reach out on Gitter if you need a hand.

[tex-bug]: http://www.ntg.nl/maps/05/34.pdf
