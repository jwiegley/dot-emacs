Minuscule client library for the Github API
===========================================

Ghub is a library that provides basic support for using the Github API
from Emacs packages.  It abstracts access to API resources using only
a handful of functions that are not resource-specific.

It also handles the creation, storage and use of access tokens using a
setup wizard, to make it easier for users to get started and to reduce
the support burden imposed on package maintainers.  It also comes with
a comprehensive manual to address the cases when things don't just
work as expected.

Ghub is intentionally limited to only provide these two essential
features — basic request functions and guided setup — to avoid being
too opinionated, which would hinder wide adaption.  It is assumed that
wide adoption would make life easier for users and maintainers alike,
because then all packages that talk to the Github API could be
configured the same way.

Consulting the [manual](https://magit.vc/manual/ghub) can be benefitial.
