#!/bin/sh

notfound=
if ! type aclocal >/dev/null 2>/dev/null; then
    notfound=aclocal
elif ! type automake >/dev/null 2>/dev/null; then
    notfound=automake
elif ! type autoconf >/dev/null 2>/dev/null; then
    notfound=autoconf
fi
if test -n "$notfound"; then
    echo OOPS: I can\'t find $notfound in your path!
    echo You need aclocal, automake, and autoconf to generate configure.
    echo Otherwise, you can install manually, see the README file.
    exit;
fi

echo -n Running aclocal to generate aclocal.m4...
aclocal
echo done.

echo -n Running automake to generate Makefile.in...
automake
echo done.

echo -n Running autoconf to generate configure...
autoconf
echo done
