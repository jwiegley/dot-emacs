## Process this file with automake to produce Makefile.in
ACLOCAL_AMFLAGS = -I m4
SUBDIRS =  gnulib/lib src doc . tests
dist_doc_DATA = README
EXTRA_DIST = autogen.sh m4/gnulib-cache.m4

splint :
	splint -I./gnulib/lib -I. -I./src src/*.c
