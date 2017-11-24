## Process this file with automake to produce Makefile.in
# $Id: Makefile.am,v 1.2 2005/04/01 06:20:06 ryants Exp $

bin_PROGRAMS = doxymacs_parser

doxymacs_parser_SOURCES = doxymacs_parser.c

INCLUDES = $(XML_CPPFLAGS)

AM_CFLAGS = -Wall -Werror -fexpensive-optimizations -fomit-frame-pointer

doxymacs_parser_LDADD = $(XML_LIBS)
