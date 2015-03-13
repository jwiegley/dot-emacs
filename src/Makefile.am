bin_PROGRAMS = org-merge-driver

# Bison and Flex
BUILT_SOURCES = org_lexer.h
AM_LFLAGS = 

org_merge_driver_SOURCES = \
	main.c         \
	org_lexer.l    \
	org_parser.c   \
	doc_ref.c      \
	print.c        \
	org_document.c \
	org_heading.c  \
	org_text.c     \
	org_property.c \
	smerger.c      \
	string_merge.c \
	print_ctxt.c   \
	merge_ctxt.c   \
	parse_ctxt.c

org_merge_driver_CFLAGS = -O0 -I$(top_srcdir)/gnulib/lib
org_merge_driver_LDADD = $(top_srcdir)/gnulib/lib/libgnu.a

org_lexer.h: org_lexer.l
	flex $^
