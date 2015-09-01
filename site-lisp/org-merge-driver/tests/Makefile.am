## Process this file with automake to produce Makefile.in
test_org_tests = heading_tests.sh heading_movement_tests.sh \
	text_tests.sh property_tests.sh

TESTS = check_org-merge-driver $(test_org_tests)

#test_suite_runner.sh 
#test_org_tests =  

## Check Unit Tests
check_PROGRAMS = check_org-merge-driver

check_org_merge_driver_SOURCES = \
	check_org-merge-driver.c

check_org_merge_driver_CFLAGS = @CHECK_CFLAGS@ -I$(top_srcdir)/src \
	-I$(top_srcdir)/gnulib/lib
check_org_merge_driver_LDADD = @CHECK_LIBS@ $(top_srcdir)/gnulib/lib/libgnu.a

## Merge Rule Tests
#check_org-merge-driver
TEST_EXTENSIONS = .sh
SH_LOG_DRIVER = env AM_TAP_AWK='$(AWK)' bash \
                      $(top_srcdir)/config/tap-driver.sh

# retangle the test files if the tests are updated
retangle : test.org
	echo "Must re-tangle files"
	emacs --batch --file test.org --eval "(org-babel-tangle)"
	chmod 700 test_suite_runner.sh # make the generated test script executable
