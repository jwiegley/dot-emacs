#include <stdlib.h>
#include <check.h>

START_TEST (parser_check)
{
  fail_if (1 > 2);
}
END_TEST

Suite *
make_parser_suite (void)
{
  Suite *s = suite_create ("Parsing");
  /* Core test case */
  TCase *tc_core = tcase_create ("Core");
  tcase_add_test (tc_core, parser_check);
  suite_add_tcase (s, tc_core);
  return s;
}
