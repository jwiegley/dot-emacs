/**
 * @file check_merge_print.c
 */
#include "config.h"
#include <check.h>
#include "gl_list.h"
#include "merge_print.c"
#include "test_elt.h"

int next_val = 0;

merge_node *
make_merge_node ()
{
  merge_node *node = ltree_node_create_empty ();
  merge_delta *delta = merge_delta_create_empty ();
  test_elt *elt = test_elt_create (next_val++);
  
  merge_delta_set_elt (delta, (doc_elt *)elt);
  merge_node_set_delta (node, delta);
  return node;
}

merge_node *
make_merge_node_with_children (size_t num)
{
  merge_node *node = make_merge_node ();
  merge_list list = merge_node_get_children (node);
  size_t i;
  for (i = 0; i < num; i++)
    {
      gl_list_nx_add_last (list, make_merge_node ());
    }
}

START_TEST (check_merge_print)
{

  merge_node *root = make_merge_node_with_children (2);

  merge_print_ctxt ctxt;
  ctxt.depth = 0;
  doc_stream *out = stdout;
  merge_print (root, &ctxt, out);

  merge_node *child     = (merge_node *)gl_list_get_at (merge_node_get_children (root), 1);
  test_elt   *child_elt = (test_elt *)merge_delta_get_elt(merge_node_get_delta (child));

  fail_if (  child_elt->merge_print_depth != 1
	   && test_elt_get_value(child_elt) != 2);
} END_TEST


Suite *
make_merge_print_suite (void)
{
  Suite *s = suite_create ("Merge Print");

  /* Core test case */
  TCase *tc_core = tcase_create ("Core");
  tcase_add_test (tc_core, check_merge_print);

  suite_add_tcase (s, tc_core);
  return s;
}
