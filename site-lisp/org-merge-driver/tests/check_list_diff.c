#include "list_diff.c"
#include <stdlib.h>
#include <check.h>
#include "gl_array_list.h"

static gl_list_t list;
static size_t pos;
static int one = 1;
static int two = 2;
static int three = 3;

static void test_insert (gl_list_t l, size_t p)
{
  pos -= p;
  list = l;
  return;
}

static void
test_delete (gl_list_t l, size_t p)
{
  list = l;
  pos += p;
}

static int 
test_compare (void* elt1, void *elt2)
{
  return *(int *)elt1 + *(int *)elt2;
}

static int 
int_compare (void* elt1, void *elt2)
{
  return (*(int *)elt1) == (*(int *)elt2);
}

START_TEST (wrap_delete_calls_delete_with_listx)
{
  struct context ct;
  ct.note_delete = test_delete;
  ct.listx = (void*) 1;
  list = 0;
  pos = 0;
  wrap_delete (&ct, 8);
  fail_unless(list == (void*) 1);
}
END_TEST

START_TEST (wrap_delete_calls_delete_with_pos)
{
  struct context ct;
  ct.note_delete = test_delete;
  ct.listx = (void*) 1;
  list = 0;
  pos = 0;
  wrap_delete (&ct, 8);
  fail_unless(pos == 8);
}
END_TEST

START_TEST (wrap_insert_calls_delete_with_listy)
{
  struct context ct;
  ct.note_insert = test_delete;
  ct.listy = (void*) 1;
  list = 0;
  pos = 0;
  wrap_insert (&ct, 8);
  fail_unless(list == (void*) 1);
}
END_TEST

START_TEST (wrap_insert_calls_delete_with_pos)
{
  struct context ct;
  ct.note_insert = test_delete;
  ct.listx = (void*) 1;
  list = 0;
  pos = 0;
  wrap_insert (&ct, 8);
  fail_unless(pos == 8);
}
END_TEST

START_TEST (compare_calls_given_elements)
{  
  struct context ct;
  gl_list_t gl = gl_list_nx_create_empty (GL_ARRAY_LIST, NULL, 
					  NULL, NULL, true);
  
  gl_list_nx_add_last (gl, &one);
  gl_list_nx_add_last (gl, &two);
  
  ct.compare = test_compare;
  ct.listx = gl;
  ct.listy = gl;

  fail_unless(wrap_compare (&ct, 0, 1) == 3);
}
END_TEST


START_TEST (list_diff_remove_check)
{
  pos = 0;
  gl_list_t gl = gl_list_nx_create_empty (GL_ARRAY_LIST, NULL, 
					  NULL, NULL, true);
  gl_list_nx_add_last (gl, &one);
  gl_list_nx_add_last (gl, &two);

  gl_list_t gl2 = gl_list_nx_create_empty (GL_ARRAY_LIST, NULL, 
					  NULL, NULL, true);
  gl_list_nx_add_last (gl2, &one);
  gl_list_nx_add_last (gl2, &two);
  gl_list_nx_add_last (gl2, &three);

  list_diff (gl2, gl,
	     test_compare,
	     test_delete,
	     test_delete);
  fail_if (pos != 2);
}
END_TEST

START_TEST (list_diff_insert_check)
{
  pos = 0;
  gl_list_t gl = gl_list_nx_create_empty (GL_ARRAY_LIST, NULL, 
					  NULL, NULL, true);
  gl_list_nx_add_last (gl, &one);
  gl_list_nx_add_last (gl, &two);

  gl_list_t gl2 = gl_list_nx_create_empty (GL_ARRAY_LIST, NULL, 
					  NULL, NULL, true);
  gl_list_nx_add_last (gl2, &one);
  gl_list_nx_add_last (gl2, &two);
  gl_list_nx_add_last (gl2, &three);

  list_diff (gl, gl2,
	     int_compare,
	     test_delete,
	     test_delete);
  fail_if (pos != 2);
}
END_TEST

START_TEST (list_diff_insert_and_remove_check)
{
  pos = 0;
  gl_list_t gl = gl_list_nx_create_empty (GL_ARRAY_LIST, NULL, 
					  NULL, NULL, true);
  gl_list_nx_add_last (gl, &one);
  gl_list_nx_add_last (gl, &two);
  gl_list_nx_add_last (gl, &three);
  gl_list_nx_add_last (gl, &three);

  gl_list_t gl2 = gl_list_nx_create_empty (GL_ARRAY_LIST, NULL, 
					   NULL, NULL, true);
  gl_list_nx_add_last (gl2, &one);
  gl_list_nx_add_last (gl2, &two);

  list_diff (gl, gl2,
	     int_compare,
	     test_insert,
	     test_delete);

  fail_if (pos != 5);
}
END_TEST

START_TEST (list_diff_insert_and_remove_check2)
{
  pos = 0;
  gl_list_t gl = gl_list_nx_create_empty (GL_ARRAY_LIST, NULL, 
					  NULL, NULL, true);
  gl_list_nx_add_last (gl, &one);
  gl_list_nx_add_last (gl, &one);
  gl_list_nx_add_last (gl, &two);
  gl_list_nx_add_last (gl, &three);


  gl_list_t gl2 = gl_list_nx_create_empty (GL_ARRAY_LIST, NULL, 
					   NULL, NULL, true);
  gl_list_nx_add_last (gl2, &one);
  gl_list_nx_add_last (gl2, &two);
  gl_list_nx_add_last (gl2, &one);
  gl_list_nx_add_last (gl2, &three);

  list_diff (gl, gl2,
	     int_compare,
	     test_insert,
	     test_delete);

  fail_unless(pos == 0 || pos == -1);
}
END_TEST

START_TEST (list_diff_insert_and_remove_small_list_check)
{
  pos = 0;
  gl_list_t gl = gl_list_nx_create_empty (GL_ARRAY_LIST, NULL, 
					  NULL, NULL, true);
  gl_list_nx_add_last (gl, &one);
  gl_list_nx_add_last (gl, &two);

  gl_list_t gl2 = gl_list_nx_create_empty (GL_ARRAY_LIST, NULL, 
					   NULL, NULL, true);
  gl_list_nx_add_last (gl2, &two);
  gl_list_nx_add_last (gl2, &one);

  list_diff (gl, gl2,
	     int_compare,
	     test_insert,
	     test_delete);

  fail_unless (pos == 1 || pos == -1);
}
END_TEST

Suite *
make_list_diff_suite (void)
{
  Suite *s = suite_create ("List Diff");
  /* Core test case */
  TCase *tc_core = tcase_create ("Core");
 
  tcase_add_test (tc_core, wrap_delete_calls_delete_with_listx);
  tcase_add_test (tc_core, wrap_delete_calls_delete_with_pos);
  tcase_add_test (tc_core, wrap_insert_calls_delete_with_listy);
  tcase_add_test (tc_core, wrap_insert_calls_delete_with_pos);
  tcase_add_test (tc_core, compare_calls_given_elements);
  tcase_add_test (tc_core, list_diff_remove_check);
  tcase_add_test (tc_core, list_diff_insert_check);
  tcase_add_test (tc_core, list_diff_insert_and_remove_check);
  tcase_add_test (tc_core, list_diff_insert_and_remove_check2);
  tcase_add_test (tc_core, list_diff_insert_and_remove_small_list_check);

  suite_add_tcase (s, tc_core);
  return s;
}
