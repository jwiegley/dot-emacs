#include <stdlib.h>
#include <check.h>
#include "doc_tree.h"
#include "merge_tree.h"
#include "gl_list.h"

#include "doc_elt.h"
#include "doc_merge.c"
#include "merge_map.h"
#include "merge_delta.h"

/* Create a phony type of element */
typedef struct phony
{
  doc_elt _;
  int id;
} phony;

static phony * phony_create (int id);

static void
phony_ops_print (doc_elt *e, void *c, doc_stream *ds)
{
  return;
}

static void
phony_ops_print_merge (merge_delta *d, void *c, doc_stream *ds)
{
  return;
}

static bool 
phony_ops_compare (doc_elt *e1, doc_src s1, doc_elt *e2, doc_src s2, void *c)
{
  phony *p1 = (phony *) e1; phony *p2 = (phony *) e2;
  //printf ("Comparing: %d from %d, %d from %d = %d..", p1->id, s1, p2->id, s2, (p1->id == p2->id));
  return ((p1->id == p2->id));// && s2 == src_ancestor);
}


static doc_elt_ops phony_ops = {
  .print = phony_ops_print,
  .merge_print = phony_ops_print_merge,
  .compare = phony_ops_compare
};

static phony *
phony_create (int id)
{
  phony * p = malloc (sizeof (phony));
  p->id = id;
  doc_elt *e = (doc_elt *)p;
  e->ops = &phony_ops;
  return p;
}

START_TEST (check_doc_tree_merge_same_trees)
{
  doc_elt *p1 = (doc_elt *)phony_create (1);
  doc_elt *p2 = (doc_elt *)phony_create (2);

  doc_tree * da = ltree_node_create_empty ();
  doc_tree * dl = ltree_node_create_empty ();
  doc_tree * dr = ltree_node_create_empty ();
  doc_list l;
  doc_node *dn;

  // create the first doc_tree
  l = doc_node_get_children (da);

  dn = ltree_node_create_empty ();
  doc_node_set_elt (dn, p1);
  gl_list_nx_add_last (l, dn);

  dn = ltree_node_create_empty ();
  doc_node_set_elt (dn, p2);
  gl_list_nx_add_last (l, dn);

  dn = ltree_node_create_empty ();
  doc_node_set_elt (dn, p1);
  gl_list_nx_add_last (l, dn);

  // create the second tree
  l = doc_node_get_children (dl);
 
  dn = ltree_node_create_empty ();
  doc_node_set_elt (dn, p1);
  gl_list_nx_add_last (l, dn);

  dn = ltree_node_create_empty ();
  doc_node_set_elt (dn, p2);
  gl_list_nx_add_last (l, dn);

  dn = ltree_node_create_empty ();
  doc_node_set_elt (dn, p1);
  gl_list_nx_add_last (l, dn);

  // create the third tree
  l = doc_node_get_children (dr);
 
   dn = ltree_node_create_empty ();
  doc_node_set_elt (dn, p1);
  gl_list_nx_add_last (l, dn);

  dn = ltree_node_create_empty ();
  doc_node_set_elt (dn, p2);
  gl_list_nx_add_last (l, dn);

  dn = ltree_node_create_empty ();
  doc_node_set_elt (dn, p1);
  gl_list_nx_add_last (l, dn);

  // doc merge!
  create_merge_tree (da, dl, dr);

  // make sure that it worked
  fail_unless (1);
}
END_TEST

START_TEST (check_doc_tree_merge_different_trees)
{
  doc_elt *p1 = (doc_elt *)phony_create (1);
  doc_elt *p2 = (doc_elt *)phony_create (2);
  doc_elt *p3 = (doc_elt *)phony_create (3);

  doc_tree * da = ltree_node_create_empty ();
  doc_tree * dl = ltree_node_create_empty ();
  doc_tree * dr = ltree_node_create_empty ();
  doc_list l;
  doc_node *dn;

  // create the first doc_tree
  l = doc_node_get_children (da);

  dn = ltree_node_create_empty ();
  doc_node_set_elt (dn, p1);
  gl_list_nx_add_last (l, dn);

  dn = ltree_node_create_empty ();
  doc_node_set_elt (dn, p1);
  gl_list_nx_add_last (l, dn);

  dn = ltree_node_create_empty ();
  doc_node_set_elt (dn, p1);
  gl_list_nx_add_last (l, dn);

  // create the second tree
  l = doc_node_get_children (dl);
 
  dn = ltree_node_create_empty ();
  doc_node_set_elt (dn, p2);
  gl_list_nx_add_last (l, dn);

  dn = ltree_node_create_empty ();
  doc_node_set_elt (dn, p2);
  gl_list_nx_add_last (l, dn);

  dn = ltree_node_create_empty ();
  doc_node_set_elt (dn, p2);
  gl_list_nx_add_last (l, dn);

  // create the third tree
  l = doc_node_get_children (dr);
 
   dn = ltree_node_create_empty ();
  doc_node_set_elt (dn, p3);
  gl_list_nx_add_last (l, dn);

  dn = ltree_node_create_empty ();
  doc_node_set_elt (dn, p3);
  gl_list_nx_add_last (l, dn);

  dn = ltree_node_create_empty ();
  doc_node_set_elt (dn, p3);
  gl_list_nx_add_last (l, dn);

  // doc merge!
  create_merge_tree (da, dl, dr);

  // make sure that it worked
  fail_unless (1);
}
END_TEST

START_TEST (check_doc_tree_merge_similar_trees)
{
  doc_elt *p1 = (doc_elt *)phony_create (1);
  doc_elt *p2 = (doc_elt *)phony_create (2);
  doc_elt *p3 = (doc_elt *)phony_create (3);

  doc_tree * da = ltree_node_create_empty ();
  doc_tree * dl = ltree_node_create_empty ();
  doc_tree * dr = ltree_node_create_empty ();
  doc_list l;
  doc_node *dn;

  // create the first doc_tree
  l = doc_node_get_children (da);

  dn = ltree_node_create_empty ();
  doc_node_set_elt (dn, p1);
  gl_list_nx_add_last (l, dn);

  dn = ltree_node_create_empty ();
  doc_node_set_elt (dn, p2);
  gl_list_nx_add_last (l, dn);

  dn = ltree_node_create_empty ();
  doc_node_set_elt (dn, p3);
  gl_list_nx_add_last (l, dn);

  // create the second tree
  l = doc_node_get_children (dl);
 
  dn = ltree_node_create_empty ();
  doc_node_set_elt (dn, p1);
  gl_list_nx_add_last (l, dn);

  dn = ltree_node_create_empty ();
  doc_node_set_elt (dn, p2);
  gl_list_nx_add_last (l, dn);

  // create the third tree
  l = doc_node_get_children (dr);
 
   dn = ltree_node_create_empty ();
  doc_node_set_elt (dn, p2);
  gl_list_nx_add_last (l, dn);

  dn = ltree_node_create_empty ();
  doc_node_set_elt (dn, p3);
  gl_list_nx_add_last (l, dn);

  dn = ltree_node_create_empty ();
  doc_node_set_elt (dn, p1);
  gl_list_nx_add_last (l, dn);

  // doc merge!
  create_merge_tree (da, dl, dr);

  // make sure that it worked
  fail_unless (1);
}
END_TEST

START_TEST (check_doc_tree_merge_nested_trees)
{
  doc_elt *p1 = (doc_elt *)phony_create (1);
  doc_elt *p2 = (doc_elt *)phony_create (2);
  doc_elt *p3 = (doc_elt *)phony_create (3);

  doc_list l, l1;
  doc_node *dn, *d1;

  // create the first doc_tree
  doc_tree * da = ltree_node_create_empty ();
  l = doc_node_get_children (da);

  dn = ltree_node_create_empty ();
  doc_node_set_elt (dn, p1);
  gl_list_nx_add_last (l, dn);

  l1 = doc_node_get_children (dn);
  d1 = ltree_node_create_empty ();
  doc_node_set_elt (d1, p1 );
  gl_list_nx_add_last (l1, d1);

  d1 = ltree_node_create_empty ();
  doc_node_set_elt (d1, p2);
  gl_list_nx_add_last (l1, d1);

  dn = ltree_node_create_empty ();
  doc_node_set_elt (dn, p2);
  gl_list_nx_add_last (l, dn);

  dn = ltree_node_create_empty ();
  doc_node_set_elt (dn, p3);
  gl_list_nx_add_last (l, dn);

  // create the second tree
  doc_tree * dl = ltree_node_create_empty ();
  l = doc_node_get_children (dl);

  dn = ltree_node_create_empty ();
  doc_node_set_elt (dn, p1);
  gl_list_nx_add_last (l, dn);

  l1 = doc_node_get_children (dn);
  d1 = ltree_node_create_empty ();
  doc_node_set_elt (d1, p2);
  gl_list_nx_add_last (l1, d1);

  dn = ltree_node_create_empty ();
  doc_node_set_elt (dn, p2);
  gl_list_nx_add_last (l, dn);

  l1 = doc_node_get_children (dn);
  d1 = ltree_node_create_empty ();
  doc_node_set_elt (d1, p1 );
  gl_list_nx_add_last (l1, d1);

  dn = ltree_node_create_empty ();
  doc_node_set_elt (dn, p3);
  gl_list_nx_add_last (l, dn);

  // create the third tree
  doc_tree * dr = ltree_node_create_empty ();
  l = doc_node_get_children (dr);

  dn = ltree_node_create_empty ();
  doc_node_set_elt (dn, p1);
  gl_list_nx_add_last (l, dn);

  dn = ltree_node_create_empty ();
  doc_node_set_elt (dn, p2);
  gl_list_nx_add_last (l, dn);

  l1 = doc_node_get_children (dn);
  d1 = ltree_node_create_empty ();
  doc_node_set_elt (d1, p1 );
  gl_list_nx_add_last (l1, d1);

  dn = ltree_node_create_empty ();
  doc_node_set_elt (dn, p3);
  gl_list_nx_add_last (l, dn);

  l1 = doc_node_get_children (dn);
  d1 = ltree_node_create_empty ();
  doc_node_set_elt (d1, p2);
  gl_list_nx_add_last (l1, d1);

  // doc merge!
  create_merge_tree (da, dl, dr);

  // make sure that it worked
  fail_unless (1);
}
END_TEST

Suite *
make_doc_merge_suite (void)
{
  Suite *s = suite_create ("Doc Merge");
  /* Core test case */
  TCase *tc_core = tcase_create ("Core");
  tcase_add_test (tc_core, check_doc_tree_merge_same_trees);
  tcase_add_test (tc_core, check_doc_tree_merge_different_trees);
  tcase_add_test (tc_core, check_doc_tree_merge_similar_trees);
  tcase_add_test (tc_core, check_doc_tree_merge_nested_trees);

  suite_add_tcase (s, tc_core);
  return s;
}
