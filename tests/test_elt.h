/**
 * @file test_elt.h
 */

#ifndef TEST_ELT_H
#define TEST_ELT_H

#include <stdlib.h>
#include <stdbool.h>
#include "merge_print_ctxt.h"
#include "doc_stream.h"
#include "merge_delta.h"
#include "doc_elt.h"
#include "doc_elt_ops.h"

static void test_elt_print_op (doc_elt *elt, void *ctxt, doc_stream *out);
static void test_elt_merge_print_op (merge_delta *delta, merge_print_ctxt *ctxt, 
				     doc_stream *out);
static bool test_elt_compare_op (doc_elt *a, doc_src a_src, 
				 doc_elt *b, doc_src b_src, void *ctxt);
/**
 * @struct test_elt
 * @brief An extremely simple doc_elt used for testing.
 */
typedef struct test_elt
{
  doc_elt elt;
  int value;
  int merge_print_depth;
} test_elt;

static doc_elt_ops test_elt_ops = {
  .print = test_elt_print_op,
  .merge_print = test_elt_merge_print_op,
  .compare = test_elt_compare_op
};

static int
test_elt_get_value (test_elt *elt)
{
  return elt->value;
}

static void
test_elt_set_value (test_elt *elt, int value)
{
  elt->value = value;
  return;
}

static int
test_elt_get_merge_print_depth (test_elt *elt)
{
  return elt->merge_print_depth;
}

static void
test_elt_set_merge_print_depth (test_elt *elt, int depth)
{
  elt->merge_print_depth = depth;
  return;
}

/**
 * Reset values in elt changed by doc_elt_ops to zero.
 */
static void
test_elt_reset (test_elt *elt)
{
  test_elt_set_merge_print_depth (elt, 0);
}

static void
test_elt_print_op (doc_elt *elt, void *ctxt, doc_stream *out)
{
  /* do nothing */
}

static void
test_elt_merge_print_op (merge_delta *delta, merge_print_ctxt *ctxt, doc_stream *out)
{
  doc_elt *elt = merge_delta_get_elt (delta);
  test_elt_set_merge_print_depth ((test_elt *)elt, ctxt->depth);
  ctxt->depth++;
  return;
}

static bool
test_elt_compare_op (doc_elt *a, doc_src a_src, 
		     doc_elt *b, doc_src b_src, void *ctxt)
{
  doc_elt_ops *a_ops = doc_elt_get_ops (a);
  doc_elt_ops *b_ops = doc_elt_get_ops (b);
  assert (a_ops == b_ops);
  assert (a_ops == &test_elt_ops);
  assert (b_ops == &test_elt_ops);
  return (test_elt_get_value ((test_elt*)a) == test_elt_get_value ((test_elt *)b));
}


static test_elt *
test_elt_create (int value)
{
  test_elt *elt = malloc (sizeof (test_elt));
  doc_elt_set_ops (&(elt->elt), &test_elt_ops);
  test_elt_set_value (elt, value);
  test_elt_set_merge_print_depth (elt, 0);
}

static void 
test_elt_free (test_elt *elt)
{
  free (elt);
}

#endif
