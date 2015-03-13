#ifndef CHECK_ORG_MERGE_DRIVER_H
#define CHECK_ORG_MERGE_DRIVER_H

#include <check.h>
 
Suite * make_parser_suite (void);
Suite * make_list_diff_suite (void);
Suite * make_org_elements_suite (void);
Suite * make_doc_merge_suite (void);
Suite * make_merge_print_suite (void);
#endif
