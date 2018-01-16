select distinct
       atc.column_name,
       atc.data_type,
       data_length,
       data_precision,
       nullable,
       data_scale,
       nvl(substr(comments, 1, 100), atc.column_name) comments
from   all_tab_columns atc,
       all_col_comments acc
where  atc.owner       = acc.owner
and    atc.table_name  = acc.table_name
and    atc.column_name = acc.column_name
and    atc.owner       = user
and    atc.table_name  = 'MY_TABLE'
and    atc.column_name = p_column_name
and    not exists (select 1
                   from   all_tab_columns atc1,
                          all_col_comments acc1
                   where  atc1.owner       = acc1.owner
                   and    atc1.table_name  = acc1.table_name
                   and    atc1.column_name = acc1.column_name
                   and    atc1.owner       = atc.owner
                   and    atc1.table_name  = atc.table_name
                   and    acc1.column_name = acc.column_name)
;

-- Local Variables:
-- mode: sql
-- mode: sqlind-minor
-- tab-width: 2
-- indent-tabs-mode: nil
-- sql-product: oracle
-- End:
