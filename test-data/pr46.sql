with some_table as (
  -- a comment at the start
  select col1,
         col2,
         col3
    from some_table)
select *
  from some_table;
