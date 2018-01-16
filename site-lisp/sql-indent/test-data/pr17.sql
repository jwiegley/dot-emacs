clear columns
set linesize 2500
-- set trimout on
-- set trimspool on

select sysdate from dual;

select col1, 'a long line of text ending with a single word'
         || col2
         || col3
         || 'some text' as composed_column,
       col4
         || col5 as composed_column2
  from   my_table
 where  cond1 = fct1
        || 'another text'
    and    cond2 = 2;

select atc.column_name,
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

delete from my_table mt
 where  col_1    = v_col1
        and   (col_2    = v_col2
               or col_3 = v_col3)
        and   col_42    = '42'
        ;

update my_table
   set    col1_has_a_long_name = value1,
          col2_is_short        = value2
 where cond1 is not null
       and  (   col_2 = v_col2
             or col_3 = v_col3)
       and   col_42   = '42'
       ;

insert into xyzxx
            ( aaa, xxx, bbb, ccc,
            ddd, eee, fff, ggg,
            hhh )
select aaa,
       xxx,
       max (m.b1) as bbb,
       min (m.b1) as ccc,
       coalesce (max (n.c2), 0) as ddd,
       coalesce (min (n.c2), 0) as eee,
       max (m.b1) over ( partition by c2
                        order by aaa desc ) as fff,
       min (m.b1) over ( partition by c2
                        order by aaa desc ) as ggg,
       avg (n.c2) as hhh
  from  (select * from (select aaa,
                               jjj + kkk as b1,
                               row_number () over ( partition by qqq
                                                   order by rrr,
                                                   sss ) as rn
                          from mno) a_nested_nested
          where rn = 1) m
          inner join (select aaa,
                             nnn + ooo as c2
                        from   pqr) n
          using (aaa),
 group by aaa,
          xxx
 order by xxx desc,
          aaa asc
          ;
-- Local Variables:
-- sql-product: oracle
-- End:
