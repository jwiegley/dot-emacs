select pk_id
       , case
         when t1.c1 is null then  '(null)'
         when t1.c1 in ('a', 'b','c','d','e') then 'a'
         else t1.c1
         end c1_alt
  from t1
 limit 10;
