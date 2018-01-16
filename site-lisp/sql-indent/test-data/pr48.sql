begin
  goto my_loop;
  dbms_output.put_line('If you read it, you''re in trouble');
  <<my_loop>>
  for ind in 1..5 loop
    dbms_output.put_line('ind: ' || ind);
  end loop my_loop;

  dbms_output.put_line('end of my_loop');
  <<my_second_loop>>
  while true loop
    dbms_output.put_line('in my_second_loop');
    goto out_of_loop;
  end loop my_second_loop;
  dbms_output.put_line('end of my_second_loop');
end;
/

-- Local Variables:
-- indent-tabs-mode: nil
-- mode: sql
-- mode: sqlind-minor
-- sql-product: oracle
-- tab-width: 2
-- End:
