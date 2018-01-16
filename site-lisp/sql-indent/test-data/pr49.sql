begin
  if true then
    <<my_third_loop>>
    while true loop
      dbms_output.put_line('in my_second_loop');
      exit my_third_loop;
    end loop my_third_loop;
    dbms_output.put_line('end of my_second_loop');
  end if;
end;
/

-- Local Variables:
-- indent-tabs-mode: nil
-- mode: sql
-- mode: sqlind-minor
-- sql-product: oracle
-- tab-width: 2
-- End:
