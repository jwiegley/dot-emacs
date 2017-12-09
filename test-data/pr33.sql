declare
  function dummy return my_user.my_table%rowtype;
  function dummy2 return my_user.my_table.my_col%type;
  var dummy3 number;
begin
  null;
end;

-- Local Variables:
-- mode: sql
-- tab-width: 2
-- indent-tabs-mode: nil
-- sql-product: oracle
-- End:
