create or replace package body my_pacakge authid current user is
  
  cursor cur1 is
    select 1 dummy
    from   my_table
    where  1 = 1
    and    col1 = p_col1;

  p_col1 my_table.col1%type := 42;

  function get_my_value(p_param1 in my_table.col1%type)
    return my_table.col2%type is

    cursor cur2 (p_val_col1 in my_table.col1%type) is
      select col2
      from   my_table
      where  col1 = p_val_col1;

    v_result my_table.col2%type;
  begin
    for rec in cur2(p_param1) loop
      v_result := rec.col2;
    end loop;
  end get_my_value;

begin
  for rec in cur1 loop
    dbms_output.put_line(rec.dummy);
  end loop;

  begin
    null;
  end;

  dbms_output.put_line(get_my_value(p_col1));
end my_pacakge;
/
-- Local Variables:
-- sql-product: oracle
-- End:
