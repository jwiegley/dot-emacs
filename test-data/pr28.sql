declare
  dummy          number;
  e_stop_program exception;
begin
  begin
    if 1 = 1 then
      proc1;
      proc2;
    elsif 1 = 2
      proc3;
      proc4;
    else
      raise e_stop_program;
    end if;
    case ind
    when 1 then dummy := 'Guy';
    when 2 then dummy := 'Abc';
    when 3 then dummy := 'Def'; 
    else dummy := 'World';
    end case;
  exception
    when no_data_found then
      proc1;
      proc2;
    when too_many_rows then
      proc3;
      proc4;
    when others then
      proc5;
  end;
end;
/
-- Local Variables:
-- mode: sqlind-minor
-- mode: sql
-- sql-product: oracle
-- End:
