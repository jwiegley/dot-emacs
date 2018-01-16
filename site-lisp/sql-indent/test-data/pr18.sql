set serveroutput on
declare
  dummy varchar2(25);
  ind   number       := 2;
begin
  dbms_output.enable(null);
  
  dummy := case
           when ind = 1 then 'Guy'
           when ind = 2 then 'Abc'
           else 'World'
           end;

  dbms_output.put_line('Hello ' || dummy);
  
  case ind
  when 1 then dummy := 'Guy';
  when 2 then dummy := 'Abc';
  when 3 then dummy := 'Def'; 
  else dummy := 'World';
  end case;

  dbms_output.put_line('Hello ' || dummy);
end;
/
-- Local Variables:
-- sql-product: oracle
-- End:
