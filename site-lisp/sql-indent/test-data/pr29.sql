select y ,
       case
       when foo>5 then "great"
       when foo=5 then "normal"
       else "poor"
       end as level
  from   bar;

declare
  dummy number;
begin
  case ind
  when 1 then
    dummy := 'Guy';
    dummy1 := 'Abc';
  when 2 then
    dummy := 'Abc';
    dummy1 := 'Abc';
  when 3 then
    dummy := 'Def'; 
  else
    dummy := 'World';
  end case;
end;
/
-- Local Variables:
-- sql-product: oracle
-- End:
