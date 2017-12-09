set serveroutput on
set trimout on trimspool on

declare
  var1 varchar2(25000);
  var2 varchar2(25000);
begin
  dbms_output.enable(null);
  if var1 is not null then
    var2 := 'var1 is set : -*-'
      || var1
      || '-*- some text after ...';
    var1 := '-*-'
      || var1
      || '-*-';
  elsif var2 is not null then
    var1 := 'var2 is set : -*-'
      || var2
      || '-*- some text after ...';
    var2 := '-*-'
      || var2
      || '-*-';
  else
    var2 := '-*-empty-*-';
    var1 := '-*-empty-*-';
  end if;

  var2 := 'var1 is set : -*-'
    || var1
    || '-*- some text after ...';
  var1 := 'var2 is set : -*-'
    || var2
    || '-*- some text after ...';
  dbms_output.put_line(var1);
  dbms_output.put_line(var2);
end;
/
-- Local Variables:
-- mode: sql
-- tab-width: 2
-- indent-tabs-mode: nil
-- sql-product: oracle
-- End:
