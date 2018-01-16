create function foo_1() returns int AS
$$
  select 5;
$$;
  
create function foo_2() returns int AS $$
  select 5;
$$;

create function foo_3() returns int
AS $$
  select 5;
$$;

create function foo_4() returns int
AS
$$
  select 5;
$$;

SELECT a();

-- Local Variables:
-- mode: sql
-- mode: sqlind-minor
-- tab-width: 2
-- indent-tabs-mode: nil
-- sql-product: postgres
-- End:
