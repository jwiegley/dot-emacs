drop index if exists IX1_SOME_TABLE;

create index IX1_SOME_TABLE
  on SOME_TABLE(some_column);

-- NOTE: syntax incorrectly detects the name of the index as being "if".  will
-- fix later
create index if not exists IX2_SOME_TABLE
  on SOME_TABLE(some_other_column);

create index IX3_SOME_TABLE
  on SOME_TABLE(some_other_column);
