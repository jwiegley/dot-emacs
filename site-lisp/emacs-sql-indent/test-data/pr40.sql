USE [testdb]
GO
SET ANSI_NULLS ON
GO
SET QUOTED_IDENTIFIER ON
GO
ALTER FUNCTION [dbo].[Test]
()
RETURNS
@TestBatch TABLE
(
  [param] [varchar](20) NOT NULL,
  [param2] [datetime] NOT NULL,
)
AS
BEGIN
  DECLARE @var int;
  DECLARE @var2 int;
  set @var = 100;
  RETURN;
END
-- Local Variables:
-- sql-product: ms
-- End:
