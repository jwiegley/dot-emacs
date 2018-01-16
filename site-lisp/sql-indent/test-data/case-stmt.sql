-- https://github.com/bsvingen/sql-indent/issues/1
SELECT y ,
       CASE
       WHEN foo>5 THEN "great"
       WHEN foo=5 THEN "normal"
       ELSE "poor"
       END AS level
  FROM bar;

var := CASE
        var                             -- tricky case
       WHEN foo>5 THEN "great"
       WHEN foo=5 THEN "normal"
       ELSE "poor"
       END;
