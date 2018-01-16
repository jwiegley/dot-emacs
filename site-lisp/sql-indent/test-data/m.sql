INSERT INTO 
  xyzxx 
  ( aaa, bbb, ccc 
  , ddd, eee, fff, ggg 
  , hhh 
  ) 
SELECT 
  aaa 
  , MAX (m.b1) AS bbb 
  , MIN (m.b1) AS ccc 
  , COALESCE (MAX (n.c2), 0)  AS ddd 
  , COALESCE (MIN (n.c2), 0)  AS eee 
  , MAX (m.b1) OVER 
    (     PARTITION BY c2 
    ORDER BY aaa DESC 
    ) AS fff 
  , MIN (m.b1) OVER 
    (   PARTITION BY c2 
    ORDER BY aaa DESC 
    ) AS ggg 
  , AVG (n.c2)  AS hhh 
  FROM 
      (SELECT * FROM 
                    ( SELECT 
                        aaa 
                        , jjj + kkk  AS b1 
                        , ROW_NUMBER () OVER 
                          (   PARTITION BY qqq 
                          ORDER BY 
                          rrr 
                          , sss 
                          ) AS rn 
                        FROM 
                            mno 
                            ) 
        WHERE 
          rn = 1 
          )  m 
      INNER JOIN 
      ( SELECT 
          aaa 
          , nnn + ooo AS c2 
          FROM 
              pqr 
              ) n 
      USING (aaa), 
 GROUP BY 
   aaa 
