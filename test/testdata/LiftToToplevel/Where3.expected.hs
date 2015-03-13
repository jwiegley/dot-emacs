module LiftToToplevel.Where3 where


foo n = bar [] n

bar _ 0 = []
bar acc c
  = acc ++ [c] ++ (bar acc (c-1))

