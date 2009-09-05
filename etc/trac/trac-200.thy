(* See trac #200 *)
theory Trac200 imports Main begin

(* Test simulating sledgehammer asynchronous output *)

ML {* Thread.fork (fn () =>
  (OS.Process.sleep (Time.fromSeconds 3); priority "urgent message"), []) *}

(* Want to preserve correct term output *)

term "x"

end

