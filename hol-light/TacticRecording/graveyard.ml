

(* Utility for applying tactic and incorproating results into goal tree.      *)
(* Takes an "infotactic", i.e. like a normal tactic that works on 'goal' and  *)
(* returns 'goalstate', but that also returns 'finfo' which summarises the    *)
(* operation.  These are easily formed by tagging normal tactics.             *)

let infotactic_wrap0 (infotac:goal->(goalstate*finfo)) (gx:xgoal) : xgoalstate =
  let (g,id) = dest_xgoal gx in
  let ((meta,gs,just),gst) = infotac g in
  let gxs = extend_gtree id gst gs in
  (meta,gxs,just);;
