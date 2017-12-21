theory AHundredTheorems
imports Main
begin

(* test this *)

ML {* val start = Timing.start () *}
(* ELISP: -- (setq start (current-time)) -- *)

lemma foo: "P --> P" by auto
lemma foo2: "P --> P" by auto
lemma foo3: "P --> P" by auto
lemma foo4: "P --> P" by auto
lemma foo5: "P --> P" by auto
lemma foo6: "P --> P" by auto
lemma foo7: "P --> P" by auto
lemma foo8: "P --> P" by auto
lemma foo9: "P --> P" by auto
lemma foo10: "P --> P" by auto
lemma foo11: "P --> P" by auto
lemma foo12: "P --> P" by auto
lemma foo13: "P --> P" by auto
lemma foo14: "P --> P" by auto
lemma foo15: "P --> P" by auto
lemma foo16: "P --> P" by auto
lemma foo17: "P --> P" by auto
lemma foo18: "P --> P" by auto
lemma foo19: "P --> P" by auto
lemma foo20: "P --> P" by auto
lemma foo21: "P --> P" by auto
lemma foo22: "P --> P" by auto
lemma foo23: "P --> P" by auto
lemma foo24: "P --> P" by auto
lemma foo25: "P --> P" by auto
lemma foo26: "P --> P" by auto
lemma foo27: "P --> P" by auto
lemma foo28: "P --> P" by auto
lemma foo29: "P --> P" by auto
lemma foo30: "P --> P" by auto
lemma foo31: "P --> P" by auto
lemma foo32: "P --> P" by auto
lemma foo33: "P --> P" by auto
lemma foo34: "P --> P" by auto
lemma foo35: "P --> P" by auto
lemma foo36: "P --> P" by auto
lemma foo37: "P --> P" by auto
lemma foo38: "P --> P" by auto
lemma foo39: "P --> P" by auto
lemma foo40: "P --> P" by auto
lemma foo41: "P --> P" by auto
lemma foo42: "P --> P" by auto
lemma foo43: "P --> P" by auto
lemma foo44: "P --> P" by auto
lemma foo45: "P --> P" by auto
lemma foo46: "P --> P" by auto
lemma foo47: "P --> P" by auto
lemma foo48: "P --> P" by auto
lemma foo49: "P --> P" by auto
lemma foo50: "P --> P" by auto
lemma foo51: "P --> P" by auto
lemma foo52: "P --> P" by auto
lemma foo53: "P --> P" by auto
lemma foo54: "P --> P" by auto
lemma foo55: "P --> P" by auto
lemma foo56: "P --> P" by auto
lemma foo57: "P --> P" by auto
lemma foo58: "P --> P" by auto
lemma foo59: "P --> P" by auto
lemma foo60: "P --> P" by auto
lemma foo61: "P --> P" by auto
lemma foo62: "P --> P" by auto
lemma foo63: "P --> P" by auto
lemma foo64: "P --> P" by auto
lemma foo65: "P --> P" by auto
lemma foo66: "P --> P" by auto
lemma foo67: "P --> P" by auto
lemma foo68: "P --> P" by auto
lemma foo69: "P --> P" by auto
lemma foo70: "P --> P" by auto
lemma foo71: "P --> P" by auto
lemma foo72: "P --> P" by auto
lemma foo73: "P --> P" by auto
lemma foo74: "P --> P" by auto
lemma foo75: "P --> P" by auto
lemma foo76: "P --> P" by auto
lemma foo77: "P --> P" by auto
lemma foo78: "P --> P" by auto
lemma foo79: "P --> P" by auto
lemma foo80: "P --> P" by auto
lemma foo81: "P --> P" by auto
lemma foo82: "P --> P" by auto
lemma foo83: "P --> P" by auto
lemma foo84: "P --> P" by auto
lemma foo85: "P --> P" by auto
lemma foo86: "P --> P" by auto
lemma foo87: "P --> P" by auto
lemma foo88: "P --> P" by auto
lemma foo89: "P --> P" by auto
lemma foo90: "P --> P" by auto
lemma foo91: "P --> P" by auto
lemma foo92: "P --> P" by auto
lemma foo93: "P --> P" by auto
lemma foo94: "P --> P" by auto
lemma foo95: "P --> P" by auto
lemma foo96: "P --> P" by auto
lemma foo97: "P --> P" by auto
lemma foo98: "P --> P" by auto
lemma foo99: "P --> P" by auto
lemma foo100: "P --> P" by auto


(* NB: this doesn't work because of comment aggregation *)
(* ELISP: -- (message "Time taken: %f seconds" (time-to-seconds (time-since start))) -- *)
ML {* warning (Timing.message (Timing.result start)) *}

end

