(* -*- coding: utf-8 -*- *)

(*
  Example theory involving unicode characters (utf-8 encoding) -- both
  formal and informal ones.
*)

theory Unicode
imports Main
begin

text {* The Hebrew Alef-Bet (א-ב). *}

datatype alef_bet =
    Alef    ("א")
  | Bet     ("ב")
  | Gimel   ("ג")
  | Dalet   ("ד")
  | He      ("ה")
  | Vav     ("ו")
  | Zayin   ("ז")
  | Het     ("ח")
  | Tet     ("ט")
  | Yod     ("י")
  | Kaf     ("כ")
  | Lamed   ("ל")
  | Mem     ("מ")
  | Nun     ("נ")
  | Samekh  ("ס")
  | Ayin    ("ע")
  | Pe      ("פ")
  | Tsadi   ("צ")
  | Qof     ("ק")
  | Resh    ("ר")
  | Shin    ("ש")
  | Tav     ("ת")

thm alef_bet.induct


text {* Interpreting Hebrew letters as numbers. *}

primrec mispar :: "alef_bet => nat"
where
  "mispar א = 1"
| "mispar ב = 2"
| "mispar ג = 3"
| "mispar ד = 4"
| "mispar ה = 5"
| "mispar ו = 6"
| "mispar ז = 7"
| "mispar ח = 8"
| "mispar ט = 9"
| "mispar י = 10"
| "mispar כ = 20"
| "mispar ל = 30"
| "mispar מ = 40"
| "mispar נ = 50"
| "mispar ס = 60"
| "mispar ע = 70"
| "mispar פ = 80"
| "mispar צ = 90"
| "mispar ק = 100"
| "mispar ר = 200"
| "mispar ש = 300"
| "mispar ת = 400"

thm mispar.simps

lemma "mispar ק + mispar ל + mispar ה = 135"
  by simp

end
