theory BackslashInStrings imports Main begin

consts test :: string

(*

10.8.04  NB: Isar currently sets \ as word constituent ("w").
Isabelle sets it as a punctuation element (".").

Experiments:  (modify-syntax-entry ?\\ "w")
	      (modify-syntax-entry ?\\ ".")

(add-hook 'isar-mode-hook
  (lambda () (modify-syntax-entry ?\\ "\\")))
*)

defs test_def: "test == ''System.out.println(\"List from here:\")''"


end 



(*

I'd be grateful for a little help in solving a bug/issue that I'm encountering in using Proof General with strings. It appears that Isar doesn't correctly understand Isabelle strings correctly.

He's an example theory that throws up the observed issues:

theory Test = Main:

consts test :: string

defs test_def: "test == ''System.out.println(\"List from here:\")''"

end

Firstly, anything between escaped double quotes is incorrectly highlighted.

This is benign, unless an Isar keyword occurs between the double quotes (eg. from). In this case, Isabelle throws an error when it trys to parse the Isabelle term - mainly, it appears, because Isar/Proof General has passed Isabelle an incorrect term.

I presume there's some Proof General regular expression that needs modifying here?

Any help in fixing the issue is greatly appreciated.

Thanks,
*)
