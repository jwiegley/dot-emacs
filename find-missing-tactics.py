import subprocess
import re

TACTIC = re.compile(r'\| IDENT "([^"]+)"')
FIRST_WORD = re.compile("^[a-zA-Z_]*")

UNDOCUMENTED = set(("autounfold_one", "autounfoldify", "casetype", "convert_concl_no_check", "exact_no_check", "fauto", "finduction", "fold_match", "fold_matches", "implify", "ipattern", "is_fix", "is_ground", "poseq", "prolog", "destauto", "substitute", "soft functional induction", "setoid_etransitivity", "new auto", "gintuition", "infoH"))
UNDOCUMENTED_LTAC = set(("external", "now", "ltac"))
MORPHISMS = set(("head_of_constr", "hget_evar", "not_evar"))
STDLIB = set(("autoapply", "destruct_with_eqn", "rew", "rewrite_all", "rewrite_db", "typeclasses eauto"))
TO_ADD = set(("info", "info_auto", "info_eauto", "info_trivial", "debug auto", "debug eauto", "debug trivial"))

def first_word(tactic):
    return FIRST_WORD.match(tactic).group(0)

def manual_tactics():
    with open('tactics') as found_file:
        return set(first_word(line.strip()) for line in found_file)

def grammar_tactics():
    COQTOP_INPUT = "Print Grammar tactic.\nQuit."
    coqtop_tactics = subprocess.check_output(["/build/coq/bin/coqtop", "-coqlib", "/build/coq/"], input=COQTOP_INPUT, stderr=-1, universal_newlines = True)
    return set(first_word(match.group(1)) for match in TACTIC.finditer(coqtop_tactics))

manual = manual_tactics()
grammar = grammar_tactics()

for tac in sorted(x for x in (grammar - manual - UNDOCUMENTED - UNDOCUMENTED_LTAC - MORPHISMS - STDLIB - TO_ADD) if len(x) > 3):
    print(tac)
