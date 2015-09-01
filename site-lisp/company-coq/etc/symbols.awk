BEGIN                   { printf "(defcustom company-coq-prettify-symbols-alist '(" }
                        { gsub("\\\\", "\\\\", $1); printf("(\"%s\" . ?%s)", $1, substr($2,0,1)) }
NR % 3 == 0 && NR != NL { printf "\n" }
NR % 3 != 0 && NR != NL { printf " " }
END                     { printf ")\n" }
