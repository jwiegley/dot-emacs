#!/usr/bin/env zsh

set -x

# '/--!' -> '--'
regexp_private_exclamation='s/orgtrello-\([a-z]*\)\/--\([a-z-]*\)!/orgtrello-\1--\2/g'
regexp_private='s/orgtrello-\([a-z]*\)\/--\([a-z-]*\)/orgtrello-\1--\2/g'
# '/' -> '-'
regexp_slash_exclamation='s/orgtrello-\([a-z]*)\/\([a-z-]*\)!/orgtrello-\1-\2/g'
regexp_slash='s/orgtrello-\([a-z]*\)\/\([a-z-]*\)/orgtrello-\1-\2/g'
# '!' -> ''
regexp_exclamation='s/orgtrello-\([a-z]*\)-\([a-z-]*\)!/orgtrello-\1-\2/g'
regexp_default='s/org-trello\/\([a-z-]*\)/org-trello-\1/g'

regexp_dash='s/org-trello\/\([a-z-]*\)/org-trello-\1/g'
for i in load-org-trello* org-trello*.el test/*.el ; do
    sed -e $regexp_private_exclamation -i $i;
    sed -e $regexp_private -i $i;
    sed -e $regexp_slash_exclamation -i $i;
    sed -e $regexp_slash -i $i;
    sed -e $regexp_exclamation -i $i;
    sed -e $regexp_default -i $i;
    sed -e $regexp_dash -i $i;
    sed -e $regexp_dash_exclamation -i $i;
    sed -e $regexp_dash_dash_exclamation -i $i;
done
