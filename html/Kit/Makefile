#
# Update exported Kit files from PG Kit repository.
# [interim]
#

.PHONY: update

CVSROOT=:pserver:da@cvs.inf.ed.ac.uk:/disk/cvs/proofgen

# checkout in temp dir because otherwise CVS complains of working dir checkout
update:	
	mkdir kittmp
	cvs -d ${CVSROOT} export -kv -D today -d kittmp kitwebfiles
	(cd kittmp; tar -c . | (cd ..; tar -xp))
	rm -rf kittmp
	cvs commit -m"Updated from Kit repo"
