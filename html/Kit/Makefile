#
# Update dtds from PG Kit repository.
#

.PHONY: dtdupdate

DTDTARGS=dtd/pgip.dtd dtd/pgml.dtd

# checkout in temp dir because otherwise CVS complains of repo clash (fixes?)
dtdupdate:	
	mkdir dtdtmp; cvs -d :ext:da@localssh.dcs.ed.ac.uk:/home/proofgen/src export -kv -D today -d dtdtmp Kit/dtd; mv dtdtmp/* dtd; rmdir dtdtmp; cvs commit -m"Updated from Kit repo" dtd
