#
# Publish files to Informatics web server.
#
# Requires permissions in /group/project/proofgeneral
#
# $Id$
#

PWD=`pwd`
IGNOREDWEBFILES="*~,*.NOEXPORT,CVS/,/test/,/test/*,/tmp,/tmp/*,/Makefile"

# Run rsync using ssh
# --cvs-exclude: auto ignore files in the same way CVS does [inc. .cvsignore]
EXCLUDEFILE=.tmp-rsync-excludes
RSYNC=rsync -e ssh -auv --delete --safe-links --force --delete-excluded --exclude-from=${EXCLUDEFILE} --exclude="/${EXCLUDEFILE}"

DESTWEB=ssh.inf.ed.ac.uk:/group/project/proofgeneral/web
DESTCGI=ssh.inf.ed.ac.uk:/group/project/proofgeneral/cgi

default: pub

excludes:
	echo '${IGNOREDWEBFILES}'  | sed 's/,/\n/g' > ${EXCLUDEFILE}

test:	excludes
	${RSYNC} --exclude=/cgi/ -n ${PWD}/ ${DESTWEB} 
#	${RSYNC} -n ${PWD}/cgi/  ${DESTCGI}

pub:	excludes
	${RSYNC} --exclude=/cgi/ ${PWD}/ ${DESTWEB} 
#	${RSYNC} ${PWD}/cgi/ ${DESTCGI}

