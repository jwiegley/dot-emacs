#
# Publish files to Informatics web server.
#
# Requires permissions in /group/project/proofgeneral
#
# $Id$
#
# FIXME: we want to have --delete and --delete-excluded in sync,
# but yet preserve ProofGeneral-*  (distribs).  How to do that?
# Might be better to put distribs elsewhere.

PWD=`pwd`
IGNOREDWEBFILES=*~,*.NOEXPORT,CVS/,/test/,/test/*,/tmp,/tmp/*,/Makefile,.cvsignore

# Run rsync using ssh
# --cvs-exclude: auto ignore files in the same way CVS does [exc. .cvsignore]
# --include=ProofGeneral-* to avoid deleting archives
# --delete-excluded
EXCLUDEFILE=.tmp-rsync-excludes
RSYNC=rsync -e ssh -auv --safe-links --force  --exclude-from=${EXCLUDEFILE} --include='releases-emacs' --exclude="/${EXCLUDEFILE}" --cvs-exclude

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

