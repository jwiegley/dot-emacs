Summary:	Proof General, Emacs interface for Proof Assistants
Name:		ProofGeneral
Version:	3.5pre021111
Release:	1
Group:		Applications/Editors/Emacs
Copyright:	LFCS, University of Edinburgh
Url:		http://www.proofgeneral.org/
Packager:	David Aspinall <da@dcs.ed.ac.uk>
Source:		http://www.proofgeneral.org/ProofGeneral-3.5pre021111.tar.gz
BuildRoot:	/tmp/ProofGeneral-root
PreReq:		/sbin/install-info
Prefixes:	/usr/share/emacs /usr/bin /usr/share/info
BuildArchitectures: noarch

%description
Proof General is a generic Emacs interface for proof assistants,
suitable for use by pacifists and Emacs militants alike.
It is supplied ready-customized for LEGO, Coq, and Isabelle.
You can adapt Proof General to other proof assistants if you know a
little bit of Emacs Lisp.

To use Proof General, use the command `proofgeneral', which launches
XEmacs (or Emacs) for you, or add the line:

   (load-file "/usr/share/emacs/ProofGeneral/generic/proof-site.el")

to your .emacs file so Proof General is available whenever 
you run Emacs.

%changelog
* Fri May  4 2001 David Aspinall <da@dcs.ed.ac.uk> 
- Changelog in CVS now; official spec file developed with source.

%prep
%setup

%build
[ -n "${RPM_BUILD_ROOT}" ] && rm -rf ${RPM_BUILD_ROOT}

%install
mkdir -p ${RPM_BUILD_ROOT}/usr/share/emacs/ProofGeneral

# Put binaries in proper place
mkdir -p ${RPM_BUILD_ROOT}/usr/bin
mv bin/proofgeneral lego/legotags coq/coqtags isar/isartags ${RPM_BUILD_ROOT}/usr/bin

# Put info file in proper place, compress it.
mkdir -p ${RPM_BUILD_ROOT}/usr/share/info
mv doc/ProofGeneral.info doc/ProofGeneral.info-* ${RPM_BUILD_ROOT}/usr/share/info
mv doc/PG-adapting.info  doc/PG-adapting.info-*  ${RPM_BUILD_ROOT}/usr/share/info
gzip ${RPM_BUILD_ROOT}/usr/share/info/ProofGeneral.info  ${RPM_BUILD_ROOT}/usr/share/info/ProofGeneral.info-*
gzip ${RPM_BUILD_ROOT}/usr/share/info/PG-adapting.info ${RPM_BUILD_ROOT}/usr/share/info/PG-adapting.info-*
# Remove duff bits
rm -f doc/dir doc/localdir 

# Put icons and menu entry into suitable place (at least for RedHat, Mandrake)
mkdir -p ${RPM_BUILD_ROOT}/usr/share/icons/mini
cp images/pgmini.xpm ${RPM_BUILD_ROOT}/usr/share/icons/mini
cp images/pgicon.png ${RPM_BUILD_ROOT}/usr/share/icons
mkdir -p ${RPM_BUILD_ROOT}/usr/share/pixmaps
cp images/pgicon.png ${RPM_BUILD_ROOT}/usr/share/pixmaps
mkdir -p ${RPM_BUILD_ROOT}/usr/lib/menu
mkdir -p ${RPM_BUILD_ROOT}/usr/share/applnk/Applications
mkdir -p ${RPM_BUILD_ROOT}/etc/X11/applnk/Applications
mv etc/ProofGeneral.menu ${RPM_BUILD_ROOT}/usr/lib/menu/ProofGeneral	     # Mandrake
cp etc/ProofGeneral.desktop ${RPM_BUILD_ROOT}/usr/share/applnk/Applications  # RH KDE
mv etc/ProofGeneral.desktop ${RPM_BUILD_ROOT}/etc/X11/applnk/Applications    # RH Gnome

for f in */README; do mv $f $f.`dirname $f`; done

cp -pr phox acl2 twelf coq lego isa isar hol98 images generic ${RPM_BUILD_ROOT}/usr/share/emacs/ProofGeneral

%clean
if [ "X" != "${RPM_BUILD_ROOT}X" ]; then
    rm -rf $RPM_BUILD_ROOT
fi

%post
/sbin/install-info /usr/share/info/ProofGeneral.info.* /usr/share/info/dir
/sbin/install-info /usr/share/info/PG-adapting.info.* /usr/share/info/dir

%preun
/sbin/install-info --delete /usr/share/info/ProofGeneral.info.* /usr/share/info/dir
/sbin/install-info --delete /usr/share/info/PG-adapting.info.* /usr/share/info/dir

%files
%attr(-,root,root) %doc AUTHORS BUGS CHANGES COPYING INSTALL README.* REGISTER doc/* */README.*
%attr(-,root,root) /usr/share/info/ProofGeneral.info.*
%attr(-,root,root) /usr/share/info/ProofGeneral.info-*.*
%attr(-,root,root) /usr/share/info/PG-adapting.info.*
%attr(-,root,root) /usr/share/info/PG-adapting.info-*.*
%attr(-,root,root) /usr/bin/proofgeneral
%attr(-,root,root) /usr/bin/coqtags
%attr(-,root,root) /usr/bin/legotags
%attr(-,root,root) /usr/bin/isartags
%attr(-,root,root) /usr/share/icons/pgicon.png
%attr(-,root,root) /usr/share/pixmaps/pgicon.png
%attr(-,root,root) /usr/share/icons/mini/pgmini.xpm
%attr(-,root,root) /usr/lib/menu/ProofGeneral
%attr(-,root,root) /usr/share/applnk/Applications/ProofGeneral.desktop
%attr(-,root,root) /etc/X11/applnk/Applications/ProofGeneral.desktop
%attr(0755,root,root) %dir /usr/share/emacs/ProofGeneral
%attr(0755,root,root) %dir /usr/share/emacs/ProofGeneral/images
%attr(0755,root,root) %dir /usr/share/emacs/ProofGeneral/generic
%attr(0755,root,root) %dir /usr/share/emacs/ProofGeneral/coq
%attr(0755,root,root) %dir /usr/share/emacs/ProofGeneral/lego
%attr(0755,root,root) %dir /usr/share/emacs/ProofGeneral/isa
%attr(0755,root,root) %dir /usr/share/emacs/ProofGeneral/isar
%attr(0755,root,root) %dir /usr/share/emacs/ProofGeneral/hol98
%attr(0755,root,root) %dir /usr/share/emacs/ProofGeneral/phox
%attr(0755,root,root) %dir /usr/share/emacs/ProofGeneral/acl2
%attr(0755,root,root) %dir /usr/share/emacs/ProofGeneral/twelf
%attr(-,root,root) /usr/share/emacs/ProofGeneral/images/*
%attr(-,root,root) /usr/share/emacs/ProofGeneral/generic/*
%attr(-,root,root) /usr/share/emacs/ProofGeneral/coq/*
%attr(-,root,root) /usr/share/emacs/ProofGeneral/lego/*
%attr(-,root,root) /usr/share/emacs/ProofGeneral/isa/*
%attr(-,root,root) /usr/share/emacs/ProofGeneral/isar/*
%attr(-,root,root) /usr/share/emacs/ProofGeneral/hol98/*
%attr(-,root,root) /usr/share/emacs/ProofGeneral/phox/*
%attr(-,root,root) /usr/share/emacs/ProofGeneral/acl2/*
%attr(-,root,root) /usr/share/emacs/ProofGeneral/twelf/*
