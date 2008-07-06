Summary:	Proof General, Emacs interface for Proof Assistants
Name:		ProofGeneral
Version:	3.7.1pre080706
Release:	1
Group:		Text Editors/Integrated Development Environments (IDE)
License:	GPL
Url:		http://proofgeneral.inf.ed.ac.uk/
Packager:	David Aspinall <David.Aspinall@ed.ac.uk>
Source:		http://proofgeneral.inf.ed.ac.uk/ProofGeneral-%{version}.tgz
BuildRoot:	/tmp/ProofGeneral-root
BuildRequires:  emacs, xemacs
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
XEmacs (or Emacs) with Proof General loaded.

%package -n ProofGeneral-emacs-elc
Summary: Compiled ELC files for Proof General/GNU Emacs
Group: Applications/Editors/Emacs
Requires: emacs >= 21.2, ProofGeneral = %{version}-%{release}

%description -n ProofGeneral-emacs-elc
Proof General is a generic Emacs interface for proof assistants.
This package contains the byte compiled elisp files for GNU Emacs,
and integrates Proof General into the Emacs startup packages.
If you want to use GNU Emacs with Proof General, this package is
recommended.

%package -n ProofGeneral-xemacs-elc
Summary: Compiled ELC files for Proof General/XEmacs
Group:		Applications/Editors/Emacs
Requires: xemacs >= 21.4.12, ProofGeneral = %{version}-%{release}

%description -n ProofGeneral-xemacs-elc
Proof General is a generic Emacs interface for proof assistants.
This package contains the byte compiled elisp files for XEmacs,
and integrates Proof General into the Emacs startup packages.
If you want to use XEmacs with Proof General, this package is
recommended.

%changelog
* Fri May  4 2001 David Aspinall <David.Aspinall@ed.ac.uk> 
- Changelog in CVS now; official spec file developed with source.

%prep
%setup

%build
[ -n "${RPM_BUILD_ROOT}" ] && rm -rf ${RPM_BUILD_ROOT}

%install
mkdir -p ${RPM_BUILD_ROOT}/usr/share/emacs/ProofGeneral

# Clean out any .elc's that were in the tar file, and
# rebuild for the required emacs version.
make distclean

# Build packages for both emacs and xemacs, with only elc's.
make install-elc install-init PREFIX=${RPM_BUILD_ROOT}/usr EMACS=emacs DEST_PREFIX=/usr
make install-elc install-init PREFIX=${RPM_BUILD_ROOT}/usr  EMACS=xemacs DEST_PREFIX=/usr 

# Finally, install the desktop and .el files into non-Emacs version specific locations
make install-desktop install-el install-bin PREFIX=${RPM_BUILD_ROOT}/usr ELISPP=share/ProofGeneral DEST_PREFIX=/usr

# Install docs too
make install-doc PREFIX=${RPM_BUILD_ROOT}/usr DEST_PREFIX=/usr DOCDIR=${RPM_BUILD_ROOT}%{_docdir}
rm -f ${RPM_BUILD_ROOT}/usr/share/info/dir
gzip ${RPM_BUILD_ROOT}/usr/share/info/*

# Rename READMEs in subdirs to avoid clashes
for f in */README; do mv $f $f.`dirname $f`; done

# Clean away elc's in main tree to avoid packaging them 
make distclean

%clean
if [ "X" != "${RPM_BUILD_ROOT}X" ]; then
    rm -rf $RPM_BUILD_ROOT
fi

%post
/sbin/install-info /usr/share/info/ProofGeneral.info* /usr/share/info/dir
/sbin/install-info /usr/share/info/PG-adapting.info* /usr/share/info/dir
if [ -x /usr/bin/gtk-update-icon-cache ]; then
  gtk-update-icon-cache -q /usr/share/icons/hicolor
fi

%preun
/sbin/install-info --delete /usr/share/info/ProofGeneral.info* /usr/share/info/dir
/sbin/install-info --delete /usr/share/info/PG-adapting.info* /usr/share/info/dir

%postun
if [ -x /usr/bin/gtk-update-icon-cache ]; then
  gtk-update-icon-cache -q /usr/share/icons/hicolor
fi


%files
%defattr(-,root,root)
%{_bindir}/*
%doc %{_datadir}/man/man1/*
%doc %{_datadir}/info/*.info*
%doc %{_datadir}/doc/*
%{_datadir}/pixmaps/proofgeneral.png
%{_datadir}/icons/hicolor/*/proofgeneral.png
%{_datadir}/ProofGeneral/*
%{_datadir}/mime-info/proofgeneral.*
%{_datadir}/applications/proofgeneral.desktop
%{_datadir}/application-registry/proofgeneral.applications

%files -n ProofGeneral-emacs-elc
%defattr(-,root,root)
%{_datadir}/emacs/*/ProofGeneral/*
%{_datadir}/emacs/*/*/pg-init.el

%files -n ProofGeneral-xemacs-elc 
%defattr(-,root,root)
%{_datadir}/xemacs/*/*/ProofGeneral/*
%{_datadir}/xemacs/*/*/*/pg-init.el
