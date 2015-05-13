# Spec file for preview-latex

# Maintainer: auctex-devel@gnu.org

# Copyright (C) 2002, 2004, 2005 Free Software Foundation, Inc.

# This file is part of AUCTeX.

# AUCTeX is free software; you can redistribute it and/or modify it
# under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 3, or (at your option)
# any later version.

# AUCTeX is distributed in the hope that it will be useful, but
# WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
# General Public License for more details.

# You should have received a copy of the GNU General Public License
# along with AUCTeX; see the file COPYING.  If not, write to the Free
# Software Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston,
# MA 02110-1301, USA.

%define HAVE_EMACS  %(which emacs  >/dev/null 2>/dev/null && echo 1 || echo 0)
%define HAVE_XEMACS %(which xemacs >/dev/null 2>/dev/null && echo 1 || echo 0)

%define FOR_SUSE    %{?suse_version:1}%{!?suse_version:0}

%if %{FOR_SUSE}
%define distri      .suse
%define commongroup Productivity/Editors/Emacs
# This is awful, but I don't have the clue to avoid it:
%define xemacspkgdir %{_datadir}/xemacs/xemacs-packages
%define xemacspkgconfdir ${datadir}/xemacs/xemacs-packages
%else
%define distri      .fedora
%define commongroup Applications/Editors
# This is awful, but I don't have the clue to avoid it:
%define xemacspkgdir %{_datadir}/xemacs/xemacs-packages
%define xemacspkgconfdir ${datadir}/xemacs/xemacs-packages
%endif

# we use xemacs-packages because the system packages can be found
# here, and preview-latex is not yet a part of any sumo tarball or
# similar.  The choice for AUCTeX would probably be site-packages
# instead.

Summary: 	Emacs/LaTeX inline preview 
Name: 		preview-latex
Version: 	0.9.1
Release: 	1%{distri}
License:        GPL
BuildArchitectures: noarch
URL: 		http://www.gnu.org/software/auctex
Source0: 	ftp://ftp.gnu.org/pub/auctex/%{name}-%{version}.tar.gz
Group: 		%{commongroup}
BuildRoot: 	%{_tmppath}/%{name}-root
Prereq:		info
Requires:	ghostscript >= 6.51
Requires:	tetex tetex-dvips
BuildRequires:	texinfo >= 4.0

%description
Does your neck hurt from turning between previewer windows and the
source too often? This Elisp/LaTeX package will render your displayed
LaTeX equations right into the editing window where they belong. 

%package common
Summary: 	Emacs/LaTeX inline preview (LaTeX style and docs)
Group: 		%{commongroup}

%description common
Does your neck hurt from turning between previewer windows and the
source too often? This Elisp/LaTeX package will render your displayed
LaTeX equations right into the editing window where they belong. 

This package contains the LaTeX style files and the documentation.

%package emacs
Summary:	Emacs/LaTeX inline preview (GNU Emacs lisp files)
Group: 		%{commongroup}
Requires:	%{name}-common = %{version}-%{release}
Requires:	emacs >= 21.1
Requires:	auctex >= 11.0
Obsoletes:	preview-latex

%description emacs
Does your neck hurt from turning between previewer windows and the
source too often? This Elisp/LaTeX package will render your displayed
LaTeX equations right into the editing window where they belong. 

This package contains the lisp modules for GNU Emacs 21.1 or higher.

%package xemacs
Summary:	Emacs/LaTeX inline preview (XEmacs lisp files)
Group: 		%{commongroup}
Requires:	%{name}-common = %{version}-%{release}
Requires:	xemacs >= 21.4.9
Conflicts:      xemacs = 21.4.16

%description xemacs
Does your neck hurt from turning between previewer windows and the
source too often? This Elisp/LaTeX package will render your displayed
LaTeX equations right into the editing window where they belong. 

This package contains the lisp modules for XEmacs 21.4.9 or higher.  

%prep
%setup -c -q

%if %{HAVE_EMACS}
  mkdir emacs
  pushd emacs
  ln -sf ../%{name}-%{version}/* .
  popd
%endif

%if %{HAVE_XEMACS}
  mkdir xemacs
  pushd xemacs
  ln -sf ../%{name}-%{version}/* .
  popd
%endif

%build

for i in *emacs; do
  pushd $i
  # The below will make the package build from a tar straight from CVS
  # NOT RECOMMENDED, but useful for testing!
  test -f ./configure || ./autogen.sh
  # --with-packagedir repairs RedHat XEmacs braindamage texmf-dir
  # moves the installation to a location searched before the (possibly
  # conflicting) system tree.  Unfortunately, this is the site-wide
  # tree that we should not really be touching.  Sigh.
  if [ $i = "emacs" ]; then
    %configure '--with-lispdir=${datadir}/emacs/site-lisp/site-start.d' \
      --with-packagelispdir=../preview '--with-texmf-dir=${prefix}/local/share/texmf'
  else
    %configure --with-xemacs '--with-packagedir=%{xemacspkgconfdir}' '--with-texmf-dir=${prefix}/local/share/texmf'
  fi
  make 'infodir=%{_infodir}'
  cd doc
  make preview-latex.pdf
  popd
done

%install 

rm -rf '%{buildroot}'
for i in *emacs; do
  pushd $i
  if [ $i == "emacs" ]; then 
    # Make directory non-searchable.
    mkdir -p '%{buildroot}%{_datadir}/emacs/site-lisp/preview'
    touch .nosearch
    install -c -m 644 .nosearch \
      '%{buildroot}%{_datadir}/emacs/site-lisp/preview'
    %makeinstall TEXHASH=:
  else
    # XEmacs MANIFEST doesn't get created unless the target dir exists
    mkdir -p %{buildroot}%{xemacspkgdir}/pkginfo
    %makeinstall TEXHASH=:
  fi
  popd
done

# Package documentation in /usr/share/doc/preview-latex-n.n
# rather than /usr/share/doc/preview-latex-common-n.n
%define docs	    %{_defaultdocdir}/%{name}-%{version}
mkdir -p '%{buildroot}%{docs}'
pushd %{name}-%{version}
for i in ChangeLog circ.tex COPYING FAQ INSTALL PROBLEMS README \
    RELEASE TODO doc/preview-latex.pdf; do
  cp -R "$i" '%{buildroot}%{docs}'
done
cp latex/README '%{buildroot}%{docs}/README-preview'

# Remove dir file that has been created by the makeinfo calls because this
# file will not been included in the rpm distribution (make RPM 4.1+ happy)
# Apparently RPM 4.2 removes the file itself?
rm -f '%{buildroot}%{_infodir}/dir'

%clean
rm -rf '%{buildroot}'

%post common
/sbin/install-info '--info-dir=%{_infodir}' '%{_infodir}/preview-latex.info'
texhash /usr/local/share/texmf

%preun common
# $1 is the number of versions of this package installed
# after this uninstallation
if [ $1 -eq 0 ]; then
  /sbin/install-info '--info-dir=%{_infodir}' --delete \
    '%{_infodir}/preview-latex.info'
fi

%files common
%defattr(-,root,root)
%dir %{_prefix}/local/share/texmf/tex/latex/preview
%{_prefix}/local/share/texmf/tex/latex/preview/*.sty
%{_prefix}/local/share/texmf/tex/latex/preview/*.def
%config %{_prefix}/local/share/texmf/tex/latex/preview/*.cfg
%doc %{_prefix}/local/share/texmf/doc/latex/styles/preview.dvi
%doc %{_infodir}/preview-latex.info*
%doc %{docs}

%if %{HAVE_EMACS}
%files emacs
%defattr(-,root,root)
%{_datadir}/emacs/site-lisp/preview
%{_datadir}/emacs/site-lisp/site-start.d/preview-latex.el 
%endif

%if %{HAVE_XEMACS}
%files xemacs
%defattr(-,root,root)
%{xemacspkgdir}/lisp/preview
%{xemacspkgdir}/etc/preview
%verify() %{xemacspkgdir}/pkginfo/MANIFEST.preview
%endif

%changelog
* Wed Jul 28 2004 David Kastrup <dak@gnu.org>
- Remove 8bit-test stuff, some changes to directories.

* Mon Apr 12 2004 David Kastrup <dak@gnu.org>
- bump XEmacs requirements to 21.4.9

* Thu Jan 29 2004 Jan-Åke Larsson <jalar@mai.liu.se>
- add support for SuSE 
   (kudos to Martin Väth <vaeth@mathematik.uni-wuerzburg.de>)

* Wed Aug  7 2002 David Kastrup <David.Kastrup@t-online.de>
- add FAQ

* Tue Apr 16 2002 David Kastrup <David.Kastrup@t-online.de>
- allow split info file, docs now go in preview-latex-n.n

* Mon Apr 15 2002 Jan-Ake Larsson <jalar@imf.au.dk>
- Docs now goes in preview-latex-n.n-n directory

* Wed Apr 10 2002 Jan-Ake Larsson <jalar@imf.au.dk>
- Triple-rpm simplifications

* Sun Mar 31 2002 Jan-Ake Larsson <jalar@imf.au.dk>
- Prepare for 0.7, initial triple rpm attempt

* Sun Mar 10 2002 David Kastrup <David.Kastrup@t-online.de>
- Prepare for 0.6.1

* Tue Feb 19 2002 Jan-Ake Larsson <jalar@imf.au.dk>
- Added site-start.d support and prauctex.cfg config file

* Thu Feb 14 2002 Jan-Ake Larsson <jalar@imf.au.dk>
- Adjusted for 0.6

* Wed Jan 23 2002 Jan-Ake Larsson <jalar@imf.au.dk>
- Initial build.
