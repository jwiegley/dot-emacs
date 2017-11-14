# Spec file for AUCTeX

# Maintainer: auctex-devel@gnu.org

# Copyright (C) 2002, 2004, 2005, 2006 Free Software Foundation, Inc.

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

%define FOR_SUSE    %{?suse_version:1}%{!?suse_version:0}

%if %{FOR_SUSE}
%define distri       .suse
%define commongroup  Productivity/Editors/Emacs
%define texgroup     Productivity/Publishing/TeX/Utilities
%define xemacspkgdir %{_datadir}/xemacs/xemacs-packages
%else
%define distri       .fedora
%define commongroup  Applications/Editors
%define texgroup     Applications/Publishing
%define xemacspkgdir %{_datadir}/xemacs/site-packages
%endif

Summary: 	Enhanced TeX modes for Emacsen
Name: 		auctex
Version: 	11.86
Release: 	1%{distri}
License: 	GPL
Group: 		%{commongroup}
URL: 		http://www.gnu.org/software/auctex/
Source0:        ftp://ftp.gnu.org/pub/gnu/auctex/%{name}-%{version}.tar.gz
BuildArchitectures: noarch
BuildRoot: 	%{_tmppath}/%{name}-root

%description
AUCTeX is an extensible package that supports writing and formatting TeX files
for most variants of Emacs.  

AUCTeX supports many different TeX macro packages, including AMS-TeX, LaTeX,
Texinfo and basic support for ConTeXt.  Documentation can be found under
/usr/share/doc, e.g. the reference card (tex-ref.pdf) and the FAQ.  The AUCTeX
manual is available in Emacs info (C-h i d m AUCTeX RET).  On the AUCTeX home
page, we provide manuals in various formats.

This version of AUCTeX comes with preview-latex, an addictive productivity
tool providing a fine-grained interactive folding WYSIWYG display in the
source buffer.

%package emacs
Summary: 	Enhanced TeX modes for GNU Emacs
Group:          %{commongroup}
Requires: 	emacs >= 21
Obsoletes:      ge_auc emacs-auctex auctex preview-latex-emacs
Conflicts:      emacspeak < 18
Provides:       auctex

%description emacs
AUCTeX is an extensible package that supports writing and formatting TeX files
for most variants of Emacs.  

AUCTeX supports many different TeX macro packages, including AMS-TeX, LaTeX,
Texinfo and basic support for ConTeXt.  Documentation can be found under
/usr/share/doc, e.g. the reference card (tex-ref.pdf) and the FAQ.  The AUCTeX
manual is available in Emacs info (C-h i d m AUCTeX RET).  On the AUCTeX home
page, we provide manuals in various formats.

This package is for GNU Emacs.  XEmacs users should use the package system for
installation.

The package enables AUCTeX modes system-wide.  The README file
contains information how users may override this choice.

%package -n preview-tetex
Summary:       LaTeX files for preview.sty
Group:         %{texgroup}
Requires:      tetex
Obsoletes:     preview-latex-common
Provides:      preview-tetex preview-latex-common

%description -n preview-tetex
The LaTeX package preview.sty can be used for extracting selected
parts of LaTeX documents into graphics of their own.  Various TeX and
editing applications use this as a subsystem.  AUCTeX by now comes
with its own integrated version of preview-latex and the style files
and does not require this package, and newer versions of teTeX might
already contain preview.sty (in which case the resulting conflict is
probably best solved by not installing this package).

%prep
%setup

%build
# The below will make the package build from a tar straight from Git
# NOT RECOMMENDED, but useful for testing!
test -f ./configure || ./autogen.sh
%configure --with-emacs INSTALL_INFO=: --without-texmf-dir
make
pushd doc
make tex-ref.pdf
popd

%install
rm -rf %{buildroot}
mkdir -p %{buildroot}{%{_datadir}/emacs/site-lisp,%{_infodir}}
%if %{FOR_SUSE}
cat <<EOFA > %{buildroot}%{_datadir}/emacs/site-lisp/suse-start-auctex.el
;; suse-start-auctex.el
;; This file enables AUCTeX globally:
(load "auctex.el" nil t t)
;; See (info "(auctex)Introduction") on how to disable AUCTeX.
EOFA
cat <<EOFP > %{buildroot}%{_datadir}/emacs/site-lisp/suse-start-preview-latex.el
;; suse-start-preview-latex.el
;; This file enables preview-latex globally:
(load "preview-latex.el" nil t t)
EOFP
%else
mkdir -p %{buildroot}%{_datadir}/emacs/site-lisp/site-start.d
%endif
%makeinstall install-docs
mkdir -p %{buildroot}%{_datadir}/texmf/tex/latex/preview
cp -p preview/latex/*.{sty,def,cfg} %{buildroot}%{_datadir}/texmf/tex/latex/preview
mkdir -p %{buildroot}%{_datadir}/texmf/doc/latex/styles
cp -p preview/latex/preview.dvi %{buildroot}%{_datadir}/texmf/doc/latex/styles

%post emacs
/sbin/install-info --info-dir=%{_infodir} %{_infodir}/auctex.info
/sbin/install-info --info-dir=%{_infodir} %{_infodir}/preview-latex.info

%preun emacs
# $1 is the number of versions of this package installed
# after this uninstallation
if [ $1 -eq 0 ]; then
  /sbin/install-info --delete --info-dir=%{_infodir} %{_infodir}/auctex.info
  /sbin/install-info --delete --info-dir=%{_infodir} %{_infodir}/preview-latex.info
fi
%clean
rm -rf %{buildroot}

%post -n preview-tetex
/usr/bin/mktexlsr %{_datadir}/texmf

%postun -n preview-tetex
/usr/bin/mktexlsr %{_datadir}/texmf

%files -n preview-tetex
%defattr(-,root,root)
%{_datadir}/texmf/tex/latex/preview
%config %{_datadir}/texmf/tex/latex/preview/prauctex.cfg
%{_datadir}/texmf/doc/latex/styles/preview.dvi

%files emacs
%defattr(-,root,root)
%doc RELEASE COPYING INSTALL README TODO FAQ CHANGES
%doc doc/tex-ref.pdf
# %doc --parents preview/RELEASE preview/README preview/INSTALL preview/TODO preview/FAQ
%doc %{_infodir}/*
# %exclude %{_infodir}/dir
%{_datadir}/emacs/site-lisp/%{name}
%{_localstatedir}/%{name}
%config %{_datadir}/emacs/site-lisp/tex-site.el
%if %{FOR_SUSE}
%{_datadir}/emacs/site-lisp/auctex.el
%{_datadir}/emacs/site-lisp/preview-latex.el
%{_datadir}/emacs/site-lisp/suse-start-auctex.el
%{_datadir}/emacs/site-lisp/suse-start-preview-latex.el
%else
%{_datadir}/emacs/site-lisp/site-start.d/auctex.el
%{_datadir}/emacs/site-lisp/site-start.d/preview-latex.el
%endif


%changelog
# Shouldn't changelog include changes in the package instead of changes in the
# spec file?

* Tue Jun  6 2006 Reiner Steib  <Reiner.Steib@gmx.de>
- Update to AUCTeX 11.83

* Wed Dec 28 2005 Reiner Steib  <Reiner.Steib@gmx.de>
- Remove bogus preview directory.  Add preview-latex in description.

* Sat Dec 17 2005 Reiner Steib  <Reiner.Steib@gmx.de>
- Update for AUCTeX 11.82.

* Tue May  3 2005 David Kastrup <dak@gnu.org>
- include preview-latex, so outdate other stuff.

* Fri Jan 21 2005 David Kastrup <dak@gnu.org>
- Conflict with outdated Emacspeak versions

* Fri Jan 14 2005 David Kastrup <dak@gnu.org>
- Install and remove auctex.info, not auctex

* Thu Aug 19 2004 David Kastrup <dak@gnu.org>
- Change tex-site.el to overwriting config file mode.  New naming scheme.

* Mon Aug 16 2004 David Kastrup <dak@gnu.org>
- Attempt a bit of SuSEism.  Might work if we are lucky.

* Sat Dec  7 2002 David Kastrup <David.Kastrup@t-online.de>
- Change addresses to fit move to Savannah.

* Mon Apr 15 2002 Jan-Ake Larsson <jalar@imf.au.dk>
- Adjusted TeX-macro-global and put autoactivation in preinstall
  script so that it can be chosen at install time.

* Tue Feb 19 2002 Jan-Ake Larsson <jalar@imf.au.dk>
- Added site-start.el support

* Sat Feb 16 2002 Jan-Ake Larsson <jalar@imf.au.dk>
- Prerelease 11.11
