Summary:	Proof General  Theorem Prover
Name:		ProofGeneral
Version:	2.0
Release:	1
Group:		Applications/Editors/Emacs
Copyright:	LFCS, University of Edinburgh
Url:		http://www.dcs.ed.ac.uk/proofgen/
Packager:	David Aspinall <da@dcs.ed.ac.uk>
Source:		http://www.dcs.ed.ac.uk/proofgen/dist/ProofGeneral-%{version}.tar.gz
BuildRoot:	/tmp/ProofGeneral-root
Patch:		ProofGeneral.patch
BuildArchitectures: noarch

%description
Proof General is a generic Emacs interface for proof assistants,
suitable for use by pacifists and Emacs lovers alike.
It is supplied ready-customized for LEGO, Coq, and Isabelle.
You can adapt Proof General to other proof assistants if you know a
little bit of Emacs Lisp.

To use Proof General, add the line

   (load-file "/usr/lib/emacs/ProofGeneral/generic/proof-site.el")

to your .emacs file.

%changelog
* Thu Sep 24 1998 David Aspinall <da@dcs.ed.ac.uk>
  First version.

%prep
%setup
%patch -p1
rm -f */*.orig

%build

%install
mkdir -p ${RPM_BUILD_ROOT}/usr/lib/ProofGeneral
cp -pr coq lego isa images generic ${RPM_BUILD_ROOT}/usr/lib/emacs/ProofGeneral

%clean
if [ "X" != "${RPM_BUILD_ROOT}X" ]; then
    rm -rf $RPM_BUILD_ROOT
fi

%files
%attr(-,root,root) %doc BUGS INSTALL doc/*
%attr(0755,root,root) %dir /usr/lib/emacs/ProofGeneral
%attr(0755,root,root) %dir /usr/lib/emacs/ProofGeneral/coq
%attr(-,root,root) %dir /usr/lib/emacs/ProofGeneral/coq/*
%attr(0755,root,root) %dir /usr/lib/emacs/ProofGeneral/lego
%attr(-,root,root) %dir /usr/lib/emacs/ProofGeneral/lego/*
%attr(0755,root,root) %dir /usr/lib/emacs/ProofGeneral/isa
%attr(-,root,root) %dir /usr/lib/emacs/ProofGeneral/isa/*
%attr(0755,root,root) %dir /usr/lib/emacs/ProofGeneral/images
%attr(-,root,root) %dir /usr/lib/emacs/ProofGeneral/images/*
%attr(0755,root,root) %dir /usr/lib/emacs/ProofGeneral/generic
%attr(-,root,root) %dir /usr/lib/emacs/ProofGeneral/generic/*









