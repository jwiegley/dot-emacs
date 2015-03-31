%define name    tramp
%define version 2.0.36
%define release 0
%define prefix  /usr

Summary:        Transparent Remote File Access for Emacs
Name:           %{name}
Version:        %{version}
Release:        %{release}
Copyright:      GPL
Group:          Applications/Editors
Source0:        %{name}-%{version}.tar.gz
Distribution:   Build for Redhat 9
Url:            http://www.nongnu.org/tramp/
Packager:       Andrew Taylor <ataylor@its.to>
Prefix:         %{prefix}
BuildRoot:      %{_tmppath}/%{name}-%{version}-buildroot
BuildRequires:  emacs
Requires:       emacs

%description
This is an Emacs extension similar to Ange-FTP, but where Ange-FTP
uses FTP to transfer the files, Tramp uses a shell login. The file
transfer itself is either via uuencode or base64 encoding through the
shell, or via external programs such as rcp or scp.

%prep
rm -rf $RPM_BUILD_ROOT

%setup -q
./configure --prefix=%{prefix}

%build
make RPM_OPT_FLAGS="$RPM_OPT_FLAGS"

%install
mkdir -p $RPM_BUILD_ROOT%{_datadir}/emacs/site-lisp
mkdir -p $RPM_BUILD_ROOT%{_infodir}
make prefix=$RPM_BUILD_ROOT%{prefix}
infodir=$RPM_BUILD_ROOT%{_infodir} install

%clean
rm -rf $RPM_BUILD_ROOT

%files
%defattr (-,root,root)
%doc README CONTRIBUTORS INSTALL
%{_datadir}/emacs/site-lisp/*
%{_infodir}/*

%changelog
* Tue Sep 30 2003 Andrew Taylor <ataylor@its.to>
- Created
