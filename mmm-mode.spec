Summary: Emacs - Edit different parts of a file in different major modes
Name: mmm-mode
Version: 0.4.7
Release: 1
URL: http://unc.dl.sourceforge.net/sourceforge/mmm-mode
Source0: ${URL}/%{name}-%{version}.tar.gz
License: GPL; Michael Abraham Shulman <viritrilbia@gmail.com>
Group: Applications/Editors
BuildRoot: %{_tmppath}/%{name}-%(id -u -n)
BuildArch: noarch
Requires: emacs

%description
MMM Mode is an add-on package for emacs that enables the user to edit
different parts of a file in different major modes. It is well suited
for editing embedded code and code-generating code.

%prep
%setup -q
%configure

%build
%__make

%install
rm -rf $RPM_BUILD_ROOT
%makeinstall

%clean
rm -rf $RPM_BUILD_ROOT

%files
%defattr(-,root,root)
%doc AUTHORS ChangeLog FAQ INSTALL NEWS README README.Mason TODO 
%{_infodir}/mmm.info*
%{_datadir}/emacs/site-lisp/*.el*

%changelog
* Sat Mar 22 2003  <bishop@flotsam.platypus.bc.ca>
- Initial build.
