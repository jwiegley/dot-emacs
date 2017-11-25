#!/usr/bin/env bash

export DEBIAN_FRONTEND=noninteractive

touch /vagrant/provision.log
chown vagrant /vagrant/provision.log
echo '* Starting; see ./provision.log for details.'

echo ""
echo '************************************'
echo '***   Installing base packages   ***'
echo '************************************'

echo '* apt-get update'
add-apt-repository -y ppa:ubuntu-elisp/ppa >> /vagrant/provision.log 2>&1
apt-get -y update >> /vagrant/provision.log 2>&1
echo '* apt-get install (needs to download about 90MB)'
apt-get -y install make m4 patch unzip git aspcud ocaml ocaml-native-compilers camlp4-extra opam emacs virtualbox-guest-dkms virtualbox-guest-utils virtualbox-guest-x11 >> /vagrant/provision.log 2>&1

sudo su vagrant <<-EOF
	cat > ~/gui-setup.sh <<-EOS
		#!/usr/bin/env bash
		apt-get -y install lubuntu-desktop

	    su vagrant <<-EOEOS
			mkdir -p ~/.fonts
			wget -O ~/.fonts/symbola-monospace.ttf https://raw.githubusercontent.com/cpitclaudel/monospacifier/master/fonts/Symbola_monospacified_for_UbuntuMono.ttf
			wget -O /tmp/ubuntu-fonts.zip http://font.ubuntu.com/download/ubuntu-font-family-0.83.zip
			unzip /tmp/ubuntu-fonts.zip -d ~/.fonts/
			fc-cache
		EOEOS
	EOS
	chmod +x ~/gui-setup.sh

	cat >> ~/.profile <<< 'export TERM=xterm-256color'

	echo '************************************'
	echo '*** Downloading and building Coq ***'
	echo '************************************'

	echo '* OPAM init'
	yes | opam init >> /vagrant/provision.log 2>&1
	echo '* OPAM repo add'
	yes | opam repo add coq-core-dev https://coq.inria.fr/opam/core-dev >> /vagrant/provision.log 2>&1
	echo '* OPAM install (will take a while; maybe 30 minutes)'
	yes | opam install -j2 coq.8.5~rc1 >> /vagrant/provision.log 2>&1

	echo ""
	echo '************************************'
	echo '***   Setting up Proof General   ***'
	echo '************************************'

	echo '* git clone'
	rm -rf ~/.emacs.d/lisp/PG
	git clone https://github.com/ProofGeneral/PG ~/.emacs.d/lisp/PG >> /vagrant/provision.log 2>&1
	echo '* make'
	make -C ~/.emacs.d/lisp/PG >> /vagrant/provision.log 2>&1

	cat > ~/.emacs.d/init.el <<-EOS
		(add-to-list 'load-path "~/.emacs.d/lisp/PG/generic")

		(require 'package)
		(add-to-list 'package-archives '("melpa" . "https://melpa.org/packages/"))
		(package-initialize)

		;; Open .v files with Proof General's coq-mode
		(require 'proof-site)

		;; Load company-coq when opening Coq files
		(add-hook 'coq-mode-hook #'company-coq-mode)

		;; Terminal keybindings
		(with-eval-after-load 'coq-mode
		  (define-key company-coq-map (kbd "C-c RET") #'company-coq-proof-goto-point)
		  (define-key company-coq-map (kbd "C-c C-j") #'company-coq-proof-goto-point))

		;; Font fallback
		(when (functionp 'set-fontset-font)
		  (set-face-attribute 'default nil :family "Ubuntu Mono")
		  (set-fontset-font t 'unicode (font-spec :name "Ubuntu Mono"))
		  (set-fontset-font t 'unicode (font-spec :name "Symbola monospacified for Ubuntu Mono") nil 'append))

		;; Basic usability
		(xterm-mouse-mode)
		(load-theme 'tango-dark t)
	EOS

	echo '* package install'
	emacs --batch --load ~/.emacs.d/init.el --eval "(progn (package-refresh-contents) (package-install 'company-coq))" >> /vagrant/provision.log 2>&1

	echo ""
	echo '************************************'
	echo '***        Setup complete        ***'
	echo '************************************'

	echo ""
	echo Log into the VM using ‘vagrant ssh’.
    echo You can now run ‘sudo \~/gui-setup.sh’ in the VM to install a GUI, or start using Coq straight away.
EOF

# Local Variables:
# indent-tabs-mode: t
# End:
