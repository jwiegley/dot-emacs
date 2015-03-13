#!/bin/sh
# Provision a unit testing VM.

# Copyright (C) 2013 Sebastian Wiesner

# This program is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.

# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.

# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.

# This script provisions a virtual machine to run EPL unit tests in.  It is used
# to provision on Travis CI as well as on the local Vagrant machine.

# This script must be run as root.

apt-get update -qq -yy

# Install basic tools
apt-get install -qq -y make curl unzip python-software-properties

# Add the Emacs PPA
add-apt-repository -y ppa:cassou/emacs
apt-get update -qq

# Install the Emacs packages
apt-get install -qq -yy emacs23-nox emacs24-nox emacs-snapshot-nox || exit 1

# Install (stable) Cask
cask_archive=/tmp/cask-master.zip
cask_dir=/opt/cask-master
rm -rf "${cask_archive}" "${cask_dir}"
curl -fsSLo "${cask_archive}" https://github.com/cask/cask/archive/master.zip
unzip -qq -d /opt "${cask_archive}" || exit 1
ln -sf "${cask_dir}/bin/cask" /usr/local/bin/cask || exit 1
