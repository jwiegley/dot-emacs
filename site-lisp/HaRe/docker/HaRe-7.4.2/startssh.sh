#!/bin/sh

#/etc/init.d/ssh start
mkdir /var/run/sshd
# Start the ssh service
/usr/sbin/sshd -D
