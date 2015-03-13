FROM alanz/haskell-platform-2013.2-deb64

MAINTAINER alan.zimm@gmail.com

ENV DEBIAN_FRONTEND noninteractive

#-----------------------------------------------------------------------
# Install emacs and ssh server
RUN echo "deb http://cdn.debian.net/debian/ testing main non-free contrib" >> /etc/apt/sources.list
RUN apt-get update
RUN apt-get -y dist-upgrade
RUN apt-get -y install ssh openssh-server
RUN apt-get -y install sudo
RUN apt-get -y install git
RUN apt-get -y install emacs24

# Copy the files into the container
ADD . /src

RUN /src/setup.sh

#RUN /src/startssh.sh

# Expose the ssh port
EXPOSE 22
# Start shell and ssh services.
CMD ["/bin/bash","/src/startssh.sh"]

# Note: to debug the partial build do the following
# docker run -i -t alanz/HaRe-7.6.3-64 /bin/bash
