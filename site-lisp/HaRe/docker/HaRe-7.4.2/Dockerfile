#FROM alanz/haskell-ghc-7.4.2-64
FROM alanz/haskell-platform-2012.4-deb64

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

#-----------------------------------------------------------------------
#DOCKER_PASSWORD=password
#echo User: docker Password: $DOCKER_PASSWORD
#DOCKER_ENCRYPYTED_PASSWORD=`perl -e 'print crypt('"$DOCKER_PASSWORD"', "aa"),"\n"'`
# result of above is aajfMKNH1hTm2
#useradd -m -d /home/docker -p $DOCKER_ENCRYPYTED_PASSWORD docker
RUN useradd -m -d /home/docker -p 'aajfMKNH1hTm2' docker
#RUN useradd -m -d /home/docker docker
RUN sed -Ei 's/adm:x:4:/docker:x:4:docker/' /etc/group
RUN adduser docker sudo

# Set the default shell as bash for docker user.
RUN chsh -s /bin/bash docker

#-----------------------------------------------------------------------

RUN sudo -i -u docker bash -c 'echo "export PATH=~/.cabal/bin:$PATH" >> ~/.bashrc'

RUN sudo -i -u docker bash -c 'cabal update'
RUN sudo -i -u docker bash -c 'cabal install cabal-install'
RUN sudo -i -u docker bash -c 'cabal update'
RUN sudo -i -u docker bash -c 'cabal install HaRe'
RUN sudo -i -u docker bash -c 'cabal install Diff hspec silently stringbuilder'

#-----------------------------------------------------------------------

RUN sudo -u docker mkdir /home/docker/emacs.d
#RUN sudo -i -u docker bash -c 'git clone https://github.com/alanz/emacs24-starter-kit.git /home/docker/emacs.d'


#RUN (cd $WD && cabal install --only-dependencies)


#RUN (cd $WD && cabal clean && cabal configure --enable-tests && cabal build)


# Copy the files into the container
ADD . /src

#RUN /src/setup.sh

#RUN /src/startssh.sh

# Expose the ssh port
EXPOSE 22
# Start shell and ssh services.
CMD ["/bin/bash","/src/startssh.sh"]


