FROM debian

MAINTAINER alan.zimm@gmail.com

ENV DEBIAN_FRONTEND noninteractive

####### GHC 7.6.3 ######################
RUN apt-get update
RUN apt-get install -y wget
RUN apt-get install -y bzip2
RUN apt-get install -y libgmp-dev

RUN wget http://www.haskell.org/ghc/dist/7.6.3/ghc-7.6.3-x86_64-unknown-linux.tar.bz2

RUN tar xvfj ghc-7.6.3-x86_64-unknown-linux.tar.bz2

RUN ln -s /usr/lib/x86_64-linux-gnu/libgmp.so /usr/lib/x86_64-linux-gnu/libgmp.so.3

RUN apt-get install -y libncursesw5 gcc apt-utils
RUN apt-get install -y make

RUN cd ghc-7.6.3 && ./configure
RUN cd ghc-7.6.3 && make install

##### haskell platform 2013.2.0.0 #################

RUN wget http://www.haskell.org/platform/download/2013.2.0.0/haskell-platform-2013.2.0.0.tar.gz

RUN tar xvfz haskell-platform-2013.2.0.0.tar.gz

RUN apt-get install -y zlib1g-dev libgl1-mesa-dev libglu1-mesa-dev freeglut3-dev

RUN apt-get install -y libglc-dev libedit-dev libglw1-mesa libglw1-mesa-dev
# RUN apt-get install -y zlib1g-dev


RUN cd haskell-platform-2013.2.0.0 && ./configure
RUN cd haskell-platform-2013.2.0.0 && make
RUN cd haskell-platform-2013.2.0.0 && make install


# Note: to debug the partial build do the following
# docker run -i -t alanz/haskell-platform-2013.2.0.0-64 /bin/bash
