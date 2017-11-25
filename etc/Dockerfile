FROM dockerfile/ubuntu:latest
MAINTAINER David Aspinall

RUN apt-get update

# Install Emacs and Proof General
RUN \
   apt-get install -y emacs && \
   cd /tmp && \
   wget http://proofgeneral.inf.ed.ac.uk/releases/ProofGeneral-latest.tgz && \
   tar -xpzf ProofGeneral-latest.tgz && \
   cd ProofGeneral && \
   make clean; make install && \
   rm -rf /tmp/ProofGeneral*
   
# Get some theorem provers...
RUN \
    apt-get install -y coq

RUN \
    cd /tmp && \
    wget http://isabelle.in.tum.de/dist/Isabelle2014_linux.tar.gz && \
    cd /usr/local && tar -xpzf Isabelle_2014_linux.tar.gz
    
# Cleanup
RUN rm -rf /var/lib/apt/lists*

# Define working directory.
WORKDIR /proofgeneral

# Define default command.
CMD ["proofgeneral"]
