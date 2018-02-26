FROM ubuntu
VOLUME /usr/local/src/dreal/tools
VOLUME /usr/local/src/dreal/bin
RUN apt-get update
RUN apt-get -y install software-properties-common 
#RUN add-apt-repository ppa:avsm/ppa -yy
#RUN apt-get update
RUN apt-get -y install -qq build-essential make ocaml opam m4 
RUN opam init
RUN opam config setup -a
RUN eval `opam config env`
RUN opam update
RUN opam install ocamlfind batteries oasis
#RUN export PATH=~/.opam/system/bin:$PATH
RUN ln -s ~/.opam/system/bin/oasis /usr/local/bin
RUN ln -s /usr/bin/* /usr/local/bin
WORKDIR /usr/local/src/dreal/tools
ENTRYPOINT make