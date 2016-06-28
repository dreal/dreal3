FROM ubuntu
MAINTAINER Fedor Shmarov <f.shmarov@ncl.ac.uk>
VOLUME /usr/local/src/dreal/src
VOLUME /usr/local/src/dreal/bin
RUN apt-get update
RUN apt-get -y install -qq build-essential
RUN apt-get -y install -qq autoconf automake bison flex git libtool make pkg-config python-software-properties texinfo
RUN apt-get -y install -qq cmake
RUN mkdir -p /usr/local/src/dreal/build/release
WORKDIR /usr/local/src/dreal/build/release
COPY build.sh .
ENTRYPOINT /bin/bash build.sh

