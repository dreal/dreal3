FROM ubuntu
MAINTAINER Fedor Shmarov <f.shmarov@ncl.ac.uk>
VOLUME /usr/local/src/dreal/src
VOLUME /usr/local/src/dreal/bin
RUN apt-get update
RUN apt-get -y install -qq build-essential
RUN apt-get -y install -qq autoconf automake bison flex git libtool make pkg-config python-software-properties texinfo
ADD https://cmake.org/files/v3.7/cmake-3.7.2-Linux-x86_64.sh /cmake-3.7.2-Linux-x86_64.sh
RUN mkdir /opt/cmake
RUN sh /cmake-3.7.2-Linux-x86_64.sh --prefix=/opt/cmake --skip-license
RUN ln -s /opt/cmake/bin/cmake /usr/local/bin/cmake
RUN apt-get -y install -qq libbz2-dev coinor-libclp-dev clang-format glpk-utils libglpk-dev glpk-doc python-glpk
RUN apt-get -y install software-properties-common python-software-properties && \
    add-apt-repository ppa:jonathonf/gcc-7.1 && \
    apt-get update && \
    apt-get -y install gcc-7 g++-7
RUN update-alternatives --install /usr/bin/g++ g++ /usr/bin/g++-7 60 && \
    update-alternatives --install /usr/bin/gcc gcc /usr/bin/gcc-7 60
RUN apt-get -y install python-dev   # for python2.x installs && \
    apt-get -y install python3-dev  # for python3.x installs

RUN mkdir -p /usr/local/src/dreal/build/release
WORKDIR /usr/local/src/dreal/build/release
COPY build.sh .
ENTRYPOINT /bin/bash build.sh
