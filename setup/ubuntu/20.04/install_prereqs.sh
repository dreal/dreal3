#!/bin/bash
set -euxo pipefail

if [[ "${EUID}" -ne 0 ]]; then
  echo 'This script must be run as root' >&2
  exit 1
fi

apt-get install -y --no-install-recommends software-properties-common || \
    ( (apt-get update || (sleep 30; apt-get update)) && \
	  apt-get install -y --no-install-recommends software-properties-common)
add-apt-repository ppa:dreal/dreal --no-update -y  # For libibex-dev
apt-get update || (sleep 30; apt-get update)
apt-get install -y --no-install-recommends $(tr '\n' ' ' <<EOF
autoconf
automake
bison
cmake
coinor-libclp-dev
flex
g++
git
libfl-dev
libgmp-dev
libtool
make
pkg-config
python
libpython-all-dev
software-properties-common
texinfo
zlib1g-dev
EOF
)
