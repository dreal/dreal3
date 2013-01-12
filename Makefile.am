AUTOMAKE_OPTIONS = foreign
SUBDIRS = src/opensmt src/realpaver src/capd_dynsys src
bin_PROGRAMS = dReal

AM_CPPFLAGS = $(config_includedirs)

dReal_SOURCES = src/main.cpp
dReal_LDFLAGS =

LDADD = src/libtheorysolver.la src/capd_dynsys/capdMake/libcapd/libcapd.a

ACLOCAL_AMFLAGS=-I m4
