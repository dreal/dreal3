AUTOMAKE_OPTIONS = foreign
SUBDIRS = src
bin_PROGRAMS = dReal

AM_CPPFLAGS = $(config_includedirs)

dReal_SOURCES = src/main.cpp
dReal_LDFLAGS =

LDADD = src/libsolvers.la src/capd_dynsys/capdMake/libcapd/libcapd.a

ACLOCAL_AMFLAGS=-I m4
