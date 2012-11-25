AUTOMAKE_OPTIONS = foreign
SUBDIRS = src/opensmt src/realpaver
bin_PROGRAMS = dReal

AM_CPPFLAGS = $(config_includedirs)

dReal_SOURCES = src/main.cpp
dReal_LDFLAGS =

LDADD = src/opensmt/libopensmt.la

ACLOCAL_AMFLAGS=-I m4
