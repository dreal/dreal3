AUTOMAKE_OPTIONS = foreign
SUBDIRS = src
bin_PROGRAMS = dReal

AM_CPPFLAGS = $(config_includedirs) $(BOOST_CPPFLAGS)
AM_LDFLAGS = $(BOOST_THREADS_LDFLAGS)
LIBS = $(BOOST_THREAD_LIBS)

dReal_SOURCES = src/main.cpp
dReal_LDFLAGS =

LDADD = src/libsolvers.la src/capd_dynsys/capdMake/libcapd/libcapd.a

ACLOCAL_AMFLAGS=-I m4
