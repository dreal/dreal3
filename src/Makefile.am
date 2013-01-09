SUBDIRS = capd

noinst_LTLIBRARIES = libtheorysolver.la

AM_CPPFLAGS=$(config_includedirs)

libtheorysolver_la_SOURCES = theory_solver.cpp icp_solver.cpp ode_solver.cpp variable.cpp literal.cpp
libtheorysolver_la_LIBADD = opensmt/libopensmt.la realpaver/librealpaver.la capd/lib/libcapd.a

