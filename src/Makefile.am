SUBDIRS = opensmt realpaver capd_dynsys

noinst_LTLIBRARIES = libsolvers.la

AM_CPPFLAGS=$(config_includedirs)

libsolvers_la_SOURCES = nra_solver.cpp icp_solver.cpp #nra_ode_solver.cpp ode_solver.cpp
libsolvers_la_LIBADD = opensmt/libopensmt.la realpaver/librealpaver.la capd_dynsys/capdMake/libcapd/libcapd.a
