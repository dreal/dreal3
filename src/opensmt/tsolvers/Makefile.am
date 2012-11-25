SUBDIRS = axsolver bvsolver dlsolver emptysolver lrasolver ctsolver

noinst_LTLIBRARIES = libtsolvers.la

AM_CPPFLAGS=$(config_includedirs)

libtsolvers_la_SOURCES = TSolver.h THandler.C THandler.h
libtsolvers_la_LIBADD = emptysolver/libemptysolver.la
