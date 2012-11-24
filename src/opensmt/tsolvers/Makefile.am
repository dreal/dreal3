SUBDIRS = axsolver bvsolver dlsolver emptysolver lrasolver ctsolver

noinst_LTLIBRARIES = libtsolvers.la

INCLUDES=$(config_includedirs)

libtsolvers_la_SOURCES = TSolver.h THandler.C THandler.h
libtsolvers_la_LIBADD = axsolver/libaxsolver.la \
			bvsolver/libbvsolver.la \
			dlsolver/libdlsolver.la \
			lrasolver/liblrasolver.la \
			ctsolver/libctsolver.la \
			emptysolver/libemptysolver.la
