SUBDIRS = src

bin_PROGRAMS = dReal

INCLUDES = $(config_includedirs)

opensmt_SOURCES = src/bin/Main.C
opensmt_LDFLAGS =
# -lgmpxx -lgmp

LDADD = src/libopensmt.la -lgmpxx -lgmp
