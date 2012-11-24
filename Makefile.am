SUBDIRS = src

bin_PROGRAMS = opensmt

INCLUDES = $(config_includedirs)

opensmt_SOURCES = src/bin/Main.C
opensmt_LDFLAGS =
# -lgmpxx -lgmp

LDADD = src/libopensmt.la -lgmpxx -lgmp
