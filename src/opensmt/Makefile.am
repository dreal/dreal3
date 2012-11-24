SUBDIRS = parsers egraph smtsolvers cnfizers simplifiers proof common tsolvers api sorts

noinst_LTLIBRARIES = libopensmt.la

libopensmt_la_SOURCES = 
libopensmt_la_LIBADD = parsers/libparsers.la \
		       smtsolvers/libsmtsolvers.la \
		       cnfizers/libcnfizers.la \
		       simplifiers/libsimplifiers.la \
		       common/libcommon.la \
		       proof/libproof.la \
		       tsolvers/libtsolvers.la \
		       egraph/libegraph.la \
		       sorts/libsorts.la \
                       api/libapi.la 

