include ${capdMake}/make/common_makefile.mkf

pkgconfigdir = @PKG_CONFIG_DIR@

bin_SCRIPTS=
pkgconfig_DATA=
lib_LIBRARIES=

if HAVE_CAPD
bin_SCRIPTS+= capd-config
pkgconfig_DATA+= capd.pc
lib_LIBRARIES+=libcapd.a


extract-libcapd.o: ${wildard ${capd_LIBS}}
	${srcdir}/extract libcapd "${capd_LIBS}"

libcapd.a: extract-libcapd.o
	${srcdir}/create libcapd

endif

if HAVE_CAPD_GUI
bin_SCRIPTS+= capd-gui-config
pkgconfig_DATA+= capd-gui.pc
lib_LIBRARIES+=libcapd-gui.a

extract-libcapd-gui.o: ${wildard ${capd_gui_LIBS}}
	${srcdir}/extract libcapd-gui "${capd_gui_LIBS}"

libcapd-gui.a: extract-libcapd-gui.o
	${srcdir}/create libcapd-gui

endif

if HAVE_MPCAPD
bin_SCRIPTS+= mpcapd-config
pkgconfig_DATA+= mpcapd.pc
lib_LIBRARIES+=libmpcapd.a

extract-libmpcapd.o: ${wildard ${mpcapd_LIBS}}
	${srcdir}/extract libmpcapd "${mpcapd_LIBS}"

libmpcapd.a: extract-libmpcapd.o
	${srcdir}/create libmpcapd


endif

if HAVE_MPCAPD_GUI
bin_SCRIPTS+= mpcapd-gui-config
pkgconfig_DATA+= mpcapd-gui.pc
lib_LIBRARIES+=libmpcapd-gui.a

extract-libmpcapd-gui.o: ${wildard ${mpcapd_gui_LIBS}}
	${srcdir}/extract libmpcapd-gui "${mpcapd_gui_LIBS}"

libmpcapd-gui.a: extract-libmpcapd-gui.o
	${srcdir}/create libmpcapd-gui

endif

all: chmodScripts

chmodScripts:
	chmod +x ${top_capd_build}/bin/*

.PHONY: chmodScripts