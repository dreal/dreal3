include ${capdMake}/make/common_makefile.mkf

if HAVE_capdkrak
   COND_SUBDIRS=krak
endif

SUBDIRS=auxil $(COND_SUBDIRS)

pkgconfigdir = @PKG_CONFIG_DIR@
pkgconfig_DATA = capdAux.pc
