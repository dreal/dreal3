abs_top_builddir = @abs_top_builddir@
noinst_bindir = $(abs_top_builddir)/test/.bin/
noinst_bin_PROGRAMS = makeTestCases
bin_PROGRAMS = check_0f check_0t check_1f check_2f check_4f check_5f
LDADD = ../libprim/libprim.la
AM_CPPFLAGS = -I..

makeTestCases_SOURCES = makeTestCases.cpp stdFunTestCases.cpp
makeTestCases_CXXFLAGS = -O0
makeTestCases_CFLAGS =

check_0f_SOURCES = check_0f.cpp
check_0t_SOURCES = check_0t.cpp
check_1f_SOURCES = check_1f.cpp
check_2f_SOURCES = check_2f.cpp
check_4f_SOURCES = check_4f.cpp
check_5f_SOURCES = check_5f.cpp

check_0f.cpp: testSet.cpp
check_0t.cpp: testSet.cpp
check_1f.cpp: testSet.cpp
check_2f.cpp: testSet.cpp
check_4f.cpp: testSet.cpp
check_5f.cpp: testSet.cpp

# CLEANFILES = tsAri.cpp  tsBounds.cpp  tsInfo.cpp  tsPredSucc.cpp  tsSetOp.cpp  tsStdFun.cpp  tsUtil.cpp testSet.cpp

testSet.cpp:
	${MAKE} makeTestCases
	./makeTestCases
tsAri.cpp:testSet.cpp
tsBounds.cpp: testSet.cpp
tsInfo.cpp: testSet.cpp
tsPredSucc.cpp: testSet.cpp
tsSetOp.cpp: testSet.cpp
tsStdFun.cpp: testSet.cpp
tsUtil.cpp: testSet.cpp
