@echo off
echo Packing the CAPD source files in Windows...
if not exist utils\*.* cd ..
zip -u -9 capd_src utils/obj/
zip -u -9 capd_src lib/ bin/ obj/ obj/*/ -x */CVS/
zip -u -9 -r capd_src * -x .cvsignore */.cvsignore */*/.cvsignore bin/* obj/* obj/*/* utils/obj/* lib/* CVS/* private*/* projects/* */CVS/* */*/CVS/* */*/*/CVS/* doc/html/* doc/rtf/* doc/latex/* doc/man/* _*
