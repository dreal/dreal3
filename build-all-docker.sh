cd tools
make dist-clean
docker build . -t dreal3-tools
docker run -v `pwd`/../bin:/usr/local/src/dreal/bin -v `pwd`:/usr/local/src/dreal/tools   dreal3-tools 
cd ../dockerbuild
docker build . -t dreal3-build
docker run -v `pwd`/../src:/usr/local/src/dreal/src -v `pwd`/../bin:/usr/local/src/dreal/bin   dreal3-build
cd ..
docker build . -t dreal3
