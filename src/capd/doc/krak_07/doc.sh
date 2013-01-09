#!/bin/sh

rm -f refs.dat
export doc_pl_refs=y
./doc.pl Frame
./doc.pl Coord3D
./doc.pl IsomCoord3D

export doc_pl_refs=n
./doc.pl Frame
./doc.pl Coord3D
./doc.pl IsomCoord3D

unset doc_pl_refs
