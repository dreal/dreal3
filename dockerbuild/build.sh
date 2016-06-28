#!/bin/bash

cmake -DCMAKE_BUILD_TYPE=RELEASE -DBUILD_STATIC_BIN=ON ../../src 
make
