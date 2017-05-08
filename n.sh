#!/bin/sh
rm -rf CMakeCache.txt CMakeFiles CPackConfig.cmake CPackSourceConfig.cmake cmake_install.cmake
cmake -DCMAKE_BUILD_TYPE=Release -DCMAKE_VERBOSE_MAKEFILE=ON -DCMAKE_INSTALL_PREFIX="$HOME" -DCPLEX_STUDIO_DIR="$CPLEX_STUDIO_DIR" .
make -j3 && make install
