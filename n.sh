#!/bin/sh
rm -rf CMakeCache.txt CMakeFiles CPackConfig.cmake CPackSourceConfig.cmake cmake_install.cmake
cmake -DCMAKE_BUILD_TYPE=Release -DCMAKE_VERBOSE_MAKEFILE=ON -DCPLEX_STUDIO_DIR= -DCMAKE_INSTALL_PREFIX="$HOME" .
make -j3 && make install
