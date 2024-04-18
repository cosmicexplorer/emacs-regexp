#!/bin/sh

cat <<EOF
prefix=$1
exec_prefix=\${prefix}
libdir=\${exec_prefix}/lib
sharedlibdir=\${libdir}
includedir=\${prefix}/include

Name: rex
Description: rex regex engine
Version: 0.0.0

Requires:
Cflags: -I\${includedir}
Libs: -L\${libdir} -L\${sharedlibdir} -Wl,-rpath,\${sharedlibdir} -lrex
EOF
