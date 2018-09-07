#!/bin/bash
echo
swig -python wolfssl.i
pythonIncludes=`python-config --includes`
pythonLibs=`python-config --libs`
gcc -c -fpic wolfssl_wrap.c -I$pythonIncludes
gcc -c -fpic wolfssl_adds.c 
gcc -shared -flat_namespace  wolfssl_adds.o  wolfssl_wrap.o -lwolfssl $pythonLibs -o _wolfssl.so
python runme.py
