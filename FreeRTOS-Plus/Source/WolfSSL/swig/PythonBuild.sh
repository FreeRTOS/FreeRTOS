#!/bin/bash
echo
swig -python cyassl.i
pythonIncludes=`python-config --includes`
pythonLibs=`python-config --libs`
gcc -c -fpic cyassl_wrap.c -I$pythonIncludes
gcc -c -fpic cyassl_adds.c 
gcc -shared -flat_namespace  cyassl_adds.o  cyassl_wrap.o -lcyassl $pythonLibs -o _cyassl.so
python runme.py
