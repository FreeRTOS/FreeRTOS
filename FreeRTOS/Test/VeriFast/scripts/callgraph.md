# Generate callgraph

## Requirements

  - python3
  - pycparser
  - graphviz/dot
  - [inconsolata](https://fonts.google.com/specimen/Inconsolata)

## Instructions

```
cd scripts
git clone https://github.com/eliben/pycparser.git #< you need this for pycparser's libc headers even if pycparser is installed
mkdir fake_include
touch fake_include/threading.h
gcc -E -I pycparser/utils/fake_libc_include/ -I ../include/ -I fake_include/ ../queue/*.c > out.pp
./callgraph.py > out.dot
dot -Nfontname=inconsolata -Tpng -o callgraph.png out.dot
```
