# FreeRTOS Kernel Unit Tests

## Prerequisites as tested
GCC
```
gcc: gcc (GCC) 9.2.0
```
LCOV
```
lcov: LCOV version 1.14-6-g40580cd
```
Make
```
GNU Make 3.82
```
Doxygen (optional)
```
1.8.5
```
## How to run
```
$ make help
Usage: $ make <unit>

 where <unit> is one of queue doc all run coverage
```
Explanation
```
$ make queue
```
Would build the kernel queue unit tests and put the executable in build/bin

```
$ make doc
```
Would generate the doxygen documentation in build/doc

```
$ make run
```
Would build all unit tests and runs them one after the other

```
$ make coverage
```
Would build all unit tests, runs them one after the other, then generates html code
coverage and places them in build/coverage with initial file index.html

