# Profiling your application

## Introduction [(from the official gprof doc)](https://sourceware.org/binutils/docs/gprof/Introduction.html#Introduction)
Profiling allows you to learn where your program spent its time and which
functions called which other functions while it was executing.  This information
can show you which pieces of your program are slower than you expected, and
might be candidates for rewriting to make your program execute faster.  It can
also tell you which functions are being called more or less often than you
expected.  This may help you spot bugs that had otherwise been unnoticed.

## Requirements
### gprof
Version as tested: GNU gprof (GNU Binutils) 2.36
### make
Version as tested: GNU Make 3.82
### gcc
Version as tested: gcc (GCC) 11.0.0

## Generating Profiles
```
$ make PROFILE=1
```
Run your application
```
$ ./build/posix_demo
```
Since FreeRTOS and its application never come to an end and typically run
forever.  The user has to kill the application with **Ctrl_C**  when they feel
satisfied that the application achieved its intented task.  Killing the
application will force the profiling file *gmon.out* to be generated
automatically.
In order to make sense of this file, the user has to convert the file with:
```
$ make profile
```
After running the previous command, two (2) profiling files
*prof_call_graph.txt* and *prof_flat.txt* will be generated and placed in
the build directory.
* *prof_call_graph.txt*: The call graph shows which functions called which
others, and how much time each function used when its subroutine calls are
included.
* *prof_flat.txt*: The flat profile shows how much time was spent
executing directly in each function.
In order to understand the outputs generated, the best way is to read the
official documentation of gprof
[here](https://sourceware.org/binutils/docs/gprof/Output.html#Output)


# Run your application with Sanitizers
## Introduction
* AddressSanitizer, a fast memory error detector.  Memory
access instructions are instrumented to detect out-of-bounds and use-after-free
bugs
* LeakSanitizer, a memory leak detector.  This option only matters for linking of
executables and the executable is linked against a library that overrides malloc
and other allocator functions

## Requirements
### gcc
Version as tested: gcc (GCC) 11.0.0
## Building and Running the Application
```
$ make SANITIZE_ADDRESS=1
or
$ make SANITIZE_LEAK=1
```
Then run your program normally.
```
$ ./build/posix_demo
```
If an error is detected by the sanitizer, a report showing the error will be printed to stdout.
