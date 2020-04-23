CBMC Proof Infrastructure
=========================

This directory contains automated proofs of the memory safety of various parts
of the FreeRTOS codebase. A continuous integration system validates every
pull request posted to the repository against these proofs, and developers can
also run the proofs on their local machines.

The proofs are checked using the
[C Bounded Model Checker](http://www.cprover.org/cbmc/), an open-source static
analysis tool
([GitHub repository](https://github.com/diffblue/cbmc)). This README describes
how to run the proofs on your local clone of a:FR.


Bulding and running proofs
--------------------------

For historical reasons, some of the proofs are built and run using CMake
and CTest. Others use a custom python-based build system. New proofs
should use CMake. This README describes how to build and run both kinds
of proof.


CMake-based build
-----------------

Follow the CBMC installation instructions below.

Suppose that the freertos source tree is located at
`~/src/freertos` and you wish to build the proofs into
`~/build/freertos`. The following three commands build and run
the proofs:

```sh
cmake -S~/src/freertos -B~/build/freertos -DCOMPILER=cbmc
-DBOARD=windows -DVENDOR=pc
cmake --build ~/build/freertos --target all-proofs
cd ~/build/freertos && ctest -L cbmc
```

Alternatively, this single command does the same thing, assuming you
have the Ninja build tool installed:

```sh
ctest --build-and-test                \
    ~/src/freertos             \
    ~/build/freertos           \
    --build-target cbmc               \
    --build-generator Ninja           \
    --build-options                   \
      -DCOMPILER=cbmc                 \
      -DBOARD=windows                 \
      -DVENDOR=pc                     \
    --test-command ctest -j4 -L cbmc --output-on-failure
```



Python-based build
------------------

### Prerequisites

You will need Python 3. On Windows, you will need Visual Studio 2015 or later
(in particular, you will need the Developer Command Prompt and NMake). On macOS
and Linux, you will need Make.


### Installing CBMC

- Clone the [CBMC repository](https://github.com/diffblue/cbmc).

- The canonical compilation and installation instructions are in the
  [COMPILING.md](https://github.com/diffblue/cbmc/blob/develop/COMPILING.md)
  file in the CBMC repository; we reproduce the most important steps for
  Windows users here, but refer to that document if in doubt.
  - Download and install CMake from the [CMake website](https://cmake.org/download).
  - Download and install the "git for Windows" package, which also
    provides the `patch` command, from [here](https://git-scm.com/download/win).
  - Download the flex and bison for Windows package from
    [this sourceforge site](https://sourceforge.net/projects/winflexbison).
    "Install" it by dropping the contents of the entire unzipped
    package into the top-level CBMC source directory.
  - Change into the top-level CBMC source directory and run
    ```
    cmake -H. -Bbuild -DCMAKE_BUILD_TYPE=Release -DWITH_JBMC=OFF
    cmake --build build
    ```

- Ensure that you can run the programs `cbmc`, `goto-cc` (or `goto-cl`
  on Windows), and `goto-instrument` from the command line. If you build
  CBMC with CMake, the programs will have been installed under the
  `build/bin/Debug` directory under the top-level `cbmc` directory; you
  should add that directory to your `$PATH`. If you built CBMC using
  Make, then those programs will have been installed in the `src/cbmc`,
  `src/goto-cc`, and `src/goto-instrument` directories respectively.


### Setting up the proofs

Change into the `proofs` directory. On Windows, run
```
python prepare.py
```
On macOS or Linux, run
```
./prepare.py
```
If you are on a Windows machine but want to generate Linux Makefiles (or vice
versa), you can pass the `--system linux` or `--system windows` options to those
programs.


### Running the proofs

Each of the leaf directories under `proofs` is a proof of the memory
safety of a single entry point in FreeRTOS. The scripts that you ran in the
previous step will have left a Makefile in each of those directories. To
run a proof, change into the directory for that proof and run `nmake` on
Windows or `make` on Linux or macOS. The proofs may take some time to
run; they eventually write their output to `cbmc.txt`, which should have
the text `VERIFICATION SUCCESSFUL` at the end.


### Proof directory structure

This directory contains the following subdirectories:

- `proofs` contains the proofs run against each pull request
- `patches` contains a set of patches that get applied to the codebase prior to
  running the proofs
- `include` and `windows` contain header files used by the proofs.
