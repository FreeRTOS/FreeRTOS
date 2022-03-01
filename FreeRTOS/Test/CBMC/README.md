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


Building and running proofs
--------------------------

Currently, only python based builds are supported for the CBMC proofs. The below
section outlines the instructions for the Python based build.

### Prerequisites

You will need Python 3. On Windows, you will need Visual Studio 2019 or later
(in particular, you will need the Developer Command Prompt and NMake). On macOS
and Linux, you will need Make.


### Installing CBMC

- Clone the [CBMC repository](https://github.com/diffblue/cbmc).

- The latest installation instructions can be found on the
  [releases](https://github.com/diffblue/cbmc/releases) page of the CBMC repository.
- Please follow all the installation instructions given for your platform.

- Ensure that you can run the programs `cbmc`, `goto-cc` (or `goto-cl`
  on Windows), and `goto-instrument` from the command line.

### Setting up the proofs

Change into the `proofs` directory and run
```
python3 prepare.py
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
  running the proofs. The patches are used to remove static and volatile qulaifiers
  from the source.
- `include` and `windows` contain header files used by the proofs.
