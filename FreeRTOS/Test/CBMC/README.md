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
how to run the proofs on your local clone of FreeRTOS.


Building and running proofs
--------------------------

Currently, only python based builds are supported for the CBMC proofs. The proofs
can be run on Linux and MacOS. Windows users can use [WSL](https://docs.microsoft.com/en-us/windows/wsl).
The below section outlines the instructions for the Python based build.

### Prerequisites

On Windows, you can install WSL using these simple [instructions](https://docs.microsoft.com/en-us/windows/wsl/install).

You will need Python version >= 3.7.
And you will need Make to build and run the proofs.

If you are running on a 64-bit machine, please install the 32-bit version of gcc
libraires. For example, on linux, one would run the following command to install
the libraries: `sudo apt-get install gcc-multilib`

### Installing CBMC

- The latest installation instructions can be found on the
  [releases](https://github.com/diffblue/cbmc/releases) page of the CBMC repository.

- Please follow all the installation instructions given for your platform.

- Ensure that you can run the programs `cbmc`, `goto-cc` (or `goto-cl`
  on Windows), and `goto-instrument` from the command line. If you cannot run these
  commands, please refer to the above instructions to install CBMC.

### Installing CBMC-viewer (to generate the report)

- The latest installation instructions can be found on the
  [releases](https://github.com/awslabs/aws-viewer-for-cbmc/releases) page of the CBMC-viewer repository.

- Please follow all the installation instructions given for your platform.

- Ensure that you can run the programs `cbmc-viewer`. If not, please verify
  that all instructions above have been followed.

### Setting up the proofs

Make sure that all the submodules of the FreeRTOS repository have been cloned. To
clone all the submodules, go to the root of the FreeRTOS repository and run this
command: `git submodule update --init --recursive --checkout`.

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
run a proof, change into the directory for that proof and run `make`.
The proofs may take some time to run.

### Proof results

The `make` command above generates a report in HTML and JSON format. Taking
[TaskCreate](./proofs/Task/TaskCreate) as an example:

* HTML report is generated at `./proofs/Task/TaskCreate/html/html`.
* JSON report is generated at `./proofs/Task/TaskCreate/html/json`.

You can open `./proofs/Task/TaskCreate/html/html/index.html` in any browser to view
the HTML report. You should see `None` under the `Errors` section in case of a
successful run.

### Proof directory structure

This directory contains the following subdirectories:

- `proofs` contains the proofs run against each pull request
- `patches` contains a set of patches that get applied to the codebase prior to
  running the proofs. The patches are used to remove static and volatile qualifiers
  from the source.
- `include` and `windows` contain header files used by the proofs.
