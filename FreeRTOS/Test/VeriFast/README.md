# FreeRTOS VeriFast proofs

This directory contains unbounded proofs of the FreeRTOS kernel queue and list
data structures. Unbounded proofs mean that these results hold independent of
the length of the queue or list.

Informally, the queue proofs demonstrate that the queue implementation is
memory safe (does not access invalid memory), thread safe (properly
synchronizes accesses) and functionally correct (behaves like a queue) under
any arbitrary number of tasks or ISRs. The list proofs demonstrate that the
list implementation is memory safe and functionally correct.

These properties are proven with the
[VeriFast](https://github.com/verifast/verifast) verifier. See the proof
[signoff](docs/signoff.md) document for more on the proof properties,
assumptions, and simplifications.

## Proof directory structure

We split proofs by data structure into separate proof directories. Each file
within a proof directory is a proof of one or more related API functions. A
proof is the source code of the FreeRTOS implementation with VeriFast
annotations (denoted by special comments `/*@ ... @*/`). A set of common
predicates, functions and lemmas used by all proofs is maintained in the
`include/proof` directory.

  - `queue`: proofs for the FreeRTOS queue data structure
  - `list`: proofs for the FreeRTOS list data structure

The following figure gives the callgraph of the queue proofs. Green=Proven
functions, Blue=Functions modeled by lock invariants (underlying implementation
assumed to provide these atomicity guarantees), Grey=Assumed stubs.

![Queue proof callgraph](docs/callgraph.png?raw=true "Queue proofs")

## Prerequisites

Proof checking needs VeriFast and proof regression further needs make and perl.

We recommend installing VeriFast from the nightly builds on the [VeriFast
GitHub page](https://github.com/verifast/verifast). After unpacking the build
tarball, the `verifast` and `vfide` binaries will be in the directory
`verifast-COMMIT/bin/` where `COMMIT` is the Git commit of the VeriFast build.

Note that for CI we use [VeriFast 19.12](https://github.com/verifast/verifast/releases).

## Proof checking a single proof in the VeriFast IDE

To load a proof in the `vfide` VeriFast IDE:

```
$ /path/to/vfide -I include queue/xQueueGenericSend.c
```

Then click `Verify` and `Verify Program` (or press F5). Note that the following
proofs require arithmetic overflow checking to be turned off (click `Verify`
and uncheck `Check arithmetic overflow`).

  - `queue/create.c`
  - `queue/prvCopyDataToQueue.c`
  - `queue/xQueueGenericSendFromISR.c`
  - `queue/xQueueReceiveFromISR.c`

A successful proof results in the top banner turning green with a statement
similar to: `0 errors found (335 statements verified)`.

## Proof checking a single proof at the command-line

The following is an example of checking a proof using the `verifast`
command-line tool. Turn off arithmetic overflow checking where necessary with
the flag `-disable_overflow_check`.

```
$ /path/to/verifast -I include -c queue/xQueueGenericSend.c
```

A successful proof results in output similar to:

```
queue/xQueueGenericSend.c
0 errors found (335 statements verified)
```

## Running proof regression

The following will check all proofs in the repo along with a statement coverage
regression.

```
$ VERIFAST=/path/to/verifast make
```

If you have made changes to the proofs so the statement coverage no longer
matches then you can temporarily turn off coverage checking:

```
$ VERIFAST=/path/to/verifast NO_COVERAGE=1 make
```

## Annotation burden

VeriFast can emit statistics about the number of source code lines and
annotations. These range from .3-2x annotations per line of source code for the
queue proofs and up to 7x for the list proofs.

```
$ VERIFAST=/path/to/verifast ./scripts/annotation_overhead.sh
```

## Reading a VeriFast proof

VeriFast is a modular deductive verifier using separation logic. A quick
introduction is given by [Jacobs and Piessens][1]. In particular, Section 1
Introduction, gives a high-level overview of the proof technique, which uses
forward symbolic execution over a symbolic heap.

Learning how to use VeriFast will help you read and understand the proofs. The
VeriFast [tutorial][2] is a good guide. You will need to understand:

  - Sec 4. Functions and Contracts
  - Sec 5. Patterns
  - Sec 6. Predicates
  - Sec 7. Recursive Predicates
  - Sec 8. Loops
  - Sec 9. Inductive Datatypes
  - Sec 10. Inductive Datatypes
  - Sec 11. Lemmas

[1]: https://people.cs.kuleuven.be/~bart.jacobs/verifast/verifast.pdf
[2]: https://people.cs.kuleuven.be/~bart.jacobs/verifast/tutorial.pdf

## Contributors

We acknowledge and thank the following contributors:

  - Bart Jacobs, KU Leuven, https://people.cs.kuleuven.be/~bart.jacobs/
  - Aalok Thakkar, University of Pennsylvania, https://aalok-thakkar.github.io/
