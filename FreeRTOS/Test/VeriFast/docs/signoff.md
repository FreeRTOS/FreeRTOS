# FreeRTOS VeriFast Proof Signoff

Verification tool: VeriFast (code-level proof)

Proofs: `queue/` and `list`

Implementation: Kernel queue data structure (`queue.c`) and list data structure (`list.c`)

Specification / Properties:
  - *Memory safety*: the implementation only accesses valid memory. In the case
    of the queue, this is true under any arbitrary number of tasks or ISRs.
  - *Thread safety*: in the case of the queue, tasks and ISRs only update
    objects that they own via proper synchronization.
  - *Functional correctness*: the queue and list implementations behave like an
    abstract queue and list. In the case of the queue, this is true under any
    arbitrary number of tasks or ISRs.

## Queue proof assumptions

Generally, we assume well-behaved clients; the correctness of underlying
primitives (memory allocation, task scheduling, scheduler suspension); and
assumptions about the system.

  - Well-behaved client: all client tasks and ISRs use the queue API in a
    manner that adheres to the specification. A badly-behaved client can
    invalidate the proven properties. For example, a client that reads or
    writes to the queue storage directly, without masking interrupts, is racy
    and no longer thread safe. The specification forbids this behavior by
    the definition of `queuehandle`, which is a handle to acquire ownership of
    the queue through interrupt masking, but we cannot, in general, enforce
    this behavior since we do not verify client code.

  - Memory safety, thread safety and function contracts for the following
    primitives. For the list and task functions we give a contract that is
    maximal in terms of the queue objects that can be updated, but we do not
    model their function effect (e.g., task blocking and the moving of task
    control blocks between scheduler lists).

        pvPortMalloc
        vPortFree
        memcpy
        vListInitialise
        xTaskRemoveFromEventList
        vTaskMissedYield
        xTaskCheckForTimeOut
        vTaskInternalSetTimeOutState
        vTaskPlaceOnEventList

  - We assume interrupt masking gives strong isolation between tasks and ISRs.
    See Appendix. We further assume the system is configured as required by
    `configASSERT`. For example, interrupts with a priority greater than the
    maximum system call priority must not call queue API functions, otherwise
    the strong isolation guarantee is not maintained.

## List proof assumptions

The list proofs are sequential. We assume the caller of the list API functions
has taken appropriate synchronization steps to avoid races.

## Simplifications

A list of changes to the source code required for the proofs can be generated:

```
make proof_changes
```

A side-by-side diff with respect to the source code can be generated. See
![`scripts/diff_files.md`](../scripts/diff_files.md).

The main queue changes are:

  - merge cTxLock and cRxLock critical regions: under approximate queue
	unlock behavior to atomically set `cTxLock` and `cRxLock` to unlocked in a
    single critical region instead of two separate critical regions. In
	practice, this is not an issue since no ISR function reads-from both
    cTxLock and cRxLock.
  - model single malloc of struct and buffer: split the single malloc of the
    queue struct and storage into two separate mallocs.
  - xQueueGenericReset happens-before concurrent behavior: assume that queue
    initialisation is not concurrent.
  - do not model pxIndex and xListEnd of xLIST struct: ignore these fields in
    the list structs of the queue implementation

The main list changes are:

  - change `MiniList_t` to `ListItem_t`: simplifying assumption on the list
    structure.
  - over-approximate list insert loop: replace a loop in the insert function
    that finds the insertion point with an over-approximating function call.

The following minor changes due to the stricter typing and parser of VeriFast:

  - replacing a union declaration with a struct
  - const pointer declaration
  - stricter casting
  - void cast of unused return value
  - void cast of unused var

The following minor changes due to the modeling of interrupts and scheduler
suspension in the proofs as ghost state.

  - ghost action
  - leak ghost state on deletion

## Configuration

We do not verify across the full configuration space of FreeRTOS. In
particular, the queue proofs do not apply when the following options are
enabled:

  - `configUSE_QUEUE_SETS`
  - `configSUPPORT_STATIC_ALLOCATION`

For both the queue and list proofs we assume that coverage and tracing
macros are no-ops.

## Trusted computing base

  - Soundness of verification tools: VeriFast, Redux prover
  - C Compiler, because the verification is at the C code-level and the
    properties proved may not be preserved by compilation.

## References

[N1570] ISO/IEC. Programming languages – C. International standard 9899:201x,
2011

## Appendix

Assumption on strong isolation induced by interrupt masking and scheduler
suspension for queue proofs. Informally, we need the following:

```
// Initially *data == 0
// Task 1
taskENTER_CRITICAL()
*data = 1;
*data = 2;
taskEXIT_CRITICAL()

// ISR or Task 2
r0 = *data; //< guaranteed to read 0 or 2, never 1
```
