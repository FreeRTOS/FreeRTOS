The harness proves memory safety of
QueueGenericCreateStatic under the assumption made in the harness.

The principal assumption is that (uxItemSize * uxQueueLength) + sizeof(Queue_t)
does not overflow. Further, ucQueueStorage must only be null iff uxItemSize is null.
In addition, the passed queue storage is assumed to be allocated to the right size.

The configurations for configSUPPORT_DYNAMIC_ALLOCATION set to 0 and 1 are checked.

This proof is a work-in-progress.  Proof assumptions are described in
the harness.  The proof also assumes the following functions are
memory safe and have no side effects relevant to the memory safety of
this function:

* vPortEnterCritical
* vPortExitCritical
