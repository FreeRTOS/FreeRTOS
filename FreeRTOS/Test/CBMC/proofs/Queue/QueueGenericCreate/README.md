The harness and configurations in this folder show memory safety of
QueueGenericCreate, given the assumption made in the harness.

The principal assumption is that (uxItemSize * uxQueueLength) + sizeof(Queue_t)
does not overflow.

This proof is a work-in-progress.  Proof assumptions are described in
the harness.  The proof also assumes the following functions are
memory safe and have no side effects relevant to the memory safety of
this function:

* vPortEnterCritical
* vPortExitCritical
