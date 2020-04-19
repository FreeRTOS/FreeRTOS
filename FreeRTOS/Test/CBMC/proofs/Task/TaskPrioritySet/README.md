This proof demonstrates the memory safety of the TaskPrioritySet function.  The
initialization for the task to be set and `pxCurrentTCB` is quite similar
(since the task handle may be NULL, and in that case `pxCurrentTCB` is used).
Task lists are initialized with these tasks and nondet. filled with a few more
items.

This proof is a work-in-progress.  Proof assumptions are described in
the harness.  The proof also assumes the following functions are
memory safe and have no side effects relevant to the memory safety of
this function:

* vPortEnterCritical
* vPortExitCritical
* vPortGenerateSimulatedInterrupt
