This proof demonstrates the memory safety of the TaskDelete function.  The
initialization for the task to be delete and `pxCurrentTCB` is quite similar
(since the task handle may be NULL, and in that case `pxCurrentTCB` is used).
The task to be deleted requires the stack in the task control block to be
allocated, and the flag for static allocation to be properly set (i.e., valid
values as defined by the macros) Task lists are initialized with these tasks
and nondet. filled with a few more items.  We assume a nondet. value for
`xSchedulerRunning`.

This proof is a work-in-progress.  Proof assumptions are described in
the harness.  The proof also assumes the following functions are
memory safe and have no side effects relevant to the memory safety of
this function:

* vPortCloseRunningThread
* vPortDeleteThread
* vPortEnterCritical
* vPortExitCritical
* vPortGenerateSimulatedInterrupt
