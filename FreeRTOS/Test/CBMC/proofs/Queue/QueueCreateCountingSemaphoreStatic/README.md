Assuming uxMaxCount > 0, uxInitialCount <= uxMaxCount and the reference
to the storage area is not null,
this harness proves the memory safety of QueueCreateCountingSemaphoreStatic.

This proof is a work-in-progress.  Proof assumptions are described in
the harness.  The proof also assumes the following functions are
memory safe and have no side effects relevant to the memory safety of
this function:

* vPortEnterCritical
* vPortExitCritical
