This proof demonstrates the memory safety of the TaskSetTimeOutState function.
No assumption is required other than its single argument being non-NULL.

This proof is a work-in-progress.  Proof assumptions are described in
the harness.  The proof also assumes the following functions are
memory safe and have no side effects relevant to the memory safety of
this function:

* vPortEnterCritical
* vPortExitCritical
