Assuming the parameter passed to QueueMessagesWaiting is a pointer to a Queue_t
struct, this harness proves the memory safety of QueueMessagesWaiting.
The concurrency related functions vPortEnterCritical and vPortExitCritical
are abstracted away.

This proof is a work-in-progress.  Proof assumptions are described in
the harness.  The proof also assumes the following functions are
memory safe and have no side effects relevant to the memory safety of
this function:

* vPortEnterCritical
* vPortExitCritical
