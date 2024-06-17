This harness proves the memory safety of the prvNotifyQueueSetContainer method.
It assumes that the queue is initalized to a valid datastructure.
The concurrency functions are abstracted away.

This proof is a work-in-progress.  Proof assumptions are described in
the harness.  The proof also assumes the following functions are
memory safe and have no side effects relevant to the memory safety of
this function:

* vPortEnterCritical
* vPortExitCritical
* xTaskPriorityDisinherit
