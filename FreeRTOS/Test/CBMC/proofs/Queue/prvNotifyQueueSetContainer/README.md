This harness proves the memory safety of the prvNotifyQueuSetContainer method.
It assumes that the queue is initalized to a valid datastructure and added
to a QueueSet. The concurrency functions and task pool functions are abstracted
away. prvCopyDataToQueue is replaced with a stub checking the preconditions
for prvCopyDataToQueue to be sucessful.

This proof is a work-in-progress.  Proof assumptions are described in
the harness.  The proof also assumes the following functions are
memory safe and have no side effects relevant to the memory safety of
this function:

* vPortEnterCritical
* vPortExitCritical
* xTaskRemoveFromEventList
