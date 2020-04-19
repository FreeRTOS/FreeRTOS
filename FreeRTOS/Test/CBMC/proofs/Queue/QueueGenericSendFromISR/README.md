The harness in this folder proves the memory safety of QueueGenericSendFromISR
with and without QueueSets. It is abstracting away the task pool and concurrency
related functions. Further, it uses a stub for prvCopyDataToQueue.

This proof is a work-in-progress.  Proof assumptions are described in
the harness.  The proof also assumes the following functions are
memory safe and have no side effects relevant to the memory safety of
this function:

* vPortEnterCritical
* vPortExitCritical
* xTaskRemoveFromEventList
