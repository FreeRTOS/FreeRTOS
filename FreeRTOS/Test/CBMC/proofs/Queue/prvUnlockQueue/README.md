This harness proves the memory safety of the prvUnlockQueue function.
It is abstracting away the prvCopyDataToQueue function and task pools and concurrency functions.

This proof is a work-in-progress.  Proof assumptions are described in
the harness.  The proof also assumes the following functions are
memory safe and have no side effects relevant to the memory safety of
this function:

* vPortEnterCritical
* vPortExitCritical
* vTaskMissedYield
* xTaskRemoveFromEventList
