This harness proves the memory safety of QueueCreateMutex
for totally unconstrained input.

This proof is a work-in-progress.  Proof assumptions are described in
the harness.  The proof also assumes the following functions are
memory safe and have no side effects relevant to the memory safety of
this function:

* vPortEnterCritical
* vPortExitCritical
* vPortGenerateSimulatedInterrupt
* xTaskGetSchedulerState
* xTaskPriorityDisinherit
* xTaskRemoveFromEventList
