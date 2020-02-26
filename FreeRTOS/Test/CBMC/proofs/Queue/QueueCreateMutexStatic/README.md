Given that the passed mutex storage area is not null, the QueueCreateMutexStatic
function is memory safe.

Otherwise an assertion violation is triggered.

This proof is a work-in-progress.  Proof assumptions are described in
the harness.  The proof also assumes the following functions are
memory safe and have no side effects relevant to the memory safety of
this function:

* vPortEnterCritical
* vPortExitCritical
* vPortGenerateSimulatedInterrupt
* xTaskGetSchedulerState
* xTaskPriorityDisinherit
