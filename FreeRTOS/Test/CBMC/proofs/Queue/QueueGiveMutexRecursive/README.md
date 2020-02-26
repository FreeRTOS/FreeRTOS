Assuming that the xMutex parameter is initialized to a valid pointer and
abstracting concurrency and task pool related functions, this harness
proves the memory safety of QueueGiveMutexRecursive.

This proof is a work-in-progress.  Proof assumptions are described in
the harness.  The proof also assumes the following functions are
memory safe and have no side effects relevant to the memory safety of
this function:

* vPortEnterCritical
* vPortExitCritical
* vPortGenerateSimulatedInterrupt
* xTaskGetCurrentTaskHandle
* xTaskGetSchedulerState
* xTaskPriorityDisinherit
* xTaskRemoveFromEventList
