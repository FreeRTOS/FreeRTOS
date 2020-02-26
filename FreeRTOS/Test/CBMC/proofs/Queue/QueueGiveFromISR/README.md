Assuming the xQueue is allocated to a valid memory block and abstracting
away concurrency and task pool related functions, this harness proves the memory
safety of QueueGiveFromISR.

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
