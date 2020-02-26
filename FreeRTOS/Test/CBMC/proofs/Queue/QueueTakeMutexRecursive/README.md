Assuming that the parameter is valid mutex data structure and reasonable
bounded, this harness proves the memory safety of QueueTakeMutexRecursive.
Task pool and concurrency functions are abstracted away and replaced with
required stubs to drive coverage.

This proof is a work-in-progress.  Proof assumptions are described in
the harness.  The proof also assumes the following functions are
memory safe and have no side effects relevant to the memory safety of
this function:

* pvTaskIncrementMutexHeldCount
* vPortEnterCritical
* vPortExitCritical
* vPortGenerateSimulatedInterrupt
* vTaskMissedYield
* vTaskPlaceOnEventList
* vTaskPriorityDisinheritAfterTimeout
* vTaskSuspendAll
* xTaskGetCurrentTaskHandle
* xTaskPriorityDisinherit
* xTaskPriorityInherit
* xTaskRemoveFromEventList
* xTaskResumeAll
