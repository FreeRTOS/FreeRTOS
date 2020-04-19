Assuming the bound specified in the harness and abstracting the task pool and
concurrency functions, this harness proves the memory safety of QueueSemaphoreTake.
Some of the task pool functions are used to model concurrent behavior required
to trigger all branches during the model creation.

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
* xTaskPriorityDisinherit
* xTaskPriorityInherit
* xTaskRemoveFromEventList
* xTaskResumeAll
