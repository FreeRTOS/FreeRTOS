Assuming the bound described in the harness, this harness proves memory safety
for the QueueReceive function abstracting away
the task pool and concurrency functions.

This proof is a work-in-progress.  Proof assumptions are described in
the harness.  The proof also assumes the following functions are
memory safe and have no side effects relevant to the memory safety of
this function:

* vPortEnterCritical
* vPortExitCritical
* vPortGenerateSimulatedInterrupt
* vTaskMissedYield
* vTaskPlaceOnEventList
* vTaskSuspendAll
* xTaskRemoveFromEventList
* xTaskResumeAll
