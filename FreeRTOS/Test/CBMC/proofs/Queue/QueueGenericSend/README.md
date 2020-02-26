The harness in this folder proves the memory safety of QueueGenericSend
with and without QueueSets. It is abstracting away the task pool and concurrency
related functions and assumes the parameters to be initialized to valid data structures.
Further, prvCopyDataToQueue, prvUnlockQueue and prvNotifyQueueSetContainer are abstracted away.

This proof is a work-in-progress.  Proof assumptions are described in
the harness.  The proof also assumes the following functions are
memory safe and have no side effects relevant to the memory safety of
this function:

* vPortEnterCritical
* vPortExitCritical
* vPortGenerateSimulatedInterrupt
* vTaskInternalSetTimeOutState
* vTaskMissedYield
* vTaskPlaceOnEventList
* vTaskSuspendAll
* xTaskRemoveFromEventList
* xTaskResumeAll
