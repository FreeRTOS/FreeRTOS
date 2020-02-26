Assuming xQueue and pvItemToQueue are non-null pointers allocated to the right
size, this harness proves the memory safety of QueueGenericPeek. Some of the
task pool behavior is abstracted away. Nevertheless, some of the concurrent
behavior has been modeled to allow full coverage of QueuePeek.

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
