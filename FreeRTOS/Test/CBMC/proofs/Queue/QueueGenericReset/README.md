Assuming that the QueueHandel_t is not null and the assumptions made
for QueueGenericCreate hold, this harness proves the memory safety of QueueGenericReset.

This proof is a work-in-progress.  Proof assumptions are described in
the harness.  The proof also assumes the following functions are
memory safe and have no side effects relevant to the memory safety of
this function:

* vPortEnterCritical
* vPortExitCritical
* vPortGenerateSimulatedInterrupt
* xTaskRemoveFromEventList
