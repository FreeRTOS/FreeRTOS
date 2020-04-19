Assuming the bound declared in the harness, this harness proves the memory
safety the QueueReceiveFromISR abstracting
away the task pool and concurrency related functions.

This proof is a work-in-progress.  Proof assumptions are described in
the harness.  The proof also assumes the following functions are
memory safe and have no side effects relevant to the memory safety of
this function:

* vPortEnterCritical
* vPortExitCritical
* xTaskRemoveFromEventList
