This proof demonstrates the memory safety of the TaskStartScheduler function.
We assume that buffers for `pxIdleTaskTCB` and `pxTimerTaskTCB` (and their
associated stacks `pxIdleTaskStack` and `pxTimerTaskStack`) have been
previously allocated. The arguments passed by reference to
`vApplicationGetIdleTaskMemory` and `vApplicationGetTimerTaskMemory` are
assigned to these pointers since both functions expect statically-allocated
buffers to be passed.

This proof is a work-in-progress.  Proof assumptions are described in
the harness.  The proof also assumes the following functions are
memory safe and have no side effects relevant to the memory safety of
this function:

* pxPortInitialiseStack
* vConfigureTimerForRunTimeStats
* vPortEnterCritical
* vPortExitCritical
* xPortStartScheduler
