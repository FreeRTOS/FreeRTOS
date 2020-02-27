This proof demonstrates the memory safety of the TaskCreate function.
We initialize task lists, but we set other data structures to
unconstrained (arbitrary) values, including the data structures
`pxCurrentTCB`, `uxCurrentNumberOfTasks`, `pcName` and `pxCreateTask`.
STACK_DEPTH is set to a fixed number (10) since it is not possible to
specify a range.

This proof is a work-in-progress.  Proof assumptions are described in
the harness.  The proof also assumes the following functions are
memory safe and have no side effects relevant to the memory safety of
this function:

* prvTraceGetObjectHandle
* prvTraceGetTaskNumber
* prvTraceSetObjectName
* prvTraceSetPriorityProperty
* prvTraceStoreKernelCall
* prvTraceStoreTaskReady
* pxPortInitialiseStack
* vPortEnterCritical
* vPortExitCritical
* vPortGenerateSimulatedInterrupt
