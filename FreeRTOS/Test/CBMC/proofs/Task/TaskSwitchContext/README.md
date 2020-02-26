This proof demonstrates the memory safety of the TaskSwitchContext function.
We assume task ready lists to be initialized and filled with one element each,
and `pxCurrentTCB` to be the highest priority task.  We also set
`uxSchedulerSuspended` to a nondeterministic value.

This proof is a work-in-progress.  Proof assumptions are described in
the harness.  The proof also assumes the following functions are
memory safe and have no side effects relevant to the memory safety of
this function:

* prvTraceGetCurrentTaskHandle
* prvTraceGetTaskNumber
* prvTraceStoreTaskswitch
* ulGetRunTimeCounterValue
