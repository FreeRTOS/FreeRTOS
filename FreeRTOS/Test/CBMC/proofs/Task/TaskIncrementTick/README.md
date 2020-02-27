This proof demonstrates the memory safety of the TaskIncrementTick function.
We assume that task lists are initialized and filled with a few list items. We
also assign nondeterministic values to some global variables.

Configurations available:
 * `default`: The default configuration.  `useTickHook1`: The default
 * configuration with `configUSE_TICK_HOOK=1`

This proof is a work-in-progress.  Proof assumptions are described in
the harness.  The proof also assumes the following functions are
memory safe and have no side effects relevant to the memory safety of
this function:

* prvTraceGetTaskNumber
* prvTracePortGetTimeStamp
* prvTraceStoreKernelCallWithNumericParamOnly
* prvTraceStoreTaskReady
* vApplicationTickHook
