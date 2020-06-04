This proof demonstrates the memory safety of the TaskResumeAll function.  We
assume that task lists are initialized and filled with a few list items. We
also assume that some global variables are set to a nondeterministic value,
except for `uxSchedulerSuspended` which cannot be 0 and `xPendedTicks` which
is either `1` (to unwind a loop in a reasonable amount of time) or `0`.

Configurations available:
 * `default`: The default configuration.
 * `useTickHook1`: The default configuration with `configUSE_TICK_HOOK=1`

This proof is a work-in-progress.  Proof assumptions are described in
the harness.  The proof also assumes the following functions are
memory safe and have no side effects relevant to the memory safety of
this function:

* vApplicationTickHook
* vPortEnterCritical
* vPortExitCritical
* vPortGenerateSimulatedInterrupt
