This proof demonstrates the memory safety of the TaskDelay function.  We assume
that `pxCurrentTCB` is initialized and inserted in one of the ready tasks lists
(with and without another task in the same list). We abstract function
`xTaskResumeAll` by assuming that `xPendingReadyList` is empty and
`xPendedTicks` is `0`. Finally, we assume nondeterministic values for global
variables `xTickCount` and `xNextTaskUnblockTime`, and `pdFALSE` for
`uxSchedulerSuspended` (to avoid assertion failure).

Configurations available:

 * `default`: The default configuration.
 * `useTickHook1`: The default configuration with `INCLUDE_vTaskSuspend=0`

This proof is a work-in-progress.  Proof assumptions are described in
the harness.  The proof also assumes the following functions are
memory safe and have no side effects relevant to the memory safety of
this function:

* vPortEnterCritical
* vPortExitCritical
* vPortGenerateSimulatedInterrupt
