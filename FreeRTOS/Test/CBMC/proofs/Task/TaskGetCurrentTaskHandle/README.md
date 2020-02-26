This proof demonstrates the memory safety of the TaskGetCurrentTaskHandle
function.  We assume that `pxCurrentTCB` is not NULL and we check that the
return value is not NULL.

This proof is a work-in-progress.  Proof assumptions are described in
the harness.
