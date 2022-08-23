This proof demonstrates bounded memory safety of the TaskResumeAll function.  
The proof only scales to bound 1.

An unbounded proof was not possible because CBMC is missing syntax needed for the assigns clause (see https://issues.amazon.com/V684721005). Further, this proof needs every list element allocated, as well as quantified invariants, both of which don't scale. Hence it is unlikely that we'll be able to get unbounded proofs in the near future.

We assume that task lists are initialized and filled with a few list items. We
also assume that some global variables are set to a nondeterministic value,
except for `uxSchedulerSuspended` which cannot be 0 and `xPendedTicks` which
is either `1` (to unwind a loop in a reasonable amount of time) or `0`.

Configurations available:
 * `default`: The default configuration.
 * `useTickHook1`: The default configuration with `configUSE_TICK_HOOK=1`
