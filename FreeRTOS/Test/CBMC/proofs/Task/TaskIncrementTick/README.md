This proof demonstrates bounded memory safety of the TaskIncrementTick function. The proof only scales to a bound of 2. 

An unbounded proof was not possible because CBMC is missing syntax needed for the assigns clause (see https://issues.amazon.com/V684721005). Further, this proof needs every list element allocated, as well as quantified invariants, both of which don't scale. Hence it is unlikely that we'll be able to get unbounded proofs in the near future.

Configurations available:
 * `default`: The default configuration.  `useTickHook1`: The default
 * configuration with `configUSE_TICK_HOOK=1`
