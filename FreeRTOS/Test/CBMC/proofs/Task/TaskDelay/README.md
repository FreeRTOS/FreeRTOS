This proof demonstrates the unbounded memory safety of the TaskDelay function.  
The proof is a work in progress since it only works for lists up to 
size 30. The bottleneck is mainly in the memory allocations that need
to be made in the harness - can't work around this currently in CBMC.

Scalability here is also made worse by the use array-theory.
However, array-theory also enables other proofs to become fully
unbounded, and hence we are committed to using it.