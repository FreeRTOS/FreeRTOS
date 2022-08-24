This proof demonstrates ubounded memory safety of the ListInsert function.
The proof is a work in progress since it only works for lists up to 
size 15. The bottleneck is mainly in the memory allocations that need
to be made in the harness. 

Scalability here is also made worse by the use array-theory.
However, array-theory also enables other proofs to become fully
unbounded, and hence we are committed to using it.

Fortunately, this scalability problem is not too important 
since the ListInsert function is only used in one Task function.
Hence we can proceed with the proofs for the remaining functions.