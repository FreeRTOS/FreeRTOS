LIST EQUIVALENCE PROOFS

(TODO: Revise the text.)
This folder contains bounded proofs for the equivalence between our array-list
implementation and the old linked-list implementation.

We use the following notion of 
equivalence between an array-list and linked-list
1) Same number of elements
2) Same pxIndex (i.e. next element in round-robin queue)
3) Same item-value for corresponding elements.

These proofs along with the memory safety proofs of the array-backed
task-scheduler should
be sufficient to prove memory safety of the linked-list-backed
task-scheduler. (RETHINK THIS ARGUMENT.)
