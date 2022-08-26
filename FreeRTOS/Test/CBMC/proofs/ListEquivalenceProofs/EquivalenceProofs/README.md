## LIST EQUIVALENCE PROOF

This is a bounded proof (upto list-size 30) for equivalence between the new array-backed list implementation and the old linked-list implementation.

#### Proof Strategy

We are going to build an inductive proof. We assume that we start off with an equivalent array-list and linked-list. Then the harness shows that after any list operation the array-list and linked-list continue to be equivalent.

This harness shows equivalence for all 3 list opertions, depending on which macros are set:
1) ListInsert
2) ListInsertEnd
3) ListRemove


#### Definition of Equivalence

We use the following notion of equivalence between an array-list and linked-list.
1) Same number of elements
2) Same pxIndex (i.e. head element in round-robin queue)
3) Same item-value for corresponding elements.

This is a reasonable defintion of equivalence because these are the properties of the list that are visible to external users of the list.


#### Proof assumptions

In addition to the definition of equivalence listed above, the proof makes the following assumptions in the harness which we list explicitly here:
1. The two lists are initialized correctly.
2. The `pxContainer` field of every list item is set to a valid list. (necessary for ListRemove)


#### Applications of this proof 

(Note: the reasoning in this section can be tricky)

This proof has 2 uses:
1) It gives us confidence to replace the linked-list implementation with the array-list implementation, since nothing will break.
2) The array-linked-list equivalence proof, along with the memory safety proofs of the array-backed task-scheduler should be sufficient to prove memory safety of the linked-list-backed task-scheduler.

Elaborating more on the second use. We have a bounded (up to bound 30) memory safety proof for a linked-list backed task-scheduler because we have all three of:
1) Unbounded proofs for the array-list backed task-scheduler 
2) An array-list-linked-list equivalence proof up to bound 30. 
3) The equivalence proof also runs with the memory safety assertions (cbmc --bounds-check --pointer-check), showing the memory safety of linked-lists up to bound 30.

Alternatively, one can also think of this as 'array-lists' being a stub for 'linked-lists'. Then proving memory safety of the task-scheduler using 'array-list' stub, and proving that the 'array-list' stub is equivalent to the original 'linked-list' code is sufficient.



