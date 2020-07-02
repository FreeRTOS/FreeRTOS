# FreeRTOS queue proofs

In the queue predicates and proofs we use the following variable names.

  - `N` : the queue length (i.e., the maximum number of items the queue can
    store)
  - `M` : the size in bytes of each element
  - `W` : the logical index of the write pointer, necessarily between `0..(N-1)`
  - `R` : the logical index of the read pointer, necessarily between `0..(N-1)`
  - `K` : the number of items currently in the queue

Consequently, the size of the concrete queue storage is `N*M` bytes.  The
`buffer` predicate, defined in `include/proof/queue.h` allows us to treat the
queue storage as a list `contents` of `N` items, each of which is `M` bytes.

The `queue` predicate, defined in `include/proof/queue.h`, relates the concrete
representation to an abstract list `abs` of `K` items. More precisely, the main
queue invariant is:

```
abs == take(K, rotate_left((R+1)%N, contents))
```

where `(R+1)%N` is the front of the queue, `rotate_left` allows for the
wraparound of queue storage, and `take` gives the first `K` elements.
