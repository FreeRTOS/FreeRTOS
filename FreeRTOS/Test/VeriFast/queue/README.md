# FreeRTOS queue proofs

In the queue predicates and proofs we use the following variable names.

  - `Storage` : The concrete queue storage of `N*M` bytes. The `buffer`
    predicate, defined in `include/proof/queue.h` allows us to treat the
    storage as a list `contents` of `N` items, each of which is `M` bytes.
  - `N` : queue length (i.e., the maximum number of items the queue can store)
  - `M` : size in bytes of each element
  - `W` : logical index of the write pointer, necessarily between
    `0..(N-1)` such that the write pointer `pcWriteTo == Storage + W * M`.
  - `R` : logical index of the read pointer, necessarily between
    `0..(N-1)` such that the read pointer `pcReadFrom == Storage + R * M`.
  - `K` : number of items currently in the queue corresponding to
    `uxMessagesWaiting`

The `queue` predicate, defined in `include/proof/queue.h`, relates the concrete
queue storage to an abstract list `abs` of `K` items. More precisely, the key
queue invariant is:

```
abs == take(K, rotate_left((R+1)%N, contents)) &*&
W == (R + 1 + K) % N
```

where `(R+1)%N` is the front of the queue, `W` is the back of the queue,
`rotate_left` allows for the wraparound of queue storage, and `take` gives the
first `K` elements.
