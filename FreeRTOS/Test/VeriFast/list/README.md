# FreeRTOS list proofs

The list predicates and proofs are inspired by and based on the work from
Ferreira et al. (STTT'14).

The main shape predicate is a doubly-linked list segment (DLS), as defined
by Ferreira et al. in Fig 15. A DLS is defined by two `xLIST_ITEM` struct
pointers `n` and `m` (possibly pointing to the same item) which are the start
and end of the segment. We track the item pointers and values within the DLS in
the lists `cells` and `vals`, respectively. Therefore `n` and `m` are the first
and last items of `cells`.

```
          +--+     +--+
 -----n-> |*n| ... |*m| -mnext->
 <-nprev- |  |     |  | <-m-----
          +--+     +--+
          ^-----------^
           DLS(n, nprev, mnext, m)
```

With base case: `n == m` (single item case)

```
          +--+
 -----n-> |*n| -mnext->
 <-nprev- |  | <-n-----
          +--+
          ^--^
          xLIST_ITEM
          DLS(n, nprev, mnext, n)
```

Cons case:

```
          +--+      +--+     +--+
 -----n-> |*n| -o-> |*o| ... |*m| -mnext->
 <-nprev- |  | <-n- |  |     |  | <-m-----
          +--+      +--+     +--+
          ^--^      ^-----------^
          xLIST_ITEM DLS(o, n, mnext, m)

          ^---------------------^
          DLS(n, nprev, mnext, m)
```

A DLS can be made into a well-formed list by joining `n` and `m` into a cycle.
Note that unlike Ferreira et al.'s list shape predicate, we always start with
the sentinel end item to avoid a top-level case-split. So in the following
diagram the start and end of the DLS are `end` and the item-before-end
`endprev`.

```
 .-----------------------------------.
 |     +--------+     +--------+     |
  `--> |*end    | ... |*endprev| ----'
 .---- |        |     |        | <---.
 |     +--------+     +--------+     |
  `----------------------------------'
       ^-----------------------^
        DLS(end, endprev, end, endprev)
```

## References

- Automated Verification of the FreeRTOS Scheduler in HIP/SLEEK\
  João F. Ferreira, Cristian Gherghina, Guanhua He, Shengchao Qin, Wei-Ngan Chin\
  https://joaoff.com/publication/2014/sttt/
