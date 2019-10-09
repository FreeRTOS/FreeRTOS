Instruction Tightly Integrated Memory
=====================================

The Instruction Tightly Integrated Memory (ITIM) is an optional feature
on certain SiFive RISC-V CPUs. The ITIM is a memory device which is
optimized in the CoreIP memory heirarchy to provide low-latency
access to instruction memory.

Freedom Metal provides the ability to designate functions to run out of
the ITIM by decorating the functions with the following "decorator":

.. doxygendefine:: METAL_PLACE_IN_ITIM
   :project: metal

For example:

.. code-block:: C

   METAL_PLACE_IN_ITIM
   void my_itim_func() {
      /* This code will run out of the ITIM */
   }

Caveats
-------
The ``METAL_PLACE_IN_ITIM`` decorator tells the toolchain to link the
decorated function into the ITIM memory. However, compiler optimizations
such as function inlining may cause execution to never transfer to
instructions fetched from the ITIM.

If this compiler optimization is not desired, one workaround is to
tell the compiler to not inline the function:

.. code-block:: C

   __attribute__((noinline))
   METAL_PLACE_IN_ITIM
   void my_itim_func() {
      /* This code will run out of the ITIM */
   }

