Exception Handlers
==================

CPU exceptions are the mechanism by which various execution and memory system
errors are handled. When an exception occurs, Freedom Metal will call the
corresponding exception handler function, if one has been registered by the
application.

Initializing the CPU
--------------------

When the user application enters the ``main()`` function, the Freedom Metal
framework has not yet performed the initialization necessary to register
exception handlers. If this initialization is not performed before an exception
occurs, any exception will cause the CPU to spin in a tight loop until reset.

To initialize the Freedom Metal exception handlers, initialize CPU interrupts:

.. code-block:: C

   struct metal_cpu *cpu0 = metal_get_cpu(0);
   if(!cpu) {
      /* There was an error acquiring the CPU hart 0 handle */
   }

   struct metal_interrupt *cpu_int = metal_cpu_interrupt_controller(cpu0);
   if(!cpu_int) {
      /* There was an error acquiring the CPU interrupt controller */
   }

   metal_interrupt_init(cpu_int);

The Freedom Metal interrupt API is further documented in :doc:`/devguide/interrupts`
and :doc:`/apiref/interrupt`.

Defining an Exception Handler
-----------------------------

Exception handlers must conform to the following function signature:

.. doxygentypedef:: metal_exception_handler_t
   :project: metal
   :no-link:

Therefore, an example exception handler might look like:

.. code-block:: C

   void my_exception_handler(struct metal_cpu *cpu, int ecode) {
      /* Contents of handler */
   }

Registering an Exception Handler
--------------------------------

Exception handlers are registered with a given CPU hart for an individual exception
code.

.. code-block:: C

   /* CPU Hart 0's interrupt controller must be initialized
    * if it is not already */
   struct metal_cpu *cpu0 = metal_get_cpu(0);

   int rc = metal_cpu_exception_register(cpu0,
               <my_ecode>, /* Set to your desired value */
               my_exception_handler);
   if(rc != 0) {
      /* Failed to register exception handler */
   }

A single exception handler may be used for multiple exception codes. For this reason,
exception handlers receive the exception code as the ``ecode`` parameter and may use
this to determine how to handle the exception.

Returing Execution after a Faulting Instruction
-----------------------------------------------

The default behavior of a RISC-V CPU is to return execution to the faulting instruction.
If this is not the desired behavior, execution can be returned to the instruction after
the faulting instruction using the following method:

.. code-block:: C

   void return_after_fault(struct metal_cpu *cpu, int ecode)
   {
      /* Get the faulting instruction address */
      uintptr_t epc = metal_cpu_get_exception_pc(cpu);

      /* Get the length of the faulting instruction */
      size_t len = metal_cpu_get_instruction_length(cpu, epc);

      /* Advance stored exception program counter by the
       * instruction length */
      metal_cpu_set_exception_pc(cpu, epc + len);
   }

Additional Documentation
------------------------

Additional documentation for the exception handler API can be found in :doc:`The CPU API Reference </apiref/cpu>`.


