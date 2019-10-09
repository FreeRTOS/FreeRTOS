Interrupt Handlers
==================

The Interrupt Heirarchy
-----------------------

Freedom Metal conceptualizes interrupts as a heirarchy of interrupt controllers.
This heirarchy is established by the interrupt heirarchy of the target platform
itself. Presently, the interrupt heirarchy for a given platform is best documented
by the target's DeviceTree representation, which can be found in
``bsp/<target-name>/design.dts``.

In Freedom Metal, the heirarchy is a tree. The nodes of the tree consist of
``struct metal_interrupt``:

.. doxygenstruct:: metal_interrupt
   :project: metal

And the vertices of the tree consist of interrupt ``id``.

.. digraph:: int_heirarchy_graph

   cpu [label="CPU"];
   cpu_int [label="CPU Interrupt Controller", shape=box];
   timer_int [label="Timer Interrupt Controller", shape=box];
   soft_int [label="Software Interrupt Controller", shape=box];

   cpu -> cpu_int [label="ID = 0"];
   cpu_int -> timer_int [label="ID = timer_id"];
   cpu_int -> soft_int [label="ID = software_id"];

The CPU Interrupt Controller
----------------------------

The CPU interrupt controller is the top of the interrupt heirarchy. It must be
initialized before any other interrupt controllers are initialized. In example:

.. code-block:: C

   struct metal_cpu *cpu0 = metal_get_cpu(0);
   if(!cpu) {
      /* Unable to get CPU handle */
   }
   struct metal_interrupt *cpu_int = metal_cpu_interrupt_controller(cpu0);
   if(!cpu_int) {
      /* Unable to get CPU interrupt handle */
   }
   metal_interrupt_init(cpu_int);

The CPU interrupt must be enabled for the CPU to receive any interrupts, and any
enabled interrupts can be masked by disabling the CPU interrupt.

.. code-block:: C

   int rc = 0;

   /* Enable the CPU interrupt */
   rc = metal_interrupt_enable(cpu_int, 0);
   if(rc != 0) {
      /* Failed to enable the CPU interrupt */
   }

   /* Disable the CPU interrupt */
   rc = metal_interrupt_disable(cpu_int, 0);
   if(rc != 0) {
      /* Failed to disable the CPU interrupt */
   }

Interrupt Handlers
------------------

Interrupt handlers must conform to the following function signature:

.. doxygentypedef:: metal_interrupt_handler_t
   :project: metal

Therefore, an interrupt handler might look like:

.. code-block:: C

   void my_interrupt_handler(int id, void *priv_data) {
      /* Contents of handler */
   }

Registering an Interrupt Handler
--------------------------------

Interrupt handlers are registered with the interrupt controller for the interrupt
they are servicing. For example, if we want to register a CPU timer interrupt:

.. code-block:: C

   struct metal_interrupt *timer_int = metal_cpu_timer_interrupt_controller(cpu0);
   if(!timer_int) {
      /* Failed to get timer interrupt controller */
   }
   metal_interrupt_init(timer_int);

   int timer_id = metal_cpu_timer_get_interrupt_id(cpu0);

   int rc = metal_interrupt_register_handler(timer_int, timer_id, my_interrupt_handler, cpu0);
   if(rc != 0) {
      /* Failed to register interrupt handler */
   }

Additional Documentation
------------------------

Additional documentation for the interrupt handler API can be found in
:doc:`the CPU API reference </apiref/cpu>` and
:doc:`the Interrupt API reference </apiref/interrupt>`.

