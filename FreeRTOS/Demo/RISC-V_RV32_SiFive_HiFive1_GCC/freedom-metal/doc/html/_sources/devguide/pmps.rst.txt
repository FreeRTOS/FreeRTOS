Physical Memory Protection
==========================

Physical Memory Protection (PMP) is a part of the RISC-V Privileged Architecture
Specification which discribes the interface for a standard RISC-V memory
protection unit.

The PMP defines a finite number of PMP regions which can be individually configured
to enforce access permissions to a range of addresses in memory. Each PMP region
is configurable with the following options:

.. doxygenstruct:: metal_pmp_config
   :project: metal
   :members:
   :no-link:

Initializing the PMP
--------------------

All PMP-related functions first depend on having a handle to the PMP device:

.. code-block:: C

   struct metal_pmp *pmp = metal_pmp_get_device();
   if(!pmp) {
      /* Failed to get PMP device handle */
   }

PMP initialization is optional and has the effect of disabling all PMP regions,
if possible:

.. code-block:: C

   metal_pmp_init(pmp);

The number of PMP regions available can be retrieved from the PMP device handle:

.. doxygenstruct:: metal_pmp
   :project: metal
   :members:
   :no-link:

Configuring a PMP Region
------------------------

Freedom Metal has a set of APIs for configuring a PMP region. The most generic of these
is

.. doxygenfunction:: metal_pmp_set_region
   :project: metal

This function allows for the configuration of all PMP region settings.

Additional APIs are provided for granularly changing individual PMP region settings.
For example:

.. doxygenfunction:: metal_pmp_set_address
   :project: metal
   :no-link:
.. doxygenfunction:: metal_pmp_lock
   :project: metal
   :no-link:
.. doxygenfunction:: metal_pmp_set_writeable
   :project: metal
   :no-link:

Additional documentation for this API is provided in :doc:`the PMP API reference </apiref/pmp>`.

The RISC-V specification allows implementation of PMP to hard-wire the configuration
values of PMP regions. In these cases, attempts to configure these PMP regions will
fail.

Handling PMP Access Faults
--------------------------

Attempted memory accesses which the PMP is configured to prevent trigger a
CPU exception. These exceptions can be handled by installing a CPU exception
handler for exception codes related to memory access faults.

Additional documentation about creating and registering exception handlers can
be found in :doc:`the Exception Handlers Developer Guide </devguide/exceptions>`.

Additional Documentation
------------------------

Additional documentation about the Physical Memory Protection system and fault
handling on RISC-V systems can be found in
`The RISC-V Privileged ISA Specification v1.10 <https://riscv.org/specifications/privileged-isa/>`_.
