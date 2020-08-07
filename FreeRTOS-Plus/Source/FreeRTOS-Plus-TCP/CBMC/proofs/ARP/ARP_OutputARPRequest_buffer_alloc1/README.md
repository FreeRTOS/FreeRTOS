This is the memory safety proof for ```FreeRTOS_OutputARPRequest```
method combined with the BufferAllocation_1.c allocation strategy.

This proof is a work-in-progress.  Proof assumptions are described in
the harness.  The proof also assumes the following functions are
memory safe and have no side effects relevant to the memory safety of
this function:

* vPortEnterCritical
* vPortExitCritical
* vPortGenerateSimulatedInterrupt
* vAssertCalled
* xTaskGetSchedulerState
* pvTaskIncrementMutexHeldCount
* xTaskRemoveFromEventList
* xTaskPriorityDisinherit

This proof checks ```FreeRTOS_OutputARPRequest``` in multiple configurations.
All assume the memory safety of vNetworkInterfaceAllocateRAMToBuffers.
* The ```config_minimal_configuration``` proof sets
  ```ipconfigUSE_LINKED_RX_MESSAGES=0```.
* The ```config_minimal_configuration_linked_rx_messages``` proof sets
  ```ipconfigUSE_LINKED_RX_MESSAGES=1```.
* The ```minimal_configuration_minimal_packet_size``` proof sets
  ```ipconfigETHERNET_MINIMUM_PACKET_BYTES``` to 50.

All harnesses include the queue.c file, but test only for the happy path.
